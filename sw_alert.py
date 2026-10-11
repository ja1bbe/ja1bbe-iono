#!/usr/bin/env python3
"""
sw_alert.py — 宇宙天気の定時通知と、傾向が変わったときの知らせ（GitHub Actions 用）

・定時通知: 日本時間 0・3・6・9・12・15・18・21時（Kpの3時間区切りと一致）。
  既定は 6〜21時の6回。0時・3時は希望者だけ（返信で選ぶ）
・配信先は、メールへの返信で受け取る知らせを選べる（「受け取る知らせの設定」の節）
・その状況に当てはまるときに「ひとこと解説」を添える（「ひとこと解説」の節）
・国分寺の電離層の値は、同じリポジトリの docs/iono.json（fetch_iono.py が毎時更新）から読む
・傾向の知らせ（夜間も送る）:
    悪化の予告  Bz 30分平均 < -10nT かつ 太陽風 30分平均 >= 500km/s（同じ知らせは3時間あける）
    悪化の確定  Kp 5以上 または NOAA Gスケール 1以上（G1）に達した（Kp 4未満に下がるまで再送しない）
    好転        Kp 4以上を経験した後、Kp 2以下・Bz 30分平均が北向き・太陽風 450km/s未満
    プロトン現象 Sスケールが上がった（段階ごと）
  判定条件と文面は dxcc_notify.py の SpaceWeather._check_alerts に合わせ、悪化の確定を加えたもの。

GitHub は毎回まっさらな環境で動くため、判定に必要な状態を state/sw_state.json に保存する。
状態ファイルが無い最初の1回は、判定の準備だけして傾向の知らせは送らない（誤報防止）。

Secrets（Settings → Secrets and variables → Actions）:
  MAIL_FROM    送信用Gmailアドレス
  MAIL_PASS    そのGmailのアプリパスワード（GitHub専用に発行したもの）
  MAIL_OWNER   管理者のアドレス（--test の送り先）
  SUBSCRIBERS  配信先。カンマまたは改行区切り。全員BCCで送る（追加・削除は管理者だけ）
  PREF_KEY     受け取る知らせの設定を、アドレスではなく番号で保存するための鍵（長い無作為な文字列）
               未設定のときは返信による設定を行わず、全員に既定の知らせを送る
公開リポジトリのActionsの記録は誰でも読めるため、メールアドレスは記録に出さない（人数だけ出す）。

標準ライブラリのみで動作（Python 3.8+）
"""
import argparse
import email
import hashlib
import hmac
import imaplib
import re
import unicodedata
import gzip
import json
import os
import smtplib
import ssl
import sys
import time
import urllib.request
from datetime import datetime, timedelta, timezone
from email import policy
from email.message import EmailMessage
from email.utils import parseaddr

JST = timezone(timedelta(hours=9))
REPORT_HOURS_JST = (0, 3, 6, 9, 12, 15, 18, 21)
DEFAULT_SLOTS = [6, 9, 12, 15, 18, 21]
DEFAULT_PREF = {'slots': DEFAULT_SLOTS, 'worse': True, 'better': True, 'stop': False}
IMAP_MAX_PER_RUN = 50           # 1回に読む返信の上限
REPORT_WAIT_KP_SEC = 45 * 60    # 区切りのKpが出るのを待つ上限。過ぎたら手元の値で送る
REPORT_LATE_SEC = 2 * 3600      # GitHubの遅れでこれ以上ずれたら、その回の定時は送らない
RTSW_STALE_SEC = 30 * 60        # 太陽風・Bzがこれより古ければ判定に使わない（衛星データの途切れ対策）
WORSE_INTERVAL = 3 * 3600
SMTP_CHUNK = 50                 # 1通あたりの宛先数（多いときは分けて送る）
USER_AGENT = 'JA1BBE-space-weather-alert/1.0'
IONO_PATH = 'docs/iono.json'    # fetch_iono.py が書き出す国分寺の値（同じリポジトリ内。NICTへは取りに行かない）
IONO_STALE_SEC = 90 * 60        # 観測からこれ以上経った値には「約○時間前の値」と書き添える

SWPC = 'https://services.swpc.noaa.gov'
SW_URLS = {
    'kp':     SWPC + '/products/noaa-planetary-k-index.json',
    'mag':    SWPC + '/json/rtsw/rtsw_mag_1m.json',
    'wind':   SWPC + '/json/rtsw/rtsw_wind_1m.json',
    'scales': SWPC + '/products/noaa-scales.json',
    'sfi':    SWPC + '/products/10cm-flux-30-day.json',
}

FOOTER = (
    '\n---\n'
    'データ元: NOAA Space Weather Prediction Center（services.swpc.noaa.gov）\n'
    '{iono_src}'
    '観測値は自動処理の結果を含みます。運用の目安としてお使いください。\n'
    '{howto}'
)

HOWTO = (
    '\n■ 受け取る知らせの変更：このメールに返信し、1行目に書いてください\n'
    '  定時を選ぶ     → 受けたい時刻を数字で、間をスペースで区切って　例：0 6 18 21（0時・3時も選べます）\n'
    '  定時をやめる   → 定時なし\n'
    '  悪化の知らせ   → 悪化あり ／ 悪化なし（悪化の予告・地磁気嵐G1以上・プロトン現象）\n'
    '  改善の知らせ   → 改善あり ／ 改善なし（好転）\n'
    '  すべて止める   → 停止　　再開するとき → 再開\n'
    '  今の設定を見る → 設定\n'
    '  数分〜15分ほどで反映し、確認のメールをお送りします。宛先の変更は JA1BBE までご連絡ください。\n'
)


# ---------------------------------------------------------------- ひとこと解説
# その状況に当てはまるときに添える。同じ解説は24時間あけ、定時メールには最大2つまで。
EXPL = {
    'kp':     'Kp指数：地磁気の乱れの大きさを0〜9で表した値です。世界の観測所のデータから3時間ごとに求め、5以上を地磁気嵐（G1）と呼びます。',
    'bz':     'Bz：太陽風が運んでくる磁場の南北の向きです。南向き（マイナス）が続くと地球の磁場とつながり、エネルギーが流れ込んで地磁気が乱れやすくなります。',
    'speed':  '太陽風の速さ：ふだんは毎秒300〜400km程度です。コロナホールからの高速風では600kmを超えることがあり、速い風と南向きのBzが重なると乱れが大きくなります。',
    'polar':  'なぜ北米・ヨーロッパ方面なのか：日本から北米やヨーロッパへの大圏経路は、北極の近くを通ります。地磁気が乱れると、極地方の電離層で電波の吸収や乱れが強まるため、この方面が先に悪くなります。',
    'lowband': 'ローバンドが影響を受けやすい理由：電離層の下の層（D層）での吸収は、周波数が低いほど強くなります（おおよそ周波数の2乗に反比例）。極地方で吸収が強まると、160m・80mが先に弱くなります。',
    'fof2':   'foF2：電離層のF2層が、真上に向けた電波を反射できる最高の周波数です。斜めに飛ぶ電波は、1ホップ約3000kmでこのおよそ3倍までの周波数が届きます。',
    'sfi':    'SFI（太陽電波の強さ）：波長10.7cmの太陽電波の強さで、太陽活動の目安です。高いほど電離層の電子が増え、高いバンドが開きやすくなる傾向があります。',
    'proton': 'プロトン現象（Sスケール）：太陽フレアなどで高エネルギーの陽子が届くと、極地方で電波が強く吸収されます（極冠吸収、PCA）。数日続くことがあります。',
    'rscale': 'Rスケール（デリンジャー現象）：太陽フレアのX線で、昼側のD層が急に強く電離され、HFが数十分〜1時間ほど聞こえにくくなります。夜側の経路には影響しません。',
    'after':  '嵐のあと：地磁気嵐が収まっても、F2層の電子が減ってMUFが下がった状態が、1〜2日続くことがあります。Kpが下がってもすぐに元通りとは限りません。',
    'quiet':  '静かな夜はローバンドの好機：地磁気が静かな夜は、極地方を通る経路での吸収が少なく、ローバンドのDXに有利になりやすい条件です。',
    'rot27':  '27日周期：太陽は約27日で1回自転するため、同じコロナホールからの高速風が、約27日ごとに戻ってくることがあります。前回の乱れの日付が、次の予想の手がかりになります。{date}',
    'l1':     '悪化の予告のしくみ：太陽風の観測衛星は、地球から約150万km太陽寄りの位置（L1点）にいます。毎秒600kmの風なら約40分で地球に届くので、この時間差を使って予告しています。',
}
EXPL_GAP = 24 * 3600            # 同じ解説を再び載せるまでの間隔
EXPL_FALLBACK_GAP = 20 * 3600   # 当てはまる解説がない日に、一般の解説を1つ載せる間隔
EXPL_MAX = 2
EXPL_GENERAL = ('kp', 'bz', 'speed', 'polar', 'lowband', 'fof2', 'sfi', 'quiet', 'rot27', 'l1', 'after', 'proton', 'rscale')
EXPL_FOR_ALERT = {'悪化の予告': ['l1', 'bz'], '悪化（地磁気嵐 G1以上）': ['polar', 'lowband'],
                  'プロトン': ['proton'], '好転': ['quiet']}

# ---------------------------------------------------------------- 取得と解析
def fetch_json(url, timeout=30):
    req = urllib.request.Request(url, headers={'Accept-Encoding': 'gzip', 'User-Agent': USER_AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        data = r.read()
        if r.headers.get('Content-Encoding', '').lower() == 'gzip' or data[:2] == b'\x1f\x8b':
            data = gzip.decompress(data)
    return json.loads(data.decode('utf-8'))


def _ts(s):
    return datetime.fromisoformat(s.replace('Z', '')[:19]).replace(tzinfo=timezone.utc).timestamp()


def parse_kp(data, v):
    """Kpの3時間値。time_tag は3時間区間の始まりの時刻とみなす（記録で要確認）"""
    if data and isinstance(data[0], list):           # 旧形式（1行目が見出し）
        head = data[0]
        data = [dict(zip(head, r)) for r in data[1:]]
    rows = []
    for r in data:
        kp = r.get('Kp', r.get('kp'))
        if kp is not None:
            rows.append((_ts(r['time_tag']), float(kp)))
    rows.sort()
    if rows:
        v['kp'], v['kp_at'] = rows[-1][1], rows[-1][0]
    return rows[-16:]                                 # 直近48時間


def parse_rtsw(data, fields, v):
    act = [r for r in data if isinstance(r, dict) and r.get('active') is True]
    if not act:
        return
    latest_t = max(_ts(r['time_tag']) for r in act)
    for name, col in fields.items():
        vals = sorted((_ts(r['time_tag']), r.get(col)) for r in act if r.get(col) is not None)
        if not vals:
            continue
        v[name] = float(vals[-1][1])
        win = [float(x) for t, x in vals if t > latest_t - 1800]
        if win:
            v[name + '30'] = sum(win) / len(win)
    v['rtsw_at'] = latest_t


def parse_scales(d, v):
    cur = d.get('0', {})
    for k in ('S', 'G', 'R'):
        sc = (cur.get(k) or {}).get('Scale')
        if sc not in (None, ''):
            v[k] = int(sc)
    prob = ((d.get('1') or {}).get('S') or {}).get('Prob')
    if prob not in (None, ''):
        v['S_prob'] = int(prob)


def collect(fetch=fetch_json):
    v, hist, errors = {}, [], []
    for key, url in SW_URLS.items():
        try:
            d = fetch(url)
            if key == 'kp':
                hist = parse_kp(d, v)
            elif key == 'mag':
                parse_rtsw(d, {'bz': 'bz_gsm', 'bt': 'bt'}, v)
            elif key == 'wind':
                parse_rtsw(d, {'speed': 'proton_speed', 'density': 'proton_density'}, v)
            elif key == 'scales':
                parse_scales(d, v)
            elif key == 'sfi':
                rows = [r for r in d if isinstance(r, dict) and r.get('flux') is not None]
                if rows:
                    v['sfi'] = float(rows[-1]['flux'])
        except Exception as e:
            errors.append(f'{key}: {e}')
    return v, hist, errors


# ---------------------------------------------------------------- 表示
def jst(t, fmt='%H:%M'):
    return datetime.fromtimestamp(t, JST).strftime(fmt)


def kp_mark(kp):
    """2.33 → '2+'、3.67 → '4-'、2.0 → '2'（無線家になじみのある表記）"""
    base = int(round(kp))
    frac = kp - base
    return f"{base}{'+' if frac > 0.15 else '-' if frac < -0.15 else ''}"


def kp_str(kp):
    """2.33 → '2.33（2+）'。整数ならそのまま"""
    m = kp_mark(kp)
    return f'{kp:.2f}（{m}）' if m[-1] in '+-' else m


def g_level(kp):
    """Kpに相当するNOAA Gスケール（5→G1 … 9→G5）。表記の段階（5-も5とみなす）で数える"""
    return max(0, min(5, int(round(kp)) - 4))


def rtsw_fresh(v, now):
    return v.get('rtsw_at') is not None and now - v['rtsw_at'] <= RTSW_STALE_SEC


def trend(v, st, now):
    kp = v.get('kp', 0)
    if kp >= 5 or v.get('G', 0) >= 1:
        return '地磁気嵐（G1以上）'
    if kp >= 4:
        return '乱れ中'
    if rtsw_fresh(v, now) and v.get('bz30', 0) < -10 and v.get('speed30', 0) >= 500:
        return '悪化の兆し'
    if st.get('disturbed'):
        return '回復途中'
    return '静穏'


def trend_note(v, st, now):
    """「回復途中」でも、高速の太陽風や強い磁場が残っているときに添える注意の1行（表示のみ。判定は変えない）"""
    if trend(v, st, now) != '回復途中' or not rtsw_fresh(v, now):
        return ''
    if v.get('speed30', 0) >= 500 or v.get('bt', 0) >= 10:
        return '（高速の太陽風や強い磁場が残っており、Bzが南に転じると再び乱れる可能性があります）'
    return ''


def expl_triggers(v, hist, st, now, slot_hour=None):
    """今の値で当てはまる解説を、大事な順に返す"""
    kp = v.get('kp', 0)
    mx = max((k for t, k in hist if t > now - 86400), default=kp)
    fresh = rtsw_fresh(v, now)
    tr = trend(v, st, now)
    keys = []
    if v.get('S', 0) >= 1:
        keys.append('proton')
    if v.get('R', 0) >= 1:
        keys.append('rscale')
    if tr == '悪化の兆し':
        keys.append('l1')
    if kp >= 5 or v.get('G', 0) >= 1:
        keys += ['polar', 'lowband']
    if kp >= 4 or mx >= 5:
        keys += ['kp', 'polar']
    if fresh and v.get('bz30', 0) <= -5:
        keys.append('bz')
    if fresh and v.get('speed30', 0) >= 500:
        keys.append('speed')
    if tr == '回復途中':
        keys.append('after')
    if mx >= 5:
        keys.append('rot27')
    if v.get('sfi', 0) >= 150:
        keys.append('sfi')
    if slot_hour in (18, 21, 0, 3) and kp <= 2 and mx < 3:
        keys.append('quiet')
    out = []
    for k in keys:
        if k not in out:
            out.append(k)
    return out


def expl_text(key, hist, now):
    date = ''
    if key == 'rot27':
        storm = [t for t, k in hist if k >= 5 and t > now - 86400]
        if storm:
            date = f"今回の乱れが高速風によるものなら、次は{jst(storm[-1] + 27 * 86400, '%m月%d日')}ごろが目安です。"
    return EXPL[key].format(date=date)


def explanations(v, hist, st, now, slot_hour=None, forced=(), max_n=EXPL_MAX):
    """メールに添える解説の本文。forced は知らせの種類に応じて必ず載せるもの"""
    shown = st.setdefault('expl_shown', {})
    pick = list(forced)
    for k in expl_triggers(v, hist, st, now, slot_hour):
        if len(pick) >= max_n:
            break
        if k not in pick and now - shown.get(k, 0) >= EXPL_GAP:
            pick.append(k)
    if not pick and slot_hour is not None and now - st.get('expl_fallback', 0) >= EXPL_FALLBACK_GAP:
        k = min(EXPL_GENERAL, key=lambda x: shown.get(x, 0))     # いちばん長く載せていないもの
        pick.append(k)
        st['expl_fallback'] = now
    for k in pick:
        shown[k] = now
    if not pick:
        return ''
    return '\n\n■ ひとこと解説\n' + '\n'.join('・' + expl_text(k, hist, now) for k in pick)


def status_text(v, hist, now):
    L = []
    if 'kp' in v:
        s, e = v['kp_at'], v['kp_at'] + 3 * 3600
        mx = max((k for t, k in hist if t > now - 86400), default=None)
        mx_txt = ''
        if mx is not None:
            mx_txt = f'　24時間の最大 {kp_str(mx)}' + (f'（G{g_level(mx)}相当）' if g_level(mx) >= 1 else '')
        L.append(f"Kp {kp_str(v['kp'])}（{jst(s)}〜{jst(e)}の値）" + mx_txt)
    if 'speed' in v:
        L.append(f"太陽風 {v['speed']:.0f}km/s（30分平均 {v.get('speed30', v['speed']):.0f}）"
                 + (f"　密度 {v['density']:.1f}/cm³" if 'density' in v else ''))
    if 'bz30' in v:
        L.append(f"Bz 30分平均 {v['bz30']:+.1f}nT（{'南向き' if v['bz30'] < 0 else '北向き'}）"
                 + (f"　Bt {v['bt']:.1f}nT" if 'bt' in v else ''))
    if 'rtsw_at' in v:
        L.append(f"（太陽風・Bzは {jst(v['rtsw_at'])} の値"
                 + ('' if rtsw_fresh(v, now) else '。データが途切れており古い値です') + '）')
    if 'sfi' in v:
        L.append(f"SFI {v['sfi']:.0f}")
    sc = [f'{k}{v[k]}' for k in ('R', 'S', 'G') if k in v]
    if sc:
        L.append('NOAAスケール ' + ' / '.join(sc)
                 + (f"　プロトン現象の確率（今日） {v['S_prob']}%" if 'S_prob' in v else ''))
    return '\n'.join(L) if L else '宇宙天気のデータを取得できませんでした。'


def iono_text(now, path=IONO_PATH):
    """iono.json の最新行から国分寺の1行を作る。読めなければ空文字（通知は送る）"""
    try:
        with open(path, encoding='utf-8') as f:
            d = json.load(f)
        r = d['recent'][-1]
        at = _ts(r['time'])
    except Exception as e:
        print('[国分寺] iono.json を読めませんでした:', e)
        return ''
    parts = []
    if r.get('hF2') is not None:
        parts.append(f"h'F2 {r['hF2']:.0f}km")
    elif r.get('hF') is not None:                     # h'F2 が求まらない時間帯は h'F で代用
        parts.append(f"h'F {r['hF']:.0f}km")
    if r.get('foF2') is not None:
        parts.append(f"foF2 {r['foF2']:.1f}MHz")
    if r.get('spreadF'):
        parts.append('Spread-Fの兆候あり')
    if not parts:
        return ''
    age = now - at
    tail = f"（{jst(at, '%m/%d %H:%M')}の値"
    if age >= IONO_STALE_SEC:
        tail += f'、約{age / 60:.0f}分前' if age < 3 * 3600 else f'、約{age / 3600:.0f}時間前'
    return f"電離層（{d.get('name', '国分寺')}）: " + ' / '.join(parts) + tail + '）'


IONO_SOURCE = '電離層: 出典：情報通信研究機構（NICT） 電離圏観測データ https://wdc.nict.go.jp/Ionosphere/index.html\n'


def footer(with_iono, howto=True):
    return FOOTER.format(iono_src=IONO_SOURCE if with_iono else '', howto=HOWTO if howto else '')


def full_text(v, hist, now, howto=True, expl=''):
    """NOAAの値＋国分寺の1行＋ひとこと解説＋フッター"""
    io = iono_text(now)
    return status_text(v, hist, now) + ('\n' + io if io else '') + expl + footer(bool(io), howto)


# ---------------------------------------------------------------- 判定
def check_alerts(v, hist, st, now, first):
    """送るべき知らせを [(種類 worse/better, 件名, 本文)] で返し、st を更新する"""
    out = []
    kp = v.get('kp')
    if kp is None:
        return out
    fresh = rtsw_fresh(v, now)
    bz30, sp30 = (v.get('bz30'), v.get('speed30')) if fresh else (None, None)
    g = v.get('G', 0)
    last = st.setdefault('last_alert', {})

    if first:   # 状態ファイルが無い最初の1回は、準備だけして知らせない
        st['disturbed'] = any(k >= 4 for t, k in hist if t > now - 86400) and kp > 2
        st['g1'] = kp >= 5 or g >= 1
        st['last_s'] = v.get('S', 0)
        return out

    if kp >= 4:
        st['disturbed'] = True

    # 悪化の確定: Kp 5以上 または G1以上
    if kp >= 5 or g >= 1:
        if not st.get('g1'):
            st['g1'] = True
            out.append(('worse', '悪化（地磁気嵐 G1以上）',
                        '地磁気嵐の水準（Kp 5以上 / G1以上）に達しました。北米・ヨーロッパ方面など'
                        '極地方を通る経路は悪く、ローバンドを中心に影響が数時間〜1日ほど続くことがあります。'))
    elif kp < 4:
        st['g1'] = False

    # 好転: Kp 4以上 → 2以下、Bz 30分平均が北向き、太陽風 450km/s 未満
    if (st.get('disturbed') and kp <= 2 and bz30 is not None and bz30 > 0
            and sp30 is not None and sp30 < 450):
        st['disturbed'] = False
        out.append(('better', '好転', '地磁気の乱れが収まり、ローバンドのコンディションが良くなる可能性があります。'))

    # 悪化の予告: Bz 30分平均が -10nT より南向き、かつ太陽風 500km/s 以上
    if (bz30 is not None and sp30 is not None and bz30 < -10 and sp30 >= 500
            and now - last.get('worse', 0) >= WORSE_INTERVAL):
        last['worse'] = now
        out.append(('worse', '悪化の予告',
                    '強い南向きのBzと高速の太陽風が続いています。1時間ほどのうちに地磁気が乱れ、'
                    '北米・ヨーロッパ方面（極地方を通る経路）が悪くなる可能性があります。'))

    # プロトン現象: Sスケールが上がった
    s = v.get('S', 0)
    if s >= 1 and s > st.get('last_s', 0):
        out.append(('worse', f'プロトン現象 S{s}',
                    '太陽プロトン現象が起きています。極地方で電波の吸収（PCA）が強まり、'
                    '北米・ヨーロッパ方面のローバンドは数日悪くなることがあります。'))
    st['last_s'] = s
    return out


def report_slot(now, st):
    """今回送るべき定時の時刻（UTC秒）。無ければ None"""
    d = datetime.fromtimestamp(now, JST)
    past = [h for h in REPORT_HOURS_JST if h <= d.hour]
    if past:
        slot = d.replace(hour=max(past), minute=0, second=0, microsecond=0)
    else:
        slot = (d - timedelta(days=1)).replace(hour=max(REPORT_HOURS_JST), minute=0, second=0, microsecond=0)
    slot_ts = slot.timestamp()
    if st.get('last_report_slot') == slot_ts or now - slot_ts > REPORT_LATE_SEC:
        return None
    return slot_ts


# ---------------------------------------------------------------- 受け取る知らせの設定（返信で変更）
def pref_id(addr, key):
    """アドレスを、鍵がなければ元に戻せない番号にする（公開リポジトリにアドレスを残さないため）"""
    return hmac.new(key.encode(), addr.strip().lower().encode(), hashlib.sha256).hexdigest()[:20]


def get_pref(st, pid):
    p = dict(DEFAULT_PREF)
    p.update((st.get('prefs') or {}).get(pid, {}))
    return p


def wants(p, kind, slot_hour=None):
    if p['stop']:
        return False
    if kind == 'report':
        return slot_hour in p['slots']
    return bool(p.get(kind))


def pref_text(p):
    on = lambda b: '☑' if b else '☐'
    lines = ['現在の設定（JA1BBE 宇宙天気配信）']
    if p['stop']:
        lines.append('■ 配信を止めています（「再開」と返信すると、下の設定で再開します）')
    lines.append(' '.join(f"{on(h in p['slots'])}{h}時" for h in REPORT_HOURS_JST))
    lines.append(f"{on(p['worse'])}悪化の知らせ　{on(p['better'])}改善の知らせ")
    return '\n'.join(lines)


_QUOTE_HEAD = re.compile(r'(wrote:|書きました|のメッセージ|^-{2,}|^_{2,}|^From:|^差出人:|Original Message)', re.I)


def command_line(text):
    """返信の本文から、引用や引用の見出しを除いた最初の1行を取り出す"""
    for ln in text.splitlines():
        t = unicodedata.normalize('NFKC', ln).strip()
        if not t or t.startswith('>'):
            continue
        if _QUOTE_HEAD.search(t):
            return ''
        return t
    return ''


def apply_command(p, line):
    """1行の指示を設定に反映する。(新しい設定, 理解できたか) を返す"""
    p = dict(p)
    line = re.sub(r'(\d+)\s*時', r'\1 ', line)          # 「6時18時」→「6 18」（「定時なし」は崩さない）
    toks = [t for t in re.split(r'[\s,、，・/／]+', line) if t]
    hours, ok = [], False
    for t in toks:
        if t.isdigit() and int(t) in (0, 3, 6, 9, 12, 15, 18, 21, 24):
            hours.append(int(t) % 24)
        elif t in ('定時なし', '定時無し'):
            p['slots'], ok = [], True
        elif t in ('悪化あり', '悪化なし', '改善あり', '改善なし'):
            p['worse' if t.startswith('悪化') else 'better'] = t.endswith('あり')
            ok = True
        elif t in ('停止', '配信停止', '全通知不要'):
            p['stop'], ok = True, True
        elif t == '再開':
            p['stop'], ok = False, True
        elif t == '設定':
            ok = True
    if hours:
        p['slots'], ok = sorted(set(hours)), True
    return p, ok


def _auth_ok(msg):
    """Gmailが付けた送信元の認証結果を見る（なりすまし対策）"""
    res = ' '.join(str(h) for h in (msg.get_all('Authentication-Results') or [])
                   if str(h).strip().startswith('mx.google.com')).lower()
    if 'dmarc=fail' in res:
        return False
    return any(k in res for k in ('dmarc=pass', 'dkim=pass', 'spf=pass'))


def _body_text(msg):
    part = msg.get_body(preferencelist=('plain', 'html'))
    if part is None:
        return ''
    text = part.get_content()
    if part.get_content_type() == 'text/html':
        text = re.sub(r'<br\s*/?>|</p>|</div>', '\n', text, flags=re.I)
        text = re.sub(r'<[^>]+>', '', text)
    return text


def process_replies(st, subscribers, key, imap_factory=None, now=None):
    """受信トレイの新しい返信を読み、設定を更新する。確認メールは [(宛先, 件名, 本文)] で返す"""
    user, pw = _secret('MAIL_FROM'), _secret('MAIL_PASS').replace(' ', '')
    connect = imap_factory or (lambda: imaplib.IMAP4_SSL('imap.gmail.com', 993))
    subs = {a.lower(): a for a in subscribers}
    replies = []
    box = connect()
    try:
        box.login(user, pw)
        box.select('INBOX', readonly=True)      # 既読などの印は付けない
        validity = (box.response('UIDVALIDITY')[1] or [b''])[0]
        validity = validity.decode() if isinstance(validity, bytes) else str(validity)
        mem = st.setdefault('imap', {})
        typ, data = box.uid('search', None, 'ALL')
        uids = sorted(int(x) for x in (data[0] or b'').split())
        if mem.get('validity') != validity or 'last_uid' not in mem:
            # 初回（または受信箱が作り直された）: 過去のメールは読まずに、ここから先を対象にする
            mem['validity'], mem['last_uid'] = validity, (uids[-1] if uids else 0)
            print(f'[返信] 受信トレイの読み取りを開始します（既存 {len(uids)}通は対象外）')
            return replies
        new = [u for u in uids if u > mem['last_uid']][:IMAP_MAX_PER_RUN]
        handled = 0
        for u in new:
            mem['last_uid'] = u
            typ, d = box.uid('fetch', str(u), '(BODY.PEEK[])')
            raw = next((x[1] for x in d if isinstance(x, tuple)), None)
            if not raw:
                continue
            msg = email.message_from_bytes(raw, policy=policy.default)
            sender = parseaddr(str(msg.get('From', '')))[1].lower()
            if sender not in subs or not _auth_ok(msg):
                continue
            pid = pref_id(sender, key)
            old = get_pref(st, pid)
            line = command_line(_body_text(msg))
            p, ok = apply_command(old, line)
            st.setdefault('prefs', {})[pid] = {k: p[k] for k in DEFAULT_PREF}
            handled += 1
            if ok:
                head = '設定を受け付けました。' if p != old else '設定を確認しました（変更はありません）。'
            else:
                head = 'ご返信の1行目から、設定の指示を読み取れませんでした。下の書き方をご覧ください。'
            body = head + '\n\n' + pref_text(p) + '\n' + HOWTO
            replies.append((subs[sender], '[宇宙天気] 設定の確認', body))
        print(f'[返信] 新着 {len(new)}通のうち、配信先からの返信 {handled}通を処理しました')
    finally:
        try:
            box.logout()
        except Exception:
            pass
    return replies


# ---------------------------------------------------------------- 送信
def recipients_from_env(name):
    raw = os.environ.get(name, '')
    return [a.strip() for a in raw.replace('\n', ',').split(',') if '@' in a]


def _secret(name):
    return (os.environ.get(name) or '').strip()


def _smtp_ssl():
    return smtplib.SMTP_SSL('smtp.gmail.com', 465, context=ssl.create_default_context(), timeout=30)


def _smtp_starttls():
    s = smtplib.SMTP('smtp.gmail.com', 587, timeout=30)
    s.starttls(context=ssl.create_default_context())
    return s


def send_mail(subject, body, rcpts, dry_run=False, personal=False):
    if dry_run:
        print(f'--- [送信しない確認モード] 宛先 {len(rcpts)}件\n件名: {subject}\n{body}')
        return
    user = _secret('MAIL_FROM')
    pw = _secret('MAIL_PASS').replace(' ', '').replace('\u3000', '')   # 表示どおりの空白入りでも通るように
    # 中身は記録に出さず、形だけを確かめる（公開リポジトリの記録は誰でも読める）
    print(f"[送信の準備] MAIL_FROM: {len(user)}文字・gmail.comで終わる: {'はい' if user.endswith('@gmail.com') else 'いいえ'}"
          f" / MAIL_PASS: {len(pw)}文字・半角英小文字だけ: {'はい' if pw.isascii() and pw.isalpha() and pw.islower() else 'いいえ'}"
          f" / 宛先 {len(rcpts)}件")
    if not (user and pw):
        raise SystemExit('MAIL_FROM / MAIL_PASS が設定されていません')
    if not rcpts:
        print('宛先がないため送信しません')
        return
    last = None
    for name, connect in (('SSL 465番', _smtp_ssl), ('STARTTLS 587番', _smtp_starttls)):
        for attempt in (1, 2):
            try:
                with connect() as s:
                    s.login(user, pw)
                    for i in range(0, len(rcpts), SMTP_CHUNK):
                        msg = EmailMessage()
                        msg['From'] = user
                        # 一斉配信は宛先欄を自分にして全員BCC（互いに見えない）。本人あての確認は宛先欄に本人
                        msg['To'] = rcpts[i] if personal and len(rcpts) == 1 else user
                        msg['Subject'] = subject
                        msg.set_content(body)
                        s.send_message(msg, to_addrs=rcpts[i:i + SMTP_CHUNK])
                print(f'送信: {subject}（宛先 {len(rcpts)}件、{name}）')
                return
            except smtplib.SMTPAuthenticationError as e:
                # Gmailが「パスワードが違う」と答えた場合は、再試行しても同じなので止める
                raise SystemExit(f'Gmailがログインを拒否しました（{name}、コード {e.smtp_code}）。'
                                 'MAIL_FROM と MAIL_PASS の組み合わせを確認してください')
            except (smtplib.SMTPException, OSError) as e:
                last = e
                print(f'[送信の再試行] {name} {attempt}回目: {type(e).__name__}: {e}')
                time.sleep(5)
    raise SystemExit(f'Gmailに送信できませんでした（最後のエラー: {type(last).__name__}: {last}）')


# ---------------------------------------------------------------- メイン
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--state', default='state/sw_state.json')
    ap.add_argument('--test', action='store_true', help='現在の状況を MAIL_OWNER にだけ送る（状態は変えない）')
    ap.add_argument('--dry-run', action='store_true', help='送信せず画面に出すだけ')
    a = ap.parse_args()

    now = time.time()
    v, hist, errors = collect()
    for e in errors:
        print('[取得できず]', e)

    first = not os.path.exists(a.state)
    st = {} if first else json.load(open(a.state, encoding='utf-8'))
    before = json.dumps(st, sort_keys=True)

    if a.test:
        rcpts = recipients_from_env('MAIL_OWNER')
        body = (f'これはテスト送信です（{jst(now, "%m月%d日 %H:%M")}）。\n'
                f'傾向: {trend(v, st, now)}{trend_note(v, st, now)}\n\n'
                + full_text(v, hist, now, expl=explanations(v, hist, st, now, slot_hour=-1)))
        send_mail('[宇宙天気] テスト送信', body, rcpts, a.dry_run)
        return

    if 'kp' not in v:
        print('Kpを取得できなかったため、今回は判定しません')
        return

    rcpts = recipients_from_env('SUBSCRIBERS')
    if not rcpts and not a.dry_run:
        print('SUBSCRIBERS が空のため送信しません')
    key = _secret('PREF_KEY')

    # 返信による設定の変更（先に反映してから、今回の知らせを送る）
    if key and rcpts and not a.dry_run:
        try:
            for to, subj, body in process_replies(st, rcpts, key):
                send_mail(subj, body, [to], personal=True)
        except Exception as e:
            print(f'[返信] 読み取りでエラー（知らせの送信は続けます）: {type(e).__name__}: {e}')
        live = {pref_id(r, key) for r in rcpts}       # 配信先から外れた人の設定は消す
        if st.get('prefs'):
            st['prefs'] = {k: p for k, p in st['prefs'].items() if k in live}
    elif not key:
        print('PREF_KEY が未設定のため、返信による設定は行わず全員に既定の知らせを送ります')

    def who(kind, slot_hour=None):
        if not key:
            return [r for r in rcpts if kind != 'report' or slot_hour in DEFAULT_SLOTS]
        return [r for r in rcpts if wants(get_pref(st, pref_id(r, key)), kind, slot_hour)]

    # 傾向の知らせ（夜間も送る）
    for kind, title, msg in check_alerts(v, hist, st, now, first):
        to = who(kind)
        forced = next((ks for name, ks in EXPL_FOR_ALERT.items() if title.startswith(name)), [])
        body = msg + '\n\n' + full_text(v, hist, now, expl=explanations(v, hist, st, now, forced=forced))
        if to or a.dry_run:
            send_mail(f'[宇宙天気] {title}', body, to, a.dry_run)

    # 定時通知
    slot = report_slot(now, st)
    if slot is not None:
        kp_end = v['kp_at'] + 3 * 3600
        if kp_end < slot and now - slot < REPORT_WAIT_KP_SEC:
            print(f'定時 {jst(slot)}: 区切りのKpがまだ出ていないため次回に送ります')
        else:
            h = datetime.fromtimestamp(slot, JST).hour
            to = who('report', h)
            tr = trend(v, st, now)
            subject = f"[宇宙天気] {h}時 Kp{kp_mark(v['kp'])} {tr}"
            body = (f"宇宙天気 定時のお知らせ（{jst(slot, '%m月%d日')} {h}時）\n傾向: {tr}{trend_note(v, st, now)}\n\n"
                    + full_text(v, hist, now, expl=explanations(v, hist, st, now, slot_hour=h)))
            if to or a.dry_run:
                send_mail(subject, body, to, a.dry_run)
            else:
                print(f'定時 {h}時: この時刻を選んでいる配信先はいません')
            st['last_report_slot'] = slot

    if json.dumps(st, sort_keys=True) != before:
        os.makedirs(os.path.dirname(a.state) or '.', exist_ok=True)
        with open(a.state, 'w', encoding='utf-8') as f:
            json.dump(st, f, ensure_ascii=False, indent=1, sort_keys=True)
        print('状態ファイルを更新しました')


if __name__ == '__main__':
    main()
