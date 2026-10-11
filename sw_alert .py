#!/usr/bin/env python3
"""
sw_alert.py — 宇宙天気の定時通知と、傾向が変わったときの知らせ（GitHub Actions 用）

・定時通知: 日本時間 6・9・12・15・18・21時（= UTC 21・0・3・6・9・12時、Kpの3時間区切りと一致）
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
  SUBSCRIBERS  配信先。カンマまたは改行区切り。全員BCCで送る
公開リポジトリのActionsの記録は誰でも読めるため、メールアドレスは記録に出さない（人数だけ出す）。

標準ライブラリのみで動作（Python 3.8+）
"""
import argparse
import gzip
import json
import os
import smtplib
import ssl
import sys
import time
import urllib.request
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage

JST = timezone(timedelta(hours=9))
REPORT_HOURS_JST = (6, 9, 12, 15, 18, 21)
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
    '配信の停止・宛先の変更は JA1BBE までご連絡ください。\n'
)


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


def kp_str(kp):
    """2.33 → '2.33（2+）' のように、無線家になじみのある表記も添える"""
    base = int(round(kp))
    frac = kp - base
    mark = '+' if frac > 0.15 else '-' if frac < -0.15 else ''
    return f'{kp:.2f}（{base}{mark}）' if mark else f'{kp:.0f}'


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


def status_text(v, hist, now):
    L = []
    if 'kp' in v:
        s, e = v['kp_at'], v['kp_at'] + 3 * 3600
        mx = max((k for t, k in hist if t > now - 86400), default=None)
        L.append(f"Kp {kp_str(v['kp'])}（{jst(s)}〜{jst(e)}の値）"
                 + (f'　24時間の最大 {kp_str(mx)}' if mx is not None else ''))
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


def footer(with_iono):
    return FOOTER.format(iono_src=IONO_SOURCE if with_iono else '')


def full_text(v, hist, now):
    """NOAAの値＋国分寺の1行＋フッター"""
    io = iono_text(now)
    return status_text(v, hist, now) + ('\n' + io if io else '') + footer(bool(io))


# ---------------------------------------------------------------- 判定
def check_alerts(v, hist, st, now, first):
    """送るべき知らせを [(件名, 本文)] で返し、st を更新する"""
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
            out.append(('悪化（地磁気嵐 G1以上）',
                        '地磁気嵐の水準（Kp 5以上 / G1以上）に達しました。北米・ヨーロッパ方面など'
                        '極地方を通る経路は悪く、ローバンドを中心に影響が数時間〜1日ほど続くことがあります。'))
    elif kp < 4:
        st['g1'] = False

    # 好転: Kp 4以上 → 2以下、Bz 30分平均が北向き、太陽風 450km/s 未満
    if (st.get('disturbed') and kp <= 2 and bz30 is not None and bz30 > 0
            and sp30 is not None and sp30 < 450):
        st['disturbed'] = False
        out.append(('好転', '地磁気の乱れが収まり、ローバンドのコンディションが良くなる可能性があります。'))

    # 悪化の予告: Bz 30分平均が -10nT より南向き、かつ太陽風 500km/s 以上
    if (bz30 is not None and sp30 is not None and bz30 < -10 and sp30 >= 500
            and now - last.get('worse', 0) >= WORSE_INTERVAL):
        last['worse'] = now
        out.append(('悪化の予告',
                    '強い南向きのBzと高速の太陽風が続いています。1時間ほどのうちに地磁気が乱れ、'
                    '北米・ヨーロッパ方面（極地方を通る経路）が悪くなる可能性があります。'))

    # プロトン現象: Sスケールが上がった
    s = v.get('S', 0)
    if s >= 1 and s > st.get('last_s', 0):
        out.append((f'プロトン現象 S{s}',
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


# ---------------------------------------------------------------- 送信
def recipients_from_env(name):
    raw = os.environ.get(name, '')
    return [a.strip() for a in raw.replace('\n', ',').split(',') if '@' in a]


def send_mail(subject, body, rcpts, dry_run=False):
    if dry_run:
        print(f'--- [送信しない確認モード] 宛先 {len(rcpts)}件\n件名: {subject}\n{body}')
        return
    user, pw = os.environ.get('MAIL_FROM'), os.environ.get('MAIL_PASS')
    if not (user and pw):
        raise SystemExit('MAIL_FROM / MAIL_PASS が設定されていません')
    ctx = ssl.create_default_context()
    with smtplib.SMTP_SSL('smtp.gmail.com', 465, context=ctx, timeout=30) as s:
        s.login(user, pw)
        for i in range(0, len(rcpts), SMTP_CHUNK):
            msg = EmailMessage()
            msg['From'] = user
            msg['To'] = user                  # 宛先欄は自分。配信先は全員BCC（互いに見えない）
            msg['Subject'] = subject
            msg.set_content(body)
            s.send_message(msg, to_addrs=rcpts[i:i + SMTP_CHUNK])
    print(f'送信: {subject}（宛先 {len(rcpts)}件）')


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
                f'傾向: {trend(v, st, now)}\n\n' + full_text(v, hist, now))
        send_mail('[宇宙天気] テスト送信', body, rcpts, a.dry_run)
        return

    if 'kp' not in v:
        print('Kpを取得できなかったため、今回は判定しません')
        return

    rcpts = recipients_from_env('SUBSCRIBERS')
    if not rcpts and not a.dry_run:
        print('SUBSCRIBERS が空のため送信しません')

    # 傾向の知らせ（夜間も送る）
    for title, msg in check_alerts(v, hist, st, now, first):
        body = msg + '\n\n' + full_text(v, hist, now)
        if rcpts or a.dry_run:
            send_mail(f'[宇宙天気] {title}', body, rcpts, a.dry_run)

    # 定時通知
    slot = report_slot(now, st)
    if slot is not None:
        kp_end = v['kp_at'] + 3 * 3600
        if kp_end < slot and now - slot < REPORT_WAIT_KP_SEC:
            print(f'定時 {jst(slot)}: 区切りのKpがまだ出ていないため次回に送ります')
        else:
            tr = trend(v, st, now)
            subject = f"[宇宙天気] {jst(slot, '%H')}時 Kp{v['kp']:.1f} {tr}"
            body = (f"宇宙天気 定時のお知らせ（{jst(slot, '%m月%d日 %H時')}）\n傾向: {tr}\n\n"
                    + full_text(v, hist, now))
            if rcpts or a.dry_run:
                send_mail(subject, body, rcpts, a.dry_run)
            st['last_report_slot'] = slot

    if json.dumps(st, sort_keys=True) != before:
        os.makedirs(os.path.dirname(a.state) or '.', exist_ok=True)
        with open(a.state, 'w', encoding='utf-8') as f:
            json.dump(st, f, ensure_ascii=False, indent=1, sort_keys=True)
        print('状態ファイルを更新しました')


if __name__ == '__main__':
    main()
