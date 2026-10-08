# -*- coding: utf-8 -*-
"""国分寺(TO536)のイオノゾンデ自動読取値(15分値)をNICTから取得し、
直近6時間分を docs/iono.json に書き出す（GitHub Actionsから15分ごとに実行）。

出典：情報通信研究機構（NICT） 電離圏観測データ
https://wdc.nict.go.jp/Ionosphere/index.html
（2026年10月、NICT電離圏観測担当より、出典明記・15分程度の取得間隔での
  個人非営利サイトへの掲載について了承を得て利用）

列の並び・単位・記号の扱いは dxcc_notify.py の Ionosonde クラスと同じ。
"""
import json, os, re, sys, time, calendar, urllib.request
from datetime import datetime, timezone, timedelta

STATION = 'TO536'
URL = 'https://wdc.nict.go.jp/Ionosphere/archive/observation-history/factor-auto-{station}-{year}.sjis.txt'
REFERER = 'https://wdc.nict.go.jp/Ionosphere/archive/isdj_auto_txt.html'
# 取得元が分かる名前でアクセスする（ブラウザを装わない）
UA = 'JA1BBE-ionosphere-nowcast/1.0 (+https://ja1bbe.wixsite.com/mysite)'
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'docs', 'iono.json')
HOURS = 6

FIELDS = ["foE", "h'E", 'foEs', "h'Es", 'fbEs', 'foF1', "h'F", "h'F2", 'foF2',
          'fxF2', 'M3F2', 'fxI', 'hpF2', 'fxEs', 'ftEs', 'fxF1', 'FSPR', 'MUF',
          'Es1', 'Es2', 'Es', 'W']
BAD = set('CDEFGHNQRSVWB')     # 値を信用しないほうがよい記号
SPREAD = set('FQ')             # Spread-Fの兆候を示す記号
TOK = re.compile(r'(\d+)?-*([A-Za-z]{0,2})$')
JST = timezone(timedelta(hours=9))


def tok(s):
    m = TOK.match(s.strip())
    if not m:
        return None, ''
    return (int(m.group(1)) if m.group(1) else None), m.group(2).upper()


def parse(line):
    p = line.rstrip('\r\n').split(',')
    if len(p) < len(FIELDS) + 2 or ':' not in p[1]:
        return None
    dt, first = p[1].split(':', 1)
    f = {'fmin': tok(first)}
    for n, t in zip(FIELDS, p[2:]):
        f[n] = tok(t)
    try:
        t = calendar.timegm(time.strptime(dt.strip(), '%Y%m%d%H%M%S')) - 9 * 3600   # JST -> UTC
    except ValueError:
        return None
    return t, f


def val(f, name, scale):
    v, flag = f.get(name, (None, ''))
    return None if v is None or flag in BAD else round(v / scale, 2)


def fetch(year):
    req = urllib.request.Request(URL.format(station=STATION, year=year),
                                 headers={'User-Agent': UA, 'Referer': REFERER, 'Accept': 'text/plain,*/*'})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read().decode('cp932', 'replace')


def rows_from(text, now):
    out = []
    for ln in text.splitlines():
        p = parse(ln)
        if not p or p[0] > now + 900:
            continue
        t, f = p
        r = {'time': datetime.fromtimestamp(t, timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
             'foF2': val(f, 'foF2', 100), 'hF': val(f, "h'F", 10), 'hF2': val(f, "h'F2", 10),
             'spreadF': any(f.get(n, (None, ''))[1] in SPREAD for n in ('foF2', "h'F2", "h'F"))}
        if r['foF2'] is not None or r['hF'] is not None or r['hF2'] is not None or r['spreadF']:
            out.append((t, r))
    return out


def main():
    now = time.time()
    jst = datetime.now(JST)
    rows = rows_from(fetch(jst.year), now)
    if jst.month == 1 and jst.day == 1 and jst.hour < HOURS + 1:       # 年をまたぐ直後は前年分も見る
        try:
            rows = rows_from(fetch(jst.year - 1), now) + rows
        except Exception as e:
            print('前年分の取得に失敗:', e)
    if not rows:
        print('有効な観測行が見つかりませんでした。既存のiono.jsonは変更しません。')
        return 1
    rows.sort(key=lambda x: x[0])
    latest = rows[-1][0]
    recent = [r for t, r in rows if t >= latest - HOURS * 3600]
    data = {'station': STATION, 'name': '国分寺',
            'source': '出典：情報通信研究機構（NICT） 電離圏観測データ https://wdc.nict.go.jp/Ionosphere/index.html',
            'note': '観測値は自動処理の結果を含みます',
            'latest': recent[-1]['time'], 'recent': recent}
    old = None
    if os.path.exists(OUT):
        with open(OUT, encoding='utf-8') as fp:
            old = fp.read()
    new = json.dumps(data, ensure_ascii=False, indent=1)
    if new != old:
        os.makedirs(os.path.dirname(OUT), exist_ok=True)
        with open(OUT, 'w', encoding='utf-8') as fp:
            fp.write(new)
        print('更新しました:', data['latest'], f'{len(recent)}行')
    else:
        print('変更なし:', data['latest'])
    return 0


if __name__ == '__main__':
    sys.exit(main())
