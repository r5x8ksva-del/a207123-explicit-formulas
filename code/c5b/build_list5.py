# -*- coding: utf-8 -*-
"""U 表本身（按反对角线展平，6 种常见约定）是否在 OEIS：程序化生成搜索 URL。"""
import os
import json

HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(HERE, 'terms.json'), encoding='utf-8') as f:
    S = json.load(f)


def U(k, m):
    if k == 0:
        return 1
    return S['U_%d(m),m=0..20' % k][m]


def antidiag(kmin, mmin, s_lo, s_hi, k_increasing):
    out = []
    for s in range(s_lo, s_hi + 1):
        cells = [(k, s - k) for k in range(kmin, s - mmin + 1)]
        if not k_increasing:
            cells = cells[::-1]
        out += [U(k, m) for k, m in cells]
    return out


variants = [
    ('search_Utab_k1m1_kinc.txt', 'U table k>=1,m>=1 antidiagonals s=k+m=4..7, k increasing', antidiag(1, 1, 4, 7, True)),
    ('search_Utab_k1m1_kdec.txt', 'U table k>=1,m>=1 antidiagonals s=4..7, k decreasing', antidiag(1, 1, 4, 7, False)),
    ('search_Utab_k1m0_kinc.txt', 'U table k>=1,m>=0 antidiagonals s=4..6, k increasing', antidiag(1, 0, 4, 6, True)),
    ('search_Utab_k1m0_kdec.txt', 'U table k>=1,m>=0 antidiagonals s=4..6, k decreasing', antidiag(1, 0, 4, 6, False)),
    ('search_Utab_k0m0_kinc.txt', 'U table k>=0,m>=0 antidiagonals s=4..6, k increasing', antidiag(0, 0, 4, 6, True)),
    ('search_Utab_k0m0_kdec.txt', 'U table k>=0,m>=0 antidiagonals s=4..6, k decreasing', antidiag(0, 0, 4, 6, False)),
]
meta_path = os.path.join(HERE, 'search_terms.json')
with open(meta_path, encoding='utf-8') as f:
    meta = json.load(f)
lines = []
for fname, desc, terms in variants:
    url = 'https://oeis.org/search?q=%s&fmt=text' % ','.join(str(t) for t in terms)
    lines.append('%s|%s' % (fname, url))
    meta[fname] = {'desc': desc, 'terms': terms, 'url': url}
# 补记 list3/list4 的条目（无搜索项）
for fname, desc, url in [
    ('search_ref_A207123_p2.txt', 'entries referencing A207123, page 2', 'https://oeis.org/search?q=A207123&start=10&fmt=text'),
]:
    meta.setdefault(fname, {'desc': desc, 'terms': None, 'url': url})
with open(meta_path, 'w', encoding='utf-8') as f:
    json.dump(meta, f, ensure_ascii=False, indent=1)
with open(os.path.join(HERE, 'list5_table.txt'), 'w', encoding='utf-8', newline='\n') as f:
    f.write('\n'.join(lines) + '\n')
print('\n'.join(lines))
