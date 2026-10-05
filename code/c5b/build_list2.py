# -*- coding: utf-8 -*-
"""由 terms.json（core 高度 DP 算出的序列）程序化生成 OEIS 搜索 URL 列表，避免手抄出错。
输出 list2_searches.txt（文件名|URL），以及 search_terms.json（每个搜索用到的精确项，供 INDEX 与 check 使用）。"""
import os
import json

HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(HERE, 'terms.json'), encoding='utf-8') as f:
    S = json.load(f)


def U(k):
    return S['U_%d(m),m=0..20' % k]


def Uk(m):
    return S['U_k(%d),k=0..25' % m]


searches = []   # (filename, description, terms)


def add(fname, desc, terms):
    searches.append((fname, desc, [int(t) for t in terms]))


add('search_U3_m0.txt', 'U_3(m), m=0..8', U(3)[0:9])
add('search_U3_m2.txt', 'U_3(m), m=2..10', U(3)[2:11])
add('search_U4_m0.txt', 'U_4(m), m=0..8', U(4)[0:9])
add('search_U4_m2.txt', 'U_4(m), m=2..10', U(4)[2:11])
for k in (5, 6, 7):
    add('search_U%d_m0.txt' % k, 'U_%d(m), m=0..7' % k, U(k)[0:8])
    add('search_U%d_m1.txt' % k, 'U_%d(m), m=1..8' % k, U(k)[1:9])
    add('search_U%d_m2.txt' % k, 'U_%d(m), m=2..9' % k, U(k)[2:10])
add('search_R.txt', 'R_k=U_k(1), k=1..12', Uk(1)[1:13])
add('search_Uk2.txt', 'U_k(2), k=2..11', Uk(2)[2:12])
add('search_Uk3.txt', 'U_k(3), k=2..11', Uk(3)[2:12])
add('search_Uk4.txt', 'U_k(4), k=2..11', Uk(4)[2:12])
add('search_Udiag.txt', 'U_k(k), k=0..9', S['U_k(k),k=0..20'][0:10])
flat = S['N_flat_rows_q=1..k,k=1..11']
add('search_Nflat.txt', 'N(k,q) rows q=1..k, k=1..6', flat[0:21])
flatr = S['N_flat_rows_reversed,k=1..11']
add('search_Nflat_rev.txt', 'N(k,q) rows q=k..1, k=1..6', flatr[0:21])
# 带 q=0 列（N(0,0)=1, N(k,0)=0）：行 k=0..5
q0 = [1]
pos = 0
for k in range(1, 6):
    row = flat[pos:pos + k]
    pos += k
    q0 += [0] + row
add('search_Nflat_q0.txt', 'N(k,q) rows q=0..k, k=0..5', q0)
add('search_Nrowsum.txt', 'sum_q N(k,q), k=1..10', S['N_rowsum,k=0..20'][1:11])
add('search_Nkk1.txt', 'N(k,k-1), k=4..13', S['N(k,k-1),k=2..20'][2:12])
add('search_Nkk2.txt', 'N(k,k-2), k=4..12', S['N(k,k-2),k=3..20'][1:10])
add('search_Nkk3.txt', 'N(k,k-3), k=5..12', S['N(k,k-3),k=4..20'][1:9])
add('search_Nk2.txt', 'N(k,2), k=2..12', S['N(k,2),k=2..20'][0:11])
add('search_Nk3.txt', 'N(k,3), k=3..12', S['N(k,3),k=3..20'][0:10])
hflat = S['h_flat,k=0..8']
# h_0=[1], h_1=[1], h_2=[1,1]，从 h_3 开始取（下标 4 起）
add('search_hflat.txt', 'h_k coefficients, k=3..7', hflat[4:4 + 3 + 3 + 4 + 5 + 5])
numflat = S['Num_flat_x^q..x^(3q-2),q=1..6']
# q=1: 1 项, q=2: 3 项, 从 q=3 开始（下标 4 起），q=3..5 共 5+7+9=21 项
add('search_C7num.txt', '(C7) numerator coeffs x^q..x^(3q-2), q=3..5', numflat[4:25])
add('search_c2.txt', 'c_2(n), n=0..13', S['c_2(n),n=0..29'][0:14])
add('search_c3.txt', 'c_3(n), n=0..13', S['c_3(n),n=0..29'][0:14])

lines = []
meta = {}
for fname, desc, terms in searches:
    q = ','.join(str(t) for t in terms)
    url = 'https://oeis.org/search?q=%s&fmt=text' % q
    lines.append('%s|%s' % (fname, url))
    meta[fname] = {'desc': desc, 'terms': terms, 'url': url}
# 反向引用查询与相关条目原文
extra = [
    ('search_ref_A207123.txt', 'entries referencing A207123', 'https://oeis.org/search?q=A207123&fmt=text'),
    ('A207069.txt', 'entry A207069 (row 2 of A207123)', 'https://oeis.org/search?q=id:A207069&fmt=text'),
    ('A207070.txt', 'entry A207070 (row 3 of A207123)', 'https://oeis.org/search?q=id:A207070&fmt=text'),
    ('A002620.txt', 'entry A002620 (column 1 of A207123 is A002620(n+2))', 'https://oeis.org/search?q=id:A002620&fmt=text'),
    ('A030179.txt', 'entry A030179 (column 2 of A207123 is A030179(n+2))', 'https://oeis.org/search?q=id:A030179&fmt=text'),
]
for fname, desc, url in extra:
    lines.append('%s|%s' % (fname, url))
    meta[fname] = {'desc': desc, 'terms': None, 'url': url}

with open(os.path.join(HERE, 'list2_searches.txt'), 'w', encoding='utf-8', newline='\n') as f:
    f.write('\n'.join(lines) + '\n')
with open(os.path.join(HERE, 'search_terms.json'), 'w', encoding='utf-8') as f:
    json.dump(meta, f, ensure_ascii=False, indent=1)
for l in lines:
    print(l)
print(len(lines), 'URLs')
