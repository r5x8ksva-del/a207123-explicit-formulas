# -*- coding: utf-8 -*-
"""探索 14：解析 notes/c4.md 中手抄的表 2、表 3、表 4、表 7，与精确计算逐项比对（防止转录错误）。"""
import re
import os
from math import factorial
from fractions import Fraction
from c4lib import *
from explore4_patterns import pattern_counts

ROOT = os.path.dirname(os.path.dirname(HERE))
md = open(os.path.join(ROOT, 'notes', 'c4.md'), encoding='utf-8').read()

KR = 140
NR = N_table_rec(KR)


def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])


P = {d: fit(d) for d in range(0, 6)}
bad = 0

# 表 2：行形如 "- d=2：k=3: 1 / 17 / −16；k=4: ..."
sec2 = md.split('**表 2')[1].split('**表 3')[0]
cnt2 = 0
for line in sec2.splitlines():
    m = re.match(r'- d=(\d+)：(.*)', line.strip())
    if not m:
        continue
    d = int(m.group(1))
    for k, Dk, pk, ek in re.findall(r'k=(\d+): (−?\d+) / (−?\d+) / (−?\d+)', m.group(2)):
        k, Dk, pk, ek = int(k), int(Dk.replace('−', '-')), int(pk.replace('−', '-')), int(ek.replace('−', '-'))
        ok = (Dk == Dval(NR, k, d) and pk == pval(P[d], k) and ek == Dk - pk)
        cnt2 += 1
        if not ok:
            bad += 1
            print('TABLE2 mismatch', d, k, Dk, pk, ek)
print('table 2 entries checked:', cnt2)

# 表 3：行形如 "- d=2：65, 74, 64, 30, 6"
sec3 = md.split('**表 3')[1].split('## 3.')[0]
cnt3 = 0
for line in sec3.splitlines():
    m = re.match(r'- d=(\d+)：([\d, ]+)$', line.strip())
    if not m:
        continue
    d = int(m.group(1))
    vals = [int(v) for v in m.group(2).split(',')]
    base = 2 * d + 2
    row = [pval(P[d], base + i) for i in range(2 * d + 1)]
    diffs = []
    for _ in range(2 * d + 1):
        diffs.append(row[0])
        row = [row[j + 1] - row[j] for j in range(len(row) - 1)]
    cnt3 += 1
    if vals != [int(x) for x in diffs]:
        bad += 1
        print('TABLE3 mismatch', d, vals, diffs)
print('table 3 rows checked:', cnt3)

# 表 4：行形如 "- d=2：β=0: σ1..4 = 1,4,3,3；β=2: σ2..6 = ...；β=4: σ6 = 6"
sec4 = md.split('**表 4')[1].split('（d = 6 见')[0]
cnt4 = 0
for line in sec4.splitlines():
    m = re.match(r'- d=(\d+)：(.*)', line.strip())
    if not m:
        continue
    d = int(m.group(1))
    M = pattern_counts(d)
    seen = {}
    for part in m.group(2).split('；'):
        mm = re.match(r'β=(\d+): σ(\d+)(?:\.\.(\d+))? ?[=:] ?([\d,]+)', part.strip())
        if not mm:
            print('cannot parse', part)
            bad += 1
            continue
        b, s0 = int(mm.group(1)), int(mm.group(2))
        s1 = int(mm.group(3)) if mm.group(3) else s0
        vals = [int(v) for v in mm.group(4).split(',')]
        if len(vals) != s1 - s0 + 1:
            bad += 1
            print('TABLE4 length mismatch', d, b)
        for s, v in zip(range(s0, s1 + 1), vals):
            seen[(s, b)] = v
    cnt4 += 1
    if {k: v for k, v in seen.items() if v} != {k: v for k, v in M.items()}:
        bad += 1
        print('TABLE4 mismatch d=', d)
print('table 4 rows checked:', cnt4)

# 表 7：Num_q 多项式
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, 8):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
sec7 = md.split('**表 7')[1].split('### 4.3')[0]
sup = str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹', '0123456789')
cnt7 = 0
for q, rhs in re.findall(r'Num_(\d) = ([^；\n]+)', sec7):
    q = int(q)
    poly = {}
    for term in rhs.replace('。', '').split('+'):
        term = term.strip()
        mm = re.match(r'(\d*)x([⁰¹²³⁴⁵⁶⁷⁸⁹]*)$', term)
        c = int(mm.group(1)) if mm.group(1) else 1
        e = int(mm.group(2).translate(sup)) if mm.group(2) else 1
        poly[e] = c
    lst = [0] * (max(poly) + 1)
    for e, c in poly.items():
        lst[e] = c
    cnt7 += 1
    if trim(lst) != trim(Num[q]):
        bad += 1
        print('TABLE7 mismatch q=', q, lst, Num[q])
print('table 7 polynomials checked:', cnt7)
print('TOTAL mismatches:', bad)
