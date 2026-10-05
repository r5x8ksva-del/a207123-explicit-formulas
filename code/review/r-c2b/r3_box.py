# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 3：参数盒单和搜索（c2b-S1）的独立重跑 + 「只要求 k>=k0 成立」的稳健性。

形状 V(k) = sum_{s>=0} A(m,s) C(k+alpha*m+beta-gamma*s, delta*m+eps*s+zeta)（组合约定，A(m,s) 对每个 m 任意有理）。
自写精确增量消元（Fraction，主元取最大列，与 c2b 的最小列不同），对每个 m 判断方程组在 k in [k0,30] 上是否相容。
目标数列：自写细化 DP 得到 A_m(k)（完整）、E(k,m)、U_k(m)；N/N^c/N^E 用标准容斥（已在 r2 中对照直接满射 DP 到 q<=9）。
"""
import sys, os, time, json
from math import comb
from fractions import Fraction

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

T0 = time.time()


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def split_dp(K, m):
    """comp[k], ascd[k]：长 k 合法序列中不以/以上升结尾的个数。"""
    comp = [0] * (K + 1)
    ascd = [0] * (K + 1)
    comp[0] = 1
    if K >= 1:
        comp[1] = m + 1
    st = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    if K >= 2:
        for (a, b), v in st.items():
            if a < b:
                ascd[2] += v
            else:
                comp[2] += v
    for k in range(3, K + 1):
        nst = {}
        for (a, b), v in st.items():
            for c in range(m + 1):
                if good(a, b, c):
                    nst[(b, c)] = nst.get((b, c), 0) + v
        st = nst
        for (b, c), v in st.items():
            if b < c:
                ascd[k] += v
            else:
                comp[k] += v
    return comp, ascd


K, M = 30, 12
TA, TE, TU = {}, {}, {}
for m in range(0, M + 1):
    cp, ad = split_dp(K, m)
    TA[m] = cp
    TE[m] = ad
    TU[m] = [cp[k] + ad[k] for k in range(K + 1)]


def ie(tab, q, base0):
    out = []
    for k in range(K + 1):
        tot = 0
        for i in range(q + 1):
            if i == 0:
                val = base0 if k == 0 else 0
            else:
                val = tab[i - 1][k]
            tot += (-1) ** (q - i) * comb(q, i) * val
        out.append(tot)
    return out


TN = {q: ie(TU, q, 1) for q in range(1, M + 1)}
TNc = {q: ie(TA, q, 1) for q in range(1, M + 1)}
TNE = {q: ie(TE, q, 0) for q in range(1, M + 1)}
TARGETS = {'A': TA, 'E': TE, 'U': TU, 'N': TN, 'Nc': TNc, 'NE': TNE}


def columns(c, g, d, e, kmax):
    """所有在某个 k<=kmax 上非零的 s。"""
    cols = []
    s = 0
    while s <= 400:
        r = d + e * s
        lo = r + g * s - c          # 需要 k >= lo 且 r >= 0
        if r >= 0 and max(0, lo) <= kmax:
            cols.append(s)
        # 终止：r<0 且 e<0 之后永远 <0；或 lo 单调增且已超出
        if e <= 0 and r < 0:
            break
        if g + e > 0 and r >= 0 and lo > kmax:
            break
        s += 1
    return cols


def solve(V, c, g, d, e, k0):
    """返回 (相容?, 检验数, 未知数个数)。检验数 = 方程数 - 秩（只在相容时有意义）。"""
    kmax = len(V) - 1
    cols = columns(c, g, d, e, kmax)
    piv = {}           # pivot col -> (row dict, rhs)
    checks = 0
    for k in range(k0, kmax + 1):
        row = {}
        for s in cols:
            v = C(k + c - g * s, d + e * s)
            if v:
                row[s] = Fraction(v)
        rhs = Fraction(V[k])
        # 消去已有主元
        for pc in sorted([p for p in row if p in piv], reverse=True):
            f = row.get(pc, 0)
            if not f:
                continue
            prow, prhs = piv[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - f * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= f * prhs
        if not row:
            if rhs != 0:
                return False, checks, len(cols)
            checks += 1
            continue
        pc = max(row)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items()}
        prhs = rhs * inv
        for q in list(piv):
            qrow, qrhs = piv[q]
            f = qrow.get(pc, 0)
            if f:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - f * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                piv[q] = (qrow, qrhs - f * prhs)
        piv[pc] = (prow, prhs)
    return True, checks, len(cols)


FAM = [(a, b, g, dl, e, z) for a in range(-1, 3) for b in range(-3, 4) for g in range(0, 4)
       for dl in range(0, 3) for e in range(-1, 4) for z in range(-3, 4)]
INF = [f for f in FAM if f[2] + f[4] >= 2]
print('families total=%d informative=%d' % (len(FAM), len(INF)), flush=True)

report = {}
for k0 in (0, 1, 2, 3, 4, 6):
    report[k0] = {}
    for name, tab in TARGETS.items():
        cache = {}
        dist = {}
        surv = []
        for f in INF:
            a, b, g, dl, e, z = f
            refm = None
            totchecks = 0
            for m in range(1, M + 1):
                key = (m, a * m + b, g, dl * m + z, e)
                if key not in cache:
                    cache[key] = solve(tab[m], a * m + b, g, dl * m + z, e, k0)
                okm, ch, nc = cache[key]
                if not okm:
                    refm = m
                    break
                totchecks += ch
            if refm is None:
                surv.append((f, totchecks))
            else:
                dist[refm] = dist.get(refm, 0) + 1
        report[k0][name] = {'dist': dict(sorted(dist.items())), 'survivors': surv}
        print('k0=%d %-3s refuted-at-m %s survivors %s  (%.1fs)' % (k0, name, dict(sorted(dist.items())), surv, time.time() - T0), flush=True)

# 对照作者声称（k0=0）
claim = {'A': {1: 8208, 2: 22}, 'E': {1: 8201, 2: 31}, 'U': {1: 8232}, 'N': {1: 7887, 2: 345},
         'Nc': {1: 7887, 2: 345}, 'NE': {2: 8217, 3: 15}}
okc = all(report[0][n]['dist'] == claim[n] for n in claim)
oks = sorted(f for f, _ in report[0]['A']['survivors']) == [(1, 0, 2, 1, 1, 0), (1, 2, 2, 1, 1, -1)] and \
    all(not report[0][n]['survivors'] for n in ('E', 'U', 'N', 'Nc', 'NE'))
print('CLAIM_MATCH (k0=0 refuted-at-m distribution == author log):', okc)
print('CLAIM_MATCH (k0=0 survivors: A only the 2 known, others none):', oks)

# 恢复 S(m+s,m)
ST = [[0] * 60 for _ in range(60)]
ST[0][0] = 1
for n in range(1, 60):
    for kk in range(1, n + 1):
        ST[n][kk] = kk * ST[n - 1][kk] + ST[n - 1][kk - 1]
okrec = True
for m in range(1, M + 1):
    okm, ch, nc = solve(TA[m], m, 2, m, 1, 0)
    if not okm or ch < 15:
        okrec = False
print('ENGINE_CONTROL complete part shape (1,0,2,1,1,0) consistent with >=15 checks for every m<=12:', okrec)

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'r3_box_result.json'), 'w', encoding='utf-8') as fh:
    json.dump({str(k0): {n: {'dist': {str(a): b for a, b in v['dist'].items()}, 'survivors': [[list(f), ch] for f, ch in v['survivors']]}
                         for n, v in d.items()} for k0, d in report.items()}, fh, ensure_ascii=False, indent=1)
print('[time] %.1fs' % (time.time() - T0))
