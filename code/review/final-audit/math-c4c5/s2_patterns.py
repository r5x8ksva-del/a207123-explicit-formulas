# -*- coding: utf-8 -*-
"""T4.2(1) 模式展开：按报告 T4.2(1) 的字面定义独立暴力枚举 Pat(d)（final-audit math-c4c5）。

定义（报告 T4.2(1) + T2.1）：块 S=[v]（单块）、T=[a,v,v]、E=[a,v]（a<v），v 为层；合法词唯一分解为层弱降、只有末块可为 E 的块词。
值 x 平凡 ⇔ x 只出现一次且这次出现是单块 [x]；否则特殊。
Pat(d) = {全部值都特殊、值域 {1..σ}（满射）、长度 σ+d 的合法词}；β = 末尾 E 块的层（无 E 为 0）。
"""
import sys
import time
from collections import defaultdict
from fractions import Fraction
from math import comb, factorial

from alib import say, check, N_tri, dfact, write_log

t0 = time.time()
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def blocks(w):
    """贪心分块（T2.1）：返回 [(type, layer, positions)]；同时断言分块合法。"""
    res = []
    i, L = 0, len(w)
    while i < L:
        u = w[i:]
        M = max(u)
        if u[0] == M:
            res.append(('S', M, (i,)))
            i += 1
        elif len(u) == 2:
            assert u[0] < M
            res.append(('E', M, (i, i + 1)))
            i += 2
        else:
            assert u[1] == M and u[2] == M and u[0] < M, (w, i)
            res.append(('T', M, (i, i + 1, i + 2)))
            i += 3
    # 层弱降、E 只在末尾且层 <= 前面所有层
    lay = [b[1] for b in res]
    assert all(lay[j] >= lay[j + 1] for j in range(len(lay) - 1)), w
    assert all(b[0] != 'E' for b in res[:-1]), w
    return res


def classify(w):
    """返回 (trivial 值集合, β)。"""
    bl = blocks(w)
    cnt = defaultdict(int)
    for x in w:
        cnt[x] += 1
    s_single = set()
    for typ, v, pos in bl:
        if typ == 'S':
            s_single.add(v)
    trivial = {x for x in cnt if cnt[x] == 1 and x in s_single}
    beta = bl[-1][1] if bl and bl[-1][0] == 'E' else 0
    return trivial, beta, bl


def legal_surj_words(L, sigma, max_excess=None):
    """DFS：长 L、值域恰为 {1..sigma} 的合法词。剪枝：剩余长度 >= 未用值数；（可选）已用超额 <= max_excess。"""
    out = []
    w = []
    used = [0] * (sigma + 1)
    nd = [0]

    def rec():
        pos = len(w)
        if pos == L:
            if nd[0] == sigma:
                out.append(tuple(w))
            return
        if L - pos < sigma - nd[0]:
            return
        for c in range(1, sigma + 1):
            if pos >= 2 and not good(w[-2], w[-1], c):
                continue
            new = (used[c] == 0)
            if max_excess is not None and (pos + 1 - (nd[0] + new)) > max_excess:
                continue
            w.append(c)
            used[c] += 1
            nd[0] += new
            rec()
            nd[0] -= new
            used[c] -= 1
            w.pop()
    rec()
    return out


NT = N_tri(80)


def D(k, d):
    q = k - d
    return NT[k][q] if 0 <= q <= k else 0


def Cplus(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def Cpoly(n, r):
    if r < 0:
        return 0
    num = 1
    for i in range(r):
        num *= (n - i)
    return Fraction(num, factorial(r))


M_all = {}
PATS = {}
for d in range(0, DMAX + 1):
    M = defaultdict(int)
    PATS[d] = []
    nwords = 0
    for sigma in range(0, 2 * d + 4):
        L = sigma + d
        if L == 0:
            words = [()]
        else:
            words = legal_surj_words(L, sigma, max_excess=d)
        for w in words:
            nwords += 1
            if len(w) == 0:
                M[(0, 0)] += 1
                PATS[d].append(((), 0, 0))
                continue
            trivial, beta, _ = classify(w)
            if not trivial:
                M[(sigma, beta)] += 1
                if d <= 3:
                    PATS[d].append((w, sigma, beta))
    M_all[d] = dict(M)
    tot = sum(M.values())
    say('INFO d=%d：枚举合法满射词 %d 个，模式 %d 个；(σ,β)->M: %s' % (d, nwords, tot, sorted(M.items())))

totals = [sum(M_all[d].values()) for d in range(DMAX + 1)]
check('T4.2.1-totals', totals == [2, 7, 51, 459, 4990, 63537, 928393][:DMAX + 1], '模式总数 d=0..%d = %s（报告 2,7,51,459,4990,63537,928393）' % (DMAX, totals))
ok = all(s <= 2 * d + 2 and (b == 0 or 2 <= b <= d + 2) for d in M_all for (s, b) in M_all[d])
check('T4.2.1-range', ok, 'σ<=2d+2（σ=2d+3 层枚举为空）、β∈{0}∪[2,d+2]（d<=%d）' % DMAX)

# 四个族 + 两个已知族 + β=d+2
fam_bad = []
for d in range(1, DMAX + 1):
    g = lambda s, b: M_all[d].get((s, b), 0)
    want = [((2 * d - 1, 0), dfact(2 * d - 1)), ((2 * d + 1, 2), dfact(2 * d - 1)),
            ((2 * d + 2, d + 1), d * factorial(d + 1) // 2), ((2 * d, 0), dfact(2 * d - 1)),
            ((2 * d + 2, 2), dfact(2 * d - 1)), ((2 * d + 2, d + 2), factorial(d + 1))]
    if d >= 2:
        want.append(((2 * d - 2, 0), 4 * (d - 1) * dfact(2 * d - 3)))
    for (s, b), val in want:
        if g(s, b) != val:
            fam_bad.append((d, s, b, g(s, b), val))
    # β=d+2 只出现在 σ=2d+2
    if any(b == d + 2 and s != 2 * d + 2 for (s, b) in M_all[d]):
        fam_bad.append((d, 'beta=d+2 at other sigma'))
check('T4.2.1-families', not fam_bad,
      'M(d;2d-1,0)=M(d;2d+1,2)=(2d-1)!!，M(d;2d+2,d+1)=d(d+1)!/2，M(d;2d-2,0)=4(d-1)(2d-3)!!（d>=2），'
      'M(d;2d,0)=M(d;2d+2,2)=(2d-1)!!，β=d+2 只在 σ=2d+2 且共 (d+1)! 个（1<=d<=%d）; bad=%s' % (DMAX, fam_bad))

# c4.md 表 4（d<=4）逐项
TAB4 = {
    0: {0: {0: 1}, 2: {2: 1}},
    1: {0: {1: 1, 2: 1}, 2: {2: 1, 3: 1, 4: 1}, 3: {4: 2}},
    2: {0: dict(zip(range(1, 5), [1, 4, 3, 3])), 2: dict(zip(range(2, 7), [1, 4, 5, 3, 3])),
        3: dict(zip(range(3, 7), [2, 6, 4, 6])), 4: {6: 6}},
    3: {0: dict(zip(range(1, 7), [1, 8, 17, 24, 15, 15])), 2: dict(zip(range(2, 9), [2, 9, 17, 26, 27, 15, 15])),
        3: dict(zip(range(3, 9), [4, 14, 34, 42, 24, 30])), 4: dict(zip(range(5, 9), [12, 30, 18, 36])), 5: {8: 24}},
    4: {0: dict(zip(range(1, 9), [1, 14, 53, 110, 155, 180, 105, 105])),
        2: dict(zip(range(2, 11), [3, 17, 54, 115, 161, 200, 195, 105, 105])),
        3: dict(zip(range(3, 11), [6, 44, 132, 210, 310, 330, 180, 210])),
        4: dict(zip(range(4, 11), [6, 48, 114, 252, 324, 180, 270])),
        5: dict(zip(range(7, 11), [72, 168, 96, 240])), 6: {10: 120}},
}
t4_bad = []
for d in range(0, min(DMAX, 4) + 1):
    flat = {(s, b): v for b, row in TAB4[d].items() for s, v in row.items()}
    if flat != M_all[d]:
        t4_bad.append(d)
check('T4.2.1-table4', not t4_bad, 'c4.md 表 4（d<=%d）与暴力枚举逐项一致; bad=%s' % (min(DMAX, 4), t4_bad))

# 模式展开（组合二项式）与多项式版本
exp_bad, poly_bad, diff_bad = [], [], []
for d in range(0, DMAX + 1):
    # p_d：由数据插值（k=2d+2..4d+2）
    from alib import interp_newton, peval
    xs = list(range(2 * d + 2, 4 * d + 3))
    pd = interp_newton(xs, [D(k, d) for k in xs])
    for k in range(d, 81):
        s_plus = sum(v * Cplus(k - d - b, s - b) for (s, b), v in M_all[d].items())
        if s_plus != D(k, d):
            exp_bad.append((d, k))
    for k in range(-5, 81):
        s_poly = sum(v * Cpoly(k - d - b, s - b) for (s, b), v in M_all[d].items())
        if s_poly != peval(pd, k):
            poly_bad.append((d, k))
check('T4.2.1-expansion', not exp_bad, 'D(k,d)=Σ M(d;σ,β)·C⁺(k-d-β,σ-β)（组合二项式，上指标<0 取 0）对 d<=k<=80 成立（d<=%d）; bad=%s' % (DMAX, exp_bad[:5]))
check('T4.2.1-expansion-poly', not poly_bad, '改用多项式二项式后 Σ M·C(k-d-β,σ-β) == p_d(k)（-5<=k<=80，d<=%d）; bad=%s' % (DMAX, poly_bad[:5]))

# 缺陷的模式来源：q=d+1 时只有 β=d+2 参与，C(-1,d)=(-1)^d
ok = all(sum(v * Cpoly(-1, s - b) for (s, b), v in M_all[d].items() if b > d + 1) * -1 == (-1) ** (d + 1) * factorial(d + 1)
         for d in range(0, DMAX + 1))
check('T4.2.1-defect-from-patterns', ok, 'e_d(2d+1) = -Σ_{β=d+2} M·C(-1,σ-β) = (-1)^{d+1}(d+1)!（d<=%d）' % DMAX)

# 约化映射 Φ 的逐词检验：d<=3, q<=7（k=q+d<=10）
pat_index = {}
for d in range(0, min(DMAX, 3) + 1):
    pass
phi_bad = []
for d in range(0, min(DMAX, 3) + 1):
    tally = defaultdict(int)
    for q in range(1, 8):
        k = q + d
        for w in legal_surj_words(k, q, max_excess=d):
            trivial, beta_w, bl = classify(w)
            # 平凡值必大于 E 层
            vE = bl[-1][1] if bl[-1][0] == 'E' else 0
            if any(x <= vE for x in trivial):
                phi_bad.append(('trivial<=vE', w))
            S = sorted(set(w) - trivial)
            rel = {x: i + 1 for i, x in enumerate(S)}
            wp = tuple(rel[x] for x in w if x not in trivial)
            # 像必须是模式：全部特殊、长度 σ+d，且 β 与 E 层的对应一致
            tr2, beta_p, _ = classify(wp) if wp else (set(), 0, [])
            sig = len(S)
            if tr2 or len(wp) != sig + d:
                phi_bad.append(('not-pattern', w, wp))
            if beta_p != (rel[vE] if vE else 0) or (vE and rel[vE] != vE):
                phi_bad.append(('beta', w, wp))
            # s_i = i (i<=β)
            if beta_p and S[:beta_p] != list(range(1, beta_p + 1)):
                phi_bad.append(('pin', w))
            tally[(q, wp)] += 1
    # 每个模式（取自上面的完整枚举）的原像数 = C⁺(q-β, σ-β)；且像全部落在枚举出的模式里
    allp = set(w for (w, s_, b_) in PATS[d])
    if any(wp not in allp for (_, wp) in tally):
        phi_bad.append(('image-not-in-Pat', d))
    for q in range(1, 8):
        for (wp, sig, beta_p) in PATS[d]:
            if tally.get((q, wp), 0) != Cplus(q - beta_p, sig - beta_p):
                phi_bad.append(('count', d, q, wp, tally.get((q, wp), 0)))
check('T4.2.1-phi', not phi_bad, '约化映射逐词：平凡值 > E 层、像是模式、最小 β 个值被钉死、每个模式的原像数 = C⁺(q-β,σ-β)（d<=3, q<=7）; bad=%s' % phi_bad[:3])

say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s2.log')
