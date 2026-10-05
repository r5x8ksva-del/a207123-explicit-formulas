# -*- coding: utf-8 -*-
"""审计 a3-requirements：报告结构、核对 id 覆盖、若干显式公式的独立精确复算。

只读：报告.md、logs/verify_all_final.log、code/core.py（import）。不写任何已有文件。
用法：py -3.14 code/audit/a3-requirements/audit_req.py
"""
import os
import re
import sys
import unicodedata
from fractions import Fraction
from math import comb, factorial
from decimal import Decimal, getcontext

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

NP = NF = 0


def rep(name, ok, msg):
    global NP, NF
    if ok:
        NP += 1
    else:
        NF += 1
    print('%s %s %s' % ('PASS' if ok else 'FAIL', name, msg), flush=True)


def info(name, msg):
    print('INFO %s %s' % (name, msg), flush=True)


# ---------------------------------------------------------------------------
# A. 报告结构
# ---------------------------------------------------------------------------
text = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read().replace('\r\n', '\n')
lines = text.split('\n')


def section(start, end):
    i = next(i for i, l in enumerate(lines) if l.startswith(start))
    j = next(j for j, l in enumerate(lines) if j > i and l.startswith(end))
    return i + 1, lines[i + 1:j]


def width(s):
    return sum(2 if unicodedata.east_asian_width(ch) in 'WF' else 1 for ch in s)


def rendered_lines(block, cols):
    n = 0
    for l in block:
        if not l.strip():
            continue
        w = width(l.strip())
        n += max(1, -(-w // cols))
    return n


for title, a, b in [('summary(1)', '## ①', '## ②'), ('formula(3)', '## ③', '## ④'),
                    ('uncertain(6)', '## ⑥', '## 完成度对照')]:
    start, blk = section(a, b)
    nonempty = [l for l in blk if l.strip()]
    chars = sum(len(l.strip()) for l in nonempty)
    info('A.' + title, 'source lines %d-%d: nonempty=%d, chars=%d, rendered lines @80 cols=%d, @120 cols=%d'
         % (start + 1, start + len(blk), len(nonempty), chars, rendered_lines(blk, 80), rendered_lines(blk, 120)))
    if title == 'summary(1)':
        items = [l for l in nonempty if re.match(r'\d+\.', l)]
        info('A.summary-items', 'numbered items=%d; per-item char counts=%s'
             % (len(items), [len(l) for l in items]))
    if title == 'uncertain(6)':
        items = [l for l in nonempty if re.match(r'\d+\.', l)]
        info('A.uncertain-items', 'numbered items=%d' % len(items))

# 等级标签统计
tags = re.findall(r'【([^】]*)】', text)
from collections import Counter  # noqa: E402
info('A.grade-tags', dict(Counter(tags)))

# ---------------------------------------------------------------------------
# B. 报告引用的检查 id 是否都在最终日志中 PASS
# ---------------------------------------------------------------------------
log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read().split('\n')
passed, cur = {}, None
for l in log:
    m = re.match(r'>>> check_(\w+)\.py', l)
    if m:
        cur = m.group(1)
        passed.setdefault(cur, set())
        continue
    if l.startswith('PASS ') and cur:
        passed[cur].add(l.split()[1])
refs = set()
for m in re.finditer(r'(?<![/A-Za-z0-9_])(c0|c1|c2a|c2b|c3a|c3b|c4|c5a|c5b|rv)\.([A-Za-z0-9][A-Za-z0-9_\-\.]*)', text):
    mod, rid = m.group(1), m.group(2).rstrip('.')
    if rid in ('md',):
        continue
    mm = re.match(r'(.*?)(\d+)\.\.m(\d+)$', rid)        # c5a-asym-m1..m8
    if mm:
        for v in range(int(mm.group(2)), int(mm.group(3)) + 1):
            refs.add((mod, mm.group(1) + str(v)))
        continue
    refs.add((mod, rid))
missing = []
for mod, rid in sorted(refs):
    lid = (mod + '.' + rid) if mod in ('c2b', 'c5b') else rid
    if lid not in passed.get(mod, set()):
        missing.append(mod + '.' + rid)
rep('B.cited-ids', not missing, 'report cites %d check ids; missing from final-log PASS lines: %s' % (len(refs), missing))
all_ids = sum(len(v) for v in passed.values())
cited = set(((mod + '.' + rid) if mod in ('c2b', 'c5b') else rid, mod) for mod, rid in refs)
uncited = sorted(m + ':' + i for m, s in passed.items() for i in s if (i, m) not in cited)
info('B.uncited', 'final log has %d PASS ids; %d not cited anywhere in report (informational): %s'
     % (all_ids, len(uncited), uncited))

# ---------------------------------------------------------------------------
# C. 独立精确复算（原始定义 DP -> N）
# ---------------------------------------------------------------------------
K = 64
T = core.U_fast_table(K, K)


def N(k, q):
    if q < 0 or k < 0:
        return 0
    return core.N_from_U(T, k, q)


Ntab = [[N(k, q) for q in range(K + 1)] for k in range(K + 1)]


def D(k, d):
    q = k - d
    return Ntab[k][q] if 0 <= q <= K and 0 <= k <= K else 0


def poly_eval_frac(coeffs_desc, den, k):
    v = 0
    for c in coeffs_desc:
        v = v * k + c
    return Fraction(v, den)


PD = {
    0: ([2], 1),
    1: ([1, -1, -4], 1),
    2: ([1, -10, 43, -98, 164], 4),
    3: ([1, -27, 331, -2225, 8560, -17392, 11088], 24),
    4: ([1, -52, 1242, -17280, 151217, -845644, 2926356, -5702176, 5014464], 192),
    5: ([1, -85, 3350, -79370, 1241073, -13308173, 98708360, -498528820, 1637903536, -3158022432, 2686170240], 1920),
}
for d, (cf, den) in PD.items():
    ok_hi = all(poly_eval_frac(cf, den, k) == D(k, d) for k in range(2 * d + 2, K + 1))
    ok_lo = all(poly_eval_frac(cf, den, k) != D(k, d) for k in range(d + 1, 2 * d + 2)) if d >= 1 else True
    e1 = D(2 * d + 1, d) - poly_eval_frac(cf, den, 2 * d + 1)
    ok_def = (e1 == (-1) ** (d + 1) * factorial(d + 1)) if d >= 1 else True
    rep('C.T4.1-p%d' % d, ok_hi and ok_lo and ok_def,
        '报告 p_%d 与 DP 的 N(k,k-%d) 在 %d<=k<=%d 全等；d+1<=k<=2d+1 全不等；k=2d+1 缺陷=%s' % (d, d, 2 * d + 2, K, e1))

# p_2 用 m=k-5 的写法
ok = all(Fraction(m ** 4 + 10 * m ** 3 + 43 * m ** 2 + 82 * m + 124, 4) == poly_eval_frac(PD[2][0], 4, m + 5) for m in range(-10, 30))
rep('C.T4.1-p2-shift', ok, 'p_2=(m^4+10m^3+43m^2+82m+124)/4, m=k-5')

# ④5 锚点 D(2d+2,d)
anch = [D(2 * d + 2, d) for d in range(0, 6)]
rep('C.fail5-anchors', anch == [2, 8, 65, 574, 6012, 70674], 'D(2d+2,d), d=0..5 = %s' % anch)

# T4.2(3) 以 2d+2 为基点的 Newton 系数
def newton_coeffs(vals):
    out, cur = [], list(vals)
    while cur:
        out.append(cur[0])
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    return out


nc2 = newton_coeffs([D(6 + i, 2) for i in range(5)])
rep('C.T4.2-newton-d2', nc2 == [65, 74, 64, 30, 6], 'Δ^i D(6,2), i=0..4 = %s' % nc2)
ok, bad = True, []
for d in range(0, 15):
    if 4 * d + 2 > K:
        break
    nc = newton_coeffs([D(2 * d + 2 + i, d) for i in range(2 * d + 1)])
    dfact = factorial(2 * d) // (2 ** d * factorial(d))
    if not (all(c > 0 for c in nc) and nc[-1] == 2 * dfact):
        ok = False
        bad.append(d)
rep('C.T4.2-newton-pos', ok, 'Newton 系数 Δ^i D(2d+2,d) 全正且末项 2(2d-1)!!，d<=15（k<=64 可及范围） bad=%s' % bad)

# ---------------------------------------------------------------------------
# Num_q（(C7) 分子）
# ---------------------------------------------------------------------------
def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def P_poly(m):
    p = [1]
    for i in range(0, m + 1):
        p = pmul(p, [1, -1, 0, -i])
    return p


def Num(q):
    F = [Ntab[k][q] for k in range(K + 1)]
    pr = pmul(P_poly(q - 1), F)[:K + 1]
    return pr


ok_poly = True
NUM = {}
for q in range(1, 20):
    pr = Num(q)
    if any(pr[i] for i in range(3 * q - 1, K + 1)):
        ok_poly = False
    NUM[q] = pr[:3 * q - 1]
rep('C.T4.3-Num-poly', ok_poly, 'P_{q-1}·Σ_k N(k,q)x^k 在 x^{3q-1}..x^64 为 0，1<=q<=19')
rep('C.T4.3-Num-small', NUM[1] == [0, 1] and NUM[2] == [0, 0, 2, 0, 1] and NUM[4] == [0, 0, 0, 0, 2, 8, 13, 15, 29, 0, 6],
    'Num_1=x, Num_2=2x^2+x^4, Num_4 与提示词一致')
ok1 = all(NUM[q][q + 1] == q * q - q - 4 for q in range(3, 20))
ok2 = all(Fraction(q ** 4 - 6 * q ** 3 + 7 * q ** 2 - 2 * q + 76, 4) == NUM[q][q + 2] for q in range(4, 20))
th1 = (NUM[2][3] if len(NUM[2]) > 3 else 0, 2 * 2 - 2 - 4)
th2 = (NUM[3][5], Fraction(81 - 162 + 63 - 6 + 76, 4))
rep('C.T4.3-low', ok1 and ok2, '[x^{q+1}]Num_q=q^2-q-4 (3<=q<=19)=%s；[x^{q+2}]Num_q=(q^4-6q^3+7q^2-2q+76)/4 (4<=q<=19)=%s；门槛外 q=2: %s, q=3: %s'
    % (ok1, ok2, th1, th2))


def Hn(n):
    return sum(Fraction(1, i) for i in range(1, n + 1))


okh = True
for q in range(2, 20):
    top = NUM[q]
    j0 = top[3 * q - 2]
    j1 = top[3 * q - 3]
    j2 = top[3 * q - 4] if 3 * q - 4 >= 0 else 0
    j3 = top[3 * q - 5] if 3 * q - 5 >= 0 else 0
    f = factorial(q - 1)
    e2 = f * (q - 1 + Hn(q - 1))
    e3 = (q - 1) * f * (Hn(q - 1) - 1)
    if not (j0 == f and j1 == 0 and j2 == e2 and (q < 3 or j3 == e3)):
        okh = False
        info('C.T4.3-high-detail', 'q=%d: j0=%s j1=%s j2=%s(exp %s) j3=%s(exp %s)' % (q, j0, j1, j2, e2, j3, e3))
rep('C.T4.3-high', okh, '高次系数 j=0:(q-1)!, j=1:0, j=2:(q-1)!(q-1+H_{q-1}), j=3:(q-1)(q-1)!(H_{q-1}-1)（H=调和数），2<=q<=19')
vals1 = [sum(NUM[q]) for q in range(1, 8)]
rep('C.T4.3-at1', vals1 == [1, 3, 13, 73, 501, 4051, 37633], 'Num_q(1), q=1..7 = %s（A000262: 1,3,13,73,501,4051,37633）' % vals1)

# ---------------------------------------------------------------------------
# h_k 首项（T5.3(3)）：c(a+2,2) 是第一类 Stirling 还是二项式？
# ---------------------------------------------------------------------------
def stirling1_unsigned(n, k):
    s = [[0] * (n + 1) for _ in range(n + 1)]
    s[0][0] = 1
    for i in range(1, n + 1):
        for j in range(1, i + 1):
            s[i][j] = s[i - 1][j - 1] + (i - 1) * s[i - 1][j]
    return s[n][k]


def h_poly(k):
    # h_k = Σ_q N(k,q) t^{q-1} (1-t)^{k-q}  (k>=1)
    h = [0] * (k + 1)
    for q in range(1, k + 1):
        nq = Ntab[k][q]
        if not nq:
            continue
        for i in range(0, k - q + 1):
            h[q - 1 + i] += nq * comb(k - q, i) * (-1) ** i
    while h and h[-1] == 0:
        h.pop()
    return h


ok_deg, ok_st, ok_bin, det = True, True, True, []
for k in range(2, 40):
    h = h_poly(k)
    if len(h) - 1 != (2 * k) // 3:
        ok_deg = False
    a, r = divmod(k, 3)
    lc = h[-1]
    if r == 0:
        e = (-1) ** a * factorial(a)
        eb = e
    elif r == 1:
        e = (-1) ** a * stirling1_unsigned(a + 2, 2)
        eb = (-1) ** a * comb(a + 2, 2)
    else:
        e = (-1) ** a * factorial(a + 1)
        eb = e
    if lc != e:
        ok_st = False
    if lc != eb:
        ok_bin = False
    if r == 1 and k <= 13:
        det.append((k, lc))
rep('C.T5.3-deg-lead', ok_deg and ok_st, 'deg h_k=floor(2k/3) 且 k=3a+1 首项=(-1)^a·c(a+2,2) 当 c=第一类无符号 Stirling 数时成立（2<=k<=39）；若把 c 读成二项式则 %s；k=3a+1 的首项样例 %s'
    % ('也成立' if ok_bin else '不成立', det))

# ---------------------------------------------------------------------------
# ③ 例：R_k = c_1(k+3)+c_1(k-2)-1
# ---------------------------------------------------------------------------
def c_seq(i, n_max):
    c = [0] * (n_max + 1)
    for n in range(n_max + 1):
        c[n] = (c[n - 1] if n >= 1 else 1 if n == 0 else 0) + (i * c[n - 3] if n >= 3 else 0)
        if n == 0:
            c[0] = 1
    return c


c1 = c_seq(1, 200)


def cc(n):
    return c1[n] if n >= 0 else 0


okR = all(cc(k + 3) + cc(k - 2) - 1 == T[k][1] for k in range(0, K + 1))
rep('C.formula3-Rk', okR, 'R_k=c_1(k+3)+c_1(k-2)-1 对 0<=k<=64（c_1(n)=0, n<0）')

# ---------------------------------------------------------------------------
# T5.1：c_m 三种闭式、γ_j 两种写法、c_1 的 Q(ρ) 表示（Decimal 80 位）
# ---------------------------------------------------------------------------
getcontext().prec = 90


def rho(m):
    y = Decimal(2) + Decimal(m) ** (Decimal(1) / Decimal(3))
    for _ in range(200):
        f = y ** 3 - y ** 2 - m
        fp = 3 * y ** 2 - 2 * y
        y2 = y - f / fp
        if abs(y2 - y) < Decimal(10) ** -85:
            y = y2
            break
        y = y2
    return y


def Pm_val(m, x):
    v = Decimal(1)
    for i in range(0, m + 1):
        v *= (1 - x - i * x ** 3)
    return v


def W_val(m, x):
    return 1 + x ** 2 * sum((j * Pm_val(j - 1, x) for j in range(1, m + 1)), Decimal(0))


ok_c, worst = True, Decimal(0)
for m in range(1, 9):
    r = rho(m)
    x = 1 / r
    G = W_val(m - 1, x) / Pm_val(m - 1, x)
    f1 = (G + m * x ** 2) / (x * (1 + 3 * m * x ** 2))
    f2 = r * (r ** (3 * m + 1) / factorial(m) - sum((r ** (3 * i) / factorial(i) for i in range(m)), Decimal(0))) / (3 * r - 2)
    f3 = r ** (3 * m + 3) / (factorial(m) * (r ** 2 + 3 * m)) * (1 + sum((Decimal(j * factorial(m) // factorial(m - j)) * r ** (-3 * j - 2) for j in range(1, m + 1)), Decimal(0)))
    kk = 3000
    U = core.U_fast_column(m, kk)[kk]
    emp = Decimal(U) / r ** kk
    for f in (f1, f2, f3):
        rel = abs(f / emp - 1)
        worst = max(worst, rel)
        if rel > Decimal(10) ** -40:
            ok_c = False
rep('C.T5.1-cm-forms', ok_c, '三种 c_m 闭式彼此相等且等于 U_3000(m)/rho^3000（1<=m<=8），最大相对偏差 %.2E' % worst)

ok_g = True
for j in range(1, 9):
    s = rho(j)
    g1 = s * (s ** (3 * j + 1) / factorial(j) - sum((s ** (3 * i) / factorial(i) for i in range(j)), Decimal(0))) / (3 * s - 2)
    g2 = (s ** (3 * j + 3) / factorial(j) + sum(((j - i) * s ** (3 * i + 1) / factorial(i) for i in range(j)), Decimal(0))) / (s ** 2 + 3 * j)
    if abs(g1 - g2) > Decimal(10) ** -70 * abs(g1):
        ok_g = False
# 复根（浮点）
import cmath  # noqa: E402
for j in range(1, 9):
    # 复根 of y^3-y^2-j: deflate real root
    r = float(rho(j))
    # y^3 - y^2 - j = (y-r)(y^2 + (r-1) y + j/r)
    bq, cq = r - 1, j / r
    disc = cmath.sqrt(bq * bq - 4 * cq)
    for s in ((-bq + disc) / 2, (-bq - disc) / 2):
        g1 = s * (s ** (3 * j + 1) / factorial(j) - sum(s ** (3 * i) / factorial(i) for i in range(j))) / (3 * s - 2)
        g2 = (s ** (3 * j + 3) / factorial(j) + sum((j - i) * s ** (3 * i + 1) / factorial(i) for i in range(j))) / (s ** 2 + 3 * j)
        if abs(g1 - g2) > 1e-9 * max(1, abs(g1)):
            ok_g = False
rep('C.T5.1-gamma-forms', ok_g, 'γ_j(σ) 两种写法在实根（90 位）与复根（浮点）处相等，1<=j<=8')
r1 = rho(1)
c1v = (10 + 15 * r1 + 17 * r1 ** 2) / 31
rep('C.T5.1-c1', abs(c1v - Decimal('2.2096081318')) < Decimal('1e-10'), 'c_1=(10+15ρ+17ρ^2)/31 = %s' % str(c1v)[:16])

# ---------------------------------------------------------------------------
# T3.3(2)：Y_β 的系数形式，x=1/5、A=1-x 处按 t 截断精确核对 L_A[Y]=(1-t)^{-β}
# ---------------------------------------------------------------------------
def poch(a, n):
    v = Fraction(1)
    for i in range(n):
        v *= (a + i)
    return v


def series_one_minus_t_pow(gamma, n):
    return [poch(gamma, i) / factorial(i) for i in range(n + 1)]


def check_Ybeta(beta, x, TT):
    A = 1 - x
    x3 = x ** 3
    Y = [Fraction(0)] * (TT + 1)
    cN = Fraction(1) / A
    for Nn in range(0, TT + 1):
        if Nn >= 1:
            cN /= (A - Nn * x3)
        for m in range(0, Nn + 1):
            coef = cN * comb(Nn, m) * poch(beta, m) * x3 ** m
            ser = series_one_minus_t_pow(beta + m, TT - Nn)
            for i, s in enumerate(ser):
                Y[Nn + i] += coef * s
    # L[Y] = (A - t)Y - x^3 t Y'
    L = [Fraction(0)] * (TT + 1)
    for n in range(TT + 1):
        L[n] = A * Y[n] - (Y[n - 1] if n >= 1 else 0) - x3 * n * Y[n]
    rhs = series_one_minus_t_pow(beta, TT)
    return all(L[n] == rhs[n] for n in range(TT + 1))


okY = all(check_Ybeta(Fraction(b), Fraction(1, 5), 14) for b in (0, 1, 2, Fraction(1, 2), -3))
rep('C.T3.3-Ybeta', okY, 'Y_β=(1-t)^{-β}Σ_N t^N/(A∏b_i) Σ_m C(N,m)(β)_m (x^3/(1-t))^m 满足 (A-t)Y-x^3 tY_t=(1-t)^{-β}（x=1/5，β∈{0,1,2,1/2,-3}，到 t^14）')

# ---------------------------------------------------------------------------
# T4.2(1)：模式总数（用 check_c4 中同一 DP 复算，核对报告抄写的数字）
# ---------------------------------------------------------------------------
from collections import defaultdict  # noqa: E402


def pattern_counts(d):
    res = defaultdict(int)
    if d == 0:
        res[(0, 0)] += 1
    for sigma in range(1, 2 * d + 4):          # 比 check_c4 多枚举一层 sigma=2d+3
        st = defaultdict(int)
        st[(0, 0, 0, 0)] = 1
        for x in range(sigma, 0, -1):
            new = defaultdict(int)
            for (p, e, closed, beta), w in st.items():
                room = d - e
                for j in range(0, p + 1):
                    wj = w * comb(p, j)
                    opts = [(0, 0, 0)] if closed else [(s, t, E) for t in range(0, room + 2) for s in range(0, room + 2) for E in (0, 1)]
                    for (s, t, E) in opts:
                        mu = s + 2 * t + E + j
                        if mu < 1 or (s == 1 and t == 0 and E == 0 and j == 0):
                            continue
                        e2 = e + mu - 1
                        if e2 > d:
                            continue
                        new[(p - j + t + E, e2, 1 if (closed or E) else 0, x if E else beta)] += wj * comb(s + t, s)
            st = new
        for (p, e, closed, beta), w in st.items():
            if p == 0 and e == d:
                res[(sigma, beta)] += w
    return dict(res)


tot = []
beyond = []
for d in range(0, 7):
    pc = pattern_counts(d)
    tot.append(sum(pc.values()))
    beyond.append(sum(w for (s, b), w in pc.items() if s > 2 * d + 2))
rep('C.T4.2-pattern-totals', tot == [2, 7, 51, 459, 4990, 63537, 928393], 'Σ_σ,β M(d;σ,β), d=0..6 = %s；σ=2d+3 层的模式数 = %s' % (tot, beyond))


# 独立暴力（按报告定义：平凡值 = 只出现一次且该次是单块 [x]），d<=2
def decompose(w):
    blocks, i, n = [], 0, len(w)
    while i < n:
        M = max(w[i:])
        if w[i] == M:
            blocks.append(('S', M))
            i += 1
        elif n - i == 2:
            blocks.append(('E', M))
            i += 2
        else:
            blocks.append(('T', M))
            i += 3
    return blocks


def brute_total(d):
    total = 0
    for sigma in range(0, 2 * d + 4):
        L = sigma + d
        if L == 0:
            total += 1
            continue
        seq = []

        def dfs():
            nonlocal total
            if len(seq) == L:
                if set(seq) != set(range(1, sigma + 1)):
                    return
                cnt = Counter(seq)
                for t, v in decompose(seq):
                    if t == 'S' and cnt[v] == 1:
                        return
                total += 1
                return
            for v in range(1, sigma + 1):
                if len(seq) >= 2 and not core.good(seq[-2], seq[-1], v):
                    continue
                seq.append(v)
                dfs()
                seq.pop()
        dfs()
    return total


bt = [brute_total(d) for d in range(0, 3)]
rep('C.T4.2-pattern-brute', bt == [2, 7, 51], '按定义暴力数模式（σ<=2d+3），d=0..2 = %s' % bt)

print('SUMMARY audit_a3 pass=%d fail=%d' % (NP, NF))
