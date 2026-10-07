# -*- coding: utf-8 -*-
"""Recompute the numbers that appear in paper/main.tex from the original definitions (code/core.py)
and compare them with what the paper prints.

Ground truth comes only from core.py (height DP U_fast_table, multichains U_multichain, direct matrix
count a_direct, DFS definition N_brute). Closed forms from the paper are evaluated independently and
compared with that ground truth; tables are parsed out of the .tex file.

Usage:
  py -3.14 code/main_extra/check_paper_numbers.py paper/main.tex          # check (exit code 1 on any FAIL)
  py -3.14 code/main_extra/check_paper_numbers.py --print                 # print tables in LaTeX form
"""
import math
import os
import re
import sys
from decimal import Decimal, getcontext
from fractions import Fraction

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import core  # noqa: E402

KMAX = 50
T = core.U_fast_table(KMAX, KMAX)          # T[k][m] = U_k(m), ground truth


def U(k, m):
    return T[k][m]


def N(k, q):
    if q < 0 or k < 0 or q > k:
        return 0
    return core.N_from_U(T, k, q)


def D(k, d):
    return N(k, k - d)


results = []


def check(cid, ok, detail=''):
    results.append((cid, bool(ok)))
    print(('PASS ' if ok else 'FAIL ') + cid + (('  ' + detail) if detail else ''))


# ---------------------------------------------------------------- polynomial helpers (Fraction coefficients, low degree first)
def p_eval(p, x):
    s = Fraction(0)
    for c in reversed(p):
        s = s * x + c
    return s


def p_mul(p, q):
    r = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def p_add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def p_trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def p_deg(p):
    p = p_trim(p)
    return -1 if (len(p) == 1 and p[0] == 0) else len(p) - 1


def interpolate(points):
    """Lagrange interpolation through (x_i, y_i); returns coefficient list."""
    n = len(points)
    res = [Fraction(0)] * n
    for i, (xi, yi) in enumerate(points):
        basis = [Fraction(1)]
        den = Fraction(1)
        for j, (xj, _) in enumerate(points):
            if j != i:
                basis = p_mul(basis, [Fraction(-xj), Fraction(1)])
                den *= (xi - xj)
        for t in range(len(basis)):
            res[t] += yi * basis[t] / den
    return p_trim(res)


def poly_from_string(s, var):
    """Parse an expression like (k^4-10k^3+43k^2-98k+164)/4 into Fraction coefficients."""
    s = s.replace(' ', '').replace('{', '').replace('}', '')
    m = re.fullmatch(r'\((.*)\)/(\d+)', s)
    den = 1
    if m:
        s, den = m.group(1), int(m.group(2))
    terms = re.findall(r'([+-]?)(\d*)(' + var + r'(?:\^(\d+))?)?', s)
    coeffs = {}
    for sign, num, v, e in terms:
        if not num and not v:
            continue
        c = int(num) if num else 1
        if sign == '-':
            c = -c
        deg = (int(e) if e else 1) if v else 0
        coeffs[deg] = coeffs.get(deg, 0) + c
    n = max(coeffs) + 1
    return [Fraction(coeffs.get(i, 0), den) for i in range(n)]


# ---------------------------------------------------------------- paper parsing
def read_paper(path):
    return open(path, encoding='utf-8').read()


def table_rows(tex, label):
    """Rows (lists of cell strings) of the tabular inside the table environment carrying \\label{label}."""
    i = tex.find('\\label{%s}' % label)
    if i < 0:
        return None
    a = tex.rfind('\\begin{table}', 0, i)
    b = tex.find('\\end{table}', i)
    body = tex[a:b]
    body = body[body.find('\\midrule') + len('\\midrule'):body.find('\\bottomrule')]
    rows = []
    for raw in body.split('\\\\'):
        raw = raw.strip()
        if not raw or raw.startswith('\\midrule'):
            continue
        rows.append([c.strip().strip('$') for c in raw.split('&')])
    return rows


def norm(s):
    return re.sub(r'\s+', '', s)


# ================================================================= the checks
def run_checks(tex):
    # --- Table of U_k(m)
    rows = table_rows(tex, 'tab:U')
    ok = rows is not None and len(rows) == 9
    if ok:
        for r in rows:
            k = int(r[0])
            vals = [int(c) for c in r[1:]]
            ok &= vals == [U(k, m) for m in range(len(vals))]
    check('P01 table U_k(m), 0<=k<=8, 0<=m<=5', ok)
    ok = all(core.U_multichain(k, m) == U(k, m) for k in range(7) for m in range(5))
    check('P01b multichains = height DP (k<=6, m<=4)', ok)

    # --- Table of N(k,q)
    rows = table_rows(tex, 'tab:N')
    ok = rows is not None and len(rows) == 9
    if ok:
        for r in rows:
            k = int(r[0])
            for q, c in enumerate(r[1:]):
                if c == '':
                    ok &= q > k
                else:
                    ok &= int(c) == N(k, q)
    check('P02 table N(k,q), 0<=k<=8', ok)
    ok = True
    for k in range(9):
        nb = core.N_brute(k)
        ok &= all(nb.get(q, 0) == N(k, q) for q in range(k + 1))
    check('P02b N by inclusion-exclusion = DFS definition (k<=8)', ok)
    ok = all(N(k, k) == 2 for k in range(2, KMAX + 1)) and all(N(k, k - 1) == k * k - k - 4 for k in range(4, KMAX + 1))
    ok &= N(3, 2) == 4 and N(1, 1) == 1
    check('P03 N(k,k)=2 (k>=2), N(k,k-1)=k^2-k-4 (k>=4), N(3,2)=4', ok)
    ok = True
    for k in range(3, KMAX + 1):
        for r in range(0, k):
            rhs = N(k - 1, r) + N(k - 1, r + 1) + r * (N(k - 3, r - 1) + 2 * N(k - 3, r) + N(k - 3, r + 1))
            ok &= N(k, r + 1) == rhs
    ok &= not (N(2, 2) == N(1, 1) + N(1, 2) + 1 * (0))      # fails at k=2
    check('P04 triangular recurrence for 3<=k<=50, and failure at k=2', ok)

    # --- reduction and the worked example
    ok = all(core.a_direct(n, k) == U(k, (n + 1) // 2) * U(k, n // 2) for k in range(1, 6) for n in range(0, 9))
    check('P05 a_k(n) = U_k(ceil(n/2)) U_k(floor(n/2)) by direct count (k<=5, n<=8)', ok)
    M = [[1, 1, 1, 1], [1, 1, 1, 0], [1, 0, 1, 1], [0, 1, 1, 0], [1, 0, 1, 1]]
    ok = all(core.row_ok(tuple(r)) for r in M) and all(core.col_ok(tuple(M[i][j] for i in range(5))) for j in range(4))
    odd = [M[0], M[2], M[4]]
    even = [M[1], M[3]]
    h_odd = [sum(r[j] for r in odd) for j in range(4)]
    h_even = [sum(r[j] for r in even) for j in range(4)]
    ok &= h_odd == [3, 1, 3, 3] and h_even == [1, 2, 2, 0]
    ok &= all(core.good(*h_odd[i:i + 3]) for i in range(2)) and all(core.good(*h_even[i:i + 3]) for i in range(2))
    ok &= norm('(3,1,3,3)') in norm(tex) and norm('(1,2,2,0)') in norm(tex)
    ok &= core.a_direct(5, 4) == U(4, 3) * U(4, 2) == 80 * 32 == 2560 and '80\\cdot32=2560' in tex
    check('P06 worked 5x4 example: rules hold, heights (3,1,3,3) and (1,2,2,0) are good', ok)

    # --- block decomposition example
    w = [3, 1, 3, 3, 2, 0, 2, 2, 1, 0, 1]
    ok = all(core.good(*w[i:i + 3]) for i in range(len(w) - 2))
    asc = sum(1 for i in range(len(w) - 1) if w[i] < w[i + 1])
    ok &= asc == 3 and w[-2] < w[-1]
    ok &= norm('(3,1,3,3,2,0,2,2,1,0,1)') in norm(tex)
    check('P07 block example: good, 3 ascents, ends with an ascent', ok)

    # --- generating function facts
    def W_at(mm, x):
        s, P = Fraction(1), Fraction(1)
        for j in range(1, mm + 1):
            P *= (1 - x - (j - 1) * x ** 3)          # P_{j-1}
            s += x * x * j * P
        return s
    ok = W_at(4, Fraction(1, 2)) == Fraction(645, 512) and '645/512' in tex
    check('P08 W_4(1/2) = 645/512', ok)

    # --- explicit formula, refined by ascents
    S2 = core.stirling2_table(80)
    bn = core.binom

    def H(mm, s, j):
        return core.h_complete(s, j, mm) if s >= 0 else 0

    def U_explicit(k, mm):
        tot = sum(S2[mm + s][mm] * bn(k + mm - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1))
        for j in range(1, mm + 1):
            tot += j * sum(H(mm, s, j) * bn(k - 2 + mm - j - 2 * s, k - 2 - 3 * s) for s in range(0, max(0, k) // 3 + 1))
        return tot
    ok = all(U_explicit(k, mm) == U(k, mm) for k in range(0, 31) for mm in range(0, 9))
    check('P09 explicit formula (k<=30, m<=8)', ok)

    def U_F3(k, mm):
        tot = sum(S2[mm + s][mm] * bn(k + 1 + mm - 2 * s, mm + s) for s in range(0, k + 2))
        tot -= sum(H(mm, s, j) * bn(k + mm - j - 2 * s, mm - j + s) for j in range(1, mm + 1) for s in range(0, k + 2))
        return tot

    def c_i(i, n):
        if n < 0:
            return 0
        return sum(bn(n - 2 * l, l) * i ** l for l in range(0, n // 3 + 1))

    def U_F4_times_mfact(k, mm):
        tot = 0
        for i in range(0, mm + 1):
            inner = c_i(i, k + 3 * mm)
            fall = 1
            for j in range(1, i + 1):
                fall *= (i - j + 1)
                inner += j * fall * c_i(i, k + 3 * mm - 3 * j - 2)
            tot += (-1) ** (mm - i) * bn(mm, i) * inner
        return tot
    ok = all(U_F3(k, mm) == U(k, mm) for k in range(0, 31) for mm in range(0, 9))
    ok &= all(U_F4_times_mfact(k, mm) == math.factorial(mm) * U(k, mm) for k in range(0, 31) for mm in range(0, 9))
    check('P09b the two other forms of Remark rem:forms (k<=30, m<=8)', ok)

    def asc_counts(k, mm):
        """dict s -> number of good sequences in {0..mm}^k with s ascents (DFS)."""
        res = {}
        seq = []

        def dfs():
            if len(seq) == k:
                s = sum(1 for i in range(k - 1) if seq[i] < seq[i + 1])
                res[s] = res.get(s, 0) + 1
                return
            for v in range(mm + 1):
                if len(seq) >= 2 and not core.good(seq[-2], seq[-1], v):
                    continue
                seq.append(v)
                dfs()
                seq.pop()
        dfs()
        return res
    ok = True
    for k in range(0, 9):
        for mm in range(0, 4):
            c = asc_counts(k, mm)
            for s in range(0, k + 1):
                f = S2[mm + s][mm] * bn(k + mm - 2 * s, k - 3 * s)
                f += sum(j * H(mm, s - 1, j) * bn(k + mm - j - 2 * s, k + 1 - 3 * s) for j in range(1, mm + 1))
                ok &= f == c.get(s, 0)
    check('P10 explicit formula refined by ascents vs DFS (k<=8, m<=3)', ok)
    ok = all(U(k, 1) == sum(bn(k + 1 - 2 * s, s + 1) for s in range(k + 1)) + sum(bn(k - 2 - 2 * s, s) for s in range(k + 1))
             for k in range(0, KMAX + 1))
    check('P11 U_k(1) = sum_s C(k+1-2s,s+1) + sum_s C(k-2-2s,s) (k<=50)', ok)

    # --- polynomiality in m, zeros at negative integers, h_k facts
    ok = True
    for k in range(0, 26):
        u = interpolate([(Fraction(m), Fraction(U(k, m))) for m in range(k + 1)])
        ok &= all(p_eval(u, m) == U(k, m) for m in range(k + 1, k + 6))
        ok &= p_deg(u) == k
        if k >= 2:
            ok &= u[k] == Fraction(2, math.factorial(k))
        if k >= 1:
            sk = (k + 2) // 3
            ok &= all(p_eval(u, -j) == 0 for j in range(1, sk + 1)) and p_eval(u, -sk - 1) != 0
    check('P12 u_k: degree k, lead 2/k! (k>=2), zeros exactly at -1..-floor((k+2)/3) among the first ones (k<=25)', ok)

    # --- columns of the original table
    ok = True
    for k in range(1, 7):
        u = interpolate([(Fraction(m), Fraction(U(k, m))) for m in range(k + 1)])
        half = Fraction(1, 2)
        Ep = p_mul([p * half ** i for i, p in enumerate(u)], [p * half ** i for i, p in enumerate(u)])   # u(n/2)^2
        up = [c for c in u]
        # u((n+1)/2) and u((n-1)/2) as polynomials in n
        def shift_scale(poly, sh):
            out = [Fraction(0)]
            base = [Fraction(sh, 2), Fraction(1, 2)]      # (n+sh)/2
            powb = [Fraction(1)]
            for c in poly:
                out = p_add(out, [c * t for t in powb])
                powb = p_mul(powb, base)
            return out
        Op = p_mul(shift_scale(up, 1), shift_scale(up, -1))
        p = [(a + b) / 2 for a, b in zip(p_add(Ep, [0] * len(Op)), p_add(Op, [0] * len(Ep)))]
        q = [(a - b) / 2 for a, b in zip(p_add(Ep, [0] * len(Op)), p_add(Op, [0] * len(Ep)))]
        ok &= p_deg(p) == 2 * k and p_deg(q) == 2 * k - 2
        a = [U(k, (n + 1) // 2) * U(k, n // 2) for n in range(0, 61)]
        ok &= all(p_eval(p, n) + (-1) ** n * p_eval(q, n) == a[n] for n in range(61))
        den = p_mul([Fraction(1)], [Fraction(1)])
        for _ in range(2 * k + 1):
            den = p_mul(den, [Fraction(1), Fraction(-1)])
        for _ in range(2 * k - 1):
            den = p_mul(den, [Fraction(1), Fraction(1)])
        num = [sum(den[i] * a[n - i] for i in range(len(den)) if 0 <= n - i) for n in range(4 * k)]
        ok &= p_eval(num, 1) != 0 and p_eval(num, -1) != 0
        prod = p_mul(num, [Fraction(1)])
        ok &= all(sum(den[i] * a[n - i] for i in range(len(den))) == 0 for n in range(4 * k, 61))
    check('P13 columns: deg p=2k, deg q=2k-2, reduced denominator (1-x)^(2k+1)(1+x)^(2k-1) (1<=k<=6)', ok)

    # --- growth constants
    getcontext().prec = 250      # U_600(1) is about 1e100 while its second-order term is -1

    def rho(mm):
        if mm == 0:
            return Decimal(1)
        y = Decimal(2) if mm < 8 else Decimal(mm) ** (Decimal(1) / 3) + 1
        for _ in range(200):
            y = y - (y ** 3 - y ** 2 - mm) / (3 * y * y - 2 * y)
        return y

    def c_const(mm):
        if mm == 0:
            return Decimal(1)
        r = rho(mm)
        s = Decimal(1)
        fall = 1
        for j in range(1, mm + 1):
            fall *= (mm - j + 1)
            s += j * fall * r ** (-(3 * j + 2))
        return r ** (3 * mm + 3) / (math.factorial(mm) * (r * r + 3 * mm)) * s

    ok = True
    for mm in range(1, 5):
        r, c = rho(mm), c_const(mm)
        K = 600
        col = core.U_fast_column(mm, K)
        rel = Decimal(col[K]) / (c * r ** K) - 1
        r1, c1 = rho(mm - 1), c_const(mm - 1)
        two = (Decimal(col[K]) - c * r ** K) / (-c1 * r1 ** (K + 3))
        ok &= abs(rel) < Decimal('1e-12') and abs(two - 1) < Decimal('1e-6')
    ok &= abs(c_const(4) - Decimal('107.5')) < Decimal('1e-60') and abs(rho(4) - 2) < Decimal('1e-60')
    r1 = rho(1)
    ok &= abs(c_const(1) - (10 + 15 * r1 + 17 * r1 * r1) / 31) < Decimal('1e-60')
    shown = {1: '2.2096', 2: '7.8411', 3: '28.976'}
    for mm, s in shown.items():
        ok &= str(c_const(mm)).startswith(s) and s in tex
    ok &= '215/2' in tex
    check('P14 c_m, rho_m: two-term asymptotics at k=600 (m<=4), c_4=215/2, c_1=(10+15rho+17rho^2)/31', ok,
          'c1=%s c2=%s c3=%s' % (str(c_const(1))[:12], str(c_const(2))[:12], str(c_const(3))[:12]))

    # --- Remark rem:asym, second paragraph: kappa_m and the relative error of the leading term (numerical observations)
    kap = {mm: c_const(mm - 1) * rho(mm - 1) ** 3 / c_const(mm) for mm in range(1, 25)}
    ok = all(kap[mm + 1] > kap[mm] for mm in range(1, 24))
    for mm, s in {1: '0.453', 4: '1.745', 24: '9.869'}.items():
        printed = ('\\kappa_{%d}\\approx%s' if mm >= 10 else '\\kappa_%d\\approx%s') % (mm, s)
        ok &= ('%.3f' % kap[mm]) == s and printed in tex
    rel = {}
    for mm in (2, 24):
        col = core.U_fast_column(mm, 10 * mm)
        r, c = rho(mm), c_const(mm)
        for kk in (3 * mm, 10 * mm):
            rel[(mm, kk)] = Decimal(col[kk]) / (c * r ** kk) - 1
    ok &= ('%.2f' % rel[(2, 6)]) == '-0.36' and ('%.3f' % rel[(24, 72)]) == '-0.996'
    ok &= ('%.2f' % rel[(2, 20)]) == '-0.05' and ('%.2f' % rel[(24, 240)]) == '-0.41'
    ok &= all(s in tex for s in ('$-0.36$', '$-0.996$', '$-0.05$', '$-0.41$', '$1\\le m\\le24$'))
    check('P24 kappa_m increasing for m<=24; kappa_1, kappa_4, kappa_24 and the relative errors at k=3m, 10m (m=2, 24) as printed', ok,
          'kappa=%.4f,%.4f,%.4f rel=%.4f,%.4f,%.4f,%.4f' % (kap[1], kap[4], kap[24], rel[(2, 6)], rel[(24, 72)],
                                                           rel[(2, 20)], rel[(24, 240)]))

    # --- norms used in Section 6
    f = lambda X: X ** 3 + X - 1                                 # monic min. poly of xi (root of b_1)
    g = lambda X: X ** 3 + Fraction(1, 2) * X - Fraction(1, 2)   # monic min. poly of eta (root of b_2)
    ok = (-f(Fraction(-1)) == 3) and (-f(Fraction(0)) == 1)
    ok &= (-g(Fraction(0)) == Fraction(1, 2)) and (8 * g(Fraction(2)) == 68)
    lo, hi = Fraction(68225, 100000), Fraction(68235, 100000)       # b_1 is decreasing on R
    ok &= (1 - lo - lo ** 3 > 0) and (1 - hi - hi ** 3 < 0) and norm('\\xi\\approx0.6823') in norm(tex)
    check('P15 norms Nm(1+xi)=3, Nm(xi)=1, Nm(eta)=1/2, Nm(4-2eta)=68; xi = 0.6823 to four places', ok)

    # --- residues at the fibres (numerical spot check of the closed forms)
    import cmath
    import numpy as np

    def poly_b(v):
        return [Fraction(1), Fraction(-1), Fraction(0), Fraction(-v)]

    def P_poly(mm):
        P = [Fraction(1)]
        for v in range(0, mm + 1):
            P = p_mul(P, poly_b(v))
        return P

    def W_poly(mm):
        Wp = [Fraction(1)]
        for j in range(1, mm + 1):
            Wp = p_add(Wp, [Fraction(0), Fraction(0)] + [j * c for c in P_poly(j - 1)])
        return Wp

    def ev(p, z):
        s = 0
        for c in reversed(p):
            s = s * z + float(c)
        return s

    def dpoly(p):
        return [i * p[i] for i in range(1, len(p))]

    ok = True
    for mm in range(1, 7):
        Pm, Wm = P_poly(mm), W_poly(mm)
        for xi in np.roots([-1, 0, -1, 1]):                     # roots of 1 - x - x^3
            res = ev(Wm, xi) / ev(dpoly(Pm), xi)
            up = (3 - 2 * xi) / xi ** 4
            closed = (-1) ** mm * (1 + xi) * xi ** (-3 * mm - 2) / math.factorial(mm - 1)
            ok &= abs(res * up - closed) < 1e-8 * max(1, abs(closed))
        if mm >= 2:
            Em = p_add(Wm, [Fraction(-1)])
            for eta in np.roots([-2, 0, -1, 1]):                # roots of 1 - x - 2x^3
                res = ev(Em, eta) / ev(dpoly(Pm), eta)
                up = (3 - 2 * eta) / (4 * eta ** 4)
                Wt = 2 * eta ** 5 + 4 * eta ** 8
                closed = (-1) ** (mm - 2 + 1) * Wt * eta ** (-3 * mm - 3) / (math.factorial(mm - 2) * 2 * 4)
                ok &= abs(res * up - closed) < 1e-8 * max(1, abs(closed))
    check('P16 residue closed forms on the fibres u=1 and u=1/2 (numerical, m<=6)', ok)

    # --- near-diagonal polynomials
    pd_strings = {
        1: 'k^2-k-4',
        2: '(k^4-10k^3+43k^2-98k+164)/4',
        3: '(k^6-27k^5+331k^4-2225k^3+8560k^2-17392k+11088)/24',
    }
    ok = True
    for d, s in pd_strings.items():
        pd = poly_from_string(s, 'k')
        ok &= all(p_eval(pd, k) == D(k, d) for k in range(2 * d + 2, KMAX + 1)) and p_eval(pd, 2 * d + 1) != D(2 * d + 1, d)
        ok &= norm(s) in norm(tex).replace('\\frac', '')  or norm(s.replace('(', '').replace(')/', '}{')) in norm(tex)
    check('P17 p_1, p_2, p_3 (formulas as printed) agree with D(k,d) exactly from k=2d+2, not at 2d+1', ok)
    ok = True
    pds = {}
    for d in range(0, 9):
        pts = [(Fraction(k), Fraction(D(k, d))) for k in range(2 * d + 2, 4 * d + 3)]
        pd = interpolate(pts)
        pds[d] = pd
        ok &= all(p_eval(pd, k) == D(k, d) for k in range(4 * d + 3, KMAX + 1))
        ok &= p_deg(pd) == 2 * d and pd[2 * d] == Fraction(2, 2 ** d * math.factorial(d))
        if d >= 1:
            ok &= pd[2 * d - 1] == -(4 * d * d - 3 * d) * pd[2 * d]
        ok &= D(2 * d + 1, d) - p_eval(pd, 2 * d + 1) == (-1) ** (d + 1) * math.factorial(d + 1)
        ok &= D(2 * d, d) - p_eval(pd, 2 * d) == Fraction((-1) ** (d + 1) * math.factorial(d + 2), 2)
    check('P18 p_d for d<=8: degree 2d, lead 2/(2^d d!), second coefficient, defects at 2d+1 and 2d', ok)
    rows = table_rows(tex, 'tab:exc')
    ok = rows is not None and len(rows) > 0
    if ok:
        for r in rows:
            d, k, Dv, pv, ev_ = (int(c) for c in r)
            ok &= Dv == D(k, d) and pv == p_eval(pds[d], k) and ev_ == Dv - pv
    check('P19 table of exceptional values D(k,d), p_d(k), e_d(k)', ok)
    ok = True
    for d in range(0, 9):
        vals = [p_eval(pds[d], 2 * d + 2 + n) for n in range(2 * d + 1)]
        newton = []
        cur = vals[:]
        while cur:
            newton.append(cur[0])
            cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
        ok &= all(t > 0 and t.denominator == 1 for t in newton)
        ok &= newton[-1] == 2 * math.prod(range(1, 2 * d, 2))
        if d == 2:
            ok &= [int(t) for t in newton] == [65, 74, 64, 30, 6] and '65, 74, 64, 30, 6' in tex
        if d == 3:
            ok &= [int(t) for t in newton] == [574, 872, 939, 802, 486, 180, 30]
    check('P20 Newton coefficients at 2d+2 are positive integers, last = 2(2d-1)!! (d<=8)', ok)

    # --- OEIS identifications quoted in the paper
    def oeis_terms(aid):
        txt = open(os.path.join(os.path.dirname(os.path.dirname(HERE)), 'data', 'oeis', aid + '.txt'), encoding='utf-8').read()
        seq = ''
        for tag in ('S', 'T', 'U'):
            for line in txt.splitlines():
                if line.startswith('%%%s %s' % (tag, aid)):
                    seq += line.split(' ', 2)[2].strip()
        return [int(x) for x in seq.split(',') if x]
    a084990 = oeis_terms('A084990')       # offset 0
    a326247 = oeis_terms('A326247')       # offset 0
    a038718 = oeis_terms('A038718')       # offset 1
    ok = all(U(3, m) == a084990[m + 1] for m in range(len(a084990) - 1))
    ok &= all(U(4, m) == a326247[m + 2] for m in range(len(a326247) - 2))
    ok &= all(U(k, 1) == a038718[k + 2 - 1] for k in range(len(a038718) - 1))
    ok &= all(U(4, m) == bn(m + 2, 2) ** 2 - 4 * bn(m + 2, 4) for m in range(0, KMAX + 1))
    ok &= norm('U_4(m)=\\binom{m+2}{2}^2-4\\binom{m+2}{4}') in norm(tex)
    check('P21 U_3(m)=A084990(m+1), U_4(m)=A326247(m+2), U_k(1)=A038718(k+2) on the snapshot terms; U_4(m)=C(m+2,2)^2-4C(m+2,4)', ok)

    # --- minimal orders of the rows n=2..7 (Remark rem:oeis), exact Berlekamp-Massey over Q
    def berlekamp_massey(seq):
        C, B = [Fraction(1)], [Fraction(1)]
        L, mshift, b = 0, 1, Fraction(1)
        for n in range(len(seq)):
            d = Fraction(seq[n]) + sum(C[i] * seq[n - i] for i in range(1, L + 1))
            if d == 0:
                mshift += 1
                continue
            coef = d / b
            T_ = C[:]
            C = C + [Fraction(0)] * max(0, len(B) + mshift - len(C))
            for i in range(len(B)):
                C[i + mshift] -= coef * B[i]
            if 2 * L <= n:
                L, B, b, mshift = n + 1 - L, T_, d, 1
            else:
                mshift += 1
        return L
    cols = {mm: core.U_fast_column(mm, 230) for mm in range(0, 5)}
    orders = []
    for n in range(2, 8):
        row = [cols[(n + 1) // 2][k] * cols[n // 2][k] for k in range(0, 231)]
        orders.append(berlekamp_massey(row))
    ok = orders == [10, 22, 28, 49, 55, 85] and norm('$10$, $22$, $28$, $49$, $55$, $85$') in norm(tex)

    def char_roots(mm):
        rts = [1.0 + 0j]
        for i in range(1, mm + 1):
            rts += list(np.roots([1, -1, 0, -i]))
        return rts
    for n, o in zip(range(2, 8), orders):
        prods = []
        for a in char_roots((n + 1) // 2):
            for b_ in char_roots(n // 2):
                z = a * b_
                if all(abs(z - w) > 1e-9 for w in prods):
                    prods.append(z)
        ok &= len(prods) == o
    check('P23 rows n=2..7: minimal orders 10,22,28,49,55,85 (exact BM) = numbers of distinct products of characteristic roots', ok,
          'orders=%s' % orders)

    # --- Sections sec:single (Theorem thm:shapes), sec:twofam and sec:realroots (added 8 October 2026)
    run_checks_tableB(tex)


# ---------------------------------------------------------------- helpers for the Table B sections
def p_der(p):
    return p_trim([i * p[i] for i in range(1, len(p))] or [Fraction(0)])


def p_divmod(a, b):
    a, b = p_trim([Fraction(c) for c in a]), p_trim([Fraction(c) for c in b])
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while p_deg(a) >= p_deg(b) and p_deg(a) >= 0:
        sh = p_deg(a) - p_deg(b)
        c = a[-1] / b[-1]
        q[sh] = c
        a = p_trim(p_add(a, [Fraction(0)] * sh + [-c * t for t in b]))
    return p_trim(q), a


def p_gcd(a, b):
    a, b = p_trim(a), p_trim(b)
    while p_deg(b) >= 0:
        a, b = b, p_divmod(a, b)[1]
    return [c / a[-1] for c in a]


def sturm_count(p, a=None, b=None):
    """Number of distinct real zeros of p in (a, b]; a=None means -infinity, b=None means +infinity."""
    seq = [p_trim(p), p_der(p)]
    while p_deg(seq[-1]) > 0:
        r = p_divmod(seq[-2], seq[-1])[1]
        if p_deg(r) < 0:
            break
        seq.append([-c for c in r])

    def sgn_at(x):
        out = []
        for s in seq:
            if x is None or isinstance(x, str):
                lead = s[-1] * (1 if x == '+' or p_deg(s) % 2 == 0 else -1)
                v = lead
            else:
                v = p_eval(s, x)
            if v != 0:
                out.append(v > 0)
        return sum(1 for i in range(len(out) - 1) if out[i] != out[i + 1])
    return sgn_at('-' if a is None else a) - sgn_at('+' if b is None else b)


def run_checks_tableB(tex):
    import numpy as np
    bn = core.binom
    z1 = [Fraction(1), Fraction(1)]                      # 1 + z

    def nrow(k):
        return p_trim([Fraction(N(k, q)) for q in range(1, k + 1)])

    def hpoly(k):                                        # from the definition: (1-t)^{k+1} sum_m U_k(m) t^m
        return p_trim([Fraction(sum((-1) ** (i - j) * bn(k + 1, i - j) * U(k, j) for j in range(0, i + 1)))
                       for i in range(0, k + 1)])

    def opD(p):
        return p_add(p_mul(z1, p_der(p)), [2 * c for c in p])

    def opT(p):
        return p_trim(p_mul([Fraction(0), Fraction(1)], opD(p)))

    def opPsi(p):
        return p_trim(p_mul(z1, opT(p)))

    def eq(p, q):
        return p_trim(p_add(p, [-c for c in q])) == [0]

    def num_inside(s):
        return norm(s) in norm(tex)

    # P25: definitions and examples at the start of Section sec:realroots
    ok = True
    for k in range(1, 31):
        hk, nk = hpoly(k), nrow(k)
        viaN = [Fraction(0)]
        for q in range(1, k + 1):
            term = [Fraction(N(k, q))]
            term = p_mul(term, [Fraction(0)] * (q - 1) + [Fraction(1)])
            for _ in range(k - q):
                term = p_mul(term, [Fraction(1), Fraction(-1)])
            viaN = p_add(viaN, term)
        ok &= eq(hk, viaN) and p_deg(nk) == k - 1 and nk[0] == 1 and N(k, 1) == 1
        # n_k(z) = (1+z)^{k-1} h_k(z/(1+z)), i.e. sum_i h_{k,i} z^i (1+z)^{k-1-i}
        rhs = [Fraction(0)]
        for i, c in enumerate(hk):
            term = p_mul([c], [Fraction(0)] * i + [Fraction(1)])
            for _ in range(k - 1 - i):
                term = p_mul(term, z1)
            rhs = p_add(rhs, term)
        ok &= eq(nk, rhs)
    ok &= nrow(2) == [1, 2] and nrow(3) == [1, 4, 2]
    ok &= hpoly(3) == [1, 2, -1] and hpoly(4) == [1, 4, -3]
    ok &= eq(nrow(4), p_mul(z1, [1, 6, 2]))
    # zeros quoted: h_3 = -(t^2-2t-1), h_4 = -(3t^2-4t-1), n_3 = 2z^2+4z+1, the quadratic factor of n_4 is 2z^2+6z+1
    s2, s7 = math.sqrt(2), math.sqrt(7)
    ok &= hpoly(3) == [1, 2, -1] and all(abs(1 + 2 * t - t * t) < 1e-12 for t in (1 + s2, 1 - s2))
    ok &= all(abs(1 + 4 * t - 3 * t * t) < 1e-12 for t in ((2 + s7) / 3, (2 - s7) / 3))
    ok &= sorted([1 - s2, (2 - s7) / 3, (2 + s7) / 3, 1 + s2]) == [1 - s2, (2 - s7) / 3, (2 + s7) / 3, 1 + s2]
    n3z, n4z = [-1 - s2 / 2, -1 + s2 / 2], [(-3 - s7) / 2, -1.0, (-3 + s7) / 2]
    ok &= all(abs(1 + 4 * z + 2 * z * z) < 1e-12 for z in n3z) and all(abs(1 + 6 * z + 2 * z * z) < 1e-12 for z in n4z[::2])
    ok &= n4z[0] < n3z[0] < n4z[1] < n3z[1] < n4z[2]
    for s in ('h_3=1+2t-t^2', 'h_4=1+4t-3t^2', 'n_2=1+2z', 'n_3=1+4z+2z^2', 'n_4=(1+z)(1+6z+2z^2)',
              '1\\pm\\sqrt2', '(2\\pm\\sqrt7)/3', '(-3\\pm\\sqrt7)/2', '-1\\pm\\sqrt2/2'):
        ok &= num_inside(s)
    check('P25 Section realroots: h_k via N and n_k via h_k (k<=30), n_2, n_3, n_4, h_3, h_4 and the quoted zeros', ok)

    # P26: the operators, the row recurrence and the base cases of Proposition prop:four
    ok = eq(opT(nrow(1)), [0, 2]) and eq(opT(nrow(2)), p_mul([0, 2], [2, 3])) and eq(opPsi(nrow(1)), p_mul([0, 2], z1))
    ok &= eq(opT(nrow(3)), p_mul(p_mul([0, 2], [1, 2]), [3, 2]))
    ok &= p_eval(nrow(3), Fraction(-1, 2)) == Fraction(-1, 2)
    ok &= eq(nrow(3), p_add(p_mul(z1, nrow(2)), [0, 1]))
    ok &= eq(nrow(4), p_mul(z1, p_add(nrow(3), [0, 2])))
    for k in range(4, 41):
        ok &= eq(nrow(k), p_add(p_mul(z1, nrow(k - 1)), opPsi(nrow(k - 3))))
        ok &= eq(nrow(k), p_mul(z1, p_add(nrow(k - 1), opT(nrow(k - 3)))))
    for p in ([1], [3, 1], [2, 5, 1], [1, 0, 4, 7]):
        p = [Fraction(c) for c in p]
        ok &= eq(opT(p_mul(z1, p)), p_mul(z1, p_add(opT(p), p_mul([0, 1], p))))
    for zz, pol in ((-Fraction(2, 3), opT(nrow(2))), (Fraction(-1), opPsi(nrow(1))), (Fraction(-3, 2), opT(nrow(3))),
                    (Fraction(-1, 2), opT(nrow(3))), (Fraction(0), opT(nrow(3)))):
        ok &= p_eval(pol, zz) == 0
    chain = [-1 - s2 / 2, -1.5, -1.0, -2 / 3, -0.5, -1 + s2 / 2, 0.0]
    ok &= all(chain[i] < chain[i + 1] for i in range(len(chain) - 1))
    for s in ('\\mathcal Tn_1=2z', '\\mathcal Tn_2=2z(2+3z)', '\\Psi n_1=2z(1+z)', '\\mathcal Tn_3=2z(2z+1)(2z+3)',
              'n_3(-1/2)=-1/2', 'n_4=(1+z)(n_3+2z)', 'n_3=(1+z)n_2+z'):
        ok &= num_inside(s)
    check('P26 operators T, Psi; row recurrence (4<=k<=40); base polynomials, their zeros and the order of the zeros', ok)

    # P27: Theorem thm:realroots, Corollary cor:logconcave and Remark rem:hk-signs (exact, k<=30 / k<=50)
    ok = True
    for k in range(2, 31):
        nk, hk = nrow(k), hpoly(k)
        mu = 0
        rest = nk
        while p_eval(rest, -1) == 0:
            rest = p_divmod(rest, z1)[0]
            mu += 1
        ok &= mu == -(-k // 3) - 1                                       # ceil(k/3) - 1
        lam = p_eval(rest, -1)                                           # Lemma lem:minusone: sign of lambda_k
        ok &= lam != 0 and (lam > 0) == (((k // 3) + (1 if k % 3 == 2 else 0)) % 2 == 0)
        ok &= p_deg(p_gcd(rest, p_der(rest))) == 0                       # simple zeros apart from -1
        ok &= sturm_count(rest) == p_deg(rest)                           # all real
        ok &= p_deg(p_gcd(hk, p_der(hk))) == 0 and sturm_count(hk) == p_deg(hk) == (2 * k) // 3
        ok &= sturm_count(hk, Fraction(1)) == k // 3 and sturm_count(hk, None, Fraction(0)) == (k + 1) // 3
        ok &= sturm_count(hk, Fraction(0), Fraction(1)) == 0 and p_eval(hk, 0) == 1
        signs = [c > 0 for c in hk if c != 0]
        ok &= sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1]) == k // 3
        ok &= (hk[-1] > 0) == ((k // 3) % 2 == 0)
    # base values (a_k, lambda_k) for k <= 3 as printed, and T((1+z)^a m) = z (1+z)^a ((a+2) m + (1+z) m')
    ok &= [(0, p_eval(nrow(k), -1)) for k in (1, 2, 3)] == [(0, 1), (0, -1), (0, -1)]
    ok &= norm('$(a_k,\lambda_k)=(0,1),(0,-1),(0,-1)$') in norm(tex)
    for a in range(0, 4):
        for m_ in ([1], [2, 1], [1, 3, 1]):
            m_ = [Fraction(c) for c in m_]
            pp = m_
            for _ in range(a):
                pp = p_mul(pp, z1)
            rhs = p_mul([0, 1], p_add([(a + 2) * c for c in m_], p_mul(z1, p_der(m_))))
            for _ in range(a):
                rhs = p_mul(rhs, z1)
            ok &= eq(opT(pp), rhs)
    for k in range(1, 51):
        row = [N(k, q) for q in range(1, k + 1)]
        ok &= all(v > 0 for v in row) and all(row[q] ** 2 > row[q - 1] * row[q + 1] for q in range(1, k - 1))
        tot = sum(row)
        e1 = Fraction(sum((q + 1) * v for q, v in enumerate(row)), tot)
        e2 = Fraction(sum((q + 1) ** 2 * v for q, v in enumerate(row)), tot)
        ok &= e2 - e1 ** 2 >= Fraction(-(-k // 3) - 1, 4)
    check('P27 n_k: zero -1 of multiplicity ceil(k/3)-1, other zeros real and simple; h_k real-rooted with simple zeros, '
          'zero counts and sign changes floor(k/3) (k<=30); rows positive, strictly log-concave, Var X_k bound (k<=50)', ok)

    # P28: Theorem thm:shapes - the constructions for alpha+beta=1 and the constants in the proof
    ok = True
    for mm in range(1, 5):
        for k in range(0, 31):
            newton = sum(sum((-1) ** (s - j) * bn(s, j) * U(j, mm) for j in range(0, s + 1)) * bn(k, s) for s in range(0, k + 1))
            psums = sum((U(s, mm) - (U(s - 1, mm) if s >= 1 else 0)) * bn(k - s, 0) for s in range(0, k + 1))
            ok &= newton == U(k, mm) and psums == U(k, mm)
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(80):
        mid = (lo + hi) / 2
        if 1 - mid - mid ** 3 > 0:
            lo = mid
        else:
            hi = mid
    ok &= 2 * hi ** 3 < Fraction(64, 100)
    inv3 = 1 / hi ** 3                                                     # xi^-3 > inv3
    ok &= inv3 * (inv3 - 1) ** 2 > Fraction(38, 10) ** 2                 # (xi^-3/2 (xi^-3 - 1))^2 > 3.8^2
    import cmath
    xr = float(hi)
    xi2 = [z for z in np.roots([-1, 0, -1, 1]) if abs(z.imag) > 1e-9][0]
    ok &= abs(abs(xi2) ** 2 - 1 / xr) < 1e-12 and abs((1 - xi2) - xi2 ** 3) < 1e-12
    for beta in (3, 5, 7, 9):
        zetas = [cmath.exp(2j * math.pi * r / beta) for r in range(beta)]
        prod_z = 1
        prod_s = 1
        for zt in zetas:
            prod_z *= zt
            prod_s *= xr ** 2 + zt
            xz = zt / (xr ** 2 + zt)
            ok &= abs(xz ** 3 / (1 - xz) - zt ** 3 / (xr ** 2 * (xr ** 2 + zt) ** 2)) < 1e-9
        ok &= abs(prod_z - 1) < 1e-9 and abs(prod_s - (xr ** (2 * beta) + 1)) < 1e-9
        chi = lambda X: (1 - X) ** beta + X ** beta
        ok &= abs(chi(xr) - (xr ** (3 * beta) + xr ** beta)) < 1e-12 and abs(chi(xi2)) > 3.8
    ok &= 1 / (1 - xr ** 2) > 1
    for s in ('2\\xi^3<0.64', '>3.8', '\\prod_\\zeta(\\xi^2+\\zeta)=\\xi^{2\\beta}+1'):
        ok &= num_inside(s)
    check('P28 shapes with alpha+beta=1 (m<=4, k<=30); 2xi^3<0.64 and xi^-3/2(xi^-3-1)>3.8 (exact); case alpha=0 identities', ok)

    # P29: Section sec:twofam - families, G_0, G^up_1, G^up_2, the certificate table and the counts
    K = 40

    def ser_inv(a):
        b = [Fraction(0)] * K
        b[0] = 1 / a[0]
        for n in range(1, K):
            b[n] = -sum(a[i] * b[n - i] for i in range(1, min(n, len(a) - 1) + 1)) / a[0]
        return b

    def ser_mul(a, b):
        return [sum(a[i] * b[n - i] for i in range(0, n + 1) if i < len(a) and n - i < len(b)) for n in range(K)]

    def bpoly(v):
        return [Fraction(1), Fraction(-1), Fraction(0), Fraction(-v)]

    def Pm(mm):
        P = [Fraction(1)]
        for v in range(0, mm + 1):
            P = p_mul(P, bpoly(v))
        return P

    def Wm(mm):
        W = [Fraction(1)]
        for j in range(1, mm + 1):
            W = p_add(W, [Fraction(0), Fraction(0)] + [j * c for c in Pm(j - 1)])
        return W
    ok = True
    for g in range(-5, 4):
        for s in range(1, 5):
            # x^g u^s = x^{g+3s} (1-x)^{-s}
            lhs = [Fraction(bn(k - g - 2 * s - 1, s - 1)) for k in range(K)]
            rhs = [Fraction(0)] * K
            for n in range(K):
                e = n - (g + 3 * s)
                rhs[n] = Fraction(bn(e + s - 1, s - 1)) if e >= 0 else Fraction(0)
            ok &= lhs == rhs
    one_minus_x = [Fraction(1), Fraction(-1)]
    ok &= ser_mul([Fraction(0)] * 3 + [Fraction(1)], ser_inv(one_minus_x))[3:] == [Fraction(1)] * (K - 3)
    up1 = ser_mul(p_add(Wm(1), [-1]) + [Fraction(0)] * K, ser_inv(Pm(1)))
    # x^{-1} u/(1-u) = x^2/(1-x-x^3)
    ok &= up1 == ser_mul([0, 0, 1] + [Fraction(0)] * K, ser_inv(bpoly(1)))
    up2 = ser_mul(p_add(Wm(2), [-1]) + [Fraction(0)] * K, ser_inv(Pm(2)))
    # x^{-4}u^2/((1-u)(1-2u)) = x^2/((1-x)^2 (1-u)(1-2u)) = x^2/(b_1 b_2);  2x^{-1}u/(1-2u) = 2x^2/b_2
    alt = p_add(ser_mul([0, 0, 1] + [Fraction(0)] * K, ser_inv(p_mul(bpoly(1), bpoly(2)))),
                ser_mul([0, 0, 2] + [Fraction(0)] * K, ser_inv(bpoly(2))))
    ok &= up2 == alt[:K]
    # enumerate U^up directly for small k as an independent check of G^up_2 (and G^up_1)
    import itertools
    for mm, ser in ((1, up1), (2, up2)):
        for k in range(2, 9):
            cnt = 0
            for h in itertools.product(range(mm + 1), repeat=k):
                if h[-2] < h[-1] and all(core.good(h[j], h[j + 1], h[j + 2]) for j in range(k - 2)):
                    cnt += 1
            ok &= cnt == ser[k]
    # the certificate table as printed
    rows = table_rows(tex, 'tab:cert')
    printed = {}
    if rows:
        for r in rows:
            i = int(re.search(r'i=(\d)', r[0]).group(1))
            printed[i] = [tuple(int(v) for v in pr) for pr in re.findall(r'\((\d+),(\d+)\)', r[1].replace(' ', ''))]
    expect = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
              2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
              3: [(13, 84), (71, 70)]}
    ok &= printed == expect

    def is_prime(n):
        return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))

    def mulmod(a, b, i, mod):                       # in Z/mod[x]/(x^3 - (1-x)/i)
        r = [0] * 5
        for p_ in range(3):
            for q_ in range(3):
                r[p_ + q_] += a[p_] * b[q_]
        inv_i = pow(i, -1, mod)
        for d in (4, 3):
            w = r[d] % mod
            r[d] = 0
            r[d - 3] += w * inv_i                   # x^3 = inv_i - inv_i x
            r[d - 2] -= w * inv_i
        return [c % mod for c in r[:3]]

    def powmod(e, i, mod):
        res, base = [1, 0, 0], [0, 1, 0]
        while e:
            if e & 1:
                res = mulmod(res, base, i, mod)
            base = mulmod(base, base, i, mod)
            e >>= 1
        return res

    for i, lst in expect.items():
        for (l, P) in lst:
            ok &= is_prime(l) and l % 2 == 1 and i % l != 0 and 5040 % P == 0
            ok &= powmod(P, i, l) == [1, 0, 0]
            ok &= all(powmod(P // r, i, l) != [1, 0, 0] for r in (2, 3, 5, 7) if P % r == 0)   # exact order
    ok &= 5040 == 2 ** 4 * 3 ** 2 * 5 * 7 and 5040 * 5039 == 25396560 and num_inside('25{,}396{,}560')

    def Wt(i):                                       # tilde W_i = 1 + sum_j j i^{(j)} x^{3j+2}
        W = [0] * (3 * i + 3)
        W[0] = 1
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            W[3 * j + 2] += j * ff
        return W

    def elem(poly, i, mod):                          # value of a polynomial at eta in Z/mod[eta]
        res = [0, 0, 0]
        pw = [1, 0, 0]
        for c in poly:
            res = [(res[t] + c * pw[t]) % mod for t in range(3)]
            pw = mulmod(pw, [0, 1, 0], i, mod)
        return res

    cache = {}

    def theta_fail(i, l, P, n0, up):
        if (i, l, up) not in cache:
            y = powmod(P, i, l * l)
            W = list(Wt(i))
            if up:
                W[0] -= 1
            cache[(i, l, up)] = (((y[1] // l) % l, (y[2] // l) % l), elem(W, i, l))
        mu, ew = cache[(i, l, up)]
        en = powmod(n0 % P, i, l)
        g = mulmod(ew, en, i, l)
        return (mu[0] * g[2] - mu[1] * g[1]) % l == 0

    ok &= Wt(1) == [1, 0, 0, 0, 0, 1]
    fail_U = [n0 for n0 in range(5040) if all(theta_fail(1, l, P, n0, False) for (l, P) in expect[1])]
    fail_E = [n0 for n0 in range(5040) if all(theta_fail(1, l, P, n0, True) for (l, P) in expect[1])]
    ok &= fail_U == [] and fail_E == [2515, 5035] and 5035 % 5040 == (-5) % 5040
    firsts = []
    for n0 in fail_E:
        first = next((l for (l, P) in expect[2] if not theta_fail(2, l, P, n0, True)), None)
        firsts.append(first)
    ok &= firsts == [7, 17]                                   # 7 resolves n0 = 2515, 17 resolves n0 = 5035
    hits = {}
    for n0 in range(5040):
        first = next((l for (l, P) in expect[1] if not theta_fail(1, l, P, n0, False)), None)
        hits[first] = hits.get(first, 0) + 1
    ok &= hits == {3: 3780, 11: 1176, 13: 72, 29: 6, 2521: 6}
    ok &= num_inside('$3780$, $1176$, $72$, $6$ and $6$') and num_inside('succeed, respectively')
    for s in ('M=5040=2^4\\cdot3^2\\cdot5\\cdot7', 'n_0\\in\\{2515,5035\\}', 'the primes $7$ and $17$',
              'G_0=1/(1-x)=x^{-3}u', 'G^{\\uparrow}_1=x^{-1}u/(1-u)', '\\tilde W_1-1=x^5'):
        ok &= num_inside(s)
    check('P29 Section twofam: families x^g u^s, G_0, G^up_1, G^up_2; certificate table (primes, exact orders | 5040); '
          '5040*5039; fibre-1 l-adic first hits 3780/1176/72/6/6 (U); failures exactly at n0 = 2515, 5035 (E), resolved by l = 7, 17', ok,
          'fail_E=%s firsts=%s hits=%s' % (fail_E, firsts, dict(sorted(hits.items()))))

    # P30: the residue formula eq:resid (numerical spot check, fibres i = 1, 2, 3)
    ok = True

    def ev(p, zz):
        s = 0
        for c in reversed(p):
            s = s * zz + float(c)
        return s

    for i in (1, 2, 3):
        for mm in range(i, i + 4):
            P_, W_ = Pm(mm), Wm(mm)
            dP = p_der(P_)
            for eta in np.roots([-i, 0, -1, 1]):
                up = eta ** 2 * (3 - 2 * eta) / (1 - eta) ** 2
                res = ev(W_, eta) / ev(dP, eta)
                Wte = ev([Fraction(c) for c in Wt(i)], eta)
                closed = (-1) ** (mm - i + 1) * Wte * eta ** (-3 * mm - 3) / (math.factorial(mm - i) * math.factorial(i) * i * i)
                ok &= abs(up * res - closed) < 1e-8 * max(1, abs(closed))
                ok &= abs(ev(W_, eta) - Wte) < 1e-9 * max(1, abs(Wte))
    check('P30 residue formula eq:resid on the fibres i=1,2,3 (numerical, i<=m<=i+3); W_m(eta) = tilde W_i(eta)', ok)


def print_tables():
    print('% table N(k,q)')
    for k in range(0, 9):
        cells = [str(N(k, q)) if q <= k else '' for q in range(0, 9)]
        print('%d & ' % k + ' & '.join(cells) + ' \\\\')
    print('% exceptional values d, k, D, p_d(k), e_d')
    for d in range(0, 4):
        pts = [(Fraction(k), Fraction(D(k, d))) for k in range(2 * d + 2, 4 * d + 3)]
        pd = interpolate(pts)
        for k in range(d + 1, 2 * d + 2):
            pv = p_eval(pd, k)
            print('%d & %d & %d & %s & %s \\\\' % (d, k, D(k, d), pv, D(k, d) - pv))
    print('% Newton coefficients')
    for d in range(0, 4):
        pts = [(Fraction(k), Fraction(D(k, d))) for k in range(2 * d + 2, 4 * d + 3)]
        pd = interpolate(pts)
        vals = [p_eval(pd, 2 * d + 2 + n) for n in range(2 * d + 1)]
        newton, cur = [], vals[:]
        while cur:
            newton.append(cur[0])
            cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
        print(d, [int(t) for t in newton])


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--print':
        print_tables()
        sys.exit(0)
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.dirname(HERE)), 'paper', 'main.tex')
    run_checks(read_paper(path))
    nfail = sum(1 for _, ok in results if not ok)
    print('%d PASS, %d FAIL' % (len(results) - nfail, nfail))
    sys.exit(1 if nfail else 0)
