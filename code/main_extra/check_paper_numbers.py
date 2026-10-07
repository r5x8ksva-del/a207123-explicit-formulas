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

    # --- norms used in Section 6
    f = lambda X: X ** 3 + X - 1                                 # monic min. poly of xi (root of b_1)
    g = lambda X: X ** 3 + Fraction(1, 2) * X - Fraction(1, 2)   # monic min. poly of eta (root of b_2)
    ok = (-f(Fraction(-1)) == 3) and (-f(Fraction(0)) == 1)
    ok &= (-g(Fraction(0)) == Fraction(1, 2)) and (8 * g(Fraction(2)) == 68)
    ok &= Fraction(1 - Fraction(68, 100)) - Fraction(68, 100) ** 3 > 0 and 1 - Fraction(69, 100) - Fraction(69, 100) ** 3 < 0
    ok &= (Fraction(100, 68) ** 3) < 6
    check('P15 norms Nm(1+xi)=3, Nm(xi)=1, Nm(eta)=1/2, Nm(4-2eta)=68; 0.68<xi<0.69; xi^-3<6', ok)

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

    # --- the shapes (alpha,beta) = (1,2), (2,3): fibre polynomials are increasing on the real line
    xi = [z for z in np.roots([-1, 0, -1, 1]) if abs(z.imag) < 1e-12][0].real
    v12, v23 = xi ** -3, xi ** -4
    ok = v12 < 6 and abs(v12 - xi ** 3 / (1 - xi) ** 2) < 1e-12 and abs(v23 - xi ** 5 / (1 - xi) ** 3) < 1e-12
    check('P22 fibre values v(xi): (1,2) gives xi^-3 < 6, (2,3) gives xi^-4', ok, 'xi^-3=%.6f xi^-4=%.6f' % (v12, v23))


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
