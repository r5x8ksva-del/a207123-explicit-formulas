# -*- coding: utf-8 -*-
"""x2-dfinite: independent re-check of the D-finite / relation-module claims of c3b (T1, C2, T3, T3N, T4)
and c2a-D.  This file does NOT import code/core.py or code/polylib.py: every table is rebuilt here from the
original definition and anchored to brute force.

Parts
  A  U_k(m) from the definition (own DP on the last two heights), anchored to: brute-force height sequences,
     brute-force m x k 0/1 matrices (monotone columns + row rule), brute-force a_k(n) of the original problem,
     and the prompt table.
  B  N(k,q) by inclusion-exclusion from U, anchored to a direct DFS over words with value set exactly {0..q-1}.
  C  Relation kernels in boxes [0..A]x[0..B] (coefficients polynomial in the two indices), equations on the
     quadrant [A..K]x[B..M]; rank modulo two primes (own numpy elimination, cross-checked by a pure-Python
     elimination on small matrices); predicted generators (left multiples of L1 / L_N, enumerated from the
     theorem, not by filtering) are verified to vanish EXACTLY (big integers) and to be independent mod p.
  D  Exact integer (content-normalised Gaussian elimination, no modular arithmetic) kernel dimension in small
     boxes on a sub-window: kernel(sub-window) contains kernel(full) contains span(gens), so equality of the
     exact sub-window dimension with #gens is a modular-free proof for the finite system.
  E  Quadrant-shift test: shrinking the quadrant to [A+d..]x[B+d..] must not create new relations (tests the
     'relations on some quadrant' formulation and the boundary handling).
  F  Generating-function dictionary and the transport identity used in Theorem 3' (random Laurent polynomials,
     exact Fractions), plus the transported relation for the special case L = l_N.
  G  Pole facts used by T1/C2/T3/T4 (exact polynomial arithmetic over Q).
Only exact integers / Fractions; modular arithmetic is exact arithmetic in GF(p).
"""
import sys, time, random
from itertools import product
from math import comb, gcd
from fractions import Fraction as Fr

try:
    import numpy as np
    HAVE_NP = True
except Exception:  # pragma: no cover
    HAVE_NP = False

T0 = time.time()
RES = []


def say(s):
    print(s)
    sys.stdout.flush()


def report(cid, ok, desc):
    RES.append((cid, bool(ok)))
    say(('PASS' if ok else 'FAIL') + ' ' + cid + ' ' + desc)


# =====================================================================================
# Part A: U from the definition
# =====================================================================================
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_col_naive(m, K):
    n = m + 1
    out = [1, n, n * n]
    cnt = {(a, b): 1 for a in range(n) for b in range(n)}
    for _k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(n):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out.append(sum(cnt.values()))
    return out[:K + 1]


def U_col_fast(m, K):
    """cnt[b][c] = number of valid prefixes whose last two heights are (b, c)."""
    n = m + 1
    out = [1, n, n * n][:K + 1]
    if K < 3:
        return out
    cnt = [[1] * n for _ in range(n)]
    for _k in range(3, K + 1):
        new = [[0] * n for _ in range(n)]
        for c in range(n):
            suf = [0] * (n + 1)
            s = 0
            for b in range(n - 1, -1, -1):
                s += cnt[b][c]
                suf[b] = s
            row = new[c]
            for d in range(n):
                row[d] = suf[0] if d == c else suf[max(c, d)]
        cnt = new
        out.append(sum(sum(r) for r in cnt))
    return out


def U_table(K, M):
    cols = [U_col_fast(m, K) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def row_ok(bits):
    for i in range(len(bits) - 2):
        t = bits[i:i + 3]
        if t == (0, 0, 1) or t == (0, 1, 0):
            return False
    return True


def col_ok(bits):
    for i in range(len(bits) - 2):
        t = bits[i:i + 3]
        if t == (0, 0, 1) or t == (0, 1, 1):
            return False
    return True


def U_heights_brute(k, m):
    if k == 0:
        return 1
    return sum(1 for h in product(range(m + 1), repeat=k)
               if all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)))


def U_matrix_brute(k, m):
    """m x k 0/1 matrices, every column non-increasing top->bottom, every row avoids 001 and 010."""
    if m == 0:
        return 1
    rows = [r for r in product((0, 1), repeat=k) if row_ok(r)]
    c = 0
    for mat in product(rows, repeat=m):
        if all(all(mat[i][j] >= mat[i + 1][j] for j in range(k)) for i in range(m - 1)):
            c += 1
    return c


def a_brute(n, k):
    """original problem: n x k 0/1 matrices, rows avoid 001/010, columns avoid 001/011."""
    if n == 0:
        return 1
    rows = [r for r in product((0, 1), repeat=k) if row_ok(r)]
    c = 0
    for mat in product(rows, repeat=n):
        if all(col_ok(tuple(mat[i][j] for i in range(n))) for j in range(k)):
            c += 1
    return c


PROMPT = {1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
          4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
          6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
          8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
          10: [1, 100, 1222, 7629, 32971, 112349, 323647]}

KT = MT = 50
UT = U_table(KT, MT)
ok = all(U_col_naive(m, 14) == [UT[k][m] for k in range(15)] for m in range(0, 11))
ok &= all(U_heights_brute(k, m) == UT[k][m] for k in range(0, 8) for m in range(0, 5))
ok &= all(U_matrix_brute(k, m) == UT[k][m] for k in range(1, 6) for m in range(0, 5))
ok &= all(U_matrix_brute(6, m) == UT[6][m] for m in range(0, 4))
ok &= all(PROMPT[k][m] == UT[k][m] for k in PROMPT for m in range(7))
alist = [(1, 10), (2, 8), (3, 7), (4, 6), (5, 4)]
ok &= all(a_brute(n, k) == UT[k][(n + 1) // 2] * UT[k][n // 2] for (k, nmax) in alist for n in range(0, nmax + 1))
report('X2-A', ok, 'own U table (k,m<=50) == naive DP (k<=14,m<=10) == brute heights (k<=7,m<=4) == brute monotone-column '
                   '0/1 matrices (k<=5,m<=4; k=6,m<=3) == prompt table (k<=10,m<=6); original a_k(n) by brute force == '
                   'U(ceil n/2)U(floor n/2) for (k,nmax)=%s' % alist)


# =====================================================================================
# Part B: N(k,q)
# =====================================================================================
def N_ie(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else UT[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


NT = [[N_ie(k, q) for q in range(MT + 1)] for k in range(KT + 1)]


def N_dfs(k):
    res = {}
    if k == 0:
        return {0: 1}
    seq = []

    def rec():
        if len(seq) == k:
            s = set(seq)
            q = len(s)
            if s == set(range(q)):
                res[q] = res.get(q, 0) + 1
            return
        for v in range(k):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return res


ok = True
for k in range(0, 9):
    d = N_dfs(k)
    ok &= all(d.get(q, 0) == NT[k][q] for q in range(0, MT + 1))
ok &= all(NT[k][q] == 0 for k in range(KT + 1) for q in range(k + 1, MT + 1))
report('X2-B', ok, 'N(k,q) by inclusion-exclusion from own U == direct DFS count of words with value set exactly {0..q-1} '
                   '(k<=8, all q); N(k,q)=0 for q>k (k,q<=50)')


# =====================================================================================
# Part C: relation kernels
# =====================================================================================
PRIMES = (1000000007, 998244353)


def rank_np(rows, p):
    if not rows:
        return 0
    A = np.array(rows, dtype=np.int64) % p
    nr, nc = A.shape
    r = 0
    for c in range(nc):
        if r == nr:
            break
        nz = np.flatnonzero(A[r:, c])
        if nz.size == 0:
            continue
        i = r + int(nz[0])
        if i != r:
            A[[r, i]] = A[[i, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        nzb = np.flatnonzero(A[r + 1:, c])
        if nzb.size:
            idx = r + 1 + nzb
            f = A[idx, c].reshape(-1, 1)
            A[idx] = (A[idx] - (f * A[r]) % p) % p
        r += 1
    return r


def rank_py(rows, p):
    A = [[x % p for x in row] for row in rows]
    if not A:
        return 0
    nr, nc = len(A), len(A[0])
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(r + 1, nr):
            f = A[i][c]
            if f:
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r


rank_mod = rank_np if HAVE_NP else rank_py


def monos_total(D):
    return [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]


def monos_graded(Dk, Dm):
    return [(i, j) for i in range(Dk + 1) for j in range(Dm + 1)]


def unknowns(A, B, monos):
    return [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]


def rows_mod(tabp, unk, k0, m0, Kmax, Mmax, p):
    emax = 1 + max(max(i, j) for (_, _, i, j) in unk)
    out = []
    for k in range(k0, Kmax + 1):
        kp = [pow(k, e, p) for e in range(emax)]
        for m in range(m0, Mmax + 1):
            mp = [pow(m, e, p) for e in range(emax)]
            out.append([tabp[k - a][m - b] * kp[i] % p * mp[j] % p for (a, b, i, j) in unk])
    return out


def rows_exact(tab, unk, ks, ms):
    return [[tab[k - a][m - b] * k ** i * m ** j for (a, b, i, j) in unk] for k in ks for m in ms]


def left_mul(alpha, beta, i0, j0, gen):
    """k^i0 m^j0 S^(alpha,beta) * gen;  gen = {(a,b,i,j): c} meaning c k^i m^j S^(a,b), (S^(a,b)u)(k,m)=u(k-a,m-b)."""
    out = {}
    for (a, b, i, j), c in gen.items():
        for s in range(i + 1):
            cs = comb(i, s) * (-alpha) ** (i - s)
            if not cs:
                continue
            for t in range(j + 1):
                ct = comb(j, t) * (-beta) ** (j - t)
                if not ct:
                    continue
                key = (a + alpha, b + beta, s + i0, t + j0)
                out[key] = out.get(key, 0) + c * cs * ct
    return {k_: v for k_, v in out.items() if v}


# L1 = 1 - E^{-1} - X - m X^3 ;  L_N = 1 - X - XY - (q-1) X^3 (1+Y)^2   (second index = m resp. q)
L1 = {(0, 0, 0, 0): 1, (0, 1, 0, 0): -1, (1, 0, 0, 0): -1, (3, 0, 0, 1): -1}
LN = {(0, 0, 0, 0): 1, (1, 0, 0, 0): -1, (1, 1, 0, 0): -1,
      (3, 0, 0, 1): -1, (3, 0, 0, 0): 1, (3, 1, 0, 1): -2, (3, 1, 0, 0): 2, (3, 2, 0, 1): -1, (3, 2, 0, 0): 1}
GENBOX = {'U': (3, 1), 'N': (3, 2)}


def predicted_gens(kind, A, B, mono_mult):
    """theorem: relations in the box = { Q * gen : supp Q in [0..A-ga]x[0..B-gb], monomials of Q in mono_mult }."""
    ga, gb = GENBOX[kind]
    gen = L1 if kind == 'U' else LN
    out = []
    if A < ga or B < gb:
        return out
    for al in range(A - ga + 1):
        for be in range(B - gb + 1):
            for (i0, j0) in mono_mult:
                out.append(left_mul(al, be, i0, j0, gen))
    return out


def formula(kind, A, B, D=None, Dk=None, Dm=None):
    bb = B if kind == 'U' else B - 1
    if A < 3 or bb < 1:
        return 0
    if D is not None:
        return (A - 2) * bb * D * (D + 1) // 2 if D >= 1 else 0
    return (A - 2) * bb * (Dk + 1) * Dm if Dm >= 1 else 0


def exact_zero(tab, op, k0, m0, Kmax, Mmax):
    items = list(op.items())
    for k in range(k0, Kmax + 1):
        for m in range(m0, Mmax + 1):
            if sum(c * k ** i * m ** j * tab[k - a][m - b] for (a, b, i, j), c in items):
                return False
    return True


TABS = {'U': UT, 'N': NT}
TABP = {(kind, p): [[x % p for x in row] for row in TABS[kind]] for kind in TABS for p in PRIMES}


def kernel_case(kind, A, B, D=None, Dk=None, Dm=None, K=40, M=40, shift=0):
    if D is not None:
        monos = monos_total(D)
        mult = monos_total(D - 1) if D >= 1 else []
        lab = '%s(A,B,D)=(%d,%d,%d)' % (kind, A, B, D)
    else:
        monos = monos_graded(Dk, Dm)
        mult = monos_graded(Dk, Dm - 1) if Dm >= 1 else []
        lab = '%s(A,B,Dk,Dm)=(%d,%d,%d,%d)' % (kind, A, B, Dk, Dm)
    unk = unknowns(A, B, monos)
    idx = {u: t for t, u in enumerate(unk)}
    k0, m0 = A + shift, B + shift
    kers = []
    for p in PRIMES:
        rows = rows_mod(TABP[(kind, p)], unk, k0, m0, K, M, p)
        kers.append(len(unk) - rank_mod(rows, p))
    gens = predicted_gens(kind, A, B, mult)
    inbox = all(a <= A and b <= B and ((i + j <= D) if D is not None else (i <= Dk and j <= Dm))
                for g in gens for (a, b, i, j) in g)
    vecs = []
    for g in gens:
        v = [0] * len(unk)
        for key, c in g.items():
            v[idx[key]] += c
        vecs.append(v)
    gr = rank_mod(vecs, PRIMES[0]) if vecs else 0
    ex = all(exact_zero(TABS[kind], g, k0, m0, K, M) for g in gens)
    f = formula(kind, A, B, D, Dk, Dm)
    nrows = (K - k0 + 1) * (M - m0 + 1)
    good_ = (kers[0] == kers[1] == gr == len(gens) == f) and inbox and ex and nrows >= len(unk)
    return good_, '%s quad=[%d..%d]x[%d..%d] %du/%deq ker_p1=%d ker_p2=%d gens=%d(rank %d,inbox %s,exact %s) formula=%d' % (
        lab, k0, K, m0, M, len(unk), nrows, kers[0], kers[1], len(gens), gr, inbox, ex, f)


def konly_case(kind, A, B, D, K=40, M=40):
    unk = unknowns(A, B, [(i, 0) for i in range(D + 1)])
    rk = []
    for p in PRIMES:
        rows = rows_mod(TABP[(kind, p)], unk, A, B, K, M, p)
        rk.append(rank_mod(rows, p))
    ok_ = all(r == len(unk) for r in rk)
    return ok_, '%s k-only (A,B,deg)=(%d,%d,%d): %du rank_p1=%d rank_p2=%d' % (kind, A, B, D, len(unk), rk[0], rk[1])


# sanity: numpy elimination == pure-python elimination on random small matrices and one real system
rnd = random.Random(20261004)
ok = True
for _ in range(30):
    nr, nc = rnd.randint(1, 25), rnd.randint(1, 25)
    p = PRIMES[0]
    mat = [[rnd.choice([0, 0, 1, rnd.randrange(p)]) for _ in range(nc)] for _ in range(nr)]
    # plant dependencies
    if nr > 3:
        mat[-1] = [(x + 3 * y) % p for x, y in zip(mat[0], mat[1])]
    ok &= (rank_np(mat, p) == rank_py(mat, p)) if HAVE_NP else True
unk = unknowns(4, 2, monos_total(2))
rows = rows_mod(TABP[('U', PRIMES[1])], unk, 4, 2, 30, 30, PRIMES[1])
ok &= (rank_np(rows, PRIMES[1]) == rank_py(rows, PRIMES[1])) if HAVE_NP else True
report('X2-C0', ok, 'own numpy GF(p) elimination == own pure-Python elimination (30 random matrices + one real U system) '
                    '(numpy=%s)' % HAVE_NP)

U_TOTAL = [(3, 1, 1), (3, 1, 2), (4, 1, 1), (4, 1, 3), (5, 1, 2), (3, 2, 2), (4, 2, 1), (3, 3, 3), (7, 2, 2),
           (6, 3, 2), (8, 1, 2), (3, 1, 9), (4, 4, 3), (2, 5, 3), (5, 0, 5), (4, 3, 0), (9, 3, 1)]
U_GRADED = [(3, 1, 0, 1), (4, 1, 2, 1), (3, 2, 1, 2), (5, 1, 0, 2), (4, 3, 2, 2), (6, 2, 3, 1), (3, 3, 4, 0)]
N_TOTAL = [(3, 2, 1), (4, 2, 1), (3, 3, 1), (3, 2, 2), (4, 3, 2), (5, 2, 3), (3, 4, 3), (6, 4, 1), (7, 3, 2),
           (3, 2, 9), (5, 5, 2), (3, 1, 4), (2, 5, 3), (6, 1, 2)]
N_GRADED = [(3, 2, 0, 1), (4, 3, 1, 1), (3, 3, 2, 2), (5, 2, 0, 3), (4, 4, 3, 1), (3, 2, 4, 0)]

for kind, lst_t, lst_g in (('U', U_TOTAL, U_GRADED), ('N', N_TOTAL, N_GRADED)):
    allok = True
    descs = []
    for (A, B, D) in lst_t:
        o, d = kernel_case(kind, A, B, D=D)
        allok &= o
        descs.append(d)
    for (A, B, Dk, Dm) in lst_g:
        o, d = kernel_case(kind, A, B, Dk=Dk, Dm=Dm)
        allok &= o
        descs.append(d)
    report('X2-C-' + kind, allok, 'kernel dim mod two primes == #predicted left multiples (exactly zero on the quadrant, '
                                  'independent mod p) == formula; ' + ' | '.join(descs))

for kind in ('U', 'N'):
    allok = True
    descs = []
    for (A, B, D) in [(5, 5, 8), (8, 2, 8), (2, 8, 8), (12, 0, 10), (0, 12, 10), (7, 7, 4), (3, 3, 20), (20, 2, 3)]:
        o, d = konly_case(kind, A, B, D)
        allok &= o
        descs.append(d)
    report('X2-C-konly-' + kind, allok, 'no relation with coefficients depending on k only (full column rank mod two '
                                        'primes, quadrant [A..40]x[B..40]): ' + ' | '.join(descs))


# =====================================================================================
# Part D: exact integer kernel dimension (no modular arithmetic) in small boxes
# =====================================================================================
def exact_rank(M):
    A = [row[:] for row in M]
    nr = len(A)
    nc = len(A[0]) if A else 0
    r = 0
    for c in range(nc):
        piv = None
        best = None
        for i in range(r, nr):
            if A[i][c] != 0:
                sz = sum(abs(x).bit_length() for x in A[i])
                if best is None or sz < best:
                    best, piv = sz, i
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pr = A[r]
        pc = pr[c]
        for i in range(r + 1, nr):
            f = A[i][c]
            if f:
                g = gcd(pc, f)
                a1, b1 = pc // g, f // g
                row = [a1 * x - b1 * y for x, y in zip(A[i], pr)]
                cont = 0
                for x in row:
                    if x:
                        cont = gcd(cont, x)
                        if cont == 1:
                            break
                if cont > 1:
                    row = [x // cont for x in row]
                A[i] = row
        r += 1
    return r


EXACT_CASES = [('U', (3, 1, 1), None), ('U', (3, 1, 2), None), ('U', (4, 1, 1), None), ('U', (4, 2, 1), None),
               ('U', (5, 1, 1), None), ('U', (3, 2, 2), None), ('U', None, (4, 1, 1, 1)),
               ('N', (3, 2, 1), None), ('N', (4, 2, 1), None), ('N', (3, 3, 1), None), ('N', (3, 2, 2), None),
               ('N', None, (4, 3, 1, 1))]
allok = True
descs = []
for kind, tot, gr_ in EXACT_CASES:
    if tot is not None:
        A, B, D = tot
        monos, mult, f = monos_total(D), monos_total(D - 1), formula(kind, A, B, D=D)
    else:
        A, B, Dk, Dm = gr_
        monos, mult, f = monos_graded(Dk, Dm), monos_graded(Dk, Dm - 1), formula(kind, A, B, Dk=Dk, Dm=Dm)
    unk = unknowns(A, B, monos)
    W = 15
    rows = rows_exact(TABS[kind], unk, range(A, A + W), range(B, B + W))
    rk = exact_rank(rows)
    gens = predicted_gens(kind, A, B, mult)
    ex = all(exact_zero(TABS[kind], g, A, B, 40, 40) for g in gens)
    this = (len(unk) - rk == len(gens) == f) and ex
    allok &= this
    descs.append('%s %s: %du, %d exact eqs (window %dx%d), exact kernel=%d, gens=%d, formula=%d, gens exact on [A..40]x[B..40]=%s'
                 % (kind, tot if tot else gr_, len(unk), len(rows), W, W, len(unk) - rk, len(gens), f, ex))
report('X2-D', allok, 'exact integer elimination (no modular step): kernel on a sub-window == #predicted generators == formula; '
                      + ' | '.join(descs))

# =====================================================================================
# Part E: quadrant-shift test (relations valid only far from the boundary would show up here)
# =====================================================================================
allok = True
descs = []
for kind, A, B, D in [('U', 5, 2, 2), ('U', 4, 3, 3), ('U', 3, 1, 4), ('N', 4, 3, 2), ('N', 5, 4, 2), ('N', 3, 2, 4)]:
    for sh in (6, 12):
        o, d = kernel_case(kind, A, B, D=D, K=50, M=50, shift=sh)
        allok &= o
        descs.append(d)
report('X2-E', allok, 'kernel unchanged when the quadrant is shrunk by 6 and 12 (table k,m<=50): ' + ' | '.join(descs))


# =====================================================================================
# Part F: generating-function dictionary and transport identity (Theorem 3')
# =====================================================================================
def lp_add(*ps):
    r = {}
    for p_ in ps:
        for key, c in p_.items():
            r[key] = r.get(key, 0) + c
    return {k_: v for k_, v in r.items() if v != 0}


def lp_mul(p_, q_):
    r = {}
    for (a, b), c in p_.items():
        for (e, f), d in q_.items():
            r[(a + e, b + f)] = r.get((a + e, b + f), 0) + c * d
    return {k_: v for k_, v in r.items() if v != 0}


def lp_sc(p_, c):
    return {k_: v * c for k_, v in p_.items() if v * c != 0}


def lp_thy(p_):
    return {(a, b): c * b for (a, b), c in p_.items() if c * b != 0}


ONE = {(0, 0): 1}
Xp, Yp = {(1, 0): 1}, {(0, 1): 1}
OPY = {(0, 0): 1, (0, 1): 1}
OPY2 = lp_mul(OPY, OPY)
X3 = {(3, 0): 1}
YINV = {(0, -1): 1}


def ellN(g):
    # l_N = 1 - x - x y - (theta_y - 1) o x^3 (1+y)^2
    h = lp_mul(lp_mul(X3, OPY2), g)
    return lp_add(g, lp_sc(lp_mul(Xp, g), -1), lp_sc(lp_mul(lp_mul(Xp, Yp), g), -1), lp_sc(lp_thy(h), -1), h)


def lhs_transport(g):
    # y * psi(l1) applied to (1+y)^2 g / y,  psi(l1) = (1+y)^{-1} - x - x^3 (1+y) theta_y
    h = lp_mul(lp_mul(OPY2, g), YINV)            # (1+y)^2 g / y   (Laurent)
    t1 = lp_mul(lp_mul(OPY, g), YINV)            # (1+y)^{-1} h = (1+y) g / y
    t2 = lp_sc(lp_mul(Xp, h), -1)
    t3 = lp_sc(lp_mul(lp_mul(X3, OPY), lp_thy(h)), -1)
    return lp_mul(Yp, lp_add(t1, t2, t3))


ok = True
rr = random.Random(7)
for _ in range(40):
    g = {}
    for _t in range(rr.randint(1, 12)):
        g[(rr.randint(0, 6), rr.randint(-4, 7))] = Fr(rr.randint(-9, 9), rr.randint(1, 7))
    g = {k_: v for k_, v in g.items() if v}
    ok &= (lhs_transport(g) == lp_mul(OPY, ellN(g)))
# dictionary: coefficients of l_N(Phi) are (L_N N)(k,q); both must equal 1 - x + x^3 + x^2 y^2 (k,q<=30)
KK = 30
Phi = {(k, q): NT[k][q] for k in range(KK + 1) for q in range(KK + 1) if NT[k][q]}
lphi = ellN(Phi)


def Nv(k, q):
    return NT[k][q] if (k >= 0 and q >= 0) else 0


arr = {}
for k in range(KK + 1):
    for q in range(KK + 1):
        v = (Nv(k, q) - Nv(k - 1, q) - Nv(k - 1, q - 1)
             - (q - 1) * (Nv(k - 3, q) + 2 * Nv(k - 3, q - 1) + Nv(k - 3, q - 2)))
        if v:
            arr[(k, q)] = v
lphi_trunc = {key: v for key, v in lphi.items() if key[0] <= KK and key[1] <= KK}
ok &= (lphi_trunc == arr == {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1})


# transported relation for L = l_N: sigma^{-1}(l_N Phi - l_N alpha) == t * l1 F, alpha = 1/(1+y)
# l_N alpha as a y-series (operator applied to the truncated series of 1/(1+y)) vs closed form (1-x-xy)/(1+y) + x^3
QT = 25
alpha = {(0, q): (-1) ** q for q in range(QT + 1)}
la = {key: v for key, v in ellN(alpha).items() if key[1] <= QT - 2}
closed = {}
for q in range(QT + 1):
    s = (-1) ** q
    closed[(0, q)] = closed.get((0, q), 0) + s                       # 1/(1+y)
    closed[(1, q)] = closed.get((1, q), 0) - s                       # -x/(1+y)
    if q >= 1:
        closed[(1, q)] = closed.get((1, q), 0) - (-1) ** (q - 1)     # -x y/(1+y)
closed[(3, 0)] = closed.get((3, 0), 0) + 1
closed = {key: v for key, v in closed.items() if v and key[1] <= QT - 2}
ok &= (la == closed)
# sigma^{-1}: y -> t/(1-t). (l_N Phi - l_N alpha) = 1 - x + x^2 y^2 - (1-x-xy)/(1+y); compare with t + x^2 t^2/(1-t)^2
TT = 20


def sub_y(poly_in_y_coeffs):
    """sum_q c_q y^q  ->  t-series (degree <= TT) under y = t/(1-t)."""
    out = [0] * (TT + 1)
    for q, c in poly_in_y_coeffs.items():
        if q == 0:
            out[0] += c
            continue
        for n in range(q, TT + 1):
            out[n] += c * comb(n - 1, q - 1)
    return out


diff = lp_add({(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}, lp_sc({key: v for key, v in closed.items()}, -1))
lhs_t = {}
for a in range(0, 4):
    col = {key[1]: v for key, v in diff.items() if key[0] == a}
    lhs_t[a] = sub_y(col)
rhs_t = {a: [0] * (TT + 1) for a in range(0, 4)}
rhs_t[0][1] = 1
for n in range(2, TT + 1):
    rhs_t[2][n] = n - 1                     # x^2 t^2/(1-t)^2 = x^2 sum_{n>=2} (n-1) t^n
ok &= all(lhs_t[a][:QT - 3] == rhs_t[a][:QT - 3] for a in range(4))
report('X2-F', ok, 'transport identity y*psi(l1)o((1+y)^2/y) == (1+y)*l_N on 40 random Laurent polynomials (exact); '
                   'coefficients of l_N(Phi) == (L_N N)(k,q) == 1-x+x^3+x^2y^2 (k,q<=30); special case L=l_N of the '
                   'transport: sigma^{-1}(l_N Phi - l_N alpha) == t*(l1 F) == t + x^2 t^2/(1-t)^2')


# =====================================================================================
# Part G: pole facts (exact polynomial arithmetic)
# =====================================================================================
def ptrim(p_):
    p_ = list(p_)
    while p_ and p_[-1] == 0:
        p_.pop()
    return p_


def padd(p_, q_):
    n = max(len(p_), len(q_))
    return ptrim([(p_[i] if i < len(p_) else 0) + (q_[i] if i < len(q_) else 0) for i in range(n)])


def pmul(p_, q_):
    if not p_ or not q_:
        return []
    r = [0] * (len(p_) + len(q_) - 1)
    for i, a in enumerate(p_):
        if a:
            for j, b in enumerate(q_):
                r[i + j] += a * b
    return ptrim(r)


def pmod(p_, q_):
    p_ = [Fr(a) for a in ptrim(p_)]
    q_ = [Fr(a) for a in ptrim(q_)]
    while len(p_) >= len(q_) and p_:
        c = p_[-1] / q_[-1]
        d = len(p_) - len(q_)
        for i, b in enumerate(q_):
            p_[i + d] -= c * b
        p_ = ptrim(p_)
    return p_


def pgcd(p_, q_):
    a, b = ptrim(p_), ptrim(q_)
    while b:
        a, b = b, pmod(a, b)
    return [Fr(c) / Fr(a[-1]) for c in a] if a else []


def pder(p_):
    return ptrim([i * p_[i] for i in range(1, len(p_))])


def bpoly(i):
    return ptrim([1, -1, 0, -i])


MM = 20
P = {-1: [1]}
Wd = {-1: [1]}
for m in range(0, MM + 1):
    P[m] = pmul(P[m - 1], bpoly(m))
    Wd[m] = padd(Wd[m - 1], [0, 0] + [m * c for c in P[m - 1]])


def series(num, den, n):
    den = [Fr(c) for c in den] + [Fr(0)] * n
    num = [Fr(c) for c in num] + [Fr(0)] * n
    out = []
    for k in range(n):
        s = num[k] - sum(den[i] * out[k - i] for i in range(1, k + 1))
        out.append(s / den[0])
    return out


ok = all([int(c) for c in series(Wd[m], P[m], 41)] == [UT[k][m] for k in range(41)] for m in range(0, 16))
for m in range(0, MM + 1):
    for v in range(0, m + 1):
        ok &= (pmod(Wd[m], bpoly(v)) == pmod(Wd[v], bpoly(v)))
    # W_m = 1 + sum_j j (m)_j x^{3j+2} mod b_m (all coefficients positive)
    Om = [0] * (3 * m + 3)
    Om[0] = 1
    ff = 1
    for j in range(1, m + 1):
        ff *= (m - j + 1)
        Om[3 * j + 2] += j * ff
    ok &= (pmod(Wd[m], bpoly(m)) == pmod(Om, bpoly(m)))
for m in range(0, 13):
    ok &= (pgcd(P[m], pder(P[m])) == [Fr(1)])
report('X2-G', ok, 'G_m=W_m/P_m series == own DP (k<=40,m<=15); W_m == W_v mod b_v for 0<=v<=m<=20 (so Res_{x_v}G_m = '
                   'W_v(x_v)/P_m\'(x_v), W_v(x_v)>=1); W_m == 1+sum_j j(m)_j x^{3j+2} mod b_m (m<=20); P_m squarefree (m<=12)')

npass = sum(1 for _, o in RES if o)
say('# elapsed %.1fs (numpy=%s)' % (time.time() - T0, HAVE_NP))
say('SUMMARY x2-dfinite pass=%d fail=%d' % (npass, len(RES) - npass))
sys.exit(0 if npass == len(RES) else 1)
