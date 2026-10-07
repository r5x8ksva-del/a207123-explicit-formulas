# Independent re-check of the T2.7' proof (Lemmas A, F, S) on concrete proper terms.
# Exact arithmetic throughout (Python ints / Fractions); numpy only for a mod-p rank/pivot search,
# whose output is always re-verified exactly.
from fractions import Fraction
from math import factorial, comb, isqrt, prod, gcd
import itertools
import numpy as np

SMALLP = 2147483647          # 2^31-1 (prime), numpy pivot search
BIGP = (1 << 521) - 1        # Mersenne prime, exact solve + rational reconstruction


def lin(L, p):
    c, k0 = L
    return sum(ci * pi for ci, pi in zip(c, p)) + k0


def linpart(L, w):
    return sum(ci * wi for ci, wi in zip(L[0], w))


def zpow(z, p):
    v = Fraction(1)
    for zi, pi in zip(z, p):
        v *= Fraction(zi) ** pi
    return v


# ---------------- multivariate integer polynomials: dict exps -> int ----------------
def pmul(a, b):
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            r[e] = r.get(e, 0) + ca * cb
    return {e: c for e, c in r.items() if c}


def plin(n, coeffs, const):
    d = {}
    if const:
        d[(0,) * n] = const
    for i, c in enumerate(coeffs):
        if c:
            e = [0] * n
            e[i] = 1
            d[tuple(e)] = c
    return d


def pshift(P, w):
    """P(x - w)"""
    n = len(w)
    res = {}
    for e, c in P.items():
        terms = {(0,) * n: c}
        for i in range(n):
            if e[i] == 0:
                continue
            new = {}
            for ee, cc in terms.items():
                for t in range(e[i] + 1):
                    coef = comb(e[i], t) * (-w[i]) ** (e[i] - t)
                    if coef == 0:
                        continue
                    e2 = list(ee)
                    e2[i] += t
                    e2 = tuple(e2)
                    new[e2] = new.get(e2, 0) + cc * coef
            terms = new
        for ee, cc in terms.items():
            res[ee] = res.get(ee, 0) + cc
    return {e: c for e, c in res.items() if c}


def peval(P, p):
    s = 0
    for e, c in P.items():
        t = c
        for ei, pi in zip(e, p):
            if ei:
                t *= pi ** ei
        s += t
    return s


def uni_eval(coefs, k):
    s = 0
    for c in reversed(coefs):
        s = s * k + c
    return s


# ---------------- proper hypergeometric term (WZ 4.1.2) ----------------
class Term:
    def __init__(self, name, num, den, P=None, z=None, r=1):
        self.name, self.r, self.n = name, r, r + 2
        self.num = [(tuple(c), int(k)) for c, k in num]
        self.den = [(tuple(c), int(k)) for c, k in den]
        self.P = P if P is not None else {(0,) * self.n: 1}
        self.z = tuple(z) if z is not None else (1,) * self.n
        for c, _ in self.num + self.den:
            assert len(c) == self.n
        self._cache = {}

    def wd(self, p):
        return all(lin(A, p) >= 0 for A in self.num)

    def val(self, p):
        """None if not well-defined, else exact value (1/(neg)! = 0)."""
        p = tuple(p)
        if p in self._cache:
            return self._cache[p]
        if not self.wd(p):
            v = None
        elif any(lin(B, p) < 0 for B in self.den):
            v = Fraction(0)
        else:
            v = Fraction(peval(self.P, p))
            if v != 0:
                for A in self.num:
                    v *= factorial(lin(A, p))
                for B in self.den:
                    v /= factorial(lin(B, p))
                v *= zpow(self.z, p)
        self._cache[p] = v
        return v

    def tilde(self, p):
        v = self.val(p)
        return Fraction(0) if v is None else v

    def beta_gamma(self):
        beta = sum(sum(abs(c) for c in L[0][1:]) for L in self.num + self.den)
        gamma = sum(abs(L[0][0]) for L in self.num + self.den)
        degP = max(sum(e) for e in self.P)
        return beta, gamma, degP


def window(J, I, r):
    return list(itertools.product(range(J + 1), range(I + 1), *([range(I + 1)] * r)))


def sub(p, w):
    return tuple(a - b for a, b in zip(p, w))


class LemmaA:
    """Builds d_s, d_s^max, e_s, e_s^min, T*, Q_w exactly as in the note (section 3.3)."""

    def __init__(self, T, J, I):
        self.T, self.J, self.I = T, J, I
        n, r = T.n, T.r
        self.Om = window(J, I, r)
        self.d = [[linpart(A, w) for w in self.Om] for A in T.num]
        self.e = [[linpart(B, w) for w in self.Om] for B in T.den]
        self.dmax = [max(x) for x in self.d]
        self.emin = [min(x) for x in self.e]
        self.wmax = (J, I) + (I,) * r
        self.zmax = zpow(T.z, self.wmax)
        self.Qint = []          # Q_w * z^{wmax}  (integer polynomial)
        for iw, w in enumerate(self.Om):
            q = pshift(T.P, w)
            for s, A in enumerate(T.num):
                for i in range(self.d[s][iw], self.dmax[s]):      # t = A_s - i, i = d_s(w)..d_s^max-1
                    q = pmul(q, plin(n, A[0], A[1] - i))
            for s, B in enumerate(T.den):
                for i in range(self.emin[s], self.e[s][iw]):      # t = B_s - i, i = e_s^min..e_s(w)-1
                    q = pmul(q, plin(n, B[0], B[1] - i))
            zf = 1
            for zi, wi, wm in zip(T.z, w, self.wmax):
                zf *= zi ** (wm - wi)
            self.Qint.append({ee: c * zf for ee, c in q.items()})

    def Q_prod(self, iw, p):
        """Q_w(p) evaluated from its product definition (fast)."""
        T, w = self.T, self.Om[iw]
        v = Fraction(peval(T.P, sub(p, w)))
        for s, A in enumerate(T.num):
            a = lin(A, p)
            for i in range(self.d[s][iw], self.dmax[s]):
                v *= a - i
        for s, B in enumerate(T.den):
            b = lin(B, p)
            for i in range(self.emin[s], self.e[s][iw]):
                v *= b - i
        return v / zpow(T.z, w)

    def Q_poly(self, iw, p):
        return Fraction(peval(self.Qint[iw], p)) / self.zmax

    def Tstar(self, p):
        T = self.T
        if any(lin(A, p) - self.dmax[s] < 0 for s, A in enumerate(T.num)):
            return None
        if any(lin(B, p) - self.emin[s] < 0 for s, B in enumerate(T.den)):
            return Fraction(0)
        v = Fraction(1)
        for s, A in enumerate(T.num):
            v *= factorial(lin(A, p) - self.dmax[s])
        for s, B in enumerate(T.den):
            v /= factorial(lin(B, p) - self.emin[s])
        return v * zpow(T.z, p)

    def mj_degree(self):
        return max(sum(e[1:]) for q in self.Qint for e in q)

    def D_bound(self):
        beta, gamma, degP = self.T.beta_gamma()
        return degP + beta * self.I + gamma * self.J

    # ---- linear system  sum_{w,t} a_{w,t} k^t Q_w == 0 ----
    def system(self, dk, extra_C0=False):
        cols = [(iw, t) for iw in range(len(self.Om)) for t in range(dk + 1)]
        rowsidx, entries = {}, []
        for ci, (iw, t) in enumerate(cols):
            for e, c in self.Qint[iw].items():
                e2 = (e[0] + t,) + e[1:]
                ri = rowsidx.setdefault(e2, len(rowsidx))
                entries.append((ri, ci, c))
        nrows = len(rowsidx)
        if extra_C0:           # C_0 = sum_nu A_nu = 0  coefficientwise
            groups = {}
            for ci, (iw, t) in enumerate(cols):
                w = self.Om[iw]
                groups.setdefault((w[0], w[1], t), []).append(ci)
            for _, cis in sorted(groups.items()):
                for ci in cis:
                    entries.append((nrows, ci, 1))
                nrows += 1
        return cols, nrows, entries

    def verify_identity(self, sol):
        """exact check: sum_w a_w(k) Qint_w == 0 as polynomial; sol: dict iw -> list coeffs in k"""
        acc = {}
        for iw, coefs in sol.items():
            for t, a in enumerate(coefs):
                if a == 0:
                    continue
                for e, c in self.Qint[iw].items():
                    e2 = (e[0] + t,) + e[1:]
                    acc[e2] = acc.get(e2, 0) + a * c
        return all(v == 0 for v in acc.values())


def ratrec(x, P):
    bound = isqrt(P // 2)
    r0, r1, t0, t1 = P, x % P, 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        t0, t1 = t1, t0 - q * t1
    if t1 == 0 or abs(t1) > bound:
        return None
    if t1 < 0:
        r1, t1 = -r1, -t1
    return Fraction(r1, t1)


def nullspace(nrows, ncols, entries, maxvecs=12):
    """Integer nullspace vectors (exactly verified) of the sparse integer matrix."""
    M = np.zeros((nrows, ncols), dtype=np.int64)
    for ri, ci, v in entries:
        M[ri, ci] = (int(M[ri, ci]) + v) % SMALLP
    used = np.zeros(nrows, dtype=bool)
    pivcols, pivrows = [], []
    for c in range(ncols):
        cand = np.nonzero((M[:, c] != 0) & ~used)[0]
        if len(cand) == 0:
            continue
        r0 = int(cand[0])
        inv = pow(int(M[r0, c]), SMALLP - 2, SMALLP)
        M[r0] = (M[r0] * inv) % SMALLP
        f = M[:, c].copy()
        f[r0] = 0
        M = (M - np.outer(f, M[r0])) % SMALLP
        used[r0] = True
        pivcols.append(c)
        pivrows.append(r0)
    free = [c for c in range(ncols) if c not in set(pivcols)]
    if not free:
        return []
    # exact dense rows (pivot rows only), RREF mod BIGP, rational reconstruction
    rowmap = {r: i for i, r in enumerate(pivrows)}
    R = [[0] * ncols for _ in pivrows]
    for ri, ci, v in entries:
        if ri in rowmap:
            R[rowmap[ri]][ci] += v
    R = [[x % BIGP for x in row] for row in R]
    pc, row = [], 0
    for c in range(ncols):
        piv = next((i for i in range(row, len(R)) if R[i][c]), None)
        if piv is None:
            continue
        R[row], R[piv] = R[piv], R[row]
        inv = pow(R[row][c], BIGP - 2, BIGP)
        R[row] = [(x * inv) % BIGP for x in R[row]]
        for i in range(len(R)):
            if i != row and R[i][c]:
                f = R[i][c]
                R[i] = [(x - f * y) % BIGP for x, y in zip(R[i], R[row])]
        pc.append(c)
        row += 1
    free2 = [c for c in range(ncols) if c not in set(pc)]
    vecs = []
    for f in free2[:maxvecs]:
        v = [Fraction(0)] * ncols
        v[f] = Fraction(1)
        ok = True
        for i, c in enumerate(pc):
            q = ratrec((-R[i][f]) % BIGP, BIGP)
            if q is None:
                ok = False
                break
            v[c] = q
        if not ok:
            continue
        L = 1
        for x in v:
            L = L * x.denominator // gcd(L, x.denominator)
        vi = [int(x * L) for x in v]
        # exact verification against the FULL system
        res = {}
        for ri, ci, val in entries:
            if vi[ci]:
                res[ri] = res.get(ri, 0) + val * vi[ci]
        if all(x == 0 for x in res.values()):
            vecs.append(vi)
    return vecs


def vec_to_sol(LA, cols, vec):
    sol = {}
    for (iw, t), a in zip(cols, vec):
        if a:
            sol.setdefault(iw, [])
    dk = max(t for _, t in cols)
    out = {}
    for iw in sol:
        out[iw] = [0] * (dk + 1)
    for (iw, t), a in zip(cols, vec):
        if a:
            out[iw][t] = a
    return out


def find_recurrence(T, windows, extra_C0=False, combine=True, seed=1):
    """Search windows [(J,I,dk),...]; return (LA, sol, nullity, cols) for first with nontrivial solution."""
    import random
    rnd = random.Random(seed)
    for (J, I, dk) in windows:
        LA = LemmaA(T, J, I)
        cols, nrows, entries = LA.system(dk, extra_C0=extra_C0)
        vecs = nullspace(nrows, len(cols), entries)
        if vecs:
            if combine and len(vecs) > 1:
                cs = [rnd.randint(1, 5) for _ in vecs]
                vec = [sum(c * v[i] for c, v in zip(cs, vecs)) for i in range(len(cols))]
            else:
                vec = vecs[0]
            sol = vec_to_sol(LA, cols, vec)
            assert LA.verify_identity(sol), "identity verification failed"
            return LA, sol, len(vecs), (J, I, dk), nrows, len(cols)
    return None


# ---------------- Lemma S machinery ----------------
def uadd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def lemmaS_ops(LA, sol):
    r, I = LA.T.r, LA.I
    nus = list(itertools.product(range(I + 1), repeat=r))
    A = {nu: {} for nu in nus}
    for iw, coefs in sol.items():
        w = LA.Om[iw]
        A[tuple(w[2:])][(w[0], w[1])] = coefs
    C = {}
    for al in nus:
        acc = {}
        for nu in nus:
            if all(x >= y for x, y in zip(nu, al)):
                b = prod(comb(x, y) for x, y in zip(nu, al))
                for key, pol in A[nu].items():
                    acc[key] = uadd(acc.get(key, [0]), [b * c for c in pol])
        C[al] = {key: v for key, v in acc.items() if any(v)}
    nonzero = [al for al in nus if C[al]]
    minimal = [al for al in nonzero
               if not any(be != al and all(x <= y for x, y in zip(be, al)) for be in nonzero)]
    # invert: A_nu = sum_{al>=nu} (-1)^{|al-nu|} C(al,nu) C_al   (check triangular inversion)
    inv_ok = True
    for nu in nus:
        acc = {}
        for al in nus:
            if all(x >= y for x, y in zip(al, nu)):
                b = (-1) ** sum(x - y for x, y in zip(al, nu)) * prod(comb(x, y) for x, y in zip(al, nu))
                for key, pol in C[al].items():
                    acc[key] = uadd(acc.get(key, [0]), [b * c for c in pol])
        acc = {k_: v for k_, v in acc.items() if any(v)}
        tgt = {k_: v for k_, v in A[nu].items() if any(v)}
        keys = set(acc) | set(tgt)
        for k_ in keys:
            a1, a2 = acc.get(k_, [0]), tgt.get(k_, [0])
            n = max(len(a1), len(a2))
            if [*(a1 + [0] * (n - len(a1)))] != [*(a2 + [0] * (n - len(a2)))]:
                inv_ok = False
    return C, nonzero, minimal, inv_ok


def binom_poly(x, b):
    if b < 0:
        return 0
    v = Fraction(1)
    for i in range(b):
        v *= (x - i)
    return v / factorial(b)


def sigma_minus_1_pow(f, alpha, jv):
    """((sigma-1)^alpha f)(jv), sigma_l: j_l -> j_l - 1 (shift down)"""
    tot = Fraction(0)
    for ii in itertools.product(*[range(a + 1) for a in alpha]):
        c = prod(comb(a, i) * (-1) ** (a - i) for a, i in zip(alpha, ii))
        tot += c * f(tuple(j - i for j, i in zip(jv, ii)))
    return tot
