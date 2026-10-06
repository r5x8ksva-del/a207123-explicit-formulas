# -*- coding: utf-8 -*-
"""s6-t27 复核「推论 T2.7′」用的公共函数。只用 Python 标准库（fractions、math、itertools、random）。

对象（记号同 notes/02-主Agent-不确定三处加固.md §3）：
  * proper 超几何项 T(k,m,j⃗)：P(p)·∏(A_s(p))!/∏(B_s(p))!·z^p，A_s、B_s 是整系数一次式加整数常数；
    良定义 ⇔ 所有分子参数 A_s(p)≥0；良定义且某个分母参数 <0（或 P(p)=0）时值为 0；
    T̃ = T（良定义处）、0（其余处）。
  * 引理 A：Ω=Ω_{I,J}={(j,μ,ν⃗):0≤j≤J,0≤μ≤I,0≤ν⃗≤I}；d_s(ω)、e_s(ω)、d_s^max、e_s^min；
    T*(p)、Q_ω(p)（按定义的乘积形式求值，不展开）；求 Σ_ω a_ω(k)Q_ω≡0 的非零解 a_ω∈Q[k]。
    求解：在随机整点上取样列方程（先模素数找最小的 (J,I,deg)，再用精确有理数解），
    然后在乘积网格上逐点核对恒等式——多项式各变量次数都小于网格边长时，网格上为 0 ⇔ 恒为 0，
    所以这一步是严格的，不是抽样。
  * 引理 S：A_ν⃗、C_α=Σ_{ν⃗≥α}C(ν⃗,α)A_ν⃗、极小元 α*、C_{α*}；分部求和恒等式的逐点核对。
被各脚本 import；各脚本开头设置 sys.dont_write_bytecode=True，不在仓库里留下 __pycache__。
"""
import sys
sys.dont_write_bytecode = True
try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
import itertools
import random
import time
from fractions import Fraction
from math import factorial, comb

PRIME = (1 << 61) - 1          # 只用于「搜索」：模 p 的秩 ≤ 有理秩，见 nullity_modp 的说明

# ------------------------------------------------------------------ 小工具

def dot(c, w):
    return sum(a * b for a, b in zip(c, w))


def binom_poly(x, b):
    """多项式二项式 C(x,b)=x(x-1)…(x-b+1)/b!（对一切整数 x 有定义）；b<0 时为 0。"""
    if b < 0:
        return Fraction(0)
    num = 1
    for i in range(b):
        num *= (x - i)
    return Fraction(num, factorial(b))


def binom_vec(xs, bs):
    v = Fraction(1)
    for x, b in zip(xs, bs):
        v *= binom_poly(x, b)
        if v == 0:
            return v
    return v


# ------------------------------------------------------------------ 多项式（dict {指数元组: Fraction}）

def p_add(p, q):
    r = dict(p)
    for e, c in q.items():
        v = r.get(e, 0) + c
        if v == 0:
            r.pop(e, None)
        else:
            r[e] = v
    return r


def p_mul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            v = r.get(e, 0) + c1 * c2
            if v == 0:
                r.pop(e, None)
            else:
                r[e] = v
    return r


def p_scale(p, c):
    if c == 0:
        return {}
    return {e: v * c for e, v in p.items()}


def p_const(c, n):
    return {} if c == 0 else {(0,) * n: Fraction(c)}


def p_lin(coeffs, const):
    n = len(coeffs)
    r = {}
    if const != 0:
        r[(0,) * n] = Fraction(const)
    for i, a in enumerate(coeffs):
        if a != 0:
            e = [0] * n
            e[i] = 1
            r[tuple(e)] = Fraction(a)
    return r


def p_eval(p, x):
    s = Fraction(0)
    for e, c in p.items():
        t = c
        for xi, ei in zip(x, e):
            if ei:
                t *= xi ** ei
        s += t
    return s


def p_shift(p, w):
    """返回 p(x - w)（展开）。"""
    n = len(w)
    r = {}
    for e, c in p.items():
        terms = {(0,) * n: Fraction(c)}
        for i in range(n):
            if e[i] == 0:
                continue
            new = {}
            for t in range(e[i] + 1):
                coef = comb(e[i], t) * (-w[i]) ** (e[i] - t)
                if coef == 0:
                    continue
                for ee, cc in terms.items():
                    e2 = list(ee)
                    e2[i] += t
                    e2 = tuple(e2)
                    new[e2] = new.get(e2, 0) + cc * coef
            terms = new
        r = p_add(r, terms)
    return r


def p_degs(p, n):
    """各变量的次数（零多项式返回全 0）。"""
    d = [0] * n
    for e in p:
        for i in range(n):
            d[i] = max(d[i], e[i])
    return d


def p_totdeg(p, idx):
    """在下标集 idx 上的总次数。"""
    return max((sum(e[i] for i in idx) for e in p), default=0)


# ------------------------------------------------------------------ proper 超几何项

class Term:
    """T(p)=P(p)·∏(A_s(p))!/∏(B_s(p))!·z^p，p=(k,m,j_1..j_r)。
    num、den：[(系数元组, 常数)]；P：多项式 dict（None 表示 1）；z：各分量非零的有理数元组（None 表示全 1）。"""

    def __init__(self, name, r, num, den, P=None, z=None, note=''):
        self.name = name
        self.r = r
        self.n = 2 + r
        self.num = [(tuple(c), int(d)) for c, d in num]
        self.den = [(tuple(c), int(d)) for c, d in den]
        for c, _ in self.num + self.den:
            assert len(c) == self.n and all(isinstance(a, int) for a in c)
        self.P = P if P is not None else p_const(1, self.n)
        self.z = tuple(Fraction(x) for x in z) if z is not None else (Fraction(1),) * self.n
        assert all(x != 0 for x in self.z)
        self.note = note
        self._cache = {}

    @staticmethod
    def lin(L, p):
        return dot(L[0], p) + L[1]

    def wd(self, p):
        return all(dot(c, p) + d >= 0 for c, d in self.num)

    def val(self, p):
        """良定义处的值（Fraction）；不良定义返回 None。"""
        p = tuple(p)
        v = self._cache.get(p, 0)
        if v != 0 or p in self._cache:
            return v
        if not self.wd(p):
            v = None
        else:
            v = Fraction(0)
            if all(dot(c, p) + d >= 0 for c, d in self.den):
                pv = p_eval(self.P, p)
                if pv != 0:
                    nu = 1
                    for c, d in self.num:
                        nu *= factorial(dot(c, p) + d)
                    de = 1
                    for c, d in self.den:
                        de *= factorial(dot(c, p) + d)
                    v = pv * Fraction(nu, de)
                    for zi, pi in zip(self.z, p):
                        if zi != 1 and pi != 0:
                            v *= zi ** pi
        self._cache[p] = v
        return v

    def tt(self, p):
        v = self.val(p)
        return Fraction(0) if v is None else v

    def beta_gamma(self):
        """引理 A 的 β=Σ‖b_s‖_1+Σ‖v_s‖_1（只取 (m,j⃗) 分量），γ=Σ|a_s|+Σ|u_s|（k 的系数）。"""
        beta = sum(sum(abs(a) for a in c[1:]) for c, _ in self.num + self.den)
        gamma = sum(abs(c[0]) for c, _ in self.num + self.den)
        return beta, gamma


def omega_set(r, I, J):
    return [tuple(w) for w in itertools.product(range(J + 1), range(I + 1), *([range(I + 1)] * r))]


class LemmaA:
    """引理 A 的 T*、Q_ω（乘积形式），以及 Σ_ω a_ω(k)Q_ω≡0 的求解与严格核对。"""

    def __init__(self, T, I, J):
        self.T, self.I, self.J = T, I, J
        self.Omega = omega_set(T.r, I, J)
        self.dmax = [max(dot(c, w) for w in self.Omega) for c, _ in T.num]
        self.emin = [min(dot(c, w) for w in self.Omega) for c, _ in T.den]
        self.Qfac = {}
        for w in self.Omega:
            facs = []
            for s, (c, d0) in enumerate(T.num):
                d = dot(c, w)
                for i in range(1, self.dmax[s] - d + 1):
                    facs.append((c, d0 - self.dmax[s] + i))      # t = A_s - d_s^max + i
            for s, (c, d0) in enumerate(T.den):
                e = dot(c, w)
                for i in range(1, e - self.emin[s] + 1):
                    facs.append((c, d0 - e + i))                 # t = B_s - e_s(ω) + i
            zf = Fraction(1)
            for zi, wi in zip(T.z, w):
                if wi:
                    zf *= zi ** (-wi)
            self.Qfac[w] = (facs, zf)
        n = T.n
        degP = p_degs(T.P, n)
        self.degQ = {}
        for w in self.Omega:
            facs, _ = self.Qfac[w]
            dq = list(degP)
            for c, _ in facs:
                for i in range(n):
                    if c[i] != 0:
                        dq[i] += 1
            self.degQ[w] = dq
        self.totdegQ_mj = {w: p_totdeg(T.P, range(1, n)) + sum(1 for c, _ in self.Qfac[w][0] if any(c[1:]))
                           for w in self.Omega}

    def Q(self, w, p):
        facs, zf = self.Qfac[w]
        v = p_eval(self.T.P, tuple(pi - wi for pi, wi in zip(p, w)))
        if v == 0:
            return Fraction(0)
        pr = 1
        for c, d in facs:
            pr *= dot(c, p) + d
            if pr == 0:
                return Fraction(0)
        return v * pr * zf

    def Q_expanded(self, w):
        facs, zf = self.Qfac[w]
        poly = p_shift(self.T.P, w)
        for c, d in facs:
            poly = p_mul(poly, p_lin(c, d))
        return p_scale(poly, zf)

    def Tstar(self, p):
        """T*(p)；分子参数有负数时返回 None（引理 F 的前提下不会发生）。"""
        nu = 1
        for s, (c, d) in enumerate(self.T.num):
            a = dot(c, p) + d - self.dmax[s]
            if a < 0:
                return None
            nu *= factorial(a)
        de = 1
        for s, (c, d) in enumerate(self.T.den):
            b = dot(c, p) + d - self.emin[s]
            if b < 0:
                return Fraction(0)
            de *= factorial(b)
        v = Fraction(nu, de)
        for zi, pi in zip(self.T.z, p):
            if zi != 1 and pi != 0:
                v *= zi ** pi
        return v

    def den_case(self, s, w, p):
        """引理 F 证明中分母的三种情形：1 普通展开；2 B_s-e_s(ω)<0≤B_s-e_s^min；3 B_s-e_s^min<0。"""
        c, d = self.T.den[s]
        B = dot(c, p) + d
        e = dot(c, w)
        if B - e >= 0:
            return 1
        if B - self.emin[s] >= 0:
            return 2
        return 3

    # ---------------- 求解 ----------------
    def columns(self, Dk):
        return [(w, dd) for w in self.Omega for dd in range(Dk + 1)]

    def sample_rows(self, Dk, npts, seed, rng_box=25):
        rnd = random.Random(seed)
        cols = self.columns(Dk)
        rows = []
        n = self.T.n
        for _ in range(npts):
            p = tuple(rnd.randint(-rng_box, rng_box) for _ in range(n))
            qv = {w: self.Q(w, p) for w in self.Omega}
            k = p[0]
            rows.append([qv[w] * (k ** dd) for (w, dd) in cols])
        return cols, rows

    def find(self, Dk, seed=1):
        """返回模 p 的零空间维数（只作搜索用）。"""
        cols = self.columns(Dk)
        _, rows = self.sample_rows(Dk, len(cols) + 25, seed)
        return nullity_modp(rows, len(cols))

    def solve_exact(self, Dk, seed=2):
        cols = self.columns(Dk)
        _, rows = self.sample_rows(Dk, len(cols) + 25, seed)
        basis = nullspace_exact(rows, len(cols))
        return cols, basis

    def coeffs_from_vec(self, cols, vec):
        a = {}
        for (w, dd), x in zip(cols, vec):
            if x != 0:
                lst = a.setdefault(w, [])
                while len(lst) <= dd:
                    lst.append(Fraction(0))
                lst[dd] += x
        return {w: lst for w, lst in a.items() if any(lst)}

    def grid_verify(self, a):
        """严格核对 Σ_ω a_ω(k)Q_ω(p)≡0：各变量次数界 +1 的乘积网格上逐点为 0。返回 (是否通过, 网格点数)。"""
        n = self.T.n
        Dk = max((len(l) - 1 for l in a.values()), default=0)
        deg = [0] * n
        for w in a:
            for i in range(n):
                deg[i] = max(deg[i], self.degQ[w][i])
        deg[0] += Dk
        cnt = 0
        for p in itertools.product(*[range(d + 1) for d in deg]):
            s = Fraction(0)
            k = p[0]
            for w, lst in a.items():
                ak = sum(c * k ** e for e, c in enumerate(lst))
                if ak != 0:
                    s += ak * self.Q(w, p)
            cnt += 1
            if s != 0:
                return False, cnt, deg
        return True, cnt, deg


def poly_k_eval(lst, k):
    return sum(c * k ** e for e, c in enumerate(lst))


def apply_rec(T, a, p):
    """(A T̃)(p)=Σ_ω a_ω(k)·T̃(p-ω)。"""
    k = p[0]
    s = Fraction(0)
    for w, lst in a.items():
        ak = poly_k_eval(lst, k)
        if ak != 0:
            s += ak * T.tt(tuple(pi - wi for pi, wi in zip(p, w)))
    return s


def apply_rec_T(T, a, p):
    """Σ_ω a_ω(k)·T(p-ω)；某项不良定义时返回 None。"""
    k = p[0]
    s = Fraction(0)
    for w, lst in a.items():
        v = T.val(tuple(pi - wi for pi, wi in zip(p, w)))
        if v is None:
            return None
        s += poly_k_eval(lst, k) * v
    return s


# ------------------------------------------------------------------ 引理 S 的算子

def lemmaS_ops(a, r, I):
    """A_ν⃗=Σ_{j,μ}a_{(j,μ,ν⃗)}(k)S_k^{-j}S_m^{-μ}；C_α=Σ_{ν⃗≥α}C(ν⃗,α)A_ν⃗。
    返回 (A, C, 极小元列表)。算子用 dict {(j,μ): k 的多项式（Fraction 列表）} 表示。"""
    def addpoly(x, y):
        n = max(len(x), len(y))
        z = [Fraction(0)] * n
        for i, c in enumerate(x):
            z[i] += c
        for i, c in enumerate(y):
            z[i] += c
        while z and z[-1] == 0:
            z.pop()
        return z
    A = {}
    for w, lst in a.items():
        nu = w[2:]
        op = A.setdefault(nu, {})
        key = (w[0], w[1])
        op[key] = addpoly(op.get(key, []), lst)
    alphas = [tuple(x) for x in itertools.product(range(I + 1), repeat=r)]
    C = {}
    for al in alphas:
        op = {}
        for nu, Aop in A.items():
            if all(n_ >= a_ for n_, a_ in zip(nu, al)):
                b = 1
                for n_, a_ in zip(nu, al):
                    b *= comb(n_, a_)
                for key, lst in Aop.items():
                    op[key] = addpoly(op.get(key, []), [b * c for c in lst])
        C[al] = {k_: v for k_, v in op.items() if v}
    nonzero = [al for al in alphas if C[al]]
    minimal = [al for al in nonzero
               if not any(be != al and all(b <= a_ for b, a_ in zip(be, al)) for be in nonzero)]
    return A, C, minimal


def apply_op(op, f, k, m):
    """(C f)(k,m)=Σ c_{jμ}(k) f(k-j, m-μ)。"""
    s = Fraction(0)
    for (j, mu), lst in op.items():
        ck = poly_k_eval(lst, k)
        if ck != 0:
            s += ck * f(k - j, m - mu)
    return s


def op_str(op):
    def pstr(lst):
        terms = []
        for e, c in enumerate(lst):
            if c != 0:
                terms.append('%s%s' % (c, '' if e == 0 else ('*k' if e == 1 else '*k^%d' % e)))
        return '(' + ' + '.join(terms) + ')'
    return ' + '.join('%s·S_k^-%d S_m^-%d' % (pstr(lst), j, mu) for (j, mu), lst in sorted(op.items()))


# ------------------------------------------------------------------ 线性代数

def nullity_modp(rows, ncols, p=PRIME):
    """模 p 的零空间维数。整数矩阵的模 p 秩 ≤ 有理秩，所以这里给出的维数 ≥ 有理零空间维数；
    只用于搜索最小规模，真正的解一律由 nullspace_exact 精确求出并严格核对。"""
    M = []
    for row in rows:
        rr = []
        for x in row:
            x = Fraction(x)
            rr.append(x.numerator % p * pow(x.denominator % p, p - 2, p) % p)
        M.append(rr)
    rank = 0
    ncol = ncols
    for c in range(ncol):
        piv = None
        for i in range(rank, len(M)):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][c], p - 2, p)
        M[rank] = [x * inv % p for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][c]:
                f = M[i][c]
                M[i] = [(x - f * y) % p for x, y in zip(M[i], M[rank])]
        rank += 1
    return ncol - rank


def nullspace_exact(rows, ncols):
    """精确有理数零空间基（RREF）。"""
    M = [[Fraction(x) for x in row] for row in rows]
    pivcols = []
    rank = 0
    for c in range(ncols):
        piv = None
        for i in range(rank, len(M)):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = 1 / M[rank][c]
        M[rank] = [x * inv for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[rank])]
        pivcols.append(c)
        rank += 1
    free = [c for c in range(ncols) if c not in set(pivcols)]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncols
        v[fc] = Fraction(1)
        for i, pc in enumerate(pivcols):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis


def integerize(vec):
    """把有理向量乘以公分母、除以公因子，变成本原整数向量（只为输出好看）。"""
    from math import gcd, lcm
    L = 1
    for x in vec:
        L = lcm(L, Fraction(x).denominator)
    iv = [int(Fraction(x) * L) for x in vec]
    g = 0
    for x in iv:
        g = gcd(g, x)
    if g == 0:
        return iv
    return [x // g for x in iv]


# ------------------------------------------------------------------ 输出

class Reporter:
    def __init__(self):
        self.ok_all = True
        self.n_ok = 0
        self.n_bad = 0
        self.t0 = time.time()

    def check(self, name, ok, extra=''):
        self.ok_all = self.ok_all and bool(ok)
        if ok:
            self.n_ok += 1
        else:
            self.n_bad += 1
        print('[%s] %s %s' % ('PASS' if ok else 'FAIL', name, extra), flush=True)

    def info(self, s):
        print('    ' + s, flush=True)

    def done(self):
        print('\n汇总：%d PASS / %d FAIL，用时 %.1f s' % (self.n_ok, self.n_bad, time.time() - self.t0))
        print('总体：%s' % ('全部通过' if self.ok_all else '有失败项'))
        return 0 if self.ok_all else 1
