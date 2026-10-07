# -*- coding: utf-8 -*-
"""复核者 s10-b1 自写的精确整数多项式工具（只用标准库；不导入项目里别的脚本）。

约定：多项式 = 整数系数列表，低次在前，末尾没有 0；零多项式 = []。

提供两种互相独立的「交错」判定（笔记 05 §1 的定义：g≪f 指两组根交替、最大的根属于 f，
允许公共根；deg f − deg g ∈ {0,1}）：
  方法 R（按定义）：把 f、g 的全部根分解成两两互素的无平方因子「原子」，逐个原子用 Sturm
           计数 + 二分隔离实根（区间端点为有理数，遇到有理根就记为精确点），再按大小合并，
           直接检查定义里的不等式链 b1≤a1≤b2≤…（相等只可能出现在同一原子的同一个根上）。
  方法 C（Cauchy 指标）：d=gcd(f,g)，检查 d 只有实根，再用 Sturm–Sylvester 序列算
           Ind_{−∞}^{+∞}((g/d)/(f/d))，要求它等于 deg(f/d)。
"""
from fractions import Fraction
from functools import cmp_to_key
from math import gcd, comb


# ---------------------------------------------------------------- 基本运算
def norm(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def deg(p):
    return len(p) - 1


def add(p, q):
    n = max(len(p), len(q))
    return norm([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def neg(p):
    return [-c for c in p]


def sub(p, q):
    return add(p, neg(q))


def scal(c, p):
    return norm([c * x for x in p])


def mul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            r[i + j] += a * b
    return norm(r)


def deriv(p):
    return norm([i * p[i] for i in range(1, len(p))])


def mulz(p):
    return norm([0] + list(p)) if p else []


ONEZ = [1, 1]


def mul1z(p):
    return mul(p, ONEZ)


def T(p):
    """笔记的算子 T n = z(1+z)n' + 2z n。"""
    return add(mul([0, 1, 1], deriv(p)), scal(2, mulz(p)))


def Phi(p):
    """Φ n = (1+z) T n。"""
    return mul1z(T(p))


def L(p):
    """L n = (1+z)n' + 2n，T n = z L n。"""
    return add(mul1z(deriv(p)), scal(2, p))


def ev_int(p, x):
    s = 0
    for c in reversed(p):
        s = s * x + c
    return s


def ev_frac(p, x):
    x = Fraction(x)
    s = Fraction(0)
    for c in reversed(p):
        s = s * x + c
    return s


def nonneg(p):
    return bool(p) and all(c >= 0 for c in p)


def content(p):
    g = 0
    for c in p:
        g = gcd(g, c)
    return g


def prim(p):
    """除以（正的）内容，不改变符号。"""
    p = norm(p)
    if not p:
        return []
    g = content(p)
    return [c // g for c in p]


def prim_pos(p):
    """本原化并使首项系数为正。"""
    p = prim(p)
    if p and p[-1] < 0:
        p = [-c for c in p]
    return p


def prem(a, b):
    """伪余式：lc(b)^(deg a − deg b + 1) · a 除以 b 的余式（整系数）。"""
    a = norm(a)
    b = norm(b)
    db = deg(b)
    lb = b[-1]
    if deg(a) < db:
        return a
    e = deg(a) - db + 1
    while a and deg(a) >= db:
        c = a[-1]
        s = deg(a) - db
        a = [x * lb for x in a]
        for i, bi in enumerate(b):
            a[i + s] -= c * bi
        assert a[-1] == 0
        a = norm(a)
        e -= 1
    if e > 0 and a:
        f = lb ** e
        a = [x * f for x in a]
    return a


def pgcd(a, b):
    """整系数多项式的最大公因子（本原、首项为正）。"""
    a = prim_pos(a)
    b = prim_pos(b)
    while b:
        r = prem(a, b)
        a, b = b, prim_pos(r)
    return a


def divexact(p, d):
    """p/d，要求整除（d 本原时商必为整系数，Gauss 引理）。"""
    p = list(norm(p))
    d = norm(d)
    dd = deg(d)
    ld = d[-1]
    if not p:
        return []
    assert deg(p) >= dd, "divexact: degree"
    q = [0] * (deg(p) - dd + 1)
    while p and deg(p) >= dd:
        c = p[-1]
        assert c % ld == 0, "divexact: not exact"
        t = c // ld
        s = deg(p) - dd
        q[s] = t
        for i, di in enumerate(d):
            p[i + s] -= t * di
        assert p[-1] == 0
        p = norm(p)
    assert not p, "divexact: nonzero remainder"
    return norm(q)


def mult_at(p, x):
    """有理数 x 作为 p 的根的重数（x = 整数或 Fraction）。"""
    x = Fraction(x)
    lin = [-x.numerator, x.denominator]
    m = 0
    q = norm(p)
    while q and ev_frac(q, x) == 0:
        q = divexact(q, lin)
        m += 1
    return m, q


# ---------------------------------------------------------------- 符号与 Sturm 序列
def sign_at(p, x):
    """p 在有理点 x 处的符号（整数运算：Σ c_i n^i d^(D−i)，d>0）。"""
    if not p:
        return 0
    x = Fraction(x)
    n, d = x.numerator, x.denominator
    acc = p[-1]
    dp = 1
    for i in range(len(p) - 2, -1, -1):
        dp *= d
        acc = acc * n + p[i] * dp
    return (acc > 0) - (acc < 0)


def sign_inf(p, s):
    if not p:
        return 0
    v = 1 if p[-1] > 0 else -1
    if s < 0 and deg(p) % 2 == 1:
        v = -v
    return v


def sylvester_seq(p0, p1):
    """广义 Sturm 序列 p0, p1, p_{i+1} = −rem(p_{i−1}, p_i)（每项只乘正数）。"""
    p0 = prim(p0)
    p1 = prim(p1)
    seq = [p0]
    if not p1:
        return seq
    seq.append(p1)
    while True:
        a, b = seq[-2], seq[-1]
        if deg(b) <= 0:
            break
        r = prem(a, b)
        if not r:
            break
        delta = deg(a) - deg(b)
        lcpow_neg = (b[-1] < 0) and ((delta + 1) % 2 == 1)
        nxt = r if lcpow_neg else [-c for c in r]
        seq.append(prim(nxt))
    return seq


def variations(signs):
    v = 0
    last = 0
    for s in signs:
        if s == 0:
            continue
        if last != 0 and s != last:
            v += 1
        last = s
    return v


def V_at(seq, x):
    return variations([sign_at(q, x) for q in seq])


def V_inf(seq, s):
    return variations([sign_inf(q, s) for q in seq])


def squarefree_part(p):
    p = prim_pos(p)
    if deg(p) <= 0:
        return p
    g = pgcd(p, deriv(p))
    return divexact(p, g)


def n_real_distinct(p):
    """p 的互不相同实根个数（Sturm）。"""
    p = norm(p)
    if deg(p) <= 0:
        return 0
    seq = sylvester_seq(p, deriv(p))
    return V_inf(seq, -1) - V_inf(seq, 1)


def n_real_distinct_in(p, a, b):
    """p 在 (a,b] 中互不相同的实根个数；a,b 为有理数或 ±None（−∞/+∞）。"""
    p = norm(p)
    if deg(p) <= 0:
        return 0
    seq = sylvester_seq(p, deriv(p))
    va = V_inf(seq, -1) if a is None else V_at(seq, a)
    vb = V_inf(seq, 1) if b is None else V_at(seq, b)
    return va - vb


def is_real_rooted(p):
    """p≠0 的全部复根都是实数（含重数）。"""
    p = norm(p)
    assert p
    if deg(p) <= 0:
        return True
    s = squarefree_part(p)
    return n_real_distinct(s) == deg(s)


def is_real_simple(p):
    """p 的根全为实数且两两不同。"""
    p = norm(p)
    if deg(p) <= 0:
        return True
    if deg(pgcd(p, deriv(p))) > 0:
        return False
    return n_real_distinct(p) == deg(p)


# ---------------------------------------------------------------- 方法 C：Cauchy 指标
def interlace_C(g, f):
    """g ≪ f ?（笔记 §1 的定义；f、g 系数非负且非零）"""
    assert nonneg(f) and nonneg(g)
    if deg(f) - deg(g) not in (0, 1):
        return False
    d = pgcd(f, g)
    if not is_real_rooted(d):
        return False
    f1 = divexact(f, d)
    g1 = divexact(g, d)
    n = deg(f1)
    if n == 0:
        return deg(g1) == 0
    seq = sylvester_seq(f1, g1)
    ind = V_inf(seq, -1) - V_inf(seq, 1)
    return ind == n


# ---------------------------------------------------------------- 方法 R：隔离实根、按定义比较
class Root:
    """一个实根：精确有理点 x，或开区间 (l,r)（p(l)p(r)<0，区间内恰一个根，p 无平方因子）。"""
    __slots__ = ('p', 'l', 'r', 'x')

    def __init__(self, p, l=None, r=None, x=None):
        self.p = p
        self.l = None if l is None else Fraction(l)
        self.r = None if r is None else Fraction(r)
        self.x = None if x is None else Fraction(x)

    def lo(self):
        return self.x if self.x is not None else self.l

    def hi(self):
        return self.x if self.x is not None else self.r

    def refine(self):
        if self.x is not None:
            return
        m = (self.l + self.r) / 2
        self.split_at(m)

    def split_at(self, v):
        s = sign_at(self.p, v)
        if s == 0:
            self.x = Fraction(v)
            return
        if s == sign_at(self.p, self.l):
            self.l = Fraction(v)
        else:
            self.r = Fraction(v)

    def approx(self):
        return float(self.x) if self.x is not None else float((self.l + self.r) / 2)


class SharedRootError(Exception):
    pass


def cmp_roots(a, b, maxit=20000):
    for _ in range(maxit):
        if a.x is not None and b.x is not None:
            if a.x == b.x:
                raise SharedRootError("two atoms share a root")
            return -1 if a.x < b.x else 1
        if a.hi() <= b.lo():
            return -1
        if b.hi() <= a.lo():
            return 1
        if a.x is not None:
            b.split_at(a.x)
            if b.x is not None and b.x == a.x:
                raise SharedRootError("two atoms share a root")
        elif b.x is not None:
            a.split_at(b.x)
            if a.x is not None and a.x == b.x:
                raise SharedRootError("two atoms share a root")
        else:
            if (a.r - a.l) >= (b.r - b.l):
                a.refine()
            else:
                b.refine()
    raise RuntimeError("cmp_roots: no separation")


def cauchy_bound(p):
    lcabs = abs(p[-1])
    M = 0
    for c in p[:-1]:
        q = -(-abs(c) // lcabs)  # ceil
        if q > M:
            M = q
    return 1 + M


_ISO_CACHE = {}


def isolate(p):
    """p 无平方因子（整系数）。返回全部实根的 Root 列表（从小到大）。结果按 p 缓存。"""
    p = prim_pos(p)
    key = tuple(p)
    if key in _ISO_CACHE:
        return _ISO_CACHE[key]
    if deg(p) <= 0:
        _ISO_CACHE[key] = []
        return []
    if deg(p) == 1:
        res = [Root(p, x=Fraction(-p[0], p[1]))]
        _ISO_CACHE[key] = res
        return res
    seq = sylvester_seq(p, deriv(p))
    B = Fraction(cauchy_bound(p))
    out = []
    stack = [(-B, B, V_at(seq, -B), V_at(seq, B))]
    while stack:
        l, r, vl, vr = stack.pop()
        c = vl - vr               # (l, r] 中的根数
        if c == 0:
            continue
        if c == 1:
            if sign_at(p, r) == 0:
                out.append(Root(p, x=r))
                continue
            if sign_at(p, l) != 0:
                out.append(Root(p, l, r))
                continue
        m = (l + r) / 2
        vm = V_at(seq, m)
        stack.append((m, r, vm, vr))
        stack.append((l, m, vl, vm))
    _ISO_CACHE[key] = out
    return out


def yun(p):
    """无平方因子分解：返回 [(s_i, i)]，p = c·∏ s_i^i，s_i 本原、首项为正、两两互素。"""
    p = prim_pos(p)
    out = []
    if deg(p) <= 0:
        return out
    # 逐次求 gcd：第 i 步 cur = ∏_{j≥i} s_j^(j−i+1)
    i = 1
    cur = p
    while deg(cur) > 0:
        g = pgcd(cur, deriv(cur))
        sq = divexact(cur, g)          # cur 的根（不计重数）
        # cur = ∏ s_j^(j - i + 1)（j ≥ i），sq = ∏_{j≥i} s_j；g = ∏ s_j^(j-i)
        nxt_sq = squarefree_part(g) if deg(g) > 0 else [1]
        s_i = divexact(sq, pgcd(sq, nxt_sq)) if deg(nxt_sq) > 0 else sq
        if deg(s_i) > 0:
            out.append((prim_pos(s_i), i))
        cur = g
        i += 1
    return out


def atoms_of(f, g):
    """把 f、g 的无平方因子分解细化成两两互素的原子：返回 [(atom, mult_in_f, mult_in_g)]。"""
    items = [[s, m, 0] for s, m in yun(f)] + [[s, 0, m] for s, m in yun(g)]
    changed = True
    while changed:
        changed = False
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                a, b = items[i][0], items[j][0]
                d = pgcd(a, b)
                if deg(d) > 0:
                    ai = divexact(a, d)
                    bj = divexact(b, d)
                    new = [[d, items[i][1] + items[j][1], items[i][2] + items[j][2]]]
                    if deg(ai) > 0:
                        new.append([ai, items[i][1], items[i][2]])
                    if deg(bj) > 0:
                        new.append([bj, items[j][1], items[j][2]])
                    rest = [items[t] for t in range(len(items)) if t != i and t != j]
                    items = rest + new
                    changed = True
                    break
            if changed:
                break
    return [(prim_pos(a), mf, mg) for a, mf, mg in items]


def merged_points(f, g):
    """f、g 全部实根合并排序：返回 (points, ok_real)，points = [(Root, mult_f, mult_g)]（从小到大）。"""
    pts = []
    cnt_f = cnt_g = 0
    for a, mf, mg in atoms_of(f, g):
        for R in isolate(a):
            pts.append((R, mf, mg))
            cnt_f += mf
            cnt_g += mg
    ok_real = (cnt_f == deg(f)) and (cnt_g == deg(g))
    pts.sort(key=cmp_to_key(lambda u, v: cmp_roots(u[0], v[0])))
    return pts, ok_real


def interlace_R(g, f):
    """g ≪ f ?（按定义：两组根（含重数）满足 b1≤a1≤…≤bn≤an 或 a1≤b1≤…≤b_{n−1}≤an）"""
    assert nonneg(f) and nonneg(g)
    n, n2 = deg(f), deg(g)
    if n - n2 not in (0, 1):
        return False
    pts, ok_real = merged_points(f, g)
    if not ok_real:
        return False
    A, Bl = [], []
    for rank, (R, mf, mg) in enumerate(pts):
        A += [rank] * mf
        Bl += [rank] * mg
    if n2 == n:
        chain = []
        for i in range(n):
            chain += [Bl[i], A[i]]
    else:
        chain = [A[0]]
        for i in range(n - 1):
            chain += [Bl[i], A[i + 1]]
    return all(chain[i] <= chain[i + 1] for i in range(len(chain) - 1))


def letters_alternate(p, q):
    """p、q 互素、只有单实根时，合并后的根序列是否交替（不论谁先谁后）。"""
    pts, ok_real = merged_points(p, q)
    if not ok_real:
        return None
    word = []
    for R, mp, mq in pts:
        if mp and mq:
            return False
        word.append('P' if mp else 'Q')
    return all(word[i] != word[i + 1] for i in range(len(word) - 1))


def sign_changes(seq):
    return variations([(c > 0) - (c < 0) for c in seq])


def binom_poly_eval(x, q):
    """多项式二项式 C(x, q) 在整数 x 处的值（x 可为负）。"""
    num = 1
    for i in range(q):
        num *= (x - i)
    den = 1
    for i in range(2, q + 1):
        den *= i
    assert num % den == 0
    return num // den
