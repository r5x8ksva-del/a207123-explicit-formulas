# -*- coding: utf-8 -*-
"""s8-b1 复核：精确多项式工具（整数系数列表，下标 = 次数，低次在前）。只用标准库，不用浮点。

交错的定义与 notes/05 一致：g << f 当且仅当 f、g 只有实根，deg f - deg g ∈ {0,1}，
两组根（含重数）弱交替、最大的根属于 f。这里有两种互相独立的精确判定：

  interlace_A(g, f)：约去 d = gcd(f,g)，要求 d 只有实根；对 f1=f/d、g1=g/d 用 Cauchy 指标
      Ind(g1/f1) = deg f1 判定「f1 只有单实根且 g1 在每个根处与 f1' 同号」，由介值定理即得 g1 与 f1
      严格交错（最大根属于 f1）；再用「两边乘同一个只有实根的多项式不改变交错」（notes/05 的引理 1，
      纯组合事实）回到 f、g。
  interlace_B(g, f)：完全按定义——用 Sturm 序列在二进有理点上二分，精确隔离 f·g 的全部互异实根，
      逐个求出它在 f、g 中的重数，再逐条比较 b_1<=a_1<=b_2<=... 。

符号余式序列用「正乘子」的整数伪除法（乘子是 |lc| 的幂，再除以正的容量），所以符号与有理数上的
真正余式序列一致；Cauchy 指标与 Sturm 计数都只在 ±∞ 处数变号（只看首项系数与次数）。
"""
from math import gcd
from fractions import Fraction


# ---------------------------------------------------------------- 基本运算
def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def deg(p):
    return len(trim(p)) - 1          # 零多项式为 -1


def lc(p):
    p = trim(p)
    return p[-1] if p else 0


def add(*ps):
    n = max((len(p) for p in ps), default=0)
    r = [0] * n
    for p in ps:
        for i, c in enumerate(p):
            r[i] += c
    return trim(r)


def neg(p):
    return [-c for c in p]


def sub(p, q):
    return add(p, neg(q))


def scal(c, p):
    return trim([c * x for x in p])


def mul(p, q):
    p = trim(p)
    q = trim(q)
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return trim(r)


def pw(p, e):
    r = [1]
    for _ in range(e):
        r = mul(r, p)
    return r


def deriv(p):
    return trim([i * p[i] for i in range(1, len(p))])


ONEZ = [1, 1]


def mulz(p):
    p = trim(p)
    return [0] + p if p else []


def mul1z(p):
    return mul(ONEZ, p)


def T(n):
    """T n = z(1+z) n' + 2 z n（notes/05 §0）"""
    return add(mul([0, 1, 1], deriv(n)), mul([0, 2], n))


def Phi(n):
    """Φ n = (1+z) T n"""
    return mul1z(T(n))


def ev(p, x):
    """精确求值（x 为 int 或 Fraction）"""
    v = 0
    for c in reversed(trim(p)):
        v = v * x + c
    return v


def sgn(x):
    return (x > 0) - (x < 0)


def from_roots(roots, c=1):
    """c·∏(den·z - num)，根 num/den（Fraction）。"""
    p = [c]
    for r in roots:
        r = Fraction(r)
        p = mul(p, [-r.numerator, r.denominator])
    return p


# ---------------------------------------------------------------- 整数上的 gcd、余式序列
def content(p):
    g = 0
    for c in p:
        g = gcd(g, c)
    return g


def primitive(p):
    """本原部分，首项系数取正。"""
    p = trim(p)
    if not p:
        return []
    g = content(p)
    if p[-1] < 0:
        g = -g
    return [c // g for c in p]


def prem_pos(a, b):
    """(正常数)·rem(a, b)：每步乘 |lc(b)|（正数）再消去首项，并随时除去正的容量。"""
    a = trim(a)
    b = trim(b)
    db = len(b) - 1
    if db < 0:
        raise ZeroDivisionError("prem by zero polynomial")
    lb = b[-1]
    s = 1 if lb > 0 else -1
    alb = abs(lb)
    r = list(a)
    while r and len(r) - 1 >= db:
        e = len(r) - 1 - db
        f = s * r[-1]
        r = [alb * c for c in r]
        for j, c in enumerate(b):
            r[e + j] -= f * c
        r = trim(r)
        if r:
            g = content(r)
            if g > 1:
                r = [c // g for c in r]
    return r


def srs(p, q):
    """符号余式序列 S0=p, S1=q, S_{i+1} = -(正常数)·rem(S_{i-1}, S_i)，到最后一个非零项为止。"""
    seq = [trim(p)]
    q = trim(q)
    if not q:
        return seq
    seq.append(q)
    while len(seq[-1]) > 1:
        r = prem_pos(seq[-2], seq[-1])
        if not r:
            break
        g = content(r)
        seq.append([-(c // g) for c in r])
    return seq


def var_count(signs):
    s = [x for x in signs if x != 0]
    return sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1])


def var_at_inf(seq):
    plus = [sgn(lc(S)) for S in seq]
    minus = [sgn(lc(S)) * (1 if deg(S) % 2 == 0 else -1) for S in seq]
    return var_count(minus), var_count(plus)


def cauchy_index(q, p):
    """Ind_{-∞}^{+∞}(q/p) = Var(SRS(p,q); -∞) - Var(SRS(p,q); +∞)（Sturm–Sylvester）。"""
    vm, vp = var_at_inf(srs(p, q))
    return vm - vp


def sturm_count(p):
    """p 的互异实根个数 = Ind(p'/p)。"""
    p = trim(p)
    if len(p) <= 1:
        return 0
    return cauchy_index(deriv(p), p)


def pgcd(a, b):
    """Q[x] 上的 gcd（本原、首项为正）。"""
    a = primitive(a)
    b = primitive(b)
    if not a:
        return b
    if not b:
        return a
    if len(a) < len(b):
        a, b = b, a
    while b:
        r = prem_pos(a, b)
        a, b = b, (primitive(r) if r else [])
    return primitive(a)


def exact_div(a, b):
    """整数系数的精确除法（不整除就报错）。b 本原且在 Q[x] 中整除 a 时商在 Z[x] 中（Gauss 引理）。"""
    a = trim(a)
    b = trim(b)
    if not b:
        raise ZeroDivisionError
    if not a:
        return []
    db = len(b) - 1
    qd = len(a) - 1 - db
    if qd < 0:
        raise ArithmeticError("exact_div: degree too small")
    q = [0] * (qd + 1)
    r = list(a)
    lb = b[-1]
    for e in range(qd, -1, -1):
        c = r[e + db]
        if c == 0:
            continue
        if c % lb:
            raise ArithmeticError("exact_div: non-integral quotient")
        t = c // lb
        q[e] = t
        for j, bc in enumerate(b):
            r[e + j] -= t * bc
    if trim(r):
        raise ArithmeticError("exact_div: nonzero remainder")
    return trim(q)


def is_squarefree(p):
    p = trim(p)
    if len(p) <= 2:
        return bool(p)
    return deg(pgcd(p, deriv(p))) == 0


def squarefree_part(p):
    p = trim(p)
    if len(p) <= 2:
        return p
    return exact_div(p, pgcd(p, deriv(p)))


def is_real_rooted(p):
    """p 的根全为实数（含重根）⇔ 互异实根个数 = 无平方因子部分的次数。"""
    p = trim(p)
    if len(p) <= 2:
        return bool(p)
    return sturm_count(p) == deg(squarefree_part(p))


def mult_at(p, x):
    """p 在有理点 x 的根重数（p 非零）。"""
    m = 0
    p = trim(p)
    while p and ev(p, x) == 0:
        m += 1
        p = deriv(p)
    return m


def mult_neg1(p):
    """p 被 (1+z) 整除的最高次数。"""
    m = 0
    p = trim(p)
    while p and ev(p, -1) == 0:
        p = exact_div(p, ONEZ)
        m += 1
    return m


# ---------------------------------------------------------------- 判定 A：Cauchy 指标
def interlace_A(g, f):
    """g << f ?  返回 (bool, 说明)。"""
    g = trim(g)
    f = trim(f)
    if not g or not f:
        return False, "zero polynomial"
    if lc(f) <= 0 or lc(g) <= 0:
        return False, "leading coefficient <= 0"
    if deg(f) - deg(g) not in (0, 1):
        return False, "degree pattern %d,%d" % (deg(g), deg(f))
    d = pgcd(f, g)
    if not is_real_rooted(d):
        return False, "gcd not real-rooted"
    f1 = exact_div(f, d)
    g1 = exact_div(g, d)
    n = deg(f1)
    if n == 0:
        return deg(g1) == 0, "f/gcd constant"
    if not is_squarefree(f1):
        return False, "f/gcd not squarefree"
    if sturm_count(f1) != n:
        return False, "f/gcd not real-rooted"
    ind = cauchy_index(g1, f1)
    if ind != n:
        return False, "Ind(g1/f1)=%d != deg f1=%d" % (ind, n)
    return True, "ok deg(gcd)=%d" % deg(d)


# ---------------------------------------------------------------- 判定 B：按定义逐根比较
def _ns(x):
    x = Fraction(x)
    den = x.denominator
    s = den.bit_length() - 1
    if den != 1 << s:
        raise ValueError("not dyadic")
    return x.numerator, s


def sign_at_dyadic(p, num, s):
    """p(num/2^s) 的符号：整数 Horner，c_i 乘 2^{s(d-i)}。"""
    p = trim(p)
    if not p:
        return 0
    d = len(p) - 1
    v = p[d]
    step = 1 << s
    m = step
    for i in range(d - 1, -1, -1):
        v = v * num + p[i] * m
        m *= step
    return sgn(v)


def sign_at(p, x):
    num, s = _ns(x)
    return sign_at_dyadic(p, num, s)


def isolate_real_roots(P):
    """P 无平方因子且非零。返回按位置排序的互异实根：('exact', x) 或 ('int', a, b)
    （开区间 (a,b) 内恰有一个根，a、b 都不是根；端点为二进有理数）。"""
    P = trim(P)
    if len(P) <= 1:
        return []
    seq = srs(P, deriv(P))

    def V(x):
        num, s = _ns(x)
        return var_count([sign_at_dyadic(S, num, s) for S in seq])

    B = 1 + max(Fraction(abs(c), abs(P[-1])) for c in P[:-1])   # Cauchy 界：|根| < B
    e = 0
    while (1 << e) < B:
        e += 1
    out = []
    stack = [(Fraction(-(1 << e)), Fraction(1 << e))]
    while stack:
        a, b = stack.pop()
        c = V(a) - V(b)                  # a、b 不是根时 = (a,b) 内的根数
        if c == 0:
            continue
        if c == 1:
            out.append(('int', a, b))
            continue
        m = (a + b) / 2
        if sign_at(P, m) != 0:
            stack.append((a, m))
            stack.append((m, b))
            continue
        out.append(('exact', m))
        eps = (b - a) / 4
        while True:
            lo, hi = m - eps, m + eps
            if sign_at(P, lo) != 0 and sign_at(P, hi) != 0 and V(lo) - V(hi) == 1:
                break
            eps /= 2
        stack.append((a, lo))
        stack.append((hi, b))
    out.sort(key=lambda r: r[1])
    return out


def _mult_in(h, P, root, cache):
    """root（isolate_real_roots 的一项）在 h 中的重数。cache[i] = gcd(P, h^{(i)})。"""
    h = trim(h)
    if root[0] == 'exact':
        return mult_at(h, root[1])
    _, a, b = root
    i = 0
    hd = h
    while True:
        if i not in cache:
            cache[i] = pgcd(P, hd) if hd else P
        G = cache[i]
        if deg(G) >= 1 and sign_at(G, a) != sign_at(G, b):
            i += 1
            hd = deriv(hd)
            continue
        return i


def interlace_B(g, f, return_roots=False):
    g = trim(g)
    f = trim(f)
    if not g or not f or lc(f) <= 0 or lc(g) <= 0:
        return (False, "zero or lc<=0") if not return_roots else (False, "zero or lc<=0", None)
    n, n2 = deg(f), deg(g)
    if n - n2 not in (0, 1):
        return (False, "degree pattern") if not return_roots else (False, "degree pattern", None)
    P = squarefree_part(mul(f, g))
    roots = isolate_real_roots(P)
    cf, cg = {}, {}
    A, Bl = [], []
    for idx, r in enumerate(roots):
        A += [idx] * _mult_in(f, P, r, cf)
        Bl += [idx] * _mult_in(g, P, r, cg)
    if len(A) != n or len(Bl) != n2:
        msg = "not real-rooted: f %d/%d real roots, g %d/%d" % (len(A), n, len(Bl), n2)
        return (False, msg) if not return_roots else (False, msg, roots)
    if n2 == n:
        word = []
        for i in range(n):
            word += [Bl[i], A[i]]
    else:
        word = [A[0]]
        for i in range(n2):
            word += [Bl[i], A[i + 1]]
    ok = all(word[i] <= word[i + 1] for i in range(len(word) - 1))
    msg = "ok" if ok else "order violated"
    return (ok, msg) if not return_roots else (ok, msg, roots)
