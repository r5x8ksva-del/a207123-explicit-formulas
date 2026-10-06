# -*- coding: utf-8 -*-
"""s6-t342 复核用高精度工具库（只用 Python 标准库：decimal、fractions、math）。

不导入、不复制 r-c3a 或项目里其他脚本的实现。内容：
  dec(q)                 Fraction/int -> Decimal（当前精度）
  pi_dec()               Machin 公式算 π
  sin_pi_frac(f)         sin(π f)，f 为精确 Fraction（先精确约化到 [0,1/2]）
  bernoulli(nmax)        精确 Bernoulli 数 B_0..B_nmax（Fraction）
  lngamma_dec(z)         ln Γ(z)，z>0（平移 + Stirling 级数，余项不超过首个略去项）
  gamma_pos(z)           Γ(z)，z>0
  gamma_neg_frac(lam)    Γ(−λ)，λ>0 为非整数 Fraction（反射公式）
  gamma_neg_frac_rec(lam)Γ(−λ) 的第二种算法（向上递推到 (0,1) 再用 lngamma），自检用
  de_exp_quad(f, digits) ∫_0^∞ f(v)dv，Ooura–Mori 指数型双指数变换 v=exp(t−e^{−t})
  ts_quad(f, a, b, digits) ∫_a^b f，tanh-sinh 双指数变换
  ts_quad_composite(...) 把 [a,b] 切成若干段分别做 tanh-sinh
所有积分例程逐级把步长减半，返回 (值, 末两级差, 级数信息)；末两级差作为误差估计
（双指数公式每减半一次正确位数约翻倍，所以末两级差是对末级误差的保守估计）。
"""
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction as Fr
import math

ONE = D(1)


def dec(q):
    """Fraction / int / Decimal -> Decimal，按当前上下文精度舍入一次。"""
    if isinstance(q, Fr):
        return D(q.numerator) / D(q.denominator)
    if isinstance(q, D):
        return +q
    return D(q)


# ---------------------------------------------------------------- π
_PI = {}


def pi_dec():
    P = getcontext().prec
    if P in _PI:
        return _PI[P]
    with localcontext() as ctx:
        ctx.prec = P + 15
        eps = D(10) ** (-(P + 15))

        def atan_inv(n):
            n = D(n)
            n2 = n * n
            power = ONE / n          # 1/n^{2k+1}
            s = power
            k = 1
            while True:
                power /= n2
                term = power / (2 * k + 1)
                if term < eps:
                    break
                s = s - term if k % 2 else s + term
                k += 1
            return s
        p = 16 * atan_inv(5) - 4 * atan_inv(239)
    p = +p
    _PI[P] = p
    return p


def sin_pi_frac(f):
    """sin(π f)，f 为 Fraction。精确约化：f mod 2 → [0,2)，再用对称性约到 [0,1/2]。"""
    f = Fr(f)
    f = f - 2 * (f.numerator // (2 * f.denominator))   # f ∈ [0,2)
    sign = 1
    if f >= 1:
        f -= 1
        sign = -1
    if f > Fr(1, 2):
        f = 1 - f
    P = getcontext().prec
    with localcontext() as ctx:
        ctx.prec = P + 15
        z = pi_dec() * dec(f)
        z2 = z * z
        term = z
        s = z
        k = 1
        eps = D(10) ** (-(P + 15))
        while abs(term) > eps:
            term = -term * z2 / ((2 * k) * (2 * k + 1))
            s += term
            k += 1
        s = s if sign > 0 else -s
    return +s


# ---------------------------------------------------------------- Bernoulli / Gamma
_BERN = [Fr(1)]


def bernoulli(nmax):
    """精确 B_0..B_nmax（B_1=−1/2 约定），递推 Σ_{j=0}^{m} C(m+1,j) B_j = 0。"""
    while len(_BERN) <= nmax:
        m = len(_BERN)
        s = Fr(0)
        for j in range(m):
            if _BERN[j]:
                s += math.comb(m + 1, j) * _BERN[j]
        _BERN.append(-s / (m + 1))
    return _BERN


def lngamma_dec(z):
    """ln Γ(z)，z 为正的 Decimal/Fraction/int。
    先用 Γ(z)=Γ(z+N)/(z(z+1)…(z+N−1)) 平移到 w=z+N ≥ W0，再用 Stirling 级数
        ln Γ(w) = (w−1/2)ln w − w + ln(2π)/2 + Σ_{k≥1} B_{2k}/(2k(2k−1)w^{2k−1})，
    实 w>0 时截断误差不超过首个略去项的绝对值（交错、单调的经典余项估计）。"""
    P = getcontext().prec
    with localcontext() as ctx:
        ctx.prec = P + 25
        w = dec(z) if not isinstance(z, D) else +z
        if w <= 0:
            raise ValueError("lngamma_dec 只接受 z>0")
        W0 = D(P + 40)
        prod = ONE
        while w < W0:
            prod *= w
            w += 1
        lw = w.ln()
        s = (w - D('0.5')) * lw - w + (2 * pi_dec()).ln() / 2
        eps = D(10) ** (-(P + 25))
        w2 = w * w
        wpow = w
        k = 1
        while True:
            B = bernoulli(2 * k)
            term = dec(B[2 * k]) / (2 * k * (2 * k - 1) * wpow)
            if abs(term) < eps:
                break
            s += term
            wpow *= w2
            k += 1
            if k > 400:
                raise RuntimeError("Stirling 级数没有收敛")
        res = s - prod.ln()
    return +res


def gamma_pos(z):
    P = getcontext().prec
    with localcontext() as ctx:
        ctx.prec = P + 10
        g = lngamma_dec(z).exp()
    return +g


def gamma_neg_frac(lam):
    """Γ(−λ)，λ>0 非整数（Fraction）。反射公式 Γ(−λ)Γ(1+λ) = π / sin(π(−λ)) = −π/sin(πλ)。"""
    lam = Fr(lam)
    if lam.denominator == 1:
        raise ValueError("λ 是整数，Γ(−λ) 是极点")
    P = getcontext().prec
    with localcontext() as ctx:
        ctx.prec = P + 15
        g1 = lngamma_dec(1 + lam).exp()
        r = -pi_dec() / (sin_pi_frac(lam) * g1)
    return +r


def gamma_neg_frac_rec(lam):
    """Γ(−λ) 的第二种算法：取 n=⌈λ⌉，f=n−λ∈(0,1)，Γ(−λ)=Γ(f)/((−λ)(−λ+1)…(−λ+n−1))。"""
    lam = Fr(lam)
    n = -((-lam.numerator) // lam.denominator)   # ceil
    f = n - lam
    P = getcontext().prec
    with localcontext() as ctx:
        ctx.prec = P + 15
        den = Fr(1)
        for k in range(n):
            den *= (-lam + k)
        r = gamma_pos(f) / dec(den)
    return +r


# ---------------------------------------------------------------- 双指数积分
def de_exp_quad(f, digits, h0=None, max_level=12, min_level=3, tmin_span=4):
    """∫_0^∞ f(v) dv。变换 v = exp(t − e^{−t})，dv/dt = v(1+e^{−t})。
    梯形和逐级把 h 减半；每级只算新增节点。t 方向两端在连续 4 个项都小于
    10^{−(digits+8)}·|当前和| 后截断（两端都是双指数衰减），且至少走到 |t| ≥ tmin_span。
    返回 (Q, |Q_k − Q_{k−1}|, 信息字符串)。"""
    if h0 is None:
        h0 = D('0.5')
    tol_rel = D(10) ** (-(digits + 8))

    def node(t):
        et = (-t).exp()
        v = (t - et).exp()
        dv = v * (1 + et)
        return v, dv

    def side_sum(h, start, step, sign, S_ref):
        total = D(0)
        j = start
        small = 0
        while True:
            t = sign * j * h
            v, dv = node(t)
            if v == 0 or dv == 0:
                term = D(0)
            else:
                term = f(v) * dv
            total += term
            ref = abs(S_ref + total)
            if abs(term) <= tol_rel * ref and abs(t) >= tmin_span:
                small += 1
                if small >= 4:
                    break
            else:
                small = 0
            j += step
            if j * h > 40:
                raise RuntimeError("de_exp_quad：t 超过 40 仍未截断")
        return total

    h = +h0
    v0, dv0 = node(D(0))
    S = f(v0) * dv0
    S += side_sum(h, 1, 1, 1, S)
    S += side_sum(h, 1, 1, -1, S)
    Q_prev = h * S
    hist = [(0, Q_prev)]
    err = None
    for lev in range(1, max_level + 1):
        h = h / 2
        add = side_sum(h, 1, 2, 1, S)
        add += side_sum(h, 1, 2, -1, S + add)
        S += add
        Q = h * S
        err = abs(Q - Q_prev)
        hist.append((lev, Q))
        if lev >= min_level and err <= abs(Q) * D(10) ** (-digits):
            return Q, err, "levels=%d h=2^-%d" % (lev, lev + 1)
        Q_prev = Q
    return Q, err, "levels=%d (max) h=2^-%d" % (max_level, max_level + 1)


def de_exp_quad_vec(f, ncomp, digits, scale=ONE, h0=None, max_level=12, min_level=3, tmin_span=3):
    """向量版：∫_0^∞ f(v) dv，f(v) 返回 ncomp 个 Decimal（共用节点，节省超越函数调用）。
    变换 v = scale·exp(t − e^{−t})；scale 取被积函数在 0 附近的衰减尺度（例如 1/(λ+2)），
    这样变换后主衰减是 e^{−s}，复带宽度不随 λ 变窄。
    停止准则：每个分量 |Q_k − Q_{k−1}| ≤ 10^{−digits}|Q_k|。返回 (Q 列表, 误差列表, 信息)。"""
    if h0 is None:
        h0 = D('0.5')
    tol_rel = D(10) ** (-(digits + 8))
    scale = +scale

    def node(t, et=None):
        if et is None:
            et = (-t).exp()
        s = (t - et).exp()
        return scale * s, scale * s * (1 + et)

    def side_sum(h, start, step, sign, S_ref):
        # e^{−t_j} 用等比递推（t_j = sign·j·h），每个节点省一次 exp；累积相对误差 ~ 节点数·10^{−prec}
        tot = [D(0)] * ncomp
        j = start
        small = 0
        et = (-(sign * start * h)).exp()
        ratio = (-(sign * step * h)).exp()
        while True:
            t = sign * j * h
            v, dv = node(t, et)
            et *= ratio
            if v == 0 or dv == 0:
                vals = [D(0)] * ncomp
            else:
                vals = [fv * dv for fv in f(v)]
            for i in range(ncomp):
                tot[i] += vals[i]
            if abs(t) >= tmin_span and all(abs(vals[i]) <= tol_rel * abs(S_ref[i] + tot[i]) for i in range(ncomp)):
                small += 1
                if small >= 4:
                    break
            else:
                small = 0
            j += step
            if j * h > 40:
                raise RuntimeError("de_exp_quad_vec：t 超过 40 仍未截断")
        return tot

    h = +h0
    v0, dv0 = node(D(0))
    S = [fv * dv0 for fv in f(v0)]
    add = side_sum(h, 1, 1, 1, S)
    S = [S[i] + add[i] for i in range(ncomp)]
    add = side_sum(h, 1, 1, -1, S)
    S = [S[i] + add[i] for i in range(ncomp)]
    Qp = [h * s for s in S]
    nodes = None
    for lev in range(1, max_level + 1):
        h = h / 2
        add = side_sum(h, 1, 2, 1, S)
        S2 = [S[i] + add[i] for i in range(ncomp)]
        add2 = side_sum(h, 1, 2, -1, S2)
        S = [S2[i] + add2[i] for i in range(ncomp)]
        Q = [h * s for s in S]
        errs = [abs(Q[i] - Qp[i]) for i in range(ncomp)]
        if lev >= min_level and all(errs[i] <= abs(Q[i]) * D(10) ** (-digits) for i in range(ncomp)):
            return Q, errs, "levels=%d h=2^-%d" % (lev, lev + 1)
        Qp = Q
    return Q, errs, "levels=%d (max) h=2^-%d" % (max_level, max_level + 1)


def ts_quad(f, a, b, digits, max_level=12, min_level=3):
    """∫_a^b f(u) du，tanh-sinh：u = (a+b)/2 + (b−a)/2·tanh(π/2·sinh t)。
    用到端点的距离 d = 1 − tanh y = 2/(1+e^{2y}) 直接算节点，避免端点附近的相消。"""
    a = +a
    b = +b
    half = (b - a) / 2
    pi2 = pi_dec() / 2
    tol_rel = D(10) ** (-(digits + 8))

    def pair(t):
        # 返回 (左节点, 右节点, 权重)；t>0
        et = t.exp()
        sh = (et - 1 / et) / 2
        ch = (et + 1 / et) / 2
        y = pi2 * sh
        E = (2 * y).exp()
        d = 2 / (1 + E)
        w = pi2 * ch * 4 * E / ((1 + E) * (1 + E))
        return a + half * d, b - half * d, w

    def side_sum(h, start, step, S_ref):
        total = D(0)
        j = start
        small = 0
        while True:
            t = j * h
            uL, uR, w = pair(t)
            if w == 0:
                break
            vals = D(0)
            if uL > a:
                vals += f(uL)
            if uR < b:
                vals += f(uR)
            term = w * vals
            total += term
            if abs(term) <= tol_rel * abs(S_ref + total) and t >= 2:
                small += 1
                if small >= 4:
                    break
            else:
                small = 0
            j += step
            if t > 12:
                break
        return total

    h = D('0.5')
    S = pi2 * f(a + half)            # t=0：权重 π/2
    S += side_sum(h, 1, 1, S)
    Q_prev = half * h * S
    for lev in range(1, max_level + 1):
        h = h / 2
        S += side_sum(h, 1, 2, S)
        Q = half * h * S
        err = abs(Q - Q_prev)
        if lev >= min_level and err <= (abs(Q) if Q != 0 else ONE) * D(10) ** (-digits):
            return Q, err, "levels=%d" % lev
        Q_prev = Q
    return Q, err, "levels=%d (max)" % max_level


def ts_quad_composite(f, a, b, digits, piece=D(1), **kw):
    """把 [a,b] 切成长度 ≤ piece 的若干段，各段 tanh-sinh 后相加；误差估计相加。"""
    a = +a
    b = +b
    n = int(((b - a) / piece).to_integral_value(rounding="ROUND_CEILING"))
    n = max(n, 1)
    step = (b - a) / n
    tot = D(0)
    errs = D(0)
    infos = []
    for i in range(n):
        lo = a + i * step
        hi = b if i == n - 1 else a + (i + 1) * step
        q, e, info = ts_quad(f, lo, hi, digits, **kw)
        tot += q
        errs += e
        infos.append(info)
    return tot, errs, "%d pieces; %s" % (n, ",".join(sorted(set(infos))))


def sci(x, k=12):
    """Decimal → 科学计数法短串，保留 k 位有效数字。"""
    if x == 0:
        return "0"
    with localcontext() as ctx:
        ctx.prec = k
        y = +x
    return format(y, ".%dE" % (k - 1))      # Decimal 自己格式化，不经 float（避免下溢）


def log10_abs(x):
    """|x| 的以 10 为底的对数（float），x 为 Decimal；只用于估计数量级。"""
    if x == 0:
        return float("-inf")
    with localcontext() as ctx:
        ctx.prec = 30
        return float(abs(x).log10())
