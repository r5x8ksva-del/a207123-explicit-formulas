# -*- coding: utf-8 -*-
"""复核 s12-b4：notes/12 §2（引理 2.0–2.5、定理 2 (a)(b)(c)、注 2.6）。
U 的真值来自 code/core.py；其余自写。v_p(A_p^(0)) 用三种互相独立的办法：
  (1) 直接在 Q[x]/(b_p) 中约化 W̃_p；(2) 由 U 的数据解线性方程组（p=3,5,7）；
  (3) p 进根：在 Q_p(√-p) 中用 Newton 求 b_p 的三个根，再做 Lagrange 插值（3<=p<=31）。"""
import random
import time
from fractions import Fraction as Fr
from math import factorial, comb
from functools import lru_cache

from s12_common import (Checker, C, ff, vp, primes_upto, U_core, tables_UEc, P_poly, Wt_poly,
                        b_poly, reduce_bi, mul_x, mul_xinv, mul_xpow, norm_K, c_seq, c_at,
                        cbar_neg, exact_solve, system_status, padd, pmul, series_div)

ck = Checker('s12_thm2')
t0 = time.time()
MP = 2147483647


@lru_cache(maxsize=None)
def A_vec(i):
    """W̃_i 在 K_i 中的约化坐标 (A^(0),A^(1),A^(2))（直接约化）。"""
    return reduce_bi(Wt_poly(i), i)


# ------------------------------------------------ 引理 2.2：负下标闭式 vs 向负方向解递推
ok = True
for i in range(1, 16):
    d = cbar_neg(i, 60)
    for n in range(1, 61):
        cf = sum(Fr((-1) ** (n - 3 - l)) * Fr(1, i ** (l + 1)) * C(l, n - 3 - 2 * l) for l in range(0, n + 1))
        if cf != d[n]:
            ok = False
ck.check('L2.2-negc', ok and cbar_neg(5, 3)[1:] == [0, 0, Fr(1, 5)],
         'c̄_i(-n)=Σ_l(-1)^{n-3-l}i^{-l-1}C(l,n-3-2l) 与向负方向解递推一致（1<=i<=15，1<=n<=60）；c̄(-1)=c̄(-2)=0、c̄(-3)=1/i')

# ------------------------------------------------ 引理 2.0：Φ 与代表无关、平移性质
ok = True
for i in range(1, 11):
    d = cbar_neg(i, 80)
    cs = c_seq(i, 80)
    cb = lambda n: Fr(cs[n]) if n >= 0 else d[-n]
    Wt = Wt_poly(i)
    Av = A_vec(i)
    for n in range(-15, 31):
        phi_un = sum(Fr(cf) * cb(n - a) for a, cf in enumerate(Wt) if cf)
        phi_red = sum(Av[r] * cb(n - r) for r in range(3))
        if phi_un != phi_red:
            ok = False
        # Φ_{xθ}(n)=Φ_θ(n-1)：xθ 的约化坐标
        xv = mul_x(Av, i)
        if sum(xv[r] * cb(n - r) for r in range(3)) != sum(Av[r] * cb(n - 1 - r) for r in range(3)):
            ok = False
    for n in range(0, 31):    # n>=0 时 Φ_θ(n)=[x^n](约化代表)/b_i
        ser = series_div([Av[0], Av[1], Av[2]], b_poly(i), 31)
        if sum(Av[r] * cb(n - r) for r in range(3)) != ser[n]:
            ok = False
ck.check('L2.0-Phi', ok, 'Φ_{W̃_i} 用未约化/约化代表一致；Φ_{xθ}(n)=Φ_θ(n-1)；n>=0 时等于 [x^n]θ/b_i（1<=i<=10，-15<=n<=30）')

# ------------------------------------------------ 引理 2.1：部分分式
U = U_core(60, 8)
ok = True
for m in range(0, 9):
    css = {i: c_seq(i, 30 + 3 * m) for i in range(1, m + 1)}
    for k in range(0, 31):
        val = Fr((-1) ** m, factorial(m))
        for i in range(1, m + 1):
            Av = A_vec(i)
            val += Fr((-1) ** (m - i), factorial(i) * factorial(m - i)) * sum(Av[r] * c_at(css[i], k + 3 * m - r) for r in range(3))
        if val != U[k][m]:
            ok = False
ck.check('L2.1-pf', ok, 'U_k(m)=(-1)^m/m!+Σ_i(-1)^{m-i}/(i!(m-i)!)Σ_r A_i^(r) c_i(k+3m-r)（0<=m<=8，0<=k<=30，精确）')

# 反向：把 (-1)^{m-i} 改成 (-1)^i 应失败
bad = 0
for m in range(2, 6):
    css = {i: c_seq(i, 30 + 3 * m) for i in range(1, m + 1)}
    for k in range(0, 31):
        val = Fr((-1) ** m, factorial(m))
        for i in range(1, m + 1):
            Av = A_vec(i)
            val += Fr((-1) ** i, factorial(i) * factorial(m - i)) * sum(Av[r] * c_at(css[i], k + 3 * m - r) for r in range(3))
        if val != U[k][m]:
            bad += 1
ck.check('L2.1-reverse', bad > 0, f'把符号改成 (-1)^i 后有 {bad} 处不等（核对确实敏感）')

# ------------------------------------------------ 定理 2(b)：任意固定 σ 的三原子表示
ok = True
for sigma in range(-4, 5):
    for m in range(1, 7):
        css = {i: c_seq(i, 40 + 3 * m + 5) for i in range(1, m + 1)}
        av = {i: mul_xpow(A_vec(i), i, sigma) for i in range(1, m + 1)}
        for k in range(6, 31):
            val = Fr((-1) ** m, factorial(m))
            for i in range(1, m + 1):
                val += Fr((-1) ** (m - i), factorial(i) * factorial(m - i)) * sum(
                    av[i][r] * c_at(css[i], k + 3 * m + sigma - r) for r in range(3))
            if val != U[k][m]:
                ok = False
ck.check('T2b-shift', ok, 'σ∈[-4,4]：U_k(m)=γ^(0)+Σ_iΣ_r γ_r c_i(k+3m+σ-r)，a^(σ)=x^σW̃_i 的约化坐标（1<=m<=6，6<=k<=30）')

# 由 U 的数据解方程组：唯一性、系数与 m 无关、p=3,5,7 的 p 进赋值（与 core 以外的推导完全独立）
data_a = {}
ok_rank = True
ok_match = True
for m in range(1, 8):
    kk = list(range(6, 6 + 3 * m + 18))
    css = {i: c_seq(i, kk[-1] + 3 * m + 2) for i in range(1, m + 1)}
    cols = [('c0', 0, 0)] + [('c', i, r) for i in range(1, m + 1) for r in range(3)]
    A = [[1 if col[0] == 'c0' else c_at(css[col[1]], k + 3 * m - col[2]) for col in cols] for k in kk]
    b = [U[k][m] for k in kk]
    okk, rank, sol = exact_solve(A, b)
    ok_rank &= okk and rank == len(cols)
    for j, col in enumerate(cols[1:], start=1):
        _, i, r = col
        a_val = sol[j] * (-1) ** (m - i) * factorial(i) * factorial(m - i)
        data_a.setdefault((i, r), set()).add(a_val)
        if a_val != A_vec(i)[r]:
            ok_match = False
    ok_match &= (sol[0] == Fr((-1) ** m, factorial(m)))
indep = all(len(s) == 1 for s in data_a.values())
ck.check('T2b-unique-data', ok_rank and ok_match and indep,
         '由 U 数据解出的 3m+1 个系数唯一（满列秩，m=1..7），a_r(i)=(-1)^{m-i}i!(m-i)!γ_r(m,i) 与 m 无关，且等于直接约化的坐标')
vals_data = {p: vp(next(iter(data_a[(p, 0)])), p) for p in (3, 5, 7)}
ck.check('L2.4-data', all(vals_data[p] == -3 * (p - 1) // 2 for p in (3, 5, 7)),
         f'由 U 数据算出的 v_p(A_p^(0))：{vals_data}（预期 -3(p-1)/2）')

# ------------------------------------------------ 引理 2.3
ok = True
for i in range(1, 41):
    d = cbar_neg(i, 3 * i + 2)
    val = 1 + sum(j * ff(i, j) * d[3 * j + 2] for j in range(1, i + 1))
    if val != A_vec(i)[0]:
        ok = False
ck.check('L2.3', ok, 'A_i^(0)=1+Σ_j j·i^(j)·c̄_i(-3j-2)（1<=i<=40；c̄ 由向负方向解递推）')

# ------------------------------------------------ 引理 2.4：直接约化，奇素数 p<=211
odd = [p for p in primes_upto(211) if p > 2]
res = {}
for p in odd:
    res[p] = vp(A_vec(p)[0], p)
okv = all(res[p] == -3 * (p - 1) // 2 for p in odd)
ck.check('L2.4-reduce', okv, f'直接在 Q[x]/(b_p) 中约化 W̃_p：v_p(A_p^(0))=-3(p-1)/2 对 {len(odd)} 个奇素数 3..211 全部成立'
         + ('' if okv else f'；不符：{[(p, res[p]) for p in odd if res[p] != -3 * (p - 1) // 2][:5]}'))
ck.check('L2.4-p2', A_vec(2)[0] == Fr(-1, 2), f'A_2^(0)={A_vec(2)[0]}（笔记：-1/2）')
ck.check('L2.4-data-small', [res[p] for p in (3, 5, 7, 11)] == [-3, -6, -9, -15], f'p=3,5,7,11：{[res[p] for p in (3, 5, 7, 11)]}')
# 反向：断言改成 -3(p-1)/2+1 时应对每个素数都失败
ck.check('L2.4-reverse', all(res[p] != -3 * (p - 1) // 2 + 1 for p in odd), '把断言改成 -3(p-1)/2+1 后每个素数都不成立')

# 证明内部的逐项结构：j=p 项唯一最小；中间界 v_p(c̄_p(-n))>=-(⌊(n-3)/2⌋+1)，n=3p+2 处取等
ok_struct = True
ok_bound = True
for p in [q for q in odd if q <= 101]:
    d = cbar_neg(p, 3 * p + 2)
    for n in range(3, 3 * p + 3):
        if d[n] != 0 and vp(d[n], p) < -((n - 3) // 2 + 1):
            ok_bound = False
    if vp(d[3 * p + 2], p) != -((3 * p + 1) // 2):
        ok_bound = False
    target = (3 - 3 * p) // 2
    vals = [0] + [vp(j * ff(p, j) * d[3 * j + 2], p) for j in range(1, p + 1)]
    vals = [v if v is not None else 10 ** 9 for v in vals]
    if vals[p] != target or min(vals[:p]) <= target:
        ok_struct = False
ck.check('L2.4-structure', ok_struct and ok_bound,
         '3<=p<=101：j=p 项赋值恰为 (3-3p)/2，其余各项（含常数 1）都严格更大；v_p(c̄_p(-n))>=-(⌊(n-3)/2⌋+1)，n=3p+2 处取等')


# ------------------------------------------------ 引理 2.4 的第三种办法：p 进根 + Lagrange 插值
def padic_A0(p, L):
    P = p
    PF = Fr(P)

    def tr(r):
        if r == 0:
            return Fr(0)
        v = vp(r, P)
        if v >= L:
            return Fr(0)
        mod = P ** (L - v)
        u = r / PF ** v
        t = (u.numerator * pow(u.denominator, -1, mod)) % mod
        return Fr(t) * PF ** v

    def mul(z, w):
        return (tr(z[0] * w[0] - P * z[1] * w[1]), tr(z[0] * w[1] + z[1] * w[0]))

    def add(z, w):
        return (tr(z[0] + w[0]), tr(z[1] + w[1]))

    def neg(z):
        return (-z[0], -z[1])

    def inv(z):
        n = z[0] * z[0] + P * z[1] * z[1]
        return (tr(z[0] / n), tr(-z[1] / n))

    def val(z):
        vs = []
        if z[0] != 0:
            vs.append(Fr(vp(z[0], P)))
        if z[1] != 0:
            vs.append(Fr(vp(z[1], P)) + Fr(1, 2))
        return min(vs) if vs else None

    one = (Fr(1), Fr(0))
    sc = lambda c: (Fr(c), Fr(0))
    # 大根：z=1/η 满足 z^3-z^2-p=0，z≈π（π^2=-p）
    z = (Fr(0), Fr(1))
    for _ in range(14):
        z2 = mul(z, z)
        g = add(add(mul(z2, z), neg(z2)), sc(-P))
        gp = add(mul(sc(3), z2), mul(sc(-2), z))
        z = add(z, neg(mul(g, inv(gp))))
    z2 = mul(z, z)
    gres = add(add(mul(z2, z), neg(z2)), sc(-P))
    # 小根：η_0≈1
    x = one
    for _ in range(14):
        x3 = mul(mul(x, x), x)
        bx = add(add(one, neg(x)), mul(sc(-P), x3))
        bpx = add(sc(-1), mul(sc(-3 * P), mul(x, x)))
        x = add(x, neg(mul(bx, inv(bpx))))
    etas = [x, inv(z), None]
    etas[2] = (etas[1][0], -etas[1][1])
    resid = []
    for eta in etas:
        e3 = mul(mul(eta, eta), eta)
        resid.append(val(add(add(one, neg(eta)), mul(sc(-P), e3))))

    def Wt_at(eta):
        tot = one
        e3 = mul(mul(eta, eta), eta)
        cur = mul(mul(eta, eta), e3)          # η^5
        top = None
        for j in range(1, P + 1):
            term = mul(sc(j * ff(P, j)), cur)
            tot = add(tot, term)
            if j == P:
                top = term
            cur = mul(cur, e3)
        return tot, top
    A0 = (Fr(0), Fr(0))
    info = {}
    for t in range(3):
        s1, s2 = [etas[s] for s in range(3) if s != t]
        num = mul(s1, s2)
        den = mul(add(etas[t], neg(s1)), add(etas[t], neg(s2)))
        Wv, top = Wt_at(etas[t])
        if t == 1:
            info['vW_big'] = val(Wv)
            info['vTop_big'] = val(top)
        A0 = add(A0, mul(Wv, mul(num, inv(den))))
    return A0, info, val(gres), resid


okpad = True
details = []
for p in [q for q in odd if q <= 31]:
    L = 2 * p + 40
    A0, info, vg, resid = padic_A0(p, L)
    exact = A_vec(p)[0]
    v_pad = vp(A0[0], p)
    agree = vp(A0[0] - exact, p)
    ok = (v_pad == -3 * (p - 1) // 2 and (A0[1] == 0 or vp(A0[1], p) > v_pad + 20)
          and (agree is None or agree > v_pad + 20)
          and info['vW_big'] == info['vTop_big'] == Fr(2) - Fr(3 * p + 2, 2))
    okpad &= ok
    details.append(f'p={p}:v={v_pad},与精确值同余到 p^{agree if agree is not None else "∞"},v(W̃(η_大))={info["vW_big"]}')
ck.check('L2.4-padic', okpad, 'Q_p(√-p) 中 Newton 求根 + Lagrange 插值：v_p(A_p^(0))=-3(p-1)/2；大根处 W̃_p(η) 的赋值等于最高项 p·p!·η^{3p+2} 的赋值 2-(3p+2)/2（注 2.6 的「占主导」）；'
         + '; '.join(details))

# ------------------------------------------------ 平移 σ：矩阵 M^{-1} 整、min_r v_p(a^(σ)) 的界
ok_int = True
for i in range(1, 30):
    for e in [(Fr(1), Fr(0), Fr(0)), (Fr(0), Fr(1), Fr(0)), (Fr(0), Fr(0), Fr(1))]:
        if any(Fr(t).denominator != 1 for t in mul_xinv(e, i)):
            ok_int = False
        if mul_x(mul_xinv(e, i), i) != e:
            ok_int = False
ck.check('T2c-Minv', ok_int, 'K_i 中乘以 x^{-1}=1+ix² 的矩阵是整数矩阵，且确是 M 的逆（1<=i<29）')
ok_sig = True
tab = []
for p in [q for q in odd if q <= 61]:
    base = A_vec(p)
    row = []
    for sigma in range(-6, 7):
        av = mul_xpow(base, p, sigma)
        mv = min(vp(t, p) for t in av if t != 0)
        row.append(mv)
        if mv > -3 * (p - 1) // 2 + abs(sigma):
            ok_sig = False
    if p in (3, 7, 31, 61):
        tab.append(f'p={p}:{row}')
ck.check('T2c-sigma', ok_sig, 'σ∈[-6,6]，3<=p<=61：min_r v_p(a_r^(σ)(p))<=-3(p-1)/2+|σ|。例（σ=-6..6）：' + '; '.join(tab))

# 范围：若平移随 m 变化（σ=-3m，即原子 c_i(k-r)），p 进障碍消失
ok_m = True
tab = []
for p in [q for q in odd if q <= 61]:
    base = A_vec(p)
    vals = []
    for m in (p, p + 1, p + 2):
        av = mul_xpow(base, p, -3 * m)
        g = [Fr((-1) ** (m - p), factorial(p) * factorial(m - p)) * t for t in av]
        vals.append(min(vp(t, p) for t in g if t != 0))
    if min(vals) < -1:
        ok_m = False
    if p in (3, 11, 31, 61):
        tab.append(f'p={p}:{vals}')
ck.check('T2c-scope-sigma=-3m', ok_m, '原子取 c_i(k-r)（相当于 σ=-3m）时，i=p、m=p,p+1,p+2 的系数 γ_r 的 min v_p >=-1（3<=p<=61）——引理 2.4/2.5 的论证在这种归一化下不起作用：'
         + '; '.join(tab))


# ------------------------------------------------ 「最后一句」的直接佐证：猜递推（模 2^31-1）
def rank_mod(rows, ncols, p=MP):
    rows = [[x % p for x in r] for r in rows]
    rank = 0
    for col in range(ncols):
        piv = None
        for r in range(rank, len(rows)):
            if rows[r][col]:
                piv = r
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        rows[rank] = [x * inv % p for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                f = rows[r][col]
                rows[r] = [(x - f * y) % p for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def modq(x, p=MP):
    x = Fr(x)
    return x.numerator % p * pow(x.denominator % p, p - 2, p) % p


coords = {i: A_vec(i) for i in range(1, 91)}
for r in range(3):
    seq = [modq(coords[i][r]) for i in range(1, 91)]
    rows = []
    order, deg = 2, 5
    for n in range(0, 90 - order):
        i = n + 1
        row = []
        for t in range(order + 1):
            for j in range(deg + 1):
                row.append(pow(i, j, MP) * seq[n + t] % MP)
        rows.append(row)
    nc = (order + 1) * (deg + 1)
    rk = rank_mod(rows, nc)
    ck.check(f'T2c-guess a_{r}', rk == nc, f'i↦a_{r}^(0)(i) 在 1<=i<=90 上没有阶<=2、多项式次数<=5 的递推（模素数满秩 {rk}/{nc}）')


def guess_mi(gamma, M, D):
    mons = [(u, w) for u in range(D + 1) for w in range(D + 1 - u)]
    rows = []
    for m in range(2, M + 1):
        for i in range(1, m):
            row = [pow(m, u, MP) * pow(i, w, MP) % MP * gamma(m, i + 1) % MP for (u, w) in mons]
            row += [(-pow(m, u, MP) * pow(i, w, MP) % MP) * gamma(m, i) % MP for (u, w) in mons]
            rows.append(row)
    return rank_mod(rows, 2 * len(mons)), 2 * len(mons)


fact = [1]
for n in range(1, 80):
    fact.append(fact[-1] * n)
for r in range(3):
    gm = lambda m, i, r=r: modq(Fr((-1) ** (m - i), fact[i] * fact[m - i]) * coords[i][r])
    rk, nc = guess_mi(gm, 30, 4)
    ck.check(f'T2c-guess-hyper r={r}', rk == nc, f'γ_{r}(m,i) 不满足 q(m,i)γ(m,i+1)=p(m,i)γ(m,i)，q、p 总次数<=4（1<=i<m<=30；模素数满秩 {rk}/{nc}）')
gm1 = lambda m, i: modq(Fr((-1) ** (m - i), fact[i] * fact[m - i]))
rk, nc = guess_mi(gm1, 30, 4)
ck.check('T2c-guess-reverse', rk < nc, f'对照：U^c 的系数 (-1)^{{m-i}}/(i!(m-i)!) 确实被找到递推（秩 {rk}<{nc}）')

# ------------------------------------------------ 定理 2(a)：每个 i 一个原子
UT = U_core(42, 4)
Uo, Eo, Uco = tables_UEc(42, 4)
K0, K1 = 10, 40
cs_all = {i: c_seq(i, 60) for i in range(0, 5)}
for name, f, m in [('U', UT, 1), ('U', UT, 2), ('U', UT, 3), ('E', Eo, 2), ('E', Eo, 3)]:
    cnt = 0
    bad = []
    import itertools
    for deltas in itertools.product(range(-6, 7), repeat=m):
        A = []
        for k in range(K0, K1 + 1):
            A.append([1] + [c_at(cs_all[i], k + deltas[i - 1]) for i in range(1, m + 1)])
        b = [f[k][m] for k in range(K0, K1 + 1)]
        st = system_status(A, b)
        cnt += 1
        if not st.startswith('inconsistent'):
            bad.append(deltas)
    ck.check(f'T2a-linsys {name} m={m}', not bad, f'{cnt} 组平移 δ(i)∈[-6,6]（δ(0) 无关），k∈[10,40]：全部无解' + (f'；可解 {bad[:4]}' if bad else ''))
# 对照：U^c（δ(i)=3m）与 E_1（δ(1)=-2）有单原子表示
for m in (1, 2, 3):
    A = [[1] + [c_at(cs_all[i], k + 3 * m) for i in range(1, m + 1)] for k in range(K0, K1 + 1)]
    okc, _, sol = exact_solve(A, [Uco[k][m] for k in range(K0, K1 + 1)])
    pred = [Fr((-1) ** m, factorial(m))] + [Fr((-1) ** (m - i), factorial(i) * factorial(m - i)) for i in range(1, m + 1)]
    ck.check(f'T2a-control Uc m={m}', okc and sol == pred, 'U^c_k(m)=Σ_i(-1)^{m-i}c_i(k+3m)/(i!(m-i)!)（注 2.6 / (C4)），按定义计数的 U^c 精确满足')
A = [[1, c_at(cs_all[1], k - 2)] for k in range(K0, K1 + 1)]
okc, _, sol = exact_solve(A, [Eo[k][1] for k in range(K0, K1 + 1)])
ck.check('T2a-control E m=1', okc and sol == [0, 1], 'E_k(1)=c_1(k-2)（E 的 m=1 有单原子表示，所以 E 要 m>=2）')

# 范数
N1 = norm_K([1, 1], b_poly(1))
Nx1 = norm_K([0, 1], b_poly(1))
W2m1 = padd(Wt_poly(2), [-1])
N2 = norm_K(W2m1, b_poly(2))
Nx2 = norm_K([0, 1], b_poly(2))
same = reduce_bi(W2m1, 2) == reduce_bi(pmul([0, 0, 0, 0, 0, 1], [4, -2]), 2)
cube_free = all(vp(Fr(17) * Fr(2) ** (-3 - n), 17) % 3 != 0 for n in range(-60, 61))
ck.check('T2a-norms', N1 == 3 and Nx1 == 1 and N2 == Fr(17, 8) and Nx2 == Fr(1, 2) and same and cube_free,
         f'N(1+ξ)={N1}，N(ξ)={Nx1}；K_2：N(W̃_2-1)={N2}，N(η)={Nx2}，W̃_2-1≡x^5(4-2x)={same}；17·2^(-3-n) 的 17 进赋值为 1（不是立方）')

print(f'time {time.time() - t0:.1f}s')
import sys
sys.exit(0 if ck.summary() else 1)
