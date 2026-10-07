# -*- coding: utf-8 -*-
"""s10-b1 核对 3：h_k 实根且互异（整数 Sturm），以及笔记 05 §4 的各个推论的数值形式，
§5（C3：t 坐标下相邻 h_k 不交错）的一致性。

用法：py s10b1_check_roots.py [KH]（KH = h_k 实根核对的上限，默认 100）
"""
import os
import sys
import time
from fractions import Fraction
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s10b1_poly import (add, sub, mul, mulz, mul1z, deriv, scal, norm, ev_int, pgcd, divexact, deg,
                        is_real_simple, is_real_rooted, n_real_distinct_in, mult_at, sign_changes,
                        letters_alternate, binom_poly_eval, isolate, merged_points,
                        sylvester_seq, V_at, V_inf)
from s10b1_data import N_tri, nrow, U_dp

KH = int(sys.argv[1]) if len(sys.argv) > 1 else 100
KC = 60                       # 推论的数值形式核对到 k≤60（另有些到 KH）
t0 = time.time()
N = N_tri(max(KH, KC) + 2)
PASS = 0
FAIL = 0


def check(name, ok, detail=''):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        print('FAIL', name, detail, flush=True)
    return ok


def powpoly(p, e):
    r = [1]
    for _ in range(e):
        r = mul(r, p)
    return r


OMT = [1, -1]          # 1 − t


def h_from_N(k):
    if k == 0:
        return [1]
    s = []
    for q in range(1, k + 1):
        if N[k][q]:
            term = scal(N[k][q], mul([0] * (q - 1) + [1], powpoly(OMT, k - q)))
            s = add(s, term)
    return s


H = {k: h_from_N(k) for k in range(0, max(KH, KC) + 2)}

# ---- h_k 与定义 Σ_m U_k(m) t^m = h_k/(1−t)^(k+1) 对照（U 用按定义的 DP），k≤40
KU = 40
U = U_dp(KU, KU + 6)
for k in range(0, KU + 1):
    coeffs = [sum((-1) ** (i - j) * comb(k + 1, i - j) * U[k][j] for j in range(i + 1)) for i in range(k + 6)]
    check('h_k from U k=%d' % k, norm(coeffs) == H[k])
print('h from U done %.1fs' % (time.time() - t0), flush=True)

# ---- 次数、端点值、首项符号
for k in range(0, max(KH, KC) + 1):
    h = H[k]
    check('deg h_k = floor(2k/3) k=%d' % k, deg(h) == (2 * k) // 3, 'deg=%d' % deg(h))
    check('h_k(0)=1 k=%d' % k, h[0] == 1)
    if k >= 2:
        check('h_k(1)=2 k=%d' % k, ev_int(h, 1) == 2)
    check('sign lc h_k = (-1)^floor(k/3) k=%d' % k, (h[-1] > 0) == ((k // 3) % 2 == 0))

# ---- 实根且互异（整数 Sturm）
t1 = time.time()
SEQ = {}
for k in range(0, KH + 1):
    h = H[k]
    if deg(h) <= 0:
        check('h_k real & simple k=%d' % k, True)
        continue
    seq = sylvester_seq(h, deriv(h))
    vm, v0, v1, vp = V_inf(seq, -1), V_at(seq, 0), V_at(seq, 1), V_inf(seq, 1)
    SEQ[k] = (v1 - vp, vm - v0, v0 - v1)               # 只存三个计数，不存整条序列（省内存）
    squarefree = deg(seq[-1]) == 0                      # 序列末项 ∝ gcd(h, h')
    nreal = V_inf(seq, -1) - V_inf(seq, 1)
    check('h_k real & simple k=%d' % k, squarefree and nreal == deg(h), 'sqfree=%s nreal=%d deg=%d' % (squarefree, nreal, deg(h)))
    if k % 25 == 0:
        print('real-simple up to k=%d  %.1fs' % (k, time.time() - t0), flush=True)
print('real-simple done k<=%d in %.1fs' % (KH, time.time() - t1), flush=True)
# 另用 is_real_simple（gcd + 独立再算一次 Sturm）复核到 k<=60
for k in range(0, 61):
    check('h_k real & simple (2nd routine) k=%d' % k, is_real_simple(H[k]))

# ---- 根的分布、系数变号（到 KH）
for k in range(1, KH + 1):
    h = H[k]
    if k in SEQ:
        r_gt1, r_neg, r_01 = SEQ[k]
    else:
        r_gt1 = r_neg = r_01 = 0
    check('#roots in (1,inf) = floor(k/3) k=%d' % k, r_gt1 == k // 3, str(r_gt1))
    check('#roots in (-inf,0) = floor((k+1)/3) k=%d' % k, r_neg == (k + 1) // 3, str(r_neg))
    check('no roots in (0,1] k=%d' % k, r_01 == 0)
    check('sign changes of h_k = floor(k/3) k=%d' % k, sign_changes(h) == k // 3, str(sign_changes(h)))
print('distribution done %.1fs' % (time.time() - t0), flush=True)

# ---- n_k：−1 的重数、(−∞,−1) 中的根数 ν_k、N(k,q)>0、严格对数凹与 Newton 不等式
for k in range(1, KH + 1):
    nk = nrow(N, k)
    a, core = mult_at(nk, -1)
    check('mult_{-1} n_k = ceil(k/3)-1 k=%d' % k, a == -(-k // 3) - 1)
    nu = n_real_distinct_in(core, None, -1)
    check('nu_k = floor(k/3) k=%d' % k, nu == k // 3, str(nu))
    check('deg h_k = k-1-mult k=%d' % k, deg(H[k]) == k - 1 - a)
    row = [N[k][q] for q in range(1, k + 1)]
    check('N(k,q)>0 for 1<=q<=k k=%d' % k, all(x > 0 for x in row))
    lc_ok = all(N[k][q] ** 2 > N[k][q - 1] * N[k][q + 1] for q in range(2, k))
    newton_ok = all(N[k][q] ** 2 * (q - 1) * (k - q) >= N[k][q - 1] * N[k][q + 1] * q * (k - q + 1) for q in range(2, k))
    check('strict log-concave k=%d' % k, lc_ok)
    check('Newton inequality k=%d' % k, newton_ok)
    # 单峰
    i = row.index(max(row))
    check('unimodal k=%d' % k, all(row[j] <= row[j + 1] for j in range(i)) and all(row[j] >= row[j + 1] for j in range(i, len(row) - 1)))
print('n_k facts done %.1fs' % (time.time() - t0), flush=True)

# ---- 中心极限定理里用到的方差下界
vs = []
for k in range(1, KH + 1):
    row = [N[k][q] for q in range(0, k + 1)]
    tot = sum(row)
    m1 = Fraction(sum(q * row[q] for q in range(k + 1)), tot)
    m2 = Fraction(sum(q * q * row[q] for q in range(k + 1)), tot)
    var = m2 - m1 * m1
    check('Var X_k >= (ceil(k/3)-1)/4 k=%d' % k, var >= Fraction(-(-k // 3) - 1, 4))
    if k in (10, 20, 40, 60, 80, 100, 150):
        vs.append((k, float(m1), float(var), float(var) / k))
print('Var X_k samples (k, E, Var, Var/k):', ['(%d, %.3f, %.3f, %.4f)' % v for v in vs])

# ---- B8 附带事实：U_k(−j) 的生成函数、Q_k、变号
for k in range(1, KC + 1):
    sk = (k + 2) // 3
    vals = [sum(N[k][q] * binom_poly_eval(1 - j, q) for q in range(1, k + 1)) for j in range(1, 10 * k + 1)]
    check('U_k(-j)=0 for j<=s_k k=%d' % k, all(v == 0 for v in vals[:sk]) and vals[sk] != 0)
    tail = vals[sk:]
    sc = sign_changes(tail)
    check('sign changes of U_k(-j), s_k<j<=10k, <= floor(k/3) k=%d' % k, sc <= k // 3, str(sc))
    # Q_k
    nk = nrow(N, k)
    a, core = mult_at(nk, -1)        # core = m_k = 2∏(z−z_i)
    r = deg(core)
    Q2 = []                           # 2·Q_k(t) = (−1)^r Σ c_i (−1)^i (1−t)^(r−i)
    for i, c in enumerate(core):
        Q2 = add(Q2, scal(((-1) ** (r + i)) * c, powpoly(OMT, r - i)))
    check('Q_k(0) != 0 k=%d' % k, Q2[0] != 0 if Q2 else False)
    check('Q_k real-rooted k=%d' % k, is_real_rooted(Q2))
    check('Q_k #pos roots = floor(k/3) k=%d' % k, n_real_distinct_in(Q2, 0, None) == k // 3)
    check('Q_k sign changes = floor(k/3) k=%d' % k, sign_changes(Q2) == k // 3)
    # Σ_{j≥1} U_k(−j) t^j = 2(−1)^k t^(s_k+1) Q_k(t)/(1−t)^(k+1)  ⇒  系数（2Q_k 已含因子 2）
    ok = True
    for j in range(1, 10 * k + 1):
        e = j - sk - 1
        rhs = 0
        if e >= 0:
            rhs = ((-1) ** k) * sum(Q2[i] * comb(e - i + k, k) for i in range(min(e, deg(Q2)) + 1))
        if rhs != vals[j - 1]:
            ok = False
            break
    check('U_k(-j) gf identity with Q_k k=%d' % k, ok)
print('B8 side facts done %.1fs' % (time.time() - t0), flush=True)

# ---- §5 / C3：t 坐标下 h_k、h_{k+1} 的根不交替；同时 z 坐标下 n_k、n_{k+1} 交替（α 已在核对 2）
check('h_3 = 1+2t-t^2, h_4 = 1+4t-3t^2', H[3] == [1, 2, -1] and H[4] == [1, 4, -3])
cnt_nonalt = 0
for k in range(2, 36):
    g = pgcd(H[k], H[k + 1])
    check('gcd(h_k,h_{k+1})=1 k=%d' % k, deg(g) == 0)
    alt = letters_alternate(H[k], H[k + 1])
    check('C3: h_k, h_{k+1} roots do NOT alternate k=%d' % k, alt is False, str(alt))
    cnt_nonalt += (alt is False)
print('C3 non-alternating for %d of 34 values 2<=k<=35' % cnt_nonalt)

# ---- 反向检查
# (1) 把 h_k 乘上 (1+t^2)：不再实根，核对必须 FAIL
rv1 = sum(1 for k in range(2, 40) if not is_real_simple(mul(H[k], [1, 0, 1])))
print('REVERSE h_k*(1+t^2) judged not real-rooted: %d of 38' % rv1)
check('reverse (1+t^2)', rv1 == 38)
# (2) 把 h_k 乘上 (1−2t)^2：有重根，核对必须 FAIL（「两两不同」）
rv2 = sum(1 for k in range(2, 40) if not is_real_simple(mul(H[k], [1, -4, 4])))
print('REVERSE h_k*(1-2t)^2 judged not simple: %d of 38' % rv2)
check('reverse double root', rv2 == 38)
# (3) 改坏 N：把 N(k, 峰值) 乘 2，看 h_k 是否仍实根（一般应失败）
rv3 = 0
for k in range(6, 40):
    row = [N[k][q] for q in range(k + 1)]
    qpk = row.index(max(row))
    hk = add(H[k], scal(N[k][qpk], mul([0] * (qpk - 1) + [1], powpoly(OMT, k - qpk))))
    rv3 += (not is_real_simple(hk))
print('REVERSE N(k,peak)*2 makes h_k non-real-rooted for %d of 34 k' % rv3)
# (4) 把推论里的计数改成 floor(k/3)+1：必须全部不符
rv4 = sum(1 for k in range(1, 61) if n_real_distinct_in(H[k], 1, None) != k // 3 + 1)
print('REVERSE claim #roots>1 = floor(k/3)+1 rejected for %d of 60 k' % rv4)
check('reverse count', rv4 == 60)

print('elapsed %.1fs' % (time.time() - t0))
print('TOTAL PASS=%d FAIL=%d' % (PASS, FAIL))
