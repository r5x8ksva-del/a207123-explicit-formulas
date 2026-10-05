# -*- coding: utf-8 -*-
"""对抗性验证 consistency 审计：独立复算 #1、#4、#12、#14 涉及的数字（只用 core 的原始定义程序 + Fraction）。"""
import os, sys, time
from fractions import Fraction as F
from math import factorial, comb
from decimal import Decimal, getcontext

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_list, N_brute, N_from_U, U_fast_table  # noqa: E402

t0 = time.time()
out = []
def log(s):
    print(s, flush=True); out.append(s)

# ---------- #4：U_k(m) 作为 m 的多项式（参考实现 U_list 取值 + Lagrange/Newton 插值）
KMAX = 12
MPTS = KMAX + 3
cols = [U_list(m, KMAX) for m in range(MPTS + 1)]          # cols[m][k] = U_k(m)

def interp(ys):
    """过点 (0,ys[0]),...,(n,ys[n]) 的多项式，返回单项式系数（低次在前）。"""
    n = len(ys) - 1
    # Newton 前向差分 -> 单项式
    diffs = [F(y) for y in ys]
    coef = []
    tbl = diffs[:]
    newton = []
    for i in range(n + 1):
        newton.append(tbl[0])
        tbl = [tbl[j + 1] - tbl[j] for j in range(len(tbl) - 1)]
    poly = [F(0)] * (n + 1)
    # sum_i newton[i] * C(m, i)
    for i, a in enumerate(newton):
        if a == 0:
            continue
        # C(m,i) = m(m-1)...(m-i+1)/i!
        p = [F(1)]
        for r in range(i):
            p = [F(0)] + p
            for j in range(len(p) - 1):
                p[j] -= r * p[j + 1]
        for j in range(len(p)):
            poly[j] += a * p[j] / factorial(i)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly

log('#4  [m^{k-1}]U_k vs (k^2-2k-1)/(k-1)!；mu_k(实际) vs (k^2-2k-1)/2')
for k in range(1, KMAX + 1):
    poly = interp([cols[m][k] for m in range(MPTS + 1)])
    deg = len(poly) - 1
    lc = poly[deg]
    sub = poly[deg - 1] if deg >= 1 else F(0)
    formula_sub = F(k * k - 2 * k - 1, factorial(k - 1))
    # 真实 mu：若 U ~ lc (m+mu)^k，则 sub = lc*k*mu
    mu_true = sub / (lc * k) if deg == k else None
    mu_formula = F(k * k - 2 * k - 1, 2)
    log('   k=%2d deg=%d lc=%s (2/k!=%s)  [m^{k-1}]=%s formula=%s  mu_true=%s mu_formula=%s  %s'
        % (k, deg, lc, F(2, factorial(k)), sub, formula_sub, mu_true, mu_formula,
           'OK' if (sub == formula_sub and lc == F(2, factorial(k))) else 'DIFF'))
p3 = interp([cols[m][3] for m in range(MPTS + 1)])
log('   U_3 = %s（低次在前；*3 = %s）' % (p3, [c * 3 for c in p3]))

# N 三角：定义（DFS）与容斥
T = U_fast_table(14, 16)
def p2(k):
    return F(k**4 - 10*k**3 + 43*k**2 - 98*k + 164, 4)
log('#4  N(k,k), N(k,k-1), N(k,k-2) 对照 2, k^2-k-4, p_2(k)')
for k in range(2, 13):
    Nb = N_brute(k) if k <= 8 else None
    nk = [N_from_U(T, k, q) for q in range(k + 1)]
    if Nb is not None:
        assert all(Nb.get(q, 0) == nk[q] for q in range(k + 1)), k
    a, b, c = nk[k], nk[k - 1], nk[k - 2]
    log('   k=%2d N(k,k)=%d N(k,k-1)=%d (k^2-k-4=%d) N(k,k-2)=%d (p_2(k)=%s)%s'
        % (k, a, b, k*k-k-4, c, p2(k), '  [DFS 定义一致]' if Nb is not None else ''))

# ---------- #12：rho_1 与 theta_1 = rho_0/rho_1（日志值 0.682327804）
getcontext().prec = 50
def rho(m):
    lo, hi = Decimal(1), Decimal(3)
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid**3 - mid**2 - m > 0:
            hi = mid
        else:
            lo = mid
    return lo
r1 = rho(1)
log('#12 rho_1=%s  1/rho_1=%s（verify_all c5a-asym-m1 打印 theta=0.682327804，故 rho_0 取 1）' % (str(r1)[:14], str(1 / r1)[:14]))
log('    m=0：y^3=y^2 的实根为 0（二重）与 1，「y^3=y^2+m 的实根」在 m=0 不唯一')
r2 = rho(2)
tau2 = (r2 * (r2 - 1)).sqrt()
log('    tau_2 = max(rho_0, sqrt(rho_2(rho_2-1))) = max(1, %s)' % str(tau2)[:10])
tau1 = (r1 * (r1 - 1)).sqrt()
log('    tau_1 = sqrt(rho_1(rho_1-1)) = %s（报告 τ_1≈0.826；max 式在 m=1 需要 rho_{-1}）' % str(tau1)[:10])

# ---------- #14：R_k = U_k(1) = c_1(k+3) + c_1(k-2) - 1，c_1(n)=[x^n]1/(1-x-x^3)
K = 60
c1 = [0] * (K + 10)
for n in range(K + 10):
    c1[n] = (1 if n == 0 else 0) + (c1[n - 1] if n >= 1 else 0) + (c1[n - 3] if n >= 3 else 0)
U1 = U_list(1, K)
ok14 = all(U1[k] == c1[k + 3] + (c1[k - 2] if k >= 2 else 0) - 1 for k in range(K + 1))
log('#14 R_k=U_k(1)=c_1(k+3)+c_1(k-2)-1（c_1(n<0)=0），0<=k<=%d：%s；R_0..R_6=%s' % (K, ok14, U1[:7]))

# ---------- #1：基点 2d+1 的第 0 个 Newton 系数 p_d(2d+1)=D(2d+1,d)-(-1)^{d+1}(d+1)!（T4.1 已证明的缺陷）
DM = 101
KK = 2 * DM + 2
N = [[0] * (KK + 2) for _ in range(KK + 1)]
N[0][0] = 1; N[1][1] = 1; N[2][1] = 1; N[2][2] = 2
def g(k, q):
    return N[k][q] if (0 <= k <= KK and 0 <= q <= k) else 0
for k in range(3, KK + 1):
    for q in range(1, k + 1):
        N[k][q] = g(k-1, q-1) + g(k-1, q) + (q-1) * (g(k-3, q-2) + 2*g(k-3, q-1) + g(k-3, q))
# 锚定：三角递推 == 容斥（k<=14）
assert all(N[k][q] == N_from_U(T, k, q) for k in range(15) for q in range(k + 1))
neg = [d for d in range(1, DM + 1) if N[2*d+1][d+1] - (-1)**(d+1) * factorial(d+1) <= 0]
log('#1  p_d(2d+1)<=0 的 d（1<=d<=%d）：%s' % (DM, neg))
log('    其中偶数 d：%s（偶数 d 时 p_d(2d+1)=D(2d+1,d)+(d+1)!>0）' % [d for d in neg if d % 2 == 0])
log('elapsed %.1fs' % (time.time() - t0))

with open(os.path.join(ROOT, 'logs', 'final_audit_verify_consistency.log'), 'a', encoding='utf-8') as f:
    f.write('\n===== v2_numbers.py =====\n' + '\n'.join(out) + '\n')
