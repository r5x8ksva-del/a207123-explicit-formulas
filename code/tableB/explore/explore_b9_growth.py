# -*- coding: utf-8 -*-
"""探索（2026-10-09）：B9 的门槛 τ_i 的增长规律。启发式模型（notes/18 §2）：
  (1/k) ln|h_k(t)| − (1/3) ln(k/(3e)) → Φ(t) := ln|1−t| − (1/3) ln|ψ(t)|，ψ(t)=t−1−Log t（主支），
于是系数 h_{k,ξk} 在 ξ<ξ* 时为正、ξ>ξ* 时振荡，ξ* = max_{0<t<1} g(t)，g(t)=tΦ'(t)=(1−t)/(3ψ(t)) − t/(1−t)，
τ_i ~ i/ξ*，ℓ_k（第一个非正系数的位置）~ ξ* k。本脚本用精确整数检验这些预测。

用法（在任务 C 根目录）：
  py -3.14 code/tableB/explore/explore_b9_growth.py theory
  py -3.14 code/tableB/explore/explore_b9_growth.py scan K I [out.json]   # 截断递推到 k<=K、i<=I，记录 ℓ_k 与经验门槛
  py -3.14 code/tableB/explore/explore_b9_growth.py roots k1,k2,...       # 完整 h_k，用 Möbius 变换加 Descartes 精确数区间里的根
  py -3.14 code/tableB/explore/explore_b9_growth.py signs k1,k2,... frac   # 0<=i<=frac*k 中的系数变号数，对照复鞍点的预测
h_k 用 T1.7 的递推：h_k = h_{k−1} + t(1−t)[(1−t)h'_{k−3} + (k−2)h_{k−3}]，h_0=h_1=1，h_2=1+t（与 check_b9.py 相同）。
"""
import json
import math
import sys
import time
from fractions import Fraction as Fr

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


# ------------------------------------------------------------------ 理论量
def psi(t):
    return t - 1 - math.log(t)


def g(t):
    return (1 - t) / (3 * psi(t)) - t / (1 - t)


def g_prime(t):
    p = psi(t)
    return (-p - (1 - t) * (1 - 1 / t)) / (3 * p * p) - 1 / (1 - t) ** 2


def argmax_g():
    lo, hi = 0.01, 0.3            # g 在 (0,1) 上单峰（见 theory 的输出），g' 在这里由正变负
    for _ in range(200):
        m = (lo + hi) / 2
        if g_prime(m) > 0:
            lo = m
        else:
            hi = m
    t = (lo + hi) / 2
    return t, g(t)


def saddle_small(xi):
    """g(s)=xi 在 (0, t*) 中的根（xi<ξ*）。"""
    ts, _ = argmax_g()
    lo, hi = 1e-300, ts
    for _ in range(300):
        m = (lo + hi) / 2
        if g(m) < xi:
            lo = m
        else:
            hi = m
    return (lo + hi) / 2


def Phi_real(t):
    return math.log(abs(1 - t)) - math.log(abs(psi(t))) / 3


def neg_root_cdf(tau):
    """模型预测：(−τ,0) 中的根数 / k。"""
    v = tau + 1 + math.log(tau)
    return (math.atan(v / math.pi) + math.pi / 2) / (3 * math.pi)


def theory():
    ts, xs = argmax_g()
    print('t* = %.12f, xi* = g(t*) = %.12f, alpha* = 1/xi* = %.10f' % (ts, xs, 1 / xs))
    for t in [0.001, 0.01, 0.03, 0.05, 0.07, 0.076, 0.08, 0.1, 0.15, 0.2, 0.3, 0.5, 0.7, 0.9]:
        print('  g(%.3f) = %+.6f' % (t, g(t)))
    print('negative-root CDF F(tau) = #roots in (-tau,0)/k:')
    for tau in [0.1, 0.5, 1, 2, 5, 10, 100]:
        print('  F(%g) = %.6f' % (tau, neg_root_cdf(tau)))
    print('  F(inf) = 1/3; positive roots: point mass 1/3 at t=1; degree 2/3')
    w0 = complex(-2, math.pi)
    print('arg(w0)/(3 pi) = %.6f  (= F(1) = %.6f)' % (math.atan2(w0.imag, w0.real) / (3 * math.pi), neg_root_cdf(1)))
    # 二阶项 β(t)=ln(1/t)/ψ(t)^{2/3} 在 t* 处的 tβ'(t)
    beta = lambda t: math.log(1 / t) / psi(t) ** (2 / 3)
    h = 1e-6
    print("t*·beta'(t*) = %.5f  (beta(t*) = %.5f)" % (ts * (beta(ts + h) - beta(ts - h)) / (2 * h), beta(ts)))
    # 复鞍点路径：局部变号频率、回到实轴的位置、恒等式 ∫arg t_s dξ/π
    import cmath
    path = saddle_complex_path(2 / 3 - 1e-6, N=40000)
    for target in (0.13, 0.155, 0.2, 0.3, 0.38, 0.5, 0.6, 0.65):
        xi, t = min(path, key=lambda p: abs(p[0] - target))
        print('  xi=%.4f  t_s=%s  arg/pi=%.4f' % (xi, t, cmath.phase(t) / math.pi))
    back = next(((xi, t) for xi, t in path if xi > 0.5 and abs(t.imag) < 1e-9 * abs(t)), None)
    print('path returns to the real axis at xi_2 ~ %s, t_2 ~ %s' % (back[0] if back else None, back[1] if back else None))
    integ = 0.0
    prev = (xs, 0.0)
    for xi, t in path:
        a = max(0.0, cmath.phase(t))
        integ += (xi - prev[0]) * (a + prev[1]) / 2
        prev = (xi, a)
    print('identity: integral of arg(t_s)/pi over (xi*, 2/3) = %.6f (= mass of positive roots 1/3; checks the continuation only)'
          % (integ / math.pi))


# ------------------------------------------------------------------ h_k 的递推
def mpow_log(x):
    """大整数的自然对数。"""
    if x <= 0:
        return None
    b = x.bit_length()
    if b < 1000:
        return math.log(x)
    s = b - 900
    return math.log(x >> s) + s * math.log(2)


def scan(K, I, out=None):
    print('scan K=%d I=%d' % (K, I))
    ts, xs = argmax_g()
    rec_req = {}
    for k in [K // 8, K // 4, K // 2, K]:
        rec_req[k] = sorted(set(int(f * k) for f in [0.02, 0.04, 0.06, 0.08, 0.09, 0.10]))
    rows = {0: [1] + [0] * I, 1: [1] + [0] * I, 2: [1, 1] + [0] * (I - 1)}
    ell = {}
    last_bad = [-1] * (I + 1)
    rec = {}
    t0 = time.time()
    for k in range(K + 1):
        if k >= 3:
            gk = rows[k - 3]
            hk1 = rows[k - 1]
            A = [(m + 1) * gk[m + 1] + (k - 2 - m) * gk[m] for m in range(I)]
            h = [hk1[0], hk1[1] + A[0]] + [hk1[n] + A[n - 1] - A[n - 2] for n in range(2, I + 1)]
            rows[k] = h
            del rows[k - 3]
        h = rows[k]
        first = None
        for i in range(I + 1):
            if h[i] <= 0:
                last_bad[i] = k
                if first is None:
                    first = i
        ell[k] = first
        if k in rec_req:
            rec[k] = {i: mpow_log(h[i]) for i in rec_req[k] if i <= I}
        if k % 500 == 0 and k:
            print('  k=%d  ell=%s  (xi* k = %.1f)  %.1fs' % (k, first, xs * k, time.time() - t0), flush=True)
    tau_emp = [lb + 1 for lb in last_bad]
    res = {'K': K, 'I': I, 'xi_star': xs, 't_star': ts,
           'ell': {k: ell[k] for k in range(K + 1)}, 'tau_emp': tau_emp,
           'lnh': {k: {i: v for i, v in d.items()} for k, d in rec.items()}}
    if out:
        with open(out, 'w', encoding='utf-8') as f:
            json.dump(res, f)
    # 摘要
    print('ell_k vs xi* k:')
    for k in sorted(set([100, 300, 600, 1000, 2000, 3000, 5000, 7000, 10000, K])):
        if k <= K and ell.get(k) is not None:
            print('  k=%6d ell=%5d  ell/k=%.5f  ell - xi*k = %+.2f' % (k, ell[k], ell[k] / k, ell[k] - xs * k))
    print('tau_emp (only k<=K checked; reliable roughly when tau_i << K):')
    for i in [10, 20, 40, 60, 80, 100, 150, 200, 300, 400, 500, 600, 800, 1000]:
        if i <= I and tau_emp[i] < K // 2:
            print('  i=%5d tau=%6d tau/i=%.4f  tau - alpha* i = %+.1f' % (i, tau_emp[i], tau_emp[i] / i, tau_emp[i] - i / xs))
    print('coefficient growth: (1/k)[ln h_{k,i} - (k/3) ln(k/3e)] vs model ln(1-s) - (1/3)ln psi(s) - xi ln s:')
    for k in sorted(rec):
        for i, v in sorted(rec[k].items()):
            xi = i / k
            if v is None or xi >= xs or i == 0:
                continue
            s = saddle_small(xi)
            model = math.log(1 - s) - math.log(psi(s)) / 3 - xi * math.log(s)
            emp = (v - (k / 3) * math.log(k / (3 * math.e))) / k
            print('  k=%6d i=%5d xi=%.3f  emp=%.5f  model=%.5f  diff=%+.5f' % (k, i, xi, emp, model, emp - model))
    print('elapsed %.1fs' % (time.time() - t0))


# ------------------------------------------------------------------ 根的区间计数（精确）
def h_full(K):
    rows = {0: [1], 1: [1], 2: [1, 1]}
    for k in range(3, K + 1):
        gk = rows[k - 3]
        hk1 = rows[k - 1]
        d = len(gk)
        A = [(m + 1) * (gk[m + 1] if m + 1 < d else 0) + (k - 2 - m) * gk[m] for m in range(d)]
        n_out = max(len(hk1), d + 2)
        h = [0] * n_out
        for n in range(n_out):
            v = hk1[n] if n < len(hk1) else 0
            if 1 <= n <= d:
                v += A[n - 1]
            if 2 <= n <= d + 1:
                v -= A[n - 2]
            h[n] = v
        while len(h) > 1 and h[-1] == 0:
            h.pop()
        rows[k] = h
        del rows[k - 3]
        yield k, h


def taylor_shift(c, p):
    """c(x+p) 的系数（c[i] 为 x^i 的系数，p 为整数），经典 O(n^2) 原地算法。"""
    c = list(c)
    n = len(c)
    for i in range(n):
        for j in range(n - 2, i - 1, -1):
            c[j] += p * c[j + 1]
    return c


def count_roots(h, a, b):
    """h 实根（已证明，A19）时，(a,b) 中的根数 = P(x)=(1+x)^d h((a+bx)/(1+x)) 的系数变号数（Descartes 对实根多项式精确）。
    做法：h(a+(b-a)x)（平移加正的缩放）→ 反转 → 平移 1。a<b 为 Fraction，全程整数运算。"""
    d = len(h) - 1
    an, ad = a.numerator, a.denominator
    bn, bd = b.numerator, b.denominator
    ht = [h[i] * ad ** (d - i) for i in range(d + 1)]      # ad^d h(w/ad)
    G = taylor_shift(ht, an)                                # ad^d h(a + z/ad)
    e = ad * bn - an * bd                                   # ad(b-a) = e/bd，e>0
    assert e > 0
    Q = [G[j] * e ** j * bd ** (d - j) for j in range(d + 1)]   # ∝ h(a+(b-a)x)
    R = Q[::-1]
    S = taylor_shift(R, 1)
    signs = [1 if c > 0 else -1 for c in S if c != 0]
    return sum(1 for u, v in zip(signs, signs[1:]) if u != v)


def roots(ks):
    ks = sorted(ks)
    want = set(ks)
    for k, h in h_full(max(ks)):
        if k not in want:
            continue
        d = len(h) - 1
        npos = count_roots(h, Fr(1), Fr(10 ** 9))
        print('k=%d deg=%d (2k/3=%.1f)  roots in (1,1e9): %d (floor(k/3)=%d)' % (k, d, 2 * k / 3, npos, k // 3), flush=True)
        for delta in [Fr(1, 2), Fr(1, 5), Fr(1, 10), Fr(1, 20)]:
            c = count_roots(h, Fr(1), 1 + delta)
            print('   roots in (1, %s): %d  (fraction of positive roots %.3f)' % (float(1 + delta), c, c / max(1, npos)), flush=True)
        for tau in [Fr(1, 10), Fr(1, 2), Fr(1), Fr(2), Fr(5), Fr(10)]:
            c = count_roots(h, -tau, Fr(0))
            print('   roots in (-%s,0): %d   model k*F = %.1f' % (float(tau), c, k * neg_root_cdf(float(tau))), flush=True)


def saddle_complex_path(xi_max, N=20000):
    """ξ∈(ξ*,xi_max] 上的复鞍点 t_s(ξ)（上半平面，从汇合点 t* 延拓），返回 [(ξ, t_s)]。"""
    import cmath

    def G(t):
        return (1 - t) / (3 * (t - 1 - cmath.log(t))) - t / (1 - t)

    def dG(t):
        p = t - 1 - cmath.log(t)
        return (-p - (1 - t) * (1 - 1 / t)) / (3 * p * p) - 1 / (1 - t) ** 2

    ts, xs = argmax_g()
    G2 = ((G(ts + 1e-4) + G(ts - 1e-4) - 2 * G(ts)) / 1e-8).real
    out, t = [], None
    for n in range(1, N + 1):
        xi = xs + (xi_max - xs) * (n / N) ** 2
        if t is None:
            t = ts + 1j * math.sqrt(2 * (xi - xs) / abs(G2))
        for _ in range(60):
            f = G(t) - xi
            st = f / dG(t)
            if abs(st) > 0.5 * abs(t):
                st *= 0.5 * abs(t) / abs(st)
            t = t - st
            if abs(f) < 1e-13:
                break
        if t.imag < 0:
            t = t.conjugate()
        out.append((xi, t))
    return out


def signs(Ks, frac):
    """h_k（k∈Ks）在 0<=i<=frac*k 中的系数变号数，与模型 k∫_{ξ*}^{frac} arg t_s(ξ)/π dξ 对照（frac<2/3）。"""
    import cmath
    Kmax = max(Ks)
    I = int(frac * Kmax) + 2
    ts, xs = argmax_g()
    path = saddle_complex_path(frac)
    integ = (path[0][0] - xs) * cmath.phase(path[0][1]) / math.pi / 2
    for (x0, t0), (x1, t1) in zip(path, path[1:]):
        integ += (x1 - x0) * (cmath.phase(t0) + cmath.phase(t1)) / (2 * math.pi)
    rows = {0: [1] + [0] * I, 1: [1] + [0] * I, 2: [1, 1] + [0] * (I - 1)}
    want = set(Ks)
    for k in range(3, Kmax + 1):
        gk, hk1 = rows[k - 3], rows[k - 1]
        A = [(m + 1) * gk[m + 1] + (k - 2 - m) * gk[m] for m in range(I)]
        rows[k] = [hk1[0], hk1[1] + A[0]] + [hk1[n] + A[n - 1] - A[n - 2] for n in range(2, I + 1)]
        del rows[k - 3]
        if k in want:
            top = int(frac * k)
            sg = [1 if c > 0 else -1 for c in rows[k][:top + 1] if c != 0]
            ch = sum(1 for u, v in zip(sg, sg[1:]) if u != v)
            zeros = sum(1 for c in rows[k][:top + 1] if c == 0)
            print('k=%d: sign changes in 0<=i<=%d (=%.2fk): %d ; model k*integral = %.1f ; zero coefficients %d'
                  % (k, top, frac, ch, k * integ, zeros), flush=True)


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'theory':
        theory()
    elif mode == 'scan':
        scan(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)
    elif mode == 'roots':
        roots([int(x) for x in sys.argv[2].split(',')])
    elif mode == 'signs':
        signs([int(x) for x in sys.argv[2].split(',')], float(sys.argv[3]))
