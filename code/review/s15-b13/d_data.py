# -*- coding: utf-8 -*-
"""s15-b13 / D：定理 1 的数值佐证（不是证明；不导入项目代码）。

用 (C3) 的 N 三角形（a-truth 已对照原始定义）精确算出 f_k(t)=λ²Σ_q N(k,q)(λ-1)^{q-1}（λ=1/(1-t)=p/q），
t=-1 到 k<=K_D，t=-3 到 k<=K_D2；看 b_n:=f_{3n+r}(t)/n! 的包络。

启发式（我自己推的，比 s14-b9 多一阶，只用于佐证）：由 (5.1)，ΔL_r(X)≈(1/3)x^{-r}J(x)，J(x)≈e^{-w_0(x)/X}Φ(x)
（主导方向 ν=0 上 κ'=0，见 c-kappa），Φ∝X^{-1/2}；b_n≈(2πi·n!)^{-1}∫s^{n-1}ΔL(1/s)ds 在 s≈n/w_0° 处做鞍点，得
  |b_n| 的包络 ≈ C·n^{r/3-1/2}·R^{-n}·exp(Re β·n^{2/3}+Re β'·n^{1/3})，
  β=c_0(w_0°)^{-2/3}（s14-b9 的 β），β'=(2/9)β²-(1/2)(w_0°)^{-1/3}（前一项来自鞍点移动，后一项来自 ε(x)/X≈1/(2x)）。
检查：
  d-cross    h_k(-1) 的三种算法一致：U 表（引理 1）→h_k 多项式；N 三角形直接求和；N 三角形齐次 Horner（k<=60）
  d-env      E_n:=log|b_n|+n log R-Reβ n^{2/3}-Reβ' n^{1/3}-(r/3-1/2)log n 的窗口最大值对 a+c·n 拟合：
             三个 r 的 |c|<2e-3（t=-1，n∈[100,600]；t=-3，n∈[80,400]），且残差 rms<0.1
  d-ref      同一数据上，若去掉 β' 中来自分支点的 -(1/2)(w_0°)^{-1/3}（即假设极点项主导），线性项变大（信息性）
  d-rev      把 R 换成 π、R(1.05τ)、R(0.95τ)，三个 r 的 |c| 都 >|log(R'/R)|/2
用法：py -3.14 code/review/s15-b13/d_data.py [K_D] [K_D2]
"""
import math
import sys
import time
from math import comb

from s15_common import Reporter, setup_stdout, N_rows, U_table_lemma1

setup_stdout()
K_D = int(sys.argv[1]) if len(sys.argv) > 1 else 1803
K_D2 = int(sys.argv[2]) if len(sys.argv) > 2 else 1203


def consts(tau):
    c0 = math.log(1 / tau) + 1j * math.pi
    w0 = c0 - 1 - tau
    beta = c0 * w0 ** (-2 / 3)
    beta1 = (2 / 9) * beta ** 2 - 0.5 * w0 ** (-1 / 3)
    beta1_pole = (2 / 9) * beta ** 2
    return abs(w0), beta, beta1, beta1_pole


def S_values(K, a, bshift):
    """S_k=Σ_q N(k,q)·a^{q-1}·b^{k-q}，b=2^bshift，齐次 Horner；返回 {k: S_k}（k>=1）。"""
    out = {}
    for k, row in N_rows(K):
        if k == 0:
            continue
        T = row[k]
        for q in range(k - 1, 0, -1):
            T = (row[q] << (bshift * (k - q))) + a * T
        out[k] = T
    return out


def fit_line(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    c = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    a = my - c * mx
    rms = math.sqrt(sum((y - a - c * x) ** 2 for x, y in zip(xs, ys)) / n)
    return a, c, rms


def envelope(S, p, q, Rtest, b_re, b1_re, r, n_lo, n_hi, win=10):
    xs, ys = [], []
    for lo in range(n_lo, n_hi - win + 2, win):
        best = None
        for n in range(lo, lo + win):
            k = 3 * n + r
            if S.get(k, 0) == 0:
                continue
            lb = math.log(abs(S[k])) + 2 * math.log(p) - (k + 1) * math.log(q) - math.lgamma(n + 1)
            E = lb + n * math.log(Rtest) - b_re * n ** (2 / 3) - b1_re * n ** (1 / 3) - (r / 3 - 0.5) * math.log(n)
            if best is None or E > best[0]:
                best = (E, n)
        if best:
            xs.append(float(best[1]))
            ys.append(best[0])
    return fit_line(xs, ys)


def main():
    rep = Reporter('s15_d_data')
    t0 = time.time()

    # ---- d-cross
    T = U_table_lemma1(60, 60)
    hm1_U = {}
    for k in range(1, 61):
        h = [sum(T[k][m] * (-1) ** (i - m) * comb(k + 1, i - m) for m in range(i + 1)) for i in range(k + 1)]
        hm1_U[k] = sum(c * (-1) ** i for i, c in enumerate(h))
    S1 = S_values(60, -1, 1)
    direct = {k: sum(row[qq] * (-1) ** (qq - 1) * 2 ** (k - qq) for qq in range(1, k + 1)) for k, row in N_rows(60) if k}
    okc = all(hm1_U[k] == S1[k] == direct[k] for k in range(1, 61))
    rep.check('d-cross', okc, 'h_k(-1)：U 表（引理 1）路线 = N 三角形直接求和 = N 三角形齐次 Horner（1<=k<=60）%s；例 h_3..h_8(-1)=%s'
              % (okc, [S1[k] for k in range(3, 9)]))

    # ---- 数据
    t1 = time.time()
    S_m1 = S_values(K_D, -1, 1)          # t=-1：λ=1/2，p=1，q=2，p-q=-1 → S_k=h_k(-1)，f_k=S_k/2^{k+1}
    t_m1 = time.time() - t1
    t1 = time.time()
    S_m3 = S_values(K_D2, -3, 2)         # t=-3：λ=1/4，p=1，q=4，p-q=-3
    t_m3 = time.time() - t1
    cases = [('t=-1', S_m1, 1, 2, 1.0, 100, (K_D - 3) // 3), ('t=-3', S_m3, 1, 4, 3.0, 80, (K_D2 - 3) // 3)]

    # ---- d-env
    ok_env, lines = True, []
    for name, S, p, q, tau, nlo, nhi in cases:
        R, beta, beta1, _ = consts(tau)
        for r in range(3):
            a, c, rms = envelope(S, p, q, R, beta.real, beta1.real, r, nlo, nhi)
            ok_env &= abs(c) < 2e-3 and rms < 0.1
            lines.append('%s r=%d：c=%+.1e，rms=%.3f' % (name, r, c, rms))
    rep.check('d-env', ok_env, 'E_n 的窗口最大值对 a+c·n 拟合，线性项 c 应 ≈0：' + '；'.join(lines)
              + '（N 三角形：t=-1 到 k<=%d 用 %.0f s，t=-3 到 k<=%d 用 %.0f s）' % (K_D, t_m1, K_D2, t_m3))
    for name, S, p, q, tau, nlo, nhi in cases:
        R, beta, beta1, b1p = consts(tau)
        rep.info('%s：R=%.6f，β=%.5f%+.5fi，β\'=%.5f%+.5fi（只有极点项时 β\'=%.5f%+.5fi）'
                 % (name, R, beta.real, beta.imag, beta1.real, beta1.imag, b1p.real, b1p.imag))

    # ---- d-ref（信息性）
    ref = []
    for name, S, p, q, tau, nlo, nhi in cases:
        R, beta, beta1, b1p = consts(tau)
        cs = [envelope(S, p, q, R, beta.real, b1p.real, r, nlo, nhi)[1] for r in range(3)]
        ref.append('%s：c=%s' % (name, '/'.join('%+.1e' % c for c in cs)))
    rep.info('d-ref 若 β\' 去掉 -(1/2)(w_0°)^{-1/3}（极点项主导的假设）：' + '；'.join(ref))

    # ---- d-rev
    rv, ok_rev = [], True
    for name, S, p, q, tau, nlo, nhi in cases:
        R, beta, beta1, _ = consts(tau)
        for lab, Rt in (('π', math.pi), ('R(1.05τ)', consts(1.05 * tau)[0]), ('R(0.95τ)', consts(0.95 * tau)[0])):
            gap = abs(math.log(Rt / R))
            cs = [envelope(S, p, q, Rt, beta.real, beta1.real, r, nlo, nhi)[1] for r in range(3)]
            ok_rev &= all(abs(c) > gap / 2 for c in cs)
            rv.append('%s 用 %s（|log(R\'/R)|=%.4f）：c=%s' % (name, lab, gap, '/'.join('%+.4f' % c for c in cs)))
    rep.check('d-rev', ok_rev, '反向：换成别的半径时线性项都偏离 0 超过 |log(R\'/R)|/2：' + '；'.join(rv))
    print('（总用时 %.1f s）' % (time.time() - t0))
    return rep.summary()


if __name__ == '__main__':
    sys.exit(main())
