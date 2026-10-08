# -*- coding: utf-8 -*-
"""B13 / (★) 探索：Lambert W 显式式给出的 H(w,x) 的 Taylor 系数是否还原 f_k(t)（2026-10-09）。

H(w,x) = g/(1-x+u)，u=(1-x)W_0(Z)，Z=(τ/(1-x))exp((w+τ)/(1-x))，g=1-x^2 u/(1+u)^2（notes/09 的 H，τ=-t）。
在多圆盘 |w|=ρw、|x|=ρx 上取点，二维 FFT 得 H_{n,j}，a_k=Σ_{3n+j=k} n! H_{n,j}，与精确的 f_k(t)=Σ_q N(k,q)S_q(t) 比较。
用法：py -3.14 code/tableB/explore/explore_b13_coef.py
"""
import math
from fractions import Fraction

import numpy as np


def lambertw0(z, iters=60):
    z = np.asarray(z, dtype=complex)
    w = np.where(np.abs(z) <= 3, np.log1p(z), np.log(z) - np.log(np.log(z)))
    for _ in range(iters):
        ew = np.exp(w)
        f = w * ew - z
        wp1 = w + 1
        w = w - f / (ew * wp1 - (w + 2) * f / (2 * wp1))
    return w


def H_lam(w, x, tau):
    Z = (tau / (1 - x)) * np.exp((w + tau) / (1 - x))
    W = lambertw0(Z)
    u = (1 - x) * W
    g = 1 - x * x * u / (1 + u) ** 2
    return g / (1 - x + u), W, Z


def H_sigma(w, x, tau, steps=40, newton=6):
    # 主分支：沿 s*w（s 从 0 到 1）对 psi_x(sigma)=s*w 做 Newton 延拓，再取 H=g/psi'
    sig = np.zeros_like(w, dtype=complex)
    for i in range(1, steps + 1):
        target = w * (i / steps)
        for _ in range(newton):
            e = tau * np.exp(sig)
            f = (1 - x) * sig + e - tau - target
            sig = sig - f / (1 - x + e)
    u = tau * np.exp(sig)
    g = 1 - x * x * u / (1 + u) ** 2
    return g / (1 - x + u), (1 - x) * sig + u - tau - w


def N_table(K):
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            v = N[k - 1][q - 1] + N[k - 1][q]
            s = N[k - 3][q - 2] if q >= 2 else 0
            s += 2 * N[k - 3][q - 1] + N[k - 3][q]
            N[k][q] = v + (q - 1) * s
    return N


def f_exact(k, t, N):
    t = Fraction(t)
    tot = Fraction(0)
    for q in range(0, k + 1):
        if N[k][q] == 0:
            continue
        S = 1 / (1 - t) if q == 0 else t ** (q - 1) / (1 - t) ** (q + 1)
        tot += N[k][q] * S
    return tot


def main():
    K = 24
    N = N_table(K)
    for (t, rw, rx) in [(-1, 1.0, 0.5), (Fraction(-1, 2), 0.8, 0.4), (-3, 1.0, 0.5)]:
        tau = float(-t)
        Mw, Mx = 64, 128
        ww = rw * np.exp(2j * np.pi * np.arange(Mw) / Mw)
        xx = rx * np.exp(2j * np.pi * np.arange(Mx) / Mx)
        Wg, Xg = np.meshgrid(ww, xx, indexing='ij')
        Hl, Wv, Zv = H_lam(Wg, Xg, tau)
        Hv, fres = H_sigma(Wg, Xg, tau)
        resid = np.max(np.abs(fres))
        dlam = np.max(np.abs(Hl - Hv))
        print('t=%s: |H(W_0) - H(sigma-continuation)| max %.1e (W_0 只在 arg Z 不越过 π 时是主分支)' % (t, dlam))
        C = np.fft.fft2(Hv) / (Mw * Mx)
        Hnj = C / (rw ** np.arange(Mw)[:, None]) / (rx ** np.arange(Mx)[None, :])
        # check value at w=0: W should equal tau/(1-x)
        _, W0, _ = H_lam(np.zeros(Mx), xx, tau)
        e0 = np.max(np.abs(W0 - tau / (1 - xx)))
        worst = 0.0
        rows = []
        for k in range(K + 1):
            a = 0
            for n in range(k // 3 + 1):
                j = k - 3 * n
                a += math.factorial(n) * Hnj[n, j]
            fe = float(f_exact(k, t, N))
            rel = abs(a - fe) / max(1e-300, abs(fe))
            worst = max(worst, rel)
            if k in (0, 1, 2, 3, 6, 12, 18, 24):
                rows.append('k=%d a=%.12g f=%.12g rel=%.1e' % (k, a.real, fe, rel))
        print('t=%s: Newton residual %.1e, W(0,x)-tau/(1-x) %.1e, max rel err (k<=%d) %.2e' % (t, resid, e0, K, worst))
        for r in rows:
            print('   ', r)


if __name__ == '__main__':
    main()
