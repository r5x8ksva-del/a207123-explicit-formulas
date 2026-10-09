# -*- coding: utf-8 -*-
"""探索（信息性）：复鞍点路径 t_s(ξ) 上主支 ψ 是否仍是 {ψ+2πil} 中模最小的。"""
import cmath, math, sys
sys.stdout.reconfigure(encoding='utf-8')
def g(t): return (1 - t) / (3 * (t - 1 - cmath.log(t))) - t / (1 - t)
def gp(t):
    p = t - 1 - cmath.log(t)
    return (-p + (1 - t) ** 2 / t) / (3 * p * p) - 1 / (1 - t) ** 2
lo, hi = 0.01, 0.3
for _ in range(200):
    m = (lo + hi) / 2
    if gp(complex(m, 0)).real > 0: lo = m
    else: hi = m
ts = (lo + hi) / 2; xs = g(complex(ts, 0)).real
sec = ((g(complex(ts + 1e-4, 0)) + g(complex(ts - 1e-4, 0)) - 2 * g(complex(ts, 0))) / 1e-8).real
t = None; N = 20000; worst = None; maxabs = 0
for n in range(1, N + 1):
    xi = xs + (0.6566 - xs) * (n / N) ** 2
    if t is None: t = complex(ts, math.sqrt(2 * (xi - xs) / abs(sec)))
    for _ in range(80):
        f = g(t) - xi; st = f / gp(t)
        if abs(st) > 0.3 * abs(t): st *= 0.3 * abs(t) / abs(st)
        t -= st
        if abs(f) < 1e-14: break
    p0 = t - 1 - cmath.log(t)
    best = min(range(-5, 6), key=lambda l: abs(p0 + 2j * math.pi * l))
    maxabs = max(maxabs, abs(t))
    if best != 0 and worst is None: worst = (xi, t, best)
    if n % 2000 == 0: print('xi=%.4f t_s=%s |t|=%.3f arg/pi=%.4f nearest l=%d' % (xi, '%.4f%+.4fi' % (t.real, t.imag), abs(t), cmath.phase(t) / math.pi, best))
print('max |t_s| on path (xi<=0.6566): %.3f; first point where principal is not nearest: %s' % (maxabs, worst))
