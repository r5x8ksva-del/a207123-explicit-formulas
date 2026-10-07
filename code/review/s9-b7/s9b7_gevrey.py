# -*- coding: utf-8 -*-
"""s9-b7 独立核对 G1-G3：f_k(t) 在 t<0（含 |t|>=1）的 Gevrey-1/3 增长（推论的佐证）与 notes/07 的数值。

不导入项目里的任何模块。f_k(t)=h_k(t)/(1-t)^{k+1} 精确（h_k 多项式递推，见 s9b7_formal.py 的 F1 核对），
用整数的 bit 长度取对数，避免浮点溢出。

G1  notes/07 §3 与 notes/09 §5 引用的 |f_k(-1/2)|^{1/k}（k=75、150、300：1.6688、2.0355、2.4874）
G2  t=-1/2,-1,-2,-3,-5,-10,-100：q_k(t) := (|f_k(t)|/Gamma(1+k/3))^{1/k} 在 k=60..900 有界（推论 4 的佐证），
    并与 |w_0|^{-1/3} 比较，w_0 = ln(1/tau)-1-tau+i*pi 是 notes/09 §5 说的 H(w,0) 最近奇点（信息性：
    若 Borel 平面的最近奇点在 zeta^3=w_0，则 q_k -> |w_0|^{-1/3}，收敛慢）
G3  推论的常数：对每个 t，sup_{k<=900} |f_k|/(Gamma(1+k/3) A^k) 有限（取 A = 1.2*max_k q_k）——只是有限范围内的数，不是证明
"""
import math
import sys
import time
from fractions import Fraction as Fr

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def h_polys(K):
    h = [[1], [1], [1, 1]]
    for k in range(3, K + 1):
        q = h[k - 3]
        der = [i * q[i] for i in range(1, len(q))] or [0]
        d = padd(padd(der, [0] + [-c for c in der]), [(k - 2) * c for c in q])
        h.append(padd(h[k - 1], padd([0] + d, [0, 0] + [-c for c in d])))
    return h


def log_abs_fk(cs, k, t):
    """ln|f_k(t)|（f_k=0 时为 -inf），cs 为 h_k 的系数，t=p/q。"""
    p, q = t.numerator, t.denominator
    d = len(cs) - 1
    # v = sum c_i p^i q^{d-i}（齐次 Horner：acc = acc*p + c_i*q^{d-i}，q 的幂逐步累乘）
    v = cs[d]
    Q = 1
    for i in range(d - 1, -1, -1):
        Q *= q
        v = v * p + cs[i] * Q
    num = abs(v) * q ** (k + 1 - d)
    den = abs(q - p) ** (k + 1)
    return math.log(num) - math.log(den) if num else -math.inf


T_LIST = (Fr(-1, 2), Fr(-1), Fr(-2), Fr(-3), Fr(-5), Fr(-10), Fr(-100))


def all_logs(K):
    """边算 h_k 边求值，只保留最近三个多项式（省内存）。返回 {t: [ln|f_k(t)|, k<=K]}，以及 deg h_K。"""
    out = {t: [] for t in T_LIST}
    h = [[1], [1], [1, 1]]
    for k in range(K + 1):
        if k >= 3:
            q = h[0]
            der = [i * q[i] for i in range(1, len(q))] or [0]
            d = padd(padd(der, [0] + [-c for c in der]), [(k - 2) * c for c in q])
            new = padd(h[2], padd([0] + d, [0, 0] + [-c for c in d]))
            h = [h[1], h[2], new]
            cs = new
        else:
            cs = h[k]
        for t in T_LIST:
            out[t].append(log_abs_fk(cs, k, t))
    return out, len(cs) - 1


def main():
    t0 = time.time()
    K = 900
    LOGS, degK = all_logs(K)
    print('h_k 与 ln|f_k| 计算完毕 k<=%d，用时 %.1fs，deg h_%d=%d' % (K, time.time() - t0, K, degK), flush=True)

    # G1
    lf = LOGS[Fr(-1, 2)]
    vals = [math.exp(lf[k] / k) for k in (75, 150, 300)]
    ok = all(abs(v - w) < 6e-5 for v, w in zip(vals, (1.6688, 2.0355, 2.4874)))
    report('G1', ok, '|f_k(-1/2)|^{1/k}（k=75,150,300）= %.5f, %.5f, %.5f（notes/07 §3：1.6688, 2.0355, 2.4874）' % tuple(vals))

    # G2, G3
    ok2 = True
    ok3 = True
    info2 = []
    info3 = []
    for t in T_LIST:
        tau = float(-t)
        lf = LOGS[t]
        q = {}
        for k in range(30, K + 1):
            if lf[k] > -math.inf:
                q[k] = math.exp((lf[k] - math.lgamma(1 + k / 3)) / k)
        ks = (60, 120, 240, 480, 900)
        qs = [q[k] for k in ks]
        w0 = complex(math.log(1 / tau) - 1 - tau, math.pi)
        pred = abs(w0) ** (-1 / 3)
        qmax = max(q.values())
        ok2 = ok2 and qmax < 10 and qs[-1] < 1.5 * qs[0] + 0.5
        info2.append('t=%s: q_k=%s（k=%s），|w_0|^{-1/3}=%.4f，零值个数 %d'
                     % (t, ', '.join('%.4f' % v for v in qs), '/'.join(map(str, ks)), pred, sum(1 for k in range(K + 1) if lf[k] == -math.inf)))
        A = 1.2 * qmax
        C = max(math.exp(lf[k] - math.lgamma(1 + k / 3) - k * math.log(A)) for k in range(K + 1) if lf[k] > -math.inf)
        ok3 = ok3 and math.isfinite(C)
        info3.append('t=%s: A=%.3f, C=%.3g' % (t, A, C))
    report('G2', ok2, '(|f_k|/Gamma(1+k/3))^{1/k} 有界：' + '; '.join(info2))
    report('G3', ok3, '有限范围 k<=900 内 |f_k|<=C·A^k·Gamma(1+k/3) 的常数：' + '; '.join(info3))
    print('time %.1fs' % (time.time() - t0))
    n = sum(RES)
    print('SUMMARY s9b7_gevrey pass=%d fail=%d' % (n, len(RES) - n))
    return 0 if n == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
