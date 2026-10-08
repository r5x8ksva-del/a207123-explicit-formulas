# -*- coding: utf-8 -*-
"""复核者 s14-b9（信息性延伸）：用 r2_tau_cert.py 里「我自己的证书」把门槛 τ_i 算到 i<=IMAX（作者只到 40），
供报告 §4 讨论 τ_i 的增长。证书与精确部分的逻辑与 r2-tau-mine 完全相同（定向舍入、L 的粗上界、自己的单调条件、
压缩 DP 的精确值），所以输出的 τ_i 同样是计算机辅助证明的结果。
用法：py -3.14 r2b_tau_more.py [IMAX]（默认 100）
"""
import sys
import time
from math import log

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import r2_tau_cert as r2  # noqa: E402
from s14_common import rt_dp_U  # noqa: E402
from math import comb

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def find_K_from(P, i, K0):
    K = K0
    while True:
        tot, mono = r2.float_total(P, i, K)
        if tot < 0.9 and mono:
            break
        K += 1
    while True:
        tot, mono = r2.cert_value(P, i, K, mine=True)
        if tot < 1 and mono:
            return K, tot
        K += 1


def main(IMAX):
    t0 = time.time()
    P = r2.Params(IMAX + 1)
    Ks, K = {}, 1
    for i in range(1, IMAX + 1):
        K, tot = find_K_from(P, i, max(i, K - 5))
        Ks[i] = (K, tot)
    Kmax = max(k for k, _ in Ks.values())
    print('证书全部通过，K*_%d=%d（%.1fs）' % (IMAX, Kmax, time.time() - t0), flush=True)
    # 精确部分：逐列 U_k(m)（m<=IMAX，k<=Kmax）
    t1 = time.time()
    U = [rt_dp_U(Kmax, m) for m in range(IMAX + 1)]
    print('DP 用时 %.1fs' % (time.time() - t1), flush=True)
    taus = []
    for i in range(1, IMAX + 1):
        Ki = Ks[i][0]
        last_bad = None
        for k in range(0, Ki + 1):
            v = sum((-1) ** r * comb(k + 1, r) * U[i - r][k] for r in range(i + 1))
            if v <= 0:
                last_bad = k
        taus.append(last_bad + 1)
    ok40 = taus[:40] == r2.TAU_CLAIM
    print('前 40 个与作者所列一致：%s' % ok40)
    print('τ_1..τ_%d = %s' % (IMAX, taus))
    diffs = [taus[i] - taus[i - 1] for i in range(1, IMAX)]
    print('差 = %s' % diffs)
    for i in (10, 20, 40, 60, 80, 100):
        if i <= IMAX:
            t = taus[i - 1]
            print('i=%d：τ_i=%d，τ_i/i=%.3f，τ_i/(3i ln i)=%.4f，τ_i/(3i(ln i+ln ln i))=%.4f，K*_mine/τ_i=%.3f'
                  % (i, t, t / i, t / (3 * i * log(i)), t / (3 * i * (log(i) + log(log(i)))), Ks[i][0] / t))
    # 差在窗口里的平均（看是否缓慢增大）
    for a, b in ((1, 20), (20, 40), (40, 60), (60, 80), (80, IMAX)):
        if b <= IMAX:
            print('i∈[%d,%d]：平均差 %.3f' % (a, b, (taus[b - 1] - taus[a - 1]) / (b - a)))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 100)
