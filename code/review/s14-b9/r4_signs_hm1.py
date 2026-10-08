# -*- coding: utf-8 -*-
"""复核者 s14-b9：§4 的符号事实、命题 4、h_k(-1) 的变号与 Borel 平面奇点的数值估计（不 import 项目代码）。

  r4-hdp     自写 T1.7 递推 = 由定义（压缩 DP）反演的 h_k（k<=150；r3 已核到 300）
  r4-signs   k<=1000：没有零系数；变号次数 = floor(k/3)；初始正段长 ℓ_k >= 1+#{i<=40: τ_i<=k}、ℓ_k <= d+1-floor(k/3)；
             ℓ_300、ℓ_600、ℓ_1000 的值
  r4-p4i     命题 4(i)：N(k,q)（由 U 的容斥 N(k,q)=sum_l (-1)^{q-l}C(q,l)U_k(l-1)）给出 h_k(-1)=sum_q (-1)^{q-1}2^{k-q}N(k,q)
             （1<=k<=100）；乘积式 h_k(-1)=2(-1)^r∏(1+2z_l) 等价于 h_k(1)=2，所以对 k>=2 成立、k=1 时不成立（h_1(-1)=1，式子给 2）
  r4-p4ii    命题 4(ii)：h_k 在 (-1,0) 中的根数用 Möbius 变换 t=-u/(1+u) 后的 Descartes 符号法则精确计数（实根多项式时精确），
             sgn h_k(-1) = (-1)^{根数}（3<=k<=240）；h_2(-1)=0，3<=k<=1000 时 h_k(-1)!=0
  r4-osc     h_k(-1) 在 3<=k<=1000 的变号次数（作者 223）与 3<=k<=500 的次数；按 w_0=-2+iπ 的相位预测
  r4-borel   （数值佐证，不是证明）s_n := h_{3n+r}(-1)/(2^{3n+r+1} n!) 的两项递推拟合 s_{n+2}=p s_{n+1}-q s_n，
             由 λ^2-pλ+q=0 得 Borel 平面最近奇点 w=1/λ 的估计（按 n^{-1/3} 外推），与 -2±iπ（及另一候选 ±iπ）比较
  r4-drift   （数值佐证）原始估计的漂移与变号次数，用 notes/09 的移动奇点 w_0(x)=w_0-iπx+… 定量预测并比较
"""
import sys
import time
import cmath
from decimal import Decimal as D, getcontext
from math import comb, lgamma, log, pi, atan2

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import rt_dp_U, h_poly_from_Ucol, h_rec_iter, sign_changes  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []
TAU = [2, 8, 16, 24, 33, 41, 50, 59, 68, 77, 86, 95, 105, 114, 123, 132, 141, 151, 160, 169,
       178, 188, 197, 206, 216, 225, 234, 244, 253, 263, 272, 281, 291, 300, 310, 319, 328, 338, 347, 357]


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def lsq_extrap(pts):
    """对 (n, w) 用 w ≈ w∞ + A n^{-1/3} + B n^{-2/3} 做最小二乘（实部、虚部分开），返回 w∞。"""
    rows = [(1.0, n ** (-1 / 3), n ** (-2 / 3)) for n, _ in pts]
    M = [[sum(r[a] * r[b] for r in rows) for b in range(3)] for a in range(3)]
    res = []
    for part in (lambda z: z.real, lambda z: z.imag):
        v = [sum(r[a] * part(w) for r, (_, w) in zip(rows, pts)) for a in range(3)]
        A = [M[i][:] + [v[i]] for i in range(3)]
        for c in range(3):
            piv = max(range(c, 3), key=lambda i: abs(A[i][c]))
            A[c], A[piv] = A[piv], A[c]
            for i in range(3):
                if i != c:
                    f = A[i][c] / A[c][c]
                    A[i] = [x - f * y for x, y in zip(A[i], A[c])]
        res.append(A[0][3] / A[0][0])
    return complex(res[0], res[1])


def main():
    t0 = time.time()
    KD = 150
    Ucols = [rt_dp_U(KD, m) for m in range(KD + 1)]          # m<=150 足够 N(k,q)（m<=k-1）与 h（m<=d）
    hdp = {k: h_poly_from_Ucol([Ucols[m][k] for m in range(2 * k // 3 + 1)], k) for k in range(0, KD + 1)}
    H = {}            # 只保留 k<=240 的完整 h_k（省内存）；其余逐个处理
    ok = True
    ok_z, ok_chg, ok_run, ok_up = True, True, True, True
    ell = {}
    hm1 = []
    hsum = []
    for k, h in h_rec_iter(1000):
        if k <= 240:
            H[k] = h
        if k <= KD and h != hdp[k]:
            ok = False
        hm1.append(sum(x if i % 2 == 0 else -x for i, x in enumerate(h)))
        hsum.append(sum(h))
        d = len(h) - 1
        if any(x == 0 for x in h):
            ok_z = False
        if sign_changes(h) != k // 3:
            ok_chg = False
        run = 0
        while run < len(h) and h[run] > 0:
            run += 1
        ell[k] = run
        if k >= 2 and run < 1 + sum(1 for t in TAU if t <= k):
            ok_run = False
        if run <= d and run > d + 1 - k // 3:
            ok_up = False
    report('r4-hdp', ok, '自写 T1.7 递推 = DP 反演（k<=%d）%s（%.1fs）' % (KD, ok, time.time() - t0))
    report('r4-signs', ok_z and ok_chg and ok_run and ok_up,
           'k<=1000：没有零系数 %s；变号次数=floor(k/3) %s；ℓ_k>=1+#{τ_i<=k} %s；ℓ_k<=d+1-floor(k/3) %s；ℓ_300=%d、ℓ_600=%d、ℓ_1000=%d'
           % (ok_z, ok_chg, ok_run, ok_up, ell[300], ell[600], ell[1000]))


    # ---- r4-p4i
    ok_N, ok_sum = True, True
    for k in range(1, 101):
        N = [0] * (k + 1)
        for q in range(1, k + 1):
            N[q] = sum((-1) ** (q - l) * comb(q, l) * Ucols[l - 1][k] for l in range(1, q + 1))
        if N[1] != 1 or (k >= 2 and N[k] != 2) or any(N[q] <= 0 for q in range(1, k + 1)):
            ok_N = False
        if hm1[k] != sum((-1) ** (q - 1) * 2 ** (k - q) * N[q] for q in range(1, k + 1)):
            ok_sum = False
    ok_h1 = all(hsum[k] == 2 for k in range(2, 1001)) and hsum[1] == 1 and hm1[1] == 1
    report('r4-p4i', ok_N and ok_sum and ok_h1,
           'N(k,q) 的容斥值合理（N(k,1)=1、N(k,k)=2、全正）%s；h_k(-1)=sum_q (-1)^{q-1}2^{k-q}N(k,q)（1<=k<=100）%s；'
           'h_k(1)=2（2<=k<=1000）而 h_1(1)=1、h_1(-1)=1 %s ⇒ 乘积式只对 k>=2 成立（k=1 时右边是 2）'
           % (ok_N, ok_sum, ok_h1))

    # ---- r4-p4ii
    t1 = time.time()
    ok_sg = True
    counts = {}
    for k in range(3, 241):
        h = H[k]
        d = len(h) - 1
        Q = [0] * (d + 1)
        for i, x in enumerate(h):
            c = x * (-1) ** i
            for e in range(d - i + 1):
                Q[i + e] += c * comb(d - i, e)
        nroot = sign_changes(Q)
        counts[k] = nroot
        if hm1[k] == 0 or (hm1[k] > 0) != (nroot % 2 == 0):
            ok_sg = False
    ok_nz = hm1[2] == 0 and all(hm1[k] != 0 for k in range(3, 1001))
    report('r4-p4ii', ok_sg and ok_nz,
           'sgn h_k(-1)=(-1)^{(-1,0) 中的根数}（3<=k<=240，根数由 Möbius+Descartes 精确计数，例 k=60:%d、k=240:%d）%s；'
           'h_2(-1)=0 且 3<=k<=1000 时 h_k(-1)!=0 %s（%.1fs）' % (counts[60], counts[240], ok_sg, ok_nz, time.time() - t1))

    # ---- r4-osc
    def chg(K):
        return sum(1 for k in range(4, K + 1) if (hm1[k] > 0) != (hm1[k - 1] > 0))
    c1000, c500 = chg(1000), chg(500)
    ph = atan2(pi, -2) / 3
    pred1000, pred500 = 997 * ph / pi, 497 * ph / pi
    report('r4-osc', c1000 == 223, 'h_k(-1) 变号次数：3<=k<=1000 为 %d（作者 223），3<=k<=500 为 %d；按 arg(w_0)/3 每步的相位预测分别为 %.1f、%.1f；'
           '若奇点在 ±iπ 则为 %.1f、%.1f' % (c1000, c500, pred1000, pred500, 997 / 6, 497 / 6))

    # ---- r4-borel（数值）
    getcontext().prec = 50
    out = []
    est = {}
    rawall = {}
    for r in range(3):
        s = []
        n = 0
        fact = 1
        while 3 * n + r <= 1000:
            k = 3 * n + r
            if n >= 2:
                fact *= n
            s.append(D(hm1[k]) / (D(2) ** (k + 1) * D(fact)))
            n += 1
        ws = []
        for N0 in range(40, len(s) - 4):
            a0, a1, a2, a3 = s[N0], s[N0 + 1], s[N0 + 2], s[N0 + 3]
            # a2 = p a1 - q a0；a3 = p a2 - q a1（Cramer）
            det = a0 * a2 - a1 * a1
            p = float((a0 * a3 - a1 * a2) / det)
            q = float((a1 * a3 - a2 * a2) / det)
            lam = (p + cmath.sqrt(complex(p * p - 4 * q))) / 2
            w = 1 / lam
            ws.append((N0, w if w.imag >= 0 else w.conjugate()))
        raw = dict(ws)
        rawall[r] = raw
        out.append('r=%d 原始估计 n=100:%.3f%+.3fi，n=200:%.3f%+.3fi，n=%d:%.3f%+.3fi'
                   % (r, raw[100].real, raw[100].imag, raw[200].real, raw[200].imag, ws[-1][0], ws[-1][1].real, ws[-1][1].imag))
        # 原始估计按 n^{-1/3} 漂移（系数里有 exp(c n^{2/3}) 型的次指数因子），用 {1, n^{-1/3}, n^{-2/3}} 最小二乘外推
        for lo in (60, 120):
            pts = [(n_, w_) for (n_, w_) in ws if n_ >= lo]
            winf = lsq_extrap(pts)
            est[(r, lo)] = winf
            out.append('r=%d 外推（n>=%d）w∞=%.4f%+.4fi（|w|=%.4f，arg=%.4f）' % (r, lo, winf.real, winf.imag, abs(winf), cmath.phase(winf)))
    target = complex(-2, pi)
    ok_b = all(abs(w - target) < 0.03 and abs(w - complex(0, pi)) > 1 for w in est.values())
    report('r4-borel', ok_b, '（数值佐证）Borel 平面最近奇点的估计：%s；目标 w_0=-2+iπ（|w_0|=%.4f，arg=%.4f），另一候选 iπ'
           % ('；'.join(out), abs(target), cmath.phase(target)))
    # ---- r4-drift（数值佐证）：漂移的定量解释。notes/09 的被积函数在 t=-1（τ=1）时的奇点 w_0(x)=w_0-iπx+O(x^2)，
    # 大阶鞍点 x^3≈3w_0/k 处 e^{-w_0(x)/x^3} 多出因子 exp(β n^{2/3})（k=3n），β=iπ w_0^{-2/3}。
    # 于是两项拟合的有效奇点 w_eff(n)≈w_0·exp(-(2/3)β n^{-1/3})，变号次数≈[(k/3)arg w_0 - Im β (k/3)^{2/3}]/π 的增量。
    beta = 1j * pi * target ** (-2 / 3)
    rows, ok_d = [], True
    for r in range(3):
        for n_ in (100, 200, max(rawall[r])):
            pred = target * cmath.exp(-(2 / 3) * beta * n_ ** (-1 / 3))
            got = rawall[r][n_]
            ok_d &= abs(abs(got) - abs(pred)) < 0.03 and abs(cmath.phase(got) - cmath.phase(pred)) < 0.01
            rows.append('r=%d n=%d：|w| %.4f/%.4f，arg %.4f/%.4f' % (r, n_, abs(got), abs(pred), cmath.phase(got), cmath.phase(pred)))
    th = cmath.phase(target)
    Phi = lambda k: ((k / 3) * th - beta.imag * (k / 3) ** (2 / 3)) / pi  # noqa: E731
    pred_chg = Phi(1000) - Phi(3)
    ok_d &= abs(pred_chg - c1000) < 1.5
    report('r4-drift', ok_d, '（数值佐证）β=iπw_0^{-2/3}=%.4f%+.4fi；原始估计/预测：%s；3<=k<=1000 的变号次数预测 %.1f（实际 %d；不计修正项为 226.1）'
           % (beta.real, beta.imag, '；'.join(rows), pred_chg, c1000))
    # 增长率的粗略核对：g_k=(ln|h_k(-1)|-lnΓ(k/3+1)-(k+1)ln2)/k 在 k∈[900,1000] 的上包络
    g = [(log(abs(hm1[k])) - lgamma(k / 3 + 1) - (k + 1) * log(2)) / k for k in range(900, 1001) if hm1[k] != 0]
    print('  信息：g_k 在 900<=k<=1000 的最大值 %.4f（-ln|w_0|/3=%.4f；有限 k 的修正项约为 Re β·(k/3)^{2/3}/k，即 k^{-1/3} 量级）' % (max(g), -log(abs(complex(-2, pi))) / 3))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RES)
    print('SUMMARY s14-b9 r4 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    sys.exit(0 if all(RES) else 1)
