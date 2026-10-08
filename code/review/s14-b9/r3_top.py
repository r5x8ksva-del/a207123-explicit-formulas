# -*- coding: utf-8 -*-
"""复核者 s14-b9：定理 3（次高项的符号）与末端系数的独立核对（不 import 项目代码）。

  r3-hdp      由定义的压缩 DP 得 U_k(m)（m<=202），反演得 h_k（k<=300），并核对 deg h_k=floor(2k/3)；
              自写的 T1.7 递推与之逐系数相等（k<=300），之后用递推到 k<=1000
  r3-stir     Stirling 数（[x^k] x(x+1)...(x+n-1) 的截断乘积）与 c(n+1,2)=n!H_n、c(n+1,3)=n!e_2(n)（n<=300，精确）
  r3-closed   c5a 定理 4.4(d) 的闭式 = 实际次高项（3<=k<=1000，递推得到的 h）
  r3-B        B_1(a)<0 ⇔ 1<=a<=54，B_1(a)>0（55<=a<=3000）；B_2(a)>0（1<=a<=3000）
  r3-phi      B_1/(a+2)! = φ_1(a+2)、B_2/(a+2)! = φ_2(a+2)（a<=300，精确）；Δφ_1、Δφ_2 的公式（3<=n<=400，精确）；
              我自己的化简 Δφ_1 = [n(n-4)H_n - 2n^2 + n + 4]/(n^2(n+1)) 与之相同；φ_1<0（3<=n<=56）、φ_1(57)>0；
              8(H_12-2)>7（精确）；n>=12 时 Δφ_1 的分子 >0 的论证所需的两件事（n-4>=8、H_n-2>=H_12-2>0）
  r3-sign     实际 h_k（k<=1000）：次高项与首项 k≡0 异号、k≡2 同号、k≡1 时 k<=163 异号、k>=166 同号
  r3-recip    由 G_{-j} 顶端系数（只跟踪最高 15 个系数）与互反式独立算出 h_k 的最高 4 个系数，与递推的 h 对照（k<=1000），
              再把定理 3 的符号规律延伸到 k<=KTOP；并统计第三高系数 h_{k,d-2} 与首项的相对符号在各剩余类中的翻转位置（信息性）
用法：py -3.14 r3_top.py [KTOP]（默认 12000）
"""
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import rt_dp_U, h_poly_from_Ucol, h_rec_iter  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def stirling_low(N):
    """c[n] = (c(n,0),c(n,1),c(n,2),c(n,3))，n=0..N，由 x(x+1)...(x+n-1) 的截断乘积。"""
    out = [(1, 0, 0, 0)]
    p = [1, 0, 0, 0]
    for n in range(1, N + 1):
        a = n - 1                       # 乘以 (x + a)
        p = [a * p[0], a * p[1] + p[0], a * p[2] + p[1], a * p[3] + p[2]]
        out.append(tuple(p))
    return out


def second_closed(k, c):
    a = k // 3
    if k % 3 == 0:
        return (-1) ** (a + 1) * 2 * a * factorial(a)
    if k % 3 == 1:
        return (-1) ** a * (c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2])
    return (-1) ** a * (c[a + 3][2] + c[a + 3][3] - 3 * (a + 1) * factorial(a + 1))


def main(KTOP):
    t0 = time.time()
    # ---- r3-hdp
    KD = 300
    MD = 2 * KD // 3 + 2
    Ucols = [rt_dp_U(KD, m) for m in range(MD + 1)]       # Ucols[m][k]
    hdp = {}
    ok_deg = True
    for k in range(0, KD + 1):
        dk = 2 * k // 3
        upto = min(MD, dk + 2)
        h = h_poly_from_Ucol([Ucols[m][k] for m in range(upto + 1)], k)
        hdp[k] = h
        if len(h) - 1 != dk and k >= 1:
            ok_deg = False
    hrec = {}          # k<=300 存完整的 h_k；其余只存最高 4 个系数（倒序存放，h[-1] 为首项）
    for k, h in h_rec_iter(1000):
        hrec[k] = list(h) if k <= KD else list(h[-4:])
    ok_eq = all(hdp[k] == hrec[k] for k in range(0, KD + 1))
    known12 = [1, 203, 1019, -1777, -1159, 2526, -643, -192, 24]
    report('r3-hdp', ok_deg and ok_eq and hdp[12] == known12,
           '由定义（压缩 DP）反演的 h_k：deg = floor(2k/3)（1<=k<=%d，含 h_{k,d+1}=h_{k,d+2}=0 的核对）%s；自写 T1.7 递推 = DP 反演（k<=%d）%s；h_12 与 c5a 所列一致（%.1fs）'
           % (KD, ok_deg, KD, ok_eq, time.time() - t0))

    # ---- r3-stir
    c = stirling_low(4010)

    def Hn(n):
        return sum(Fr(1, i) for i in range(1, n + 1))

    def e2(n):
        s, h = Fr(0), Fr(0)
        for i in range(1, n + 1):
            s += h / i
            h += Fr(1, i)
        return s
    Hs = [Fr(0)]
    for n in range(1, 402):
        Hs.append(Hs[-1] + Fr(1, n))
    E2 = [Fr(0)]
    for n in range(1, 402):
        E2.append(E2[-1] + Hs[n - 1] / n)
    ok_st = all(c[n + 1][2] == factorial(n) * Hs[n] and c[n + 1][3] == factorial(n) * E2[n] for n in range(1, 301))
    ok_st &= E2[5] == e2(5) and Hs[7] == Hn(7)
    report('r3-stir', ok_st, 'c(n+1,2)=n!H_n、c(n+1,3)=n!e_2(n)（1<=n<=300，精确；Stirling 数由截断乘积独立算出）%s' % ok_st)

    # ---- r3-closed
    ok_cf = all(hrec[k][-2] == second_closed(k, c) for k in range(3, 1001))
    report('r3-closed', ok_cf, 'c5a 定理 4.4(d) 的次高项闭式 = 实际 h_{k,d-1}（3<=k<=1000）%s' % ok_cf)

    # ---- r3-B
    B1 = {a: c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2] for a in range(1, 3001)}
    B2 = {a: c[a + 3][2] + c[a + 3][3] - 3 * (a + 1) * factorial(a + 1) for a in range(1, 3001)}
    neg = [a for a in B1 if B1[a] < 0]
    zero = [a for a in B1 if B1[a] == 0]
    ok_b1 = neg == list(range(1, 55)) and not zero
    ok_b2 = all(v > 0 for v in B2.values())
    report('r3-B', ok_b1 and ok_b2, 'B_1(a)<0 恰为 1<=a<=54，其余 a<=3000 为正 %s（B_1(54)=%.3e，B_1(55)=%.3e）；B_2(a)>0（a<=3000）%s'
           % (ok_b1, float(B1[54]), float(B1[55]), ok_b2))

    # ---- r3-phi
    def phi1(n):
        return Hs[n] + E2[n] - 1 - Fr(3 * n - 4, n) * Hs[n - 1]

    def phi2(n):
        return Hs[n] + E2[n] - Fr(3 * (n - 1), n)
    ok_map = all(Fr(B1[a], factorial(a + 2)) == phi1(a + 2) and Fr(B2[a], factorial(a + 2)) == phi2(a + 2) for a in range(1, 299))
    ok_d1 = all(phi1(n + 1) - phi1(n) == ((n - 4) * (Hs[n] - 2) - 7 + Fr(4, n)) / (n * (n + 1)) for n in range(3, 400))
    ok_d1b = all(phi1(n + 1) - phi1(n) == (n * (n - 4) * Hs[n] - 2 * n * n + n + 4) / Fr(n * n * (n + 1)) for n in range(3, 400))
    ok_d2 = all(phi2(n + 1) - phi2(n) == (n + n * Hs[n] - 3) / Fr(n * (n + 1)) for n in range(3, 400))
    ok_p2 = phi2(3) == Fr(5, 6)
    ok_neg = all(phi1(n) < 0 for n in range(3, 57)) and phi1(57) > 0
    ok_h12 = 8 * (Hs[12] - 2) > 7 and Hs[12] - 2 > 0 and 8 * (Hs[12] - 2) > Fr(88, 10)
    # 数值上 Δφ_1 何时开始为正（论证只需要 n>=12）
    dphi = {n: phi1(n + 1) - phi1(n) for n in range(3, 400)}
    first_pos = min(n for n in range(3, 400) if all(dphi[m] > 0 for m in range(n, 400)))
    report('r3-phi', ok_map and ok_d1 and ok_d1b and ok_d2 and ok_p2 and ok_neg and ok_h12,
           'B_i/(a+2)! = φ_i(a+2)（a<=298）%s；Δφ_1 公式（3<=n<=399）%s，与我的化简一致 %s；Δφ_2 公式 %s，φ_2(3)=5/6 %s；'
           'φ_1<0（3<=n<=56）且 φ_1(57)>0 %s；8(H_12-2)>8.8>7 %s；（信息）Δφ_1 从 n=%d 起恒正（n<400）'
           % (ok_map, ok_d1, ok_d1b, ok_d2, ok_p2, ok_neg, ok_h12, first_pos))

    # ---- r3-sign（实际 h）
    bad = []
    for k in range(3, 1001):
        h = hrec[k]
        same = (h[-1] > 0) == (h[-2] > 0)
        r = k % 3
        want = {0: False, 2: True}.get(r, k >= 166)
        if same != want:
            bad.append(k)
    report('r3-sign', not bad, '实际 h_k（3<=k<=1000）：k≡0 异号、k≡2 同号、k≡1 时 k<=163 异号且 k>=166 同号 %s' % (bad[:5] if bad else 'True'))

    # ---- r3-recip：顶端系数
    t1 = time.time()
    L = 15
    # 完整的 G_{-j}（j<=20），之后只跟踪最高 L 个系数：top[δ] = [x^{3j-3-δ}] G_{-j}
    full = {1: [1]}
    for j in range(1, 40):
        g = full[j]
        n = [0] * (len(g) + 3)
        for e, x in enumerate(g):
            n[e] += x
            n[e + 1] -= x
            n[e + 3] += j * x
        n[2] += j
        while len(n) > 1 and n[-1] == 0:
            n.pop()
        full[j + 1] = n
    ok_full = all(len(full[j]) - 1 == 3 * j - 3 for j in range(2, 41))

    def top_of(poly, j):
        deg = 3 * j - 3
        return [poly[deg - d] if deg - d >= 0 else 0 for d in range(L)]

    def step_top(top, j):
        """G_{-j} 的 top -> G_{-j-1} 的 top（j>=20 时 jx^2 项不进入前 L 层）。"""
        return [(top[d - 3] if d >= 3 else 0) - (top[d - 2] if d >= 2 else 0) + j * top[d] for d in range(L)]
    # 核对 step_top 与完整多项式（20<=j<40）
    ok_track = all(step_top(top_of(full[j], j), j) == top_of(full[j + 1], j + 1) for j in range(20, 40))

    def top4_from_tops(k, tops):
        """由 U_k(-(s_k+1+n))（n=0..3）与互反式解出 h_{k,g-n}，n=0..3。tops[j] 为 G_{-j} 的 top。"""
        s = (k + 2) // 3
        g = k - s
        hs = {}
        for n in range(4):
            j = s + 1 + n
            d = 3 * j - 3 - k
            Uneg = tops[j][d]
            val = (-1) ** k * Uneg
            for i in range(g - n + 1, g + 1):
                val -= hs[i] * comb(i + s + n, k)
            hs[g - n] = val
        return [hs[g - n] for n in range(4)]   # [h_g, h_{g-1}, h_{g-2}, h_{g-3}]

    # 依次生成 top_j，滑动窗口
    tops = {}
    for j in range(1, 21):
        tops[j] = top_of(full[j], j)
    jmax = 20
    ok_rec, ok_sign_big, ok_cf_big = True, True, True
    third = {0: [], 1: [], 2: []}    # 记录 (k, 第三高系数与首项是否同号)
    for k in range(3, KTOP + 1):
        s = (k + 2) // 3
        need = s + 4
        while jmax < need:
            tops[jmax + 1] = step_top(tops[jmax], jmax)
            jmax += 1
        for jj in [x for x in tops if x < s - 1]:
            del tops[jj]
        t4 = top4_from_tops(k, tops)
        if k <= 1000:
            h = hrec[k]
            nn = min(4, len(h))
            if t4[:nn] != [h[-1 - x] for x in range(nn)]:
                ok_rec = False
        a = k // 3
        same2 = (t4[0] > 0) == (t4[1] > 0)
        want = {0: False, 2: True}.get(k % 3, k >= 166)
        if same2 != want:
            ok_sign_big = False
        if a + 3 <= 4010 and t4[1] != second_closed(k, c):
            ok_cf_big = False
        third[k % 3].append((k, (t4[0] > 0) == (t4[2] > 0)))
    flips = {}
    for r in range(3):
        seq = third[r]
        flips[r] = [seq[i][0] for i in range(1, len(seq)) if seq[i][1] != seq[i - 1][1]]
    report('r3-recip', ok_full and ok_track and ok_rec and ok_sign_big and ok_cf_big,
           'G_{-j} 次数 3j-3（j<=40）%s；只跟踪顶端 %d 层的递推与完整多项式一致 %s；互反式得到的最高 4 个系数 = 递推的 h（k<=1000）%s；'
           '定理 3 的符号规律在 3<=k<=%d 成立 %s；次高项闭式到 k<=%d 成立 %s（%.1fs）'
           % (ok_full, L, ok_track, ok_rec, KTOP, ok_sign_big, min(KTOP, 3 * 4007), ok_cf_big, time.time() - t1))
    for r in range(3):
        seq = third[r]
        print('  信息：k≡%d 时第三高系数与首项「同号」的初值（k=%d）%s，翻转发生在 k = %s' % (r, seq[0][0], seq[0][1], flips[r][:12]))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    KTOP = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
    main(KTOP)
    n_pass = sum(RES)
    print('SUMMARY s14-b9 r3 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    sys.exit(0 if all(RES) else 1)
