# -*- coding: utf-8 -*-
"""复核者 s14-b9：反向检查（故意改坏一处，确认对应的检查会报错）。每一项 PASS 表示「改坏后检查确实 FAIL」。

  v1 三元组条件改成 a>max(b,c)（严格）：朴素对 DP 与压缩 DP 不再一致
  v2 定理 2.2 的整数核对里漏掉 j=0 项（σ=1）：等式不成立
  v3 引理 2(b) 写成 |σ|^2=ρ(ρ+1)：数值等式不成立
  v4 余项界漏掉 j=0 项 / 漏掉 j=i 的复根对：「界 >= 实际余项」的健全性检查 FAIL
  v5 把 c_i 的下界放大 1000 倍（无效的界）：健全性检查 FAIL，且这样「认证」出的 τ 与正确值不同（说明精确部分必须覆盖到 K*）
  v6 τ_7 改成 49：与独立算出的门槛不一致
  v7 Δφ_1 公式里的 -7 改成 -6：恒等式 FAIL；把翻转点说成 a<=55：B_1 的符号核对 FAIL
  v8 次高项闭式 k=3a+1 情形里 (3a+2) 改成 (3a+1)：与实际 h 不符
  v9 命题 4(i) 写成 2^{k-q+1}：与 h_k(-1) 不符
"""
import sys
import time
from decimal import Decimal as D, Context, ROUND_HALF_EVEN, getcontext
from fractions import Fraction as Fr
from math import comb, factorial

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import rt_dp_U, U_table, h_coef, h_rec_iter  # noqa: E402
import r1_truth_binet as r1  # noqa: E402
import r2_tau_cert as r2  # noqa: E402
import r3_top as r3  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, detected, msg):
    RES.append(bool(detected))
    print('%s %s %s' % ('PASS' if detected else 'FAIL', cid, msg), flush=True)


def pair_dp_strict(K, m):
    out = [1, m + 1, (m + 1) ** 2]
    cnt = [[1] * (m + 1) for _ in range(m + 1)]
    for _k in range(3, K + 1):
        new = [[0] * (m + 1) for _ in range(m + 1)]
        for a in range(m + 1):
            for b in range(m + 1):
                x = cnt[a][b]
                if x:
                    for c in range(m + 1):
                        if b == c or a > max(b, c):      # 故意改坏：>= 改成 >
                            new[b][c] += x
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out[:K + 1]


def sane_check(P, Imax, drop=None, c_scale=1):
    """r2 的健全性检查（可选择漏掉某类项、或放大 c_i 下界）。返回 True 表示「界 >= 实际」处处成立。"""
    HP = Context(prec=90, rounding=ROUND_HALF_EVEN)
    U2 = U_table(Imax, 2 * r2.KSTAR_CLAIM[Imax - 1])
    for i in range(1, Imax + 1):
        rho = HP.divide(HP.add(P.lo[i], P.hi[i]), 2)
        ci = HP.divide(HP.add(P.c_dn[i], P.c_up[i]), 2)
        specs = r2.term_specs(P, i)
        if drop == 'j0':
            specs = [sp for sp in specs if not (sp[1] == 1 and sp[2] == i)]
        elif drop == 'cpx_i':
            specs = specs[1:]
        clo = P.c_dn[i] * c_scale
        for k in range(0, 2 * r2.KSTAR_CLAIM[i - 1] + 1):
            main_ = HP.multiply(ci, HP.power(rho, k))
            act = abs(HP.subtract(D(h_coef(U2, k, i)), main_)) / main_
            bnd = D(0)
            for (A, base, n, a) in specs:
                q = base / P.lo[i]
                bnd += A * q ** k * r2.L_exact_up(n, k, a) / clo
            if bnd < act * (1 - D(10) ** -20):
                return False
    return True


def main():
    t0 = time.time()
    getcontext().prec = 60
    # v1
    detected = any(pair_dp_strict(20, m) != rt_dp_U(20, m) for m in range(1, 6))
    report('v1', detected, '三元组条件改成严格不等号后，朴素 DP 与压缩 DP 不一致：%s' % detected)
    # v2
    M = 6
    U = U_table(M, 3 * M + 12)
    Nmax = 3 * M + 12 + 3 * M + 2
    S = [r1.S_table(j, Nmax) for j in range(M + 1)]
    bad = False
    for m in range(1, M + 1):
        for k in range(0, 3 * m + 13):
            rhs = sum((-1) ** (m - j) * comb(m, j) * S[j][k + 3 * (m - j)] for j in range(1, m + 1))  # 漏掉 j=0
            if rhs != factorial(m) * U[m][k]:
                bad = True
    report('v2', bad, '定理 2.2 漏掉 j=0 项后精确核对失败：%s' % bad)
    # v3
    rho, rs = r1.roots_dec(5)
    s = [z for z in rs if abs(z[1]) > D(10) ** -40][0]
    wrong = abs(r1.cabs2(s) - rho * (rho + 1)) > D(10) ** -10
    report('v3', wrong, '|σ|^2 写成 ρ(ρ+1) 时与 Newton 求出的根不符：%s' % wrong)
    # v4、v5
    P = r2.Params(13)
    PA = r2.ParamsAuthor(13, P)
    ok_full = sane_check(PA, 8)
    f1 = not sane_check(PA, 8, drop='j0')
    f2 = not sane_check(PA, 8, drop='cpx_i')
    report('v4', ok_full and f1 and f2, '完整的界通过健全性检查 %s；漏掉 j=0 项后 FAIL %s；漏掉 j=i 的复根对后 FAIL %s' % (ok_full, f1, f2))
    f3 = not sane_check(PA, 8, c_scale=1000)
    # 用放大后的（无效）c_i 下界做「认证」，再按精确部分求 τ
    taus_bad = []
    U3 = U_table(8, 200)
    for i in range(1, 9):
        K = i
        while True:
            tot = D(0)
            mono = True
            for (A, base, n, a) in r2.term_specs(PA, i):
                q = base / PA.lo[i]
                tot += A * q ** K * r2.L_exact_up(n, K, a) / (PA.c_dn[i] * 1000)
                mono &= (K + 2 - n) > 0 and q * (K + 2) < (K + 2 - n)
            if tot < 1 and mono:
                break
            K += 1
        last_bad = None
        for k in range(0, K + 1):
            if h_coef(U3, k, i) <= 0:
                last_bad = k
        taus_bad.append(last_bad + 1 if last_bad is not None else 0)
    differs = taus_bad != r2.TAU_CLAIM[:8]
    report('v5', f3 and differs, 'c_i 下界放大 1000 倍：健全性检查 FAIL %s；这样「认证」出的 τ_1..τ_8=%s 与正确值不同 %s'
           % (f3, taus_bad, differs))
    # v6
    U4 = U_table(8, 120)
    tau7 = 1 + max(k for k in range(0, 106) if h_coef(U4, k, 7) <= 0)
    report('v6', tau7 != 49, 'τ_7 改成 49 后与独立算出的 τ_7=%d 不符：%s' % (tau7, tau7 != 49))
    # v7
    Hs = [Fr(0)]
    for n in range(1, 80):
        Hs.append(Hs[-1] + Fr(1, n))
    E2 = [Fr(0)]
    for n in range(1, 80):
        E2.append(E2[-1] + Hs[n - 1] / n)

    def phi1(n):
        return Hs[n] + E2[n] - 1 - Fr(3 * n - 4, n) * Hs[n - 1]
    wrong_id = any(phi1(n + 1) - phi1(n) != ((n - 4) * (Hs[n] - 2) - 6 + Fr(4, n)) / (n * (n + 1)) for n in range(3, 70))
    c = r3.stirling_low(80)
    B1 = {a: c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2] for a in range(1, 70)}
    wrong_flip = not all((B1[a] < 0) == (a <= 55) for a in range(1, 70))
    report('v7', wrong_id and wrong_flip, 'Δφ_1 中 -7 改成 -6 后恒等式不成立 %s；翻转点说成 a<=55 时符号核对失败 %s' % (wrong_id, wrong_flip))
    # v8、v9
    H = {}
    for k, h in h_rec_iter(60):
        H[k] = h
    cbig = r3.stirling_low(40)

    def second_bad(k):
        a = k // 3
        if k % 3 == 1:
            return (-1) ** a * (cbig[a + 3][2] + cbig[a + 3][3] - factorial(a + 2) - (3 * a + 1) * cbig[a + 2][2])
        return r3.second_closed(k, cbig)
    v8 = any(H[k][-2] != second_bad(k) for k in range(3, 61))
    report('v8', v8, '次高项闭式改坏后与实际 h_{k,d-1} 不符：%s' % v8)
    Ucols = [rt_dp_U(30, m) for m in range(31)]
    v9 = False
    for k in range(1, 31):
        N = [0] + [sum((-1) ** (q - l) * comb(q, l) * Ucols[l - 1][k] for l in range(1, q + 1)) for q in range(1, k + 1)]
        hm1 = sum(x if i % 2 == 0 else -x for i, x in enumerate(H[k]))
        if hm1 != sum((-1) ** (q - 1) * 2 ** (k - q + 1) * N[q] for q in range(1, k + 1)):
            v9 = True
    report('v9', v9, '命题 4(i) 改成 2^{k-q+1} 后与 h_k(-1) 不符：%s' % v9)
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RES)
    print('SUMMARY s14-b9 r6 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    sys.exit(0 if all(RES) else 1)
