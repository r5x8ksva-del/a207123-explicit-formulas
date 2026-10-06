# -*- coding: utf-8 -*-
"""t27_good：满足 (N1)(N2) 的 proper 项上，逐步核对引理 A、F、(N2)、引理 S 与最后的拼接。

例子（变量顺序 p=(k,m,j⃗)）：
  E1  C(m,j)C(k,j)                               （和 = C(k+m,k)）
  E2  C(k+j,2j)C(m,j)                            （带缓冲带：j<−k 才不良定义）
  E3  m!/(j1! j2! (m−j1−j2)!)·C(k,j1)·(−1)^{j2}   （r=2，检验多重指标 α* 的选取；和 = C(k,m)）
  E4  (k−2j+1)·C(k+j,2j)C(m,j)·3^k·(1/2)^m·2^j     （非平凡 P，且 P 在支撑内部有零点；非平凡几何因子）
  E5  C(k,j)C(2m−j,j)                            （上侧缓冲带：j>2m 才不良定义；Q_R={k≥R,m≥3R}）
  E6  C(m,j)·k!/(k+j)!                           （递推系数真正依赖 k）
每个例子：
  A  用小的 (J,I) 求 Σ_ω a_ω(k)Q_ω≡0 的非零解（取样 + 网格严格核对），并核对次数界 D；
  F  在一个盒子里所有「T(p−ω) 全部良定义」的格点上核对 T(p−ω)=T*(p)Q_ω(p) 与递推，统计边界点与分母三种情形；
  N2 对 R=diam_∞Ω=max(I,J) 在 Q_R 上暴力核对 (N2)；
  拼接 Q′={k≥k_R+J, m≥m_R+I}：对一切 j⃗ 核对 Σa_ω T̃(p−ω)=0；
  S  构造 C_α、α*、C_{α*}，核对分部求和恒等式，并核对 C_{α*}U=0（这里 U 换成 Σ_j⃗ T̃）在 Q′ 上成立。
"""
import sys
sys.dont_write_bytecode = True
import itertools
import time
from fractions import Fraction
from math import comb, factorial
import t27lib as L
import t27pipe as PP

rep = L.Reporter()
SEARCH = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (3, 2), (2, 3), (4, 1), (3, 3), (4, 2)]


def win1(k, m):
    return [(-2, max(k, m, 0) + 2)]


def run_example(T, kR, mR, Rlabel, closed=None, win=win1, maxDk=3, Fbox=None, search=SEARCH):
    print('\n' + '=' * 100)
    print('例子 %s：%s' % (T.name, T.note))
    beta, gamma = T.beta_gamma()
    print('    分子参数 %s；分母参数 %s；P=%s；z=%s；β=%d，γ=%d'
          % (T.num, T.den, T.P, tuple(str(x) for x in T.z), beta, gamma))
    t0 = time.time()
    res = PP.search_rec(T, search, maxDk, rep, label='[%s] ' % T.name)
    rep.check('[%s] 引理 A：找到非平凡的、系数只依赖 k 的递推（并经网格严格核对为多项式恒等式）' % T.name, res is not None)
    if res is None:
        return
    LA, Dk, good = res
    a = good[0]
    rep.info('[%s] 递推：%s = 0' % (T.name, PP.rec_str(a)))
    PP.check_degree_bound(T, LA, rep, label='[%s] ' % T.name)
    # ---- 引理 F
    if Fbox is None:
        Fbox = [range(-2, 12), range(-2, 12)] + [range(-4, 15)] * T.r
    PP.check_lemmaF(T, LA, a, Fbox, rep, label='[%s] ' % T.name)
    # ---- (N2)
    I, J = LA.I, LA.J
    R = max(I, J)
    k1, m1 = kR(R), mR(R)
    ok, npts, viol = PP.check_N2(T, R, range(k1, k1 + 9), range(m1, m1 + 9), win)
    rep.check('[%s] (N2)：R=diam_∞Ω=%d，Q_R=%s={k≥%d,m≥%d}；%d 个支撑点的 R 邻域都良定义'
              % (T.name, R, Rlabel, k1, m1, npts), ok, '' if ok else '违反：%s' % (viol,))
    # 也看看 Q_R 取得太靠外时 (N2) 会不会失败（说明 Q_R 的取法不是摆设）
    okc, _, violc = PP.check_N2(T, R, range(max(0, k1 - 2), max(0, k1 - 2) + 9), range(max(0, m1 - 2), max(0, m1 - 2) + 9), win)
    rep.info('[%s] 对照：把象限外移到 {k≥%d,m≥%d} 时 (N2) %s'
             % (T.name, max(0, k1 - 2), max(0, m1 - 2), '仍成立' if okc else '失败（如 %s 的邻点 %s 不良定义）' % violc))
    # ---- 拼接：Q′ 上对一切 j⃗ 递推成立
    kq, mq = k1 + J, m1 + I
    Qk, Qm = range(kq, kq + 7), range(mq, mq + 7)
    fails, npts = PP.rec_failures(T, a, Qk, Qm, win, I)
    rep.check('[%s] 拼接：Q′={k≥%d,m≥%d} 中 7×7 个 (k,m)、窗口内一切 j⃗（共 %d 点）上 Σa_ω(k)T̃(p−ω)=0'
              % (T.name, kq, mq, npts), not fails, '' if not fails else '反例 %s' % (fails[:3],))
    fo, npo = PP.rec_failures(T, a, range(0, 4), range(0, 4), win, I)
    rep.info('[%s] 对照：靠近原点的 (k,m)∈[0,3]² 上 T̃ 递推不成立的点 %d 个（共查 %d 点）%s'
             % (T.name, len(fo), npo, ('，例如 %s' % (fo[0][0],)) if fo else ''))
    # ---- 引理 S
    S = PP.make_S(T, win)
    kpts = [(k, m) for k in range(-1, kq + 5) for m in range(-1, mq + 5)]
    Qpts = [(k, m) for k in Qk for m in Qm]
    out = PP.check_lemmaS(T, a, rep, I, S, win, kpts, Qpts, label='[%s] ' % T.name)
    rep.check('[%s] 窗口外的 T̃ 都为 0（和式窗口取得足够大）' % T.name, not S.shell_bad,
              '' if not S.shell_bad else str(S.shell_bad[:3]))
    if out:
        rep.check('[%s] 结论：C_{α*}(Σ_j⃗T̃)=0 在 Q′ 的 7×7 个点上成立，C_{α*}≠0' % T.name,
                  out['zero_on_Qp'] and bool(out['Cst']))
        nz_out = sum(1 for q, v in out['resid'].items() if v != 0)
        rep.info('[%s] 对照：在含 Q′ 之外的 %d 个 (k,m) 上，C_{α*}S≠0 的点 %d 个（都在 Q′ 之外）'
                 % (T.name, len(out['resid']), nz_out))
        bad_in_Q = [q for q, v in out['resid'].items() if v != 0 and q[0] >= kq and q[1] >= mq]
        rep.check('[%s] 这些非零点确实都不在 Q′ 中' % T.name, not bad_in_Q, str(bad_in_Q[:3]))
    if closed is not None:
        okc = all(S(k, m) == closed(k, m) for k in range(0, 12) for m in range(0, 12))
        rep.check('[%s] 和式锚点：Σ_j⃗ T̃(k,m,j⃗) 与独立公式一致（0≤k,m≤11）' % T.name, okc)
    rep.info('[%s] 用时 %.1f s' % (T.name, time.time() - t0))


# ---------------------------------------------------------------- 例子
E1 = L.Term('E1', 1, num=[((1, 0, 0), 0), ((0, 1, 0), 0)],
            den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0)],
            note='C(m,j)C(k,j)；j 只在分母，分子 k!、m!')
run_example(E1, lambda R: R, lambda R: R, '{k≥R,m≥R}', closed=lambda k, m: comb(k + m, k))

E2 = L.Term('E2', 1, num=[((1, 0, 1), 0), ((0, 1, 0), 0)],
            den=[((0, 0, 2), 0), ((1, 0, -1), 0), ((0, 0, 1), 0), ((0, 1, -1), 0)],
            note='C(k+j,2j)C(m,j)；分子 (k+j)! 在 j<−k 才不良定义，缓冲带 [−k,−1]')
run_example(E2, lambda R: 2 * R, lambda R: R, '{k≥2R,m≥R}',
            closed=lambda k, m: sum(comb(k + j, 2 * j) * comb(m, j) for j in range(0, min(k, m) + 1)))


def win3(k, m):
    return [(-2, max(k, m, 0) + 2), (-2, max(m, 0) + 2)]


E3 = L.Term('E3', 2, num=[((0, 1, 0, 0), 0), ((1, 0, 0, 0), 0)],
            den=[((0, 0, 1, 0), 0), ((0, 0, 0, 1), 0), ((0, 1, -1, -1), 0), ((0, 0, 1, 0), 0), ((1, 0, -1, 0), 0)],
            z=(1, 1, 1, -1), note='m!/(j1! j2! (m−j1−j2)!)·C(k,j1)·(−1)^{j2}（r=2）')
run_example(E3, lambda R: R, lambda R: R, '{k≥R,m≥R}', closed=lambda k, m: comb(k, m) if m <= k else 0,
            win=win3, maxDk=2, Fbox=[range(-1, 8), range(-1, 8), range(-3, 10), range(-3, 10)],
            search=[(1, 1), (2, 1), (1, 2), (2, 2)])

P4 = {(1, 0, 0): Fraction(1), (0, 0, 1): Fraction(-2), (0, 0, 0): Fraction(1)}
E4 = L.Term('E4', 1, num=[((1, 0, 1), 0), ((0, 1, 0), 0)],
            den=[((0, 0, 2), 0), ((1, 0, -1), 0), ((0, 0, 1), 0), ((0, 1, -1), 0)],
            P=P4, z=(3, Fraction(1, 2), 2), note='(k−2j+1)·C(k+j,2j)C(m,j)·3^k·(1/2)^m·2^j')
run_example(E4, lambda R: 2 * R, lambda R: R, '{k≥2R,m≥R}',
            closed=lambda k, m: sum((k - 2 * j + 1) * comb(k + j, 2 * j) * comb(m, j) * Fraction(3) ** k
                                    * Fraction(1, 2) ** m * 2 ** j for j in range(0, min(k, m) + 1)))

E5 = L.Term('E5', 1, num=[((1, 0, 0), 0), ((0, 2, -1), 0)],
            den=[((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 0, 1), 0), ((0, 2, -2), 0)],
            note='C(k,j)C(2m−j,j)；分子 (2m−j)! 在 j>2m 才不良定义')
run_example(E5, lambda R: R, lambda R: 3 * R, '{k≥R,m≥3R}',
            closed=lambda k, m: sum(comb(k, j) * comb(2 * m - j, j) for j in range(0, min(k, m) + 1)))

E6 = L.Term('E6', 1, num=[((0, 1, 0), 0), ((1, 0, 0), 0)],
            den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((1, 0, 1), 0)],
            note='C(m,j)·k!/(k+j)!；递推系数要依赖 k')
run_example(E6, lambda R: R, lambda R: R, '{k≥R,m≥R}',
            closed=lambda k, m: sum(comb(m, j) * Fraction(factorial(k), factorial(k + j)) for j in range(0, m + 1)))

sys.exit(rep.done())
