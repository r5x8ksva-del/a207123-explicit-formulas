# -*- coding: utf-8 -*-
"""审计 a1-formulas：T4.2(1) 模式数 M(d;σ,β) 的自写按层 DP（与 audit_c4 的定义暴力对照 d<=4），
再算 d=5,6 的总数（报告 63537、928393）并核对模式展开 D(k,d)=Σ M C(k-d-β,σ-β)（d<=8）。

按层 DP：从最大值 σ 往下处理每个值 x：
  * 先从待分配的谷位中选 j 个赋值 x（C(p,j) 种；谷位按位置区分）；
  * 再定 x 层的块：s 个 S、t 个 T（排列 C(s+t,s)），可选在此层放末尾 E（之后不再有块）；
  * x 的出现次数 = j+s+2t+[E]，必须 >=1；x 平凡 ⇔ j=0 且 (s,t,E)=(1,0,0)，模式要求无平凡值；
  * 超额 += 出现次数-1；新谷位 += t+[E]。结束时谷位全部分配、超额 = d。
"""
import time
from math import comb
from common import *  # noqa

t0 = time.time()

def M_dp(d):
    res = {}
    for sigma in range(0, 2 * d + 4):
        # state: (p, e, Eplaced, beta) -> count
        st = {(0, 0, False, 0): 1}
        for x in range(sigma, 0, -1):
            new = {}
            for (p, e, Ep, beta), c in st.items():
                for j in range(0, p + 1):
                    cj = comb(p, j)
                    p1 = p - j
                    opts = []
                    if Ep:
                        opts.append((0, 0, False))
                    else:
                        for s in range(0, d + 2):
                            for t in range(0, d + 1):
                                for E in (False, True):
                                    opts.append((s, t, E))
                    for (s, t, E) in opts:
                        occ = j + s + 2 * t + (1 if E else 0)
                        if occ == 0:
                            continue
                        if j == 0 and s == 1 and t == 0 and not E:
                            continue
                        e2 = e + occ - 1
                        if e2 > d:
                            continue
                        p2 = p1 + t + (1 if E else 0)
                        if p2 > d + 1:
                            continue
                        key = (p2, e2, Ep or E, x if E else beta)
                        new[key] = new.get(key, 0) + c * cj * comb(s + t, s)
            st = new
        for (p, e, Ep, beta), c in st.items():
            if p == 0 and e == d:
                res[(sigma, beta)] = res.get((sigma, beta), 0) + c
    return res

# N 表（三角递推，k<=80；已在 audit_c1/audit_c4 与定义比对）
KM = 80
NT = [[0] * (KM + 3) for _ in range(KM + 1)]
NT[0][0] = 1
def Ng(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return NT[k][q]
NT[1][1] = 1; NT[2][1] = 1; NT[2][2] = 2
for k in range(3, KM + 1):
    for r in range(0, k):
        NT[k][r + 1] = Ng(k - 1, r) + Ng(k - 1, r + 1) + r * (Ng(k - 3, r - 1) + 2 * Ng(k - 3, r) + Ng(k - 3, r + 1))
TU = core.U_fast_table(40, 41)
report(all(N_from_table(TU, k, q) == Ng(k, q) for k in range(41) for q in range(41)), 'base.N', '三角表 == 定义 DP 容斥 (k<=40)')

brute = {0: 2, 1: 7, 2: 51, 3: 459, 4: 4990}        # audit_c4 的定义暴力结果（见 logs/audit_a1-formulas_c4.log）
tot = []
ok_exp = True
for d in range(0, 9):
    Mc = M_dp(d)
    tot.append(sum(Mc.values()))
    for k in range(d, KM + 1):
        if sum(c * C(k - d - b, s - b) for (s, b), c in Mc.items()) != Ng(k, k - d):
            ok_exp = False
report(all(tot[d] == brute[d] for d in brute), 'T4.2.1-dp-vs-brute', '自写按层 DP 的模式总数 d<=4 与定义暴力一致：%s' % tot[:5])
report(tot[5] == 63537 and tot[6] == 928393, 'T4.2.1-d56', '模式总数 d=5,6 = %d, %d（报告 63537, 928393）；d=7,8 = %d, %d' % (tot[5], tot[6], tot[7], tot[8]))
from math import prod, factorial
fam = True
rng = True
for d in range(1, 9):
    Mc = M_dp(d)
    df = prod(range(1, 2 * d, 2))
    top = {s_: c for (s_, b), c in Mc.items() if b == d + 2}
    if not (Mc.get((2 * d, 0), 0) == df and Mc.get((2 * d + 2, 2), 0) == df and sum(top.values()) == factorial(d + 1) and set(top) == {2 * d + 2}):
        fam = False
    if any(s_ > 2 * d + 2 or not (b == 0 or 2 <= b <= d + 2) for (s_, b) in Mc):
        rng = False
report(fam and rng, 'T4.2.1-families-d8', 'σ<=2d+2、β∈{0}∪[2,d+2]；M(2d,0)=M(2d+2,2)=(2d-1)!!；β=d+2 的模式恰 (d+1)! 个且 σ=2d+2（1<=d<=8，按层 DP）')
report(ok_exp, 'T4.2.1-expansion-d8', '模式展开 D(k,d)=Σ M(d;σ,β)C(k-d-β,σ-β) 对 d<=k<=80、d<=8 成立')

summary('audit_c4_patterns')
print('elapsed %.1fs' % (time.time() - t0))
