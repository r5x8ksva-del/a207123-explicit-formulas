# -*- coding: utf-8 -*-
"""s8-b1 第 3 步：核对 notes/05 §5 的数字（h_3、h_4、n_3、n_4 的根）与「射影」解释：
把 (1-t)h_{k-1}(t) 与 h_k(t) 都看成 k-1 次二元型（h_k 缺的次数是 t=∞ 处的根，来自 z=-1；
(1-t) 来自 n_{k-1} 在 z=∞ 处的根），它们在射影直线上循环交错——这正是 α_k 经 t=z/(1+z) 的像。
精确部分用整数多项式；numpy 只用来打印近似根。"""
import sys

import numpy as np

from px import mul, pw, add, deg, exact_div, ONEZ, interlace_A
from truth import N_table_from_U, nrow

K = 14
N = N_table_from_U(K)
n = {k: nrow(N, k) for k in range(1, K + 1)}


def h_from_N(Nrow, k):
    h = []
    for q in range(1, k + 1):
        if Nrow[q]:
            h = add(h, mul([0] * (q - 1) + [Nrow[q]], pw([1, -1], k - q)))
    return h


def roots(p):
    r = np.roots(list(reversed([float(c) for c in p])))
    return sorted(x.real for x in r)


fails = 0
h3, h4 = h_from_N(N[3], 3), h_from_N(N[4], 4)
print("h_3 =", h3, " (expect 1+2t-t^2)", "roots", ["%.4f" % x for x in roots(h3)])
print("h_4 =", h4, " (expect 1+4t-3t^2)", "roots", ["%.4f" % x for x in roots(h4)])
print("n_3 =", n[3], "roots", ["%.4f" % x for x in roots(n[3])])
print("n_4 =", n[4], "= (1+z)*", exact_div(n[4], ONEZ), "roots", ["%.4f" % x for x in roots(n[4])])
if h3 != [1, 2, -1] or h4 != [1, 4, -3] or exact_div(n[4], ONEZ) != [1, 6, 2]:
    fails += 1
    print("FAIL sec5 explicit forms")

# 射影循环交错：对 2<=k<=K，把 A(t)=(1-t)h_{k-1}(t)（k-1 次型）与 B(t)=h_k(t)（k-1 次型，缺的次数 = t=∞ 处的根）
# 的根放在射影直线上（∞ 计入 B），检查循环交替。只用于说明 §5，结论等价于 α_k。
for k in range(3, K + 1):
    A = mul([1, -1], h_from_N(N[k - 1], k - 1))
    B = h_from_N(N[k], k)
    fin = sorted([(x, 'A') for x in roots(A)] + [(x, 'B') for x in roots(B)], key=lambda u: u[0])
    labs = [lab for _, lab in fin]
    na, nb = (k - 1) - deg(A), (k - 1) - deg(B)       # 在 t=∞ 的根数（来自 z=-1）
    # ∞ 处 A、B 的根可以任意排先后：试两种交替排法
    blocks = []
    for start in 'AB':
        blk, cur, ca, cb, ok = [], start, na, nb, True
        while ca + cb > 0:
            if (cur == 'A' and ca == 0) or (cur == 'B' and cb == 0):
                ok = False
                break
            if cur == 'A':
                ca -= 1
            else:
                cb -= 1
            blk.append(cur)
            cur = 'B' if cur == 'A' else 'A'
        if ok:
            blocks.append(blk)
    if na + nb == 0:
        blocks = [[]]

    def cyc(w):
        return len(w) <= 1 or all(w[i] != w[(i + 1) % len(w)] for i in range(len(w)))
    good = [b for b in blocks if cyc(labs + b)]
    ok_z = interlace_A(n[k - 1], n[k])[0]
    print("k=%2d  finite t-roots word: %s  + at t=inf A^%d B^%d  -> cyclic-alternating=%s ; alpha_k in z=%s ; "
          "plain t-line interlacing of h_{k-1},h_k: %s"
          % (k, "".join(labs), na, nb, bool(good), ok_z,
             interlace_A(h_from_N(N[k - 1], k - 1) if h_from_N(N[k - 1], k - 1)[-1] > 0 else [-c for c in h_from_N(N[k - 1], k - 1)],
                         B if B[-1] > 0 else [-c for c in B])[0]))
    if not good or not ok_z:
        fails += 1
print("sec5 checks: %d failures" % fails)
sys.exit(1 if fails else 0)
