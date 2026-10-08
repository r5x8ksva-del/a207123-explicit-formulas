# -*- coding: utf-8 -*-
"""复核者 s14-b9（信息性，不是 PASS/FAIL 检查）：h_k 最高 NTOP 个系数相对首项的符号，在各剩余类中何时翻转。
方法与 r3_top.py 的 r3-recip 相同：只跟踪 G_{-j} 的顶端 L 层（G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2），再用互反式
  (-1)^k U_k(-(s_k+1+n)) = sum_{i=g-n}^{g} h_{k,i} C(i+s_k+n, k)（g=deg h_k=k-s_k，s_k=floor((k+2)/3)）
三角地解出 h_{k,g}, h_{k,g-1}, ...。前 1000 个 k 与自写 T1.7 递推逐个对照。
用法：py -3.14 r3b_top_layers.py [KTOP] [NTOP]（默认 30000、7）
"""
import sys
import time
from math import comb

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import h_rec_iter  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def main(KTOP, NTOP):
    t0 = time.time()
    L = 3 * NTOP + 6
    J0 = L // 3 + 3          # j>=J0 时 jx^2 项（在 G_{-j-1} 的第 3j-2 层）不进入前 L 层
    J1 = J0 + 6
    full = {1: [1]}
    for j in range(1, J1):
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

    def top_of(poly, j):
        deg = 3 * j - 3
        return [poly[deg - d] if deg - d >= 0 else 0 for d in range(L)]

    def step_top(top, j):
        return [(top[d - 3] if d >= 3 else 0) - (top[d - 2] if d >= 2 else 0) + j * top[d] for d in range(L)]
    assert all(step_top(top_of(full[j], j), j) == top_of(full[j + 1], j + 1) for j in range(J0, J1))
    tops = {j: top_of(full[j], j) for j in range(1, J1 + 1)}
    jmax = J1
    href = {}
    for k, h in h_rec_iter(600):
        href[k] = list(h[-NTOP:])
    flips = {(n, r): [] for n in range(1, NTOP) for r in range(3)}
    last = {}
    ok_ref = True
    for k in range(3, KTOP + 1):
        s = (k + 2) // 3
        g = k - s
        while jmax < s + NTOP:
            tops[jmax + 1] = step_top(tops[jmax], jmax)
            jmax += 1
        for jj in [x for x in tops if x < s]:
            del tops[jj]
        hs = {}
        nmax = min(NTOP - 1, g)
        for n in range(nmax + 1):
            j = s + 1 + n
            val = (-1) ** k * tops[j][3 * j - 3 - k]
            for i in range(g - n + 1, g + 1):
                val -= hs[i] * comb(i + s + n, k)
            hs[g - n] = val
        if k <= 600:
            ref = href[k]
            mine = [hs[g - n] for n in range(nmax + 1)]
            if mine != [ref[-1 - x] for x in range(nmax + 1)]:
                ok_ref = False
        lead = hs[g] > 0
        r = k % 3
        for n in range(1, nmax + 1):
            same = (hs[g - n] > 0) == lead
            key = (n, r)
            if key in last and last[key] != same:
                flips[key].append(k)
            last[key] = same
    print('互反式得到的最高 %d 个系数与 T1.7 递推一致（k<=600）：%s' % (NTOP, ok_ref))
    print('第 n 高系数（n=1 为次高项）与首项「同号」与否，各剩余类的末状态与翻转位置（3<=k<=%d）：' % KTOP)
    for n in range(1, NTOP):
        row = []
        for r in range(3):
            row.append('k≡%d: 末态 %s，翻转于 %s' % (r, '同号' if last.get((n, r)) else '异号', flips[(n, r)][:8]))
        print('  n=%d  ' % n + '；'.join(row))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    KTOP = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
    NTOP = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    main(KTOP, NTOP)
