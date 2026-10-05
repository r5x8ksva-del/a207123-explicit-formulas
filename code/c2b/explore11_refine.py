# -*- coding: utf-8 -*-
"""探索 11：
 (a) E(k,m,s) 的「最终」单项性：k>=3s-1 时 E(k,m,s) 是 k 的 m+s-2 次多项式 P（由定理 4 的公式）。
     P = A*C(k+c,d) ⇔ d = deg P 且 P 的根恰为 d 个相邻整数。用精确插值求 P，再数整数根。
 (b) 两项 u 型（E 的 m=3、U 的 m=2）：统计 不可解 / 可解但真检验<5 / 可解且>=5 的形状对个数。
"""
import sys, os, time
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp, binom, E_asc
from polylib import interpolate, peval

t0 = time.time()
print('(a) eventual single-term test for E(k,m,s), polynomial in k for k>=3s-1:')
res = {}
for m in range(1, 9):
    for s in range(1, 7):
        deg = m + s - 2
        ks = list(range(3 * s - 1, 3 * s - 1 + deg + 3))
        P = interpolate(ks, [E_asc(k, m, s) for k in ks])
        # 再用更大的 k 验证插值（确认次数）
        okfit = all(peval(P, k) == E_asc(k, m, s) for k in range(3 * s - 1, 3 * s + 40))
        roots = [r for r in range(-300, 301) if peval(P, r) == 0]
        consecutive = len(roots) == deg and (deg == 0 or roots == list(range(roots[0], roots[0] + deg)))
        res[(m, s)] = (okfit, len(P) - 1, roots, consecutive)
single = sorted(key for key, v in res.items() if v[3])
print('   (m,s) whose eventual polynomial is A*C(k+c,deg):', single)
print('   examples of integer roots:', {key: res[key][2] for key in [(2, 2), (2, 3), (3, 2), (1, 3), (4, 1)]})
print('   all interpolations confirmed on 40 extra k:', all(v[0] for v in res.values()))

print('(b) two-term u-shape: refuted / consistent<5 checks / consistent>=5 checks')
src = open(os.path.join(HERE, 'explore7_more_search.py'), encoding='utf-8').read()
ns = {}
exec('from fractions import Fraction\nfrom formulas import binom\n' +
     src[src.index('def test_two'):src.index("print('(ii) two-term u-shape search:')")], ns)
test_two = ns['test_two']
K = 30
T = core.U_fast_table(K, 6)
for name, m in (('E', 3), ('U', 2), ('E', 4), ('U', 3)):
    tot, asc = refined_dp(K, m)
    V = [sum(asc[k]) for k in range(K + 1)] if name == 'E' else [T[k][m] for k in range(K + 1)]
    shapes = [(c, d) for c in range(-6, 3 * m + 7) for d in range(-3, 2 * m + 5)]
    cnt = [0, 0, 0]
    low = []
    for i1, (c1, d1) in enumerate(shapes):
        for (c2, d2) in shapes[i1 + 1:]:
            if c1 + 2 * d1 == c2 + 2 * d2:
                continue
            ok, ch = test_two(V, c1, d1, c2, d2)
            if not ok:
                cnt[0] += 1
            elif ch < 5:
                cnt[1] += 1
                if len(low) < 5:
                    low.append((c1, d1, c2, d2, ch))
            else:
                cnt[2] += 1
    print('   %s m=%d: refuted %d, consistent with <5 checks %d %s, consistent with >=5 checks %d' % (name, m, cnt[0], cnt[1], low, cnt[2]))
print('elapsed %.1fs' % (time.time() - t0))
