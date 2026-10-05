# -*- coding: utf-8 -*-
"""探索 7：
 (i)  E(k,m,s) 是否能写成单项 A(m,s)*C(k+c', d')（对每个 (m,s) 找所有可行 (c',d')）；
 (ii) 两项 u 型：V(k) = sum_s [A_s C(k+c1-2s, d1+s) + B_s C(k+c2-2s, d2+s)]，对 E 和 U 搜索 (c1,d1,c2,d2) 盒子；
 (iii) u 型阻碍定理扩展到 m <= 30。
"""
import sys, os, time
from fractions import Fraction
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp, binom, E_asc
from explore5_ushape_obstruction import obstruction

t0 = time.time()
K, MM = 30, 12
T = core.U_fast_table(K, MM)
DPs = {m: refined_dp(K, m) for m in range(MM + 1)}

# (i) single-term test for E(k,m,s), k = 0..K
print('(i) E(k,m,s) = A * C(k+c, d) single-term test (k<=%d):' % K)
bad_pairs = []
good_pairs = {}
for m in range(1, MM + 1):
    tot, asc = DPs[m]
    for s in range(1, 9):
        V = [asc[k][s] for k in range(K + 1)]
        if not any(V):
            continue
        sols = []
        for c in range(-3 * s - 6, 3 * m + 6):
            for d in range(0, 3 * m + 3 * s + 6):
                ratio = None; ok = True
                for k in range(K + 1):
                    b = binom(k + c, d)
                    if b == 0:
                        if V[k] != 0:
                            ok = False; break
                    else:
                        r = Fraction(V[k], b)
                        if ratio is None:
                            ratio = r
                        elif r != ratio:
                            ok = False; break
                if ok and ratio is not None and ratio != 0:
                    nz = sum(1 for k in range(K + 1) if binom(k + c, d))
                    sols.append((c, d, ratio, nz))
        if sols:
            good_pairs[(m, s)] = sols
        else:
            bad_pairs.append((m, s))
print('   (m,s) with a single-term representation:', sorted(good_pairs.keys()))
print('   examples:', {key: [(c, d, str(r)) for c, d, r, nz in v[:2]] for key, v in list(good_pairs.items())[:12]})
print('   (m,s) with NO single-term representation (in the c,d box):', bad_pairs[:40], '... total', len(bad_pairs))

# (ii) two-term u-shape search
def test_two(V, c1, d1, c2, d2):
    """精确增量消元，未知数 (fam, s)。返回 (consistent, checks)。"""
    Kk = len(V) - 1
    fams = [(c1, d1), (c2, d2)]
    cols = []
    for f, (c, d) in enumerate(fams):
        for s in range(0, Kk + 3):
            r = d + s
            if r < 0:
                continue
            kmin = max(0, r + 2 * s - c)
            if kmin <= Kk:
                cols.append((f, s))
    pivots = {}
    checks = 0
    for k in range(Kk + 1):
        row = {}
        for (f, s) in cols:
            c, d = fams[f]
            v = binom(k + c - 2 * s, d + s)
            if v:
                row[(f, s)] = Fraction(v)
        rhs = Fraction(V[k])
        for pc in [p for p in row if p in pivots]:
            coef = row.get(pc)
            if not coef:
                continue
            prow, prhs = pivots[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - coef * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= coef * prhs
        nz = [cc for cc, vv in row.items() if vv]
        if not nz:
            if rhs != 0:
                return False, checks
            checks += 1
            continue
        pc = min(nz)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items() if vv}
        prhs = rhs * inv
        for qc in list(pivots.keys()):
            qrow, qrhs = pivots[qc]
            coef = qrow.get(pc)
            if coef:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - coef * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                qrhs -= coef * prhs
                pivots[qc] = (qrow, qrhs)
        pivots[pc] = (prow, prhs)
    return True, checks

print('(ii) two-term u-shape search:')
for name in ['E', 'U']:
    for m in range(1, 7):
        tot, asc = DPs[m]
        V = [sum(asc[k]) for k in range(K + 1)] if name == 'E' else [T[k][m] for k in range(K + 1)]
        # 规范化：两族的类 N = c+2d+3 不同才有意义；盒子 c in [-6, 3m+6], d in [-3, 2m+4]
        hits = []
        ntest = 0
        rngc = range(-6, 3 * m + 7); rngd = range(-3, 2 * m + 5)
        shapes = [(c, d) for c in rngc for d in rngd]
        for i1, (c1, d1) in enumerate(shapes):
            for (c2, d2) in shapes[i1 + 1:]:
                if c1 + 2 * d1 == c2 + 2 * d2:
                    continue
                ntest += 1
                ok, ch = test_two(V, c1, d1, c2, d2)
                if ok and ch >= 5:
                    hits.append((c1, d1, c2, d2, ch))
        print('   %s m=%d: tested %d pairs of shapes, consistent with >=5 checks: %d  e.g. %s' % (name, m, ntest, len(hits), hits[:4]))

# (iii) obstruction up to m=30
print('(iii) u-shape obstruction for m<=30:')
for which in ['E', 'U']:
    fails = []
    for m in range(1, 31):
        res = obstruction(m, which)
        if not res[0]:
            fails.append(m)
    print('   %s: m in 1..30 WITHOUT obstruction certificate: %s' % (which, fails))
print('elapsed %.1fs' % (time.time() - t0))
