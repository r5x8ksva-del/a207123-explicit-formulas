# -*- coding: utf-8 -*-
"""探索 4：单和形状穷举搜索（任务 (b)(c)）。

目标数列（全部来自直接 DP / 容斥，k<=30，m 或 q <= 12）：
  E[m][k]   以上升结尾（截断块部分）
  U[m][k]   全部
  A[m][k]   不以上升结尾（完整部分；理论上有已知单和，用于检验搜索引擎能否找回）
  N[q][k], Nc[q][k], NE[q][k]   合法满射词（全部 / 不以上升结尾 / 以上升结尾）
形状族：V(k) = sum_s A(m,s) C(k + alpha*m + beta - gamma*s, delta*m + eps*s + zeta)
参数盒：alpha∈{-1..2}, beta∈{-3..3}, gamma∈{0..3}, delta∈{0,1,2}, eps∈{-1..3}, zeta∈{-3..3}（共 11760 组）。
对每个 m（或 q）=1..12 单独判定可解性（A(m,s) 允许任意有理数），族存活 ⇔ 全部 12 个 m 都可解。
"""
import sys, os, time, json
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp, binom
from search import test_shape, solution

K, MM = 30, 12
t0 = time.time()
T = core.U_fast_table(K, MM)
E = {}; U = {}; A = {}
for m in range(0, MM + 1):
    tot, asc = refined_dp(K, m)
    U[m] = [T[k][m] for k in range(K + 1)]
    E[m] = [sum(asc[k]) for k in range(K + 1)]
    A[m] = [U[m][k] - E[m][k] for k in range(K + 1)]
    assert all(sum(tot[k]) == U[m][k] for k in range(K + 1))

def incl_excl(tab, k, q, base_empty=1):
    # tab_{-1}(k) = base_empty*[k==0]（U、A 为 1：空词计入；E 为 0：空词不以上升结尾）
    s = 0
    for i in range(q + 1):
        u = (base_empty if k == 0 else 0) if i == 0 else tab[i - 1][k]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s

N = {}; Nc = {}; NE = {}
for q in range(1, MM + 1):
    N[q] = [incl_excl(U, k, q) for k in range(K + 1)]
    Nc[q] = [incl_excl(A, k, q) for k in range(K + 1)]
    NE[q] = [incl_excl(E, k, q, 0) for k in range(K + 1)]
    assert all(N[q][k] == Nc[q][k] + NE[q][k] for k in range(K + 1))
    assert all(N[q][k] == core.N_from_U(T, k, q) for k in range(K + 1))
print('targets built %.1fs' % (time.time() - t0))

ALPHA = range(-1, 3); BETA = range(-3, 4); GAMMA = range(0, 4)
DELTA = range(0, 3); EPS = range(-1, 4); ZETA = range(-3, 4)

def scan(target, name):
    t1 = time.time()
    per = {}   # (m, c, g, d, e) -> (consistent, checks, free)
    for m in range(1, MM + 1):
        V = target[m]
        cs = sorted({a * m + b for a in ALPHA for b in BETA})
        ds = sorted({dl * m + z for dl in DELTA for z in ZETA})
        for c in cs:
            for d in ds:
                for g in GAMMA:
                    for e in EPS:
                        ok, nch, nfree, ff = test_shape(V, c, g, d, e)
                        per[(m, c, g, d, e)] = (ok, nch, nfree)
    # 族
    fam_total = 0; fam_survive = []; fam_informative_survive = []
    n_informative = 0
    for a in ALPHA:
        for b in BETA:
            for g in GAMMA:
                for dl in DELTA:
                    for e in EPS:
                        for z in ZETA:
                            fam_total += 1
                            res = [per[(m, a * m + b, g, dl * m + z, e)] for m in range(1, MM + 1)]
                            checks = sum(r[1] for r in res if r[0])
                            informative = (g + e >= 2)
                            if informative:
                                n_informative += 1
                            if all(r[0] for r in res):
                                fam_survive.append(((a, b, g, dl, e, z), checks, [r[1] for r in res], [r[2] for r in res]))
                                if informative:
                                    fam_informative_survive.append(((a, b, g, dl, e, z), checks))
    # 每个 m 上有多少 (c,g,d,e) 可解且有 >=5 次真检验
    perm_hits = {}
    for (m, c, g, d, e), (ok, nch, nfree) in per.items():
        if ok and nch >= 5 and g + e >= 2:
            perm_hits.setdefault(m, []).append((c, g, d, e, nch, nfree))
    print('[%s] families: total=%d, informative(gamma+eps>=2)=%d, surviving(all m=1..12)=%d, informative surviving=%d  (%.1fs)'
          % (name, fam_total, n_informative, len(fam_survive), len(fam_informative_survive), time.time() - t1))
    for f, ch in fam_informative_survive[:40]:
        print('    informative survivor', f, 'total checks', ch)
    for m in sorted(perm_hits):
        hits = perm_hits[m]
        print('    m/q=%2d: per-m shapes with gamma+eps>=2 consistent & >=5 checks: %d  e.g. %s' % (m, len(hits), hits[:6]))
    return per, fam_survive, fam_informative_survive

results = {}
for target, name in [(A, 'A_complete'), (E, 'E_ascent'), (U, 'U_all'), (N, 'N_surj'), (Nc, 'Nc_surj_complete'), (NE, 'NE_surj_ascent')]:
    per, fs, fis = scan(target, name)
    results[name] = {'n_survive': len(fs), 'informative_survivors': [list(f) + [ch] for f, ch in fis]}

# 找回检验：A 的已知形状 (alpha,beta,gamma,delta,eps,zeta) = (1,0,2,1,1,0)，A(m,s)=S(m+s,m)
from formulas import stirling2
ok = True
for m in range(1, MM + 1):
    sol = solution(A[m], m, 2, m, 1)
    if sol is None or any(sol[s] != stirling2(m + s, m) for s in sol):
        ok = False
print('recovery check: A_m(k) shape (1,0,2,1,1,0) has unique solution A(m,s)=S(m+s,m) for m=1..12:', ok)
with open(os.path.join(os.path.dirname(HERE), '..', 'logs', 'c2b_search_results.json'), 'w', encoding='utf-8') as fh:
    json.dump(results, fh, ensure_ascii=False, indent=1)
print('total %.1fs' % (time.time() - t0))
