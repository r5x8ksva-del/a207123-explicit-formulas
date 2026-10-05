# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 4：两项 u 型（c2b-S4）。

背景：作者在 explore7 里对 E m=5,6、U m=4,5,6 只统计了「相容且检验数>=5」的形状对，
而声称是「盒内无任何可解形状对 / 没有检验不足的对」。相容但检验数<5 的对只可能出现在
活跃未知数 n1+n2 >= 27 的对里（31 个方程，检验数 = 31 - 秩 >= 31-(n1+n2)），
本脚本对这些 m 把 n1+n2 >= 27 的对全部重测，统计「相容」的对（不论检验数）。
另：对 E m=3、U m=2 做 k0=1,2 的稳健性（只要求 k>=k0 成立）。

用法：py -3.14 r4_twoterm.py [mode]   mode = big | k0
"""
import sys, os, time
from math import comb
from fractions import Fraction
from multiprocessing import Pool

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


K = 30


def split_dp(K, m):
    comp = [0] * (K + 1)
    ascd = [0] * (K + 1)
    comp[0] = 1
    if K >= 1:
        comp[1] = m + 1
    st = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for (a, b), v in st.items():
        if a < b:
            ascd[2] += v
        else:
            comp[2] += v
    for k in range(3, K + 1):
        nst = {}
        for (a, b), v in st.items():
            for c in range(m + 1):
                if good(a, b, c):
                    nst[(b, c)] = nst.get((b, c), 0) + v
        st = nst
        for (b, c), v in st.items():
            if b < c:
                ascd[k] += v
            else:
                comp[k] += v
    return comp, ascd


def fam_cols(c, d, kmax):
    out = []
    for s in range(0, kmax + 40):
        r = d + s
        if r < 0:
            continue
        if max(0, r + 2 * s - c) <= kmax:
            out.append(s)
        else:
            break
    return out


def solve_two(V, c1, d1, c2, d2, k0):
    kmax = len(V) - 1
    cols = [(0, s) for s in fam_cols(c1, d1, kmax)] + [(1, s) for s in fam_cols(c2, d2, kmax)]
    fam = [(c1, d1), (c2, d2)]
    piv = {}
    checks = 0
    for k in range(k0, kmax + 1):
        row = {}
        for (f, s) in cols:
            c, d = fam[f]
            v = C(k + c - 2 * s, d + s)
            if v:
                row[(f, s)] = Fraction(v)
        rhs = Fraction(V[k])
        for pc in [p for p in row if p in piv]:
            fct = row.get(pc, 0)
            if not fct:
                continue
            prow, prhs = piv[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - fct * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= fct * prhs
        if not row:
            if rhs != 0:
                return False, checks
            checks += 1
            continue
        pc = max(row)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items()}
        prhs = rhs * inv
        for q in list(piv):
            qrow, qrhs = piv[q]
            fct = qrow.get(pc, 0)
            if fct:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - fct * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                piv[q] = (qrow, qrhs - fct * prhs)
        piv[pc] = (prow, prhs)
    return True, checks


TAB = {}


def init():
    for m in range(0, 7):
        cp, ad = split_dp(K, m)
        TAB[('E', m)] = ad
        TAB[('U', m)] = [cp[k] + ad[k] for k in range(K + 1)]


def work(args):
    name, m, c1, d1, c2, d2, k0 = args
    ok, ch = solve_two(TAB[(name, m)], c1, d1, c2, d2, k0)
    return (name, m, c1, d1, c2, d2, k0, ok, ch)


def pairs_for(m, minunk=None):
    shapes = [(c, d) for c in range(-6, 3 * m + 7) for d in range(-3, 2 * m + 5)]
    out = []
    for i, (c1, d1) in enumerate(shapes):
        n1 = len(fam_cols(c1, d1, K))
        for (c2, d2) in shapes[i + 1:]:
            if c1 + 2 * d1 == c2 + 2 * d2:
                continue
            if minunk is not None and n1 + len(fam_cols(c2, d2, K)) < minunk:
                continue
            out.append((c1, d1, c2, d2))
    return out


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'big'
    T0 = time.time()
    init()
    jobs = []
    if mode == 'big':
        for name, ms in (('E', (3, 4, 5, 6)), ('U', (2, 3, 4, 5, 6))):
            for m in ms:
                ps = pairs_for(m, 27)
                tot = len(pairs_for(m))
                print('%s m=%d: total pairs %d, pairs with n1+n2>=27: %d' % (name, m, tot, len(ps)), flush=True)
                jobs += [(name, m, c1, d1, c2, d2, 0) for (c1, d1, c2, d2) in ps]
    else:
        for name, m in (('E', 3), ('U', 2)):
            ps = pairs_for(m)
            for k0 in (1, 2):
                jobs += [(name, m, c1, d1, c2, d2, k0) for (c1, d1, c2, d2) in ps]
            print('%s m=%d: %d pairs x k0 in {1,2}' % (name, m, len(ps)), flush=True)
    print('jobs: %d' % len(jobs), flush=True)
    with Pool(4, initializer=init) as pool:
        res = pool.map(work, jobs, chunksize=200)
    summ = {}
    for (name, m, c1, d1, c2, d2, k0, ok, ch) in res:
        key = (name, m, k0)
        d = summ.setdefault(key, {'tested': 0, 'consistent': 0, 'lt5': 0, 'ex': []})
        d['tested'] += 1
        if ok:
            d['consistent'] += 1
            if ch < 5:
                d['lt5'] += 1
            if len(d['ex']) < 8:
                d['ex'].append((c1, d1, c2, d2, ch))
    for key in sorted(summ):
        d = summ[key]
        print('%s m=%d k0=%d: tested %d, consistent %d (of which checks<5: %d) examples %s' %
              (key[0], key[1], key[2], d['tested'], d['consistent'], d['lt5'], d['ex']), flush=True)
    print('[time] %.1fs' % (time.time() - T0))
