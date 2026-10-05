# -*- coding: utf-8 -*-
"""final-audit / math-c3 / a3: T3.8 data — dimension formulas vs the boxes printed in logs/verify_all_final.log,
plus an independent mod-p recomputation (new prime 2147483587, own elimination code) of every box in verify_all."""
import sys, os, re, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
ROOT = os.path.abspath(os.path.join(CODE, '..'))
sys.path.insert(0, CODE)
import core

T0 = time.time()
RES = []


def report(name, ok, msg):
    RES.append(bool(ok))
    print('%s %s :: %s' % ('PASS' if ok else 'FAIL', name, msg))
    sys.stdout.flush()


# report's formulas (04_C3.md T3.8), with the stated boundary conditions
def fU(A, B, D):
    return (A - 2) * B * D * (D + 1) // 2 if (A >= 3 and B >= 1 and D >= 1) else 0


def fUs(A, B, Dk, Dm):
    return (A - 2) * B * (Dk + 1) * Dm if (A >= 3 and B >= 1 and Dm >= 1) else 0


def fN(A, B, D):
    return (A - 2) * (B - 1) * D * (D + 1) // 2 if (A >= 3 and B >= 2 and D >= 1) else 0


def fNs(A, B, Dk, Dq):
    return (A - 2) * (B - 1) * (Dk + 1) * Dq if (A >= 3 and B >= 2 and Dq >= 1) else 0


log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read()
lines = {m.group(1): m.group(0) for m in re.finditer(r'PASS (C3B-[A-Z0-9]+) .*', log)}
boxes = {}
for tag, f, nargs in (('C3B-E2', fU, 3), ('C3B-E2S', fUs, 4), ('C3B-E3B', fN, 3), ('C3B-E3S', fNs, 4)):
    ln = lines[tag]
    pat = r'\(' + ', '.join([r'(\d+)'] * nargs) + r'\):(\d+)u/(\d+)eq ker=(\d+) pred=(\d+) gens=(\d+)'
    found = [tuple(int(g) for g in mm.groups()) for mm in re.finditer(pat, ln)]
    boxes[tag] = found
ok = True
summary = []
for tag, f, nargs in (('C3B-E2', fU, 3), ('C3B-E2S', fUs, 4), ('C3B-E3B', fN, 3), ('C3B-E3S', fNs, 4)):
    zeros = 0
    for bx in boxes[tag]:
        par = bx[:nargs]
        u, eq, ker, pred, gens = bx[nargs:]
        ok &= (ker == pred == gens == f(*par))
        zeros += (ker == 0)
    summary.append('%s: %d boxes (%d with dim 0)' % (tag, len(boxes[tag]), zeros))
nU = len(boxes['C3B-E2']) + len(boxes['C3B-E2S'])
nN = len(boxes['C3B-E3B']) + len(boxes['C3B-E3S'])
zU = sum(1 for bx in boxes['C3B-E2'] + boxes['C3B-E2S'] if bx[-3] == 0)
zN = sum(1 for bx in boxes['C3B-E3B'] + boxes['C3B-E3S'] if bx[-3] == 0)
report('T3.8-log-vs-formula', ok and nU == 11 and nN == 11 and zU == 3 and zN == 3 and len(boxes['C3B-E2']) == 8 and len(boxes['C3B-E3B']) == 8,
       'every box in verify_all_final.log satisfies ker == pred == gens == report formula (with its boundary conditions); ' + '; '.join(summary) +
       '; U total %d (dim0: %d), N total %d (dim0: %d)' % (nU, zU, nN, zN))

konly = {}
for tag in ('C3B-E1', 'C3B-E3A'):
    konly[tag] = [tuple(int(g) for g in mm.groups()) for mm in re.finditer(r'\(A,B,deg\)=\((\d+),(\d+),(\d+)\):(\d+) unknowns/(\d+) eqs rank (\d+)', lines[tag])]
want = [(6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8)]
ok = all([bx[:3] for bx in konly[t]] == want and all(bx[3] == bx[5] for bx in konly[t]) for t in konly)
report('T3.8-konly-log', ok, 'C3B-E1 / C3B-E3A parameter lists == report (6,6,6),(10,3,6),(3,10,6),(4,4,12),(15,1,8),(1,15,8); all full column rank')

# ------------------------------------------------------------------------------------------------
# independent recomputation mod a new prime
# ------------------------------------------------------------------------------------------------
p = 2147483587
K = M = 40
T = core.U_fast_table(K, M)
NT = [[core.N_from_U(T, k, q) for q in range(M + 1)] for k in range(K + 1)]


def rank_mod(Mx, p):
    Mx = Mx.copy() % p
    rows, cols = Mx.shape
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        piv = None
        nzr = np.nonzero(Mx[r:, c])[0]
        if len(nzr) == 0:
            continue
        piv = r + nzr[0]
        if piv != r:
            Mx[[r, piv]] = Mx[[piv, r]]
        inv = pow(int(Mx[r, c]), p - 2, p)
        Mx[r] = (Mx[r] * inv) % p
        col = Mx[:, c].copy()
        col[r] = 0
        nzrows = np.nonzero(col)[0]
        if len(nzrows):
            Mx[nzrows] = (Mx[nzrows] - (col[nzrows, None] * Mx[r][None, :]) % p) % p
        r += 1
    return r


def build(tab, A, B, monos):
    unk = [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]
    rows = []
    for k in range(A, K + 1):
        for m in range(B, M + 1):
            row = [(pow(k, i, p) * pow(m, j, p) % p) * (tab[k - a][m - b] % p) % p for (a, b, i, j) in unk]
            rows.append(row)
    return np.array(rows, dtype=np.int64), len(unk)


def monos_total(D):
    return [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]


def monos_sep(Dk, Dm):
    return [(i, j) for i in range(Dk + 1) for j in range(Dm + 1)]


def monos_konly(d):
    return [(i, 0) for i in range(d + 1)]


ok = True
out = []
for tag, tab, kind, f in (('C3B-E2', T, 'tot', fU), ('C3B-E2S', T, 'sep', fUs), ('C3B-E3B', NT, 'tot', fN), ('C3B-E3S', NT, 'sep', fNs)):
    for bx in boxes[tag]:
        if kind == 'tot':
            A, B, Dd = bx[:3]
            monos = monos_total(Dd)
            pred = f(A, B, Dd)
        else:
            A, B, Dk, Dm = bx[:4]
            monos = monos_sep(Dk, Dm)
            pred = f(A, B, Dk, Dm)
        Mx, nu = build(tab, A, B, monos)
        r = rank_mod(Mx, p)
        ker = nu - r
        ok &= (ker == pred) and nu == bx[-5] and Mx.shape[0] == bx[-4]
        out.append('%s%s:%d' % ('U' if tab is T else 'N', bx[:-5], ker))
print('#   ' + '; '.join(out))
report('T3.8-recompute', ok, 'own mod-%d elimination: kernel dimension == report formula and unknown/equation counts == log, for all 22 (k,m)/(k,q)-coefficient boxes in verify_all' % p)

ok = True
for tag, tab in (('C3B-E1', T), ('C3B-E3A', NT)):
    for (A, B, d) in want:
        Mx, nu = build(tab, A, B, monos_konly(d))
        r = rank_mod(Mx, p)
        ok &= (r == nu)
report('T3.8-konly-recompute', ok, 'own mod-%d elimination: the 6 k-only parameter sets are full column rank for U and for N' % p)

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a3 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
