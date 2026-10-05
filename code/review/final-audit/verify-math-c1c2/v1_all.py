# -*- coding: utf-8 -*-
"""Adversarial verification of auditor math-c1c2 findings #0..#4 (read-only).

Run:  PYTHONUTF8=1 py -3.14 v1_all.py
"""
import os, re, sys, math
from fractions import Fraction as Fr
from decimal import Decimal, getcontext

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
LOGS = os.path.join(ROOT, 'logs')
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402

def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read()

print('=' * 72)
print('[Q] exact quote presence')
quotes = [
    (0, '03_C2.md', '其余奇数形状【已验证（数值，浮点纤维检验 α≥1、α+β≤12，只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3）】'),
    (1, '03_C2.md', '主 Agent 与审计者共 6 次运行的范围：F4 最快，H、F3 最慢；见 logs/c2a_e5_bench_K200_M30.log 与各次 verify_all 日志的 c2a.bench_k200_m30 行；复核者机器负载高时整体慢约 3 倍'),
    (2, '03_C2.md', '要用 k≤60 才全部被反驳（复核者 r-c2b，logs/review_r-c2b_r4b_full.log，不在 verify_all 中；verify_all 只复现 E m=3、U m=2）'),
    (3, '03_C2.md', 'x⁵−v_0(1−x)³）在实轴上都严格单调'),
    (4, '02_C1.md', 'ρ_m 为 y³=y²+m 的实根，x_m=1/ρ_m'),
]
rep = rd(os.path.join(ROOT, '报告.md'))
for i, fn, q in quotes:
    t = rd(os.path.join(PARTS, fn))
    print('  #%d %s count_in_part=%d count_in_report=%d' % (i, fn, t.count(q), rep.count(q)))

# ---------------------------------------------------------------- #0
print('=' * 72)
print('[#0] grade definition and float-only evidence')
head = rd(os.path.join(PARTS, '00_head.md'))
m = re.search(r'【已验证】= ([^；]*)；', head)
print('  00_head definition of 已验证:', m.group(1) if m else None)
task = rd(os.path.join(ROOT, 'notes', '原始任务说明.md'))
print('  original task: verify_all must cover every 已验证 ->', '覆盖报告里每一条【已验证】' in task)
r4 = rd(os.path.join(LOGS, 'review_r-c2a_r4_negative.log'))
print('  r-c2a r4 log odd_shapes line:', [l for l in r4.splitlines() if 'odd_shapes_fiber' in l])
vf = rd(os.path.join(LOGS, 'verify_all_final.log'))
print('  verify_all_final mentions odd_shapes / fiber test:', ('odd_shapes' in vf), ('fiber-point' in vf))
failed = rd(os.path.join(PARTS, '08_failed.md'))
print('  08_failed says float only:', '其余奇数形状只有浮点纤维检验' in failed)
c3 = rd(os.path.join(PARTS, '04_C3.md'))
print('  precedent: numeric-only Gevrey claim labelled 猜想 in 04_C3:', '【猜想】f_k(t) 呈 Gevrey-1/3 增长' in c3)

# independent float fiber test + high-precision margins
getcontext().prec = 60

def xi_dec():
    x = Decimal('0.68')
    for _ in range(200):
        f = 1 - x - x ** 3
        fp = -1 - 3 * x ** 2
        x = x - f / fp
    return x

XI = xi_dec()

class C:
    __slots__ = ('r', 'i')
    def __init__(s, r, i=Decimal(0)):
        s.r = Decimal(r); s.i = Decimal(i)
    def __add__(s, o):
        o = o if isinstance(o, C) else C(o); return C(s.r + o.r, s.i + o.i)
    __radd__ = __add__
    def __sub__(s, o):
        o = o if isinstance(o, C) else C(o); return C(s.r - o.r, s.i - o.i)
    def __rsub__(s, o):
        return C(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, C) else C(o)
        return C(s.r * o.r - s.i * o.i, s.r * o.i + s.i * o.r)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = o if isinstance(o, C) else C(o)
        d = o.r * o.r + o.i * o.i
        return C((s.r * o.r + s.i * o.i) / d, (s.i * o.r - s.r * o.i) / d)
    def __rtruediv__(s, o):
        return C(o) / s
    def abs(s):
        return (s.r * s.r + s.i * s.i).sqrt()

def fiber_coeffs_dec(al, be):
    n = al + be
    v0 = XI ** n / (1 - XI) ** be
    co = [Decimal(0)] * (n + 1)  # ascending
    co[n] += 1
    for i in range(be + 1):
        co[i] -= v0 * math.comb(be, i) * (-1) ** i
    return co, v0

def peval(co, z):
    acc = C(0); dacc = C(0)
    for c in reversed(co):
        dacc = dacc * z + acc
        acc = acc * z + c
    return acc, dacc

def refine(co, z0):
    z = C(Decimal(repr(z0.real)), Decimal(repr(z0.imag)))
    for _ in range(80):
        f, fp = peval(co, z)
        if fp.abs() == 0:
            break
        z = z - f / fp
    return z

not_excl = []
min_margin = None
witness = {}
for n in range(2, 13):
    for al in range(1, n + 1):
        be = n - al
        co, v0 = fiber_coeffs_dec(al, be)
        npco = np.array([float(c) for c in reversed(co)], dtype=float)
        rts = np.roots(npco)
        crit = Fr(n, al)
        best = None
        for r in rts:
            z = refine(co, complex(r))
            if z.abs() < Decimal('1e-30') or (z - 1).abs() < Decimal('1e-30') or (z - C(Decimal(crit.numerator) / Decimal(crit.denominator))).abs() < Decimal('1e-30'):
                continue
            w = (1 - z) / (z * z * z)
            # margin: how far w is from the set of positive integers
            if w.r < Decimal('0.5'):
                marg = max(abs(w.i), Decimal('0.5') - w.r)
            else:
                nearest = Decimal(int(w.r.to_integral_value()))
                marg = max(abs(w.i), abs(w.r - nearest))
            if best is None or marg > best[0]:
                best = (marg, z, w)
        if best is None or best[0] < Decimal('1e-20'):
            not_excl.append((al, be))
        else:
            witness[(al, be)] = best
            if min_margin is None or best[0] < min_margin[0]:
                min_margin = (best[0], (al, be))
print('  own fiber test (numpy roots + 60-digit Newton): shapes not excluded =', not_excl)
print('  smallest exclusion margin over excluded shapes = %.3e at %s' % (float(min_margin[0]), min_margin[1]))
for sh in [(1, 2), (2, 3), (1, 4), (3, 2), (4, 1)]:
    mg, z, w = witness[sh]
    print('    %s witness eta=%.6f%+.6fi, w=%.4f%+.4fi, margin %.3e' % (sh, float(z.r), float(z.i), float(w.r), float(w.i), float(mg)))
print('  NOTE: still floating/high-precision numerics, no interval arithmetic -> data, not proof')

# ---------------------------------------------------------------- #1
print('=' * 72)
print('[#1] bench_k200_m30 runs')
runs = {
    'c2a_e5_bench_K200_M30.log': 'c2a author (round 1 exploration e5_bench.py)',
    'c2a_check_run.log': 'c2a author (round 1 check_c2a run)',
    'verify_all_run1.log': 'main agent (verify_all)',
    'verify_all_final.log': 'main agent (verify_all)',
    'audit_a3-requirements_verify_rerun.log': 'auditor a3 (verify_all rerun)',
    'review_x2-dfinite_check_c2a_run.log': 'reviewer x2 (check_c2a)',
    'review_r-c2a_checkrun.log': 'reviewer r-c2a (check_c2a, high load)',
    'review_x1-single-sum_check_c2a.log': 'reviewer x1 (check_c2a, high load)',
}
data = {}
for fn in runs:
    t = rd(os.path.join(LOGS, fn))
    if fn.startswith('c2a_e5'):
        d = {}
        for l in t.splitlines():
            mm = re.match(r'\s+(.*?)\s+([0-9.]+)s\s+equal_to_DP=True', l)
            if mm:
                d[mm.group(1).strip()] = float(mm.group(2))
        lem = d['Lemma1 recurrence']
        expl = {k: v for k, v in d.items() if k.startswith(('H form', 'F3', 'Theta', 'H-outer', 'F4'))}
        data[fn] = (lem, expl, d)
    else:
        l = [x for x in t.splitlines() if 'bench_k200_m30' in x][0]
        d = {k: float(v) for k, v in re.findall(r'(DP|Lemma1|linrec|Ntri|rStirling_table|c_table|H|F3|Theta|ThetaH|F4) ([0-9.]+)', l.split('seconds')[1])}
        lem = d['Lemma1']
        expl = {k: d[k] for k in ('H', 'F3', 'Theta', 'ThetaH', 'F4')}
        data[fn] = (lem, expl, d)
for fn, who in runs.items():
    lem, expl, d = data[fn]
    lo = min(expl.values()); hi = max(expl.values())
    print('  %-42s %-45s lemma1 %.3f  explicit %.3f-%.3f  fastest=%s slowest=%s ratio %.0f-%.0f' % (
        fn, who, lem, lo, hi, min(expl, key=expl.get), max(expl, key=expl.get), lo / lem, hi / lem))
normal = [fn for fn in runs if 'high load' not in runs[fn]]
cited = ['c2a_e5_bench_K200_M30.log', 'verify_all_run1.log', 'verify_all_final.log', 'audit_a3-requirements_verify_rerun.log']
def rng(fns):
    lo = min(min(data[f][1].values()) for f in fns); hi = max(max(data[f][1].values()) for f in fns)
    llo = min(data[f][0] for f in fns); lhi = max(data[f][0] for f in fns)
    rlo = min(min(data[f][1].values()) / data[f][0] for f in fns); rhi = max(max(data[f][1].values()) / data[f][0] for f in fns)
    return lo, hi, llo, lhi, rlo, rhi
print('  all 6 normal-load runs: explicit %.3f-%.3f s, lemma1 %.3f-%.3f, ratio %.0f-%.0f' % rng(normal))
print('  only the cited logs (e5 + verify_all-type logs): explicit %.3f-%.3f s, lemma1 %.3f-%.3f, ratio %.0f-%.0f' % rng(cited))
mainaud = ['verify_all_run1.log', 'verify_all_final.log', 'audit_a3-requirements_verify_rerun.log']
print('  only main agent + auditor surviving logs: explicit %.3f-%.3f s, lemma1 %.3f-%.3f, ratio %.0f-%.0f' % rng(mainaud))
print('  normal-load runs by main agent or auditor: %d of %d' % (sum(1 for f in normal if runs[f].startswith(('main', 'auditor'))), len(normal)))
# slowdown of the high-load runs
keys = ['DP', 'Lemma1', 'linrec', 'Ntri', 'c_table', 'H', 'F3', 'Theta', 'ThetaH', 'F4']
same_script = ['c2a_check_run.log', 'review_x2-dfinite_check_c2a_run.log']
vall = ['verify_all_run1.log', 'verify_all_final.log', 'audit_a3-requirements_verify_rerun.log']
for hf in ['review_r-c2a_checkrun.log', 'review_x1-single-sum_check_c2a.log']:
    hd = data[hf][2]
    r_same = [hd[k] / data[f][2][k] for f in same_script for k in keys]
    r_vall = [hd[k] / data[f][2][k] for f in vall for k in keys]
    r_all = r_same + r_vall
    med = sorted(r_all)[len(r_all) // 2]
    print('  %s slowdown vs same-script normal runs %.2f-%.2f ; vs verify_all runs %.2f-%.2f ; median over both %.2f' % (
        hf, min(r_same), max(r_same), min(r_vall), max(r_vall), med))
rc2a = rd(os.path.join(ROOT, 'notes', 'review', 'r-c2a-review.md'))
print('  r-c2a-review §1 says:', '绝对值大 3–5 倍' in rc2a)
# lower bound 0.2 appears only in uncited logs?
print('  F4 values: ' + ', '.join('%s=%.3f' % (f.split('.')[0], data[f][1].get('F4', data[f][1].get('F4 c_i partial fractions', float('nan'))) if 'F4' in data[f][1] else data[f][1]['F4 c_i partial fractions']) for f in normal))
st = {f: os.path.getmtime(os.path.join(LOGS, f)) for f in ['verify_all_final.log']}
st2 = os.path.getmtime(os.path.join(PARTS, '03_C2.md'))
print('  03_C2.md mtime < verify_all_final.log mtime:', st2 < st['verify_all_final.log'])

# ---------------------------------------------------------------- #2
print('=' * 72)
print('[#2] two-term box logs')
for fn in ['review_r-c2b_r4b_full.log', 'review_r-c2b_r4b_full_small.log', 'review_r-c2b_r4b_k60.log', 'review_r-c2b_r4c_example.log']:
    t = rd(os.path.join(LOGS, fn))
    print('  %-36s mentions k<=60: %-5s | lines: %s' % (fn, ('k<=60' in t or 'K=60' in t), ' || '.join(l.strip()[:90] for l in t.splitlines()[:6])))
ex = rd(os.path.join(LOGS, 'review_r-c2b_r4c_example.log'))
print('  example pairs inconsistent already at K=35:', all('INCONSISTENT' in l for l in ex.splitlines() if 'K=35' in l))
print('  verify_all_final twoterm line has E m=3 & U m=2 only:', 'E m=3: 46178 pairs, 0 solvable; U m=2: 25191 pairs, 0 solvable' in vf)

# ---------------------------------------------------------------- #3
print('=' * 72)
print('[#3] v_0 for shapes (1,2) and (2,3)')
# exact arithmetic in Q(xi), xi^3 = 1 - xi, basis (1, xi, xi^2)
def mul(a, b):
    c = [Fr(0)] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] += a[i] * b[j]
    # xi^4 = xi - xi^2 ; xi^3 = 1 - xi
    c4 = c[4]; c[1] += c4; c[2] -= c4
    c3 = c[3]; c[0] += c3; c[1] -= c3
    return [c[0], c[1], c[2]]
def powe(a, e):
    r = [Fr(1), Fr(0), Fr(0)]
    for _ in range(e):
        r = mul(r, a)
    return r
def inv(a):
    # solve a*x = 1 via 3x3 linear system
    cols = [mul(a, e) for e in ([Fr(1), Fr(0), Fr(0)], [Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)])]
    M = [[cols[j][i] for j in range(3)] + [Fr(1 if i == 0 else 0)] for i in range(3)]
    for c in range(3):
        p = next(r for r in range(c, 3) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][3] for i in range(3)]
X = [Fr(0), Fr(1), Fr(0)]
one_minus = [Fr(1), Fr(-1), Fr(0)]
v12 = mul(powe(X, 3), inv(powe(one_minus, 2)))
v23 = mul(powe(X, 5), inv(powe(one_minus, 3)))
print('  exact: v_(1,2)(xi) == xi^-3 :', v12 == inv(powe(X, 3)))
print('  exact: v_(2,3)(xi) == xi^-4 :', v23 == inv(powe(X, 4)))
print('  exact: v_(2,3)(xi) == xi^-3 :', v23 == inv(powe(X, 3)))
# with the wrong value v0 = xi^-3, is xi a root of x^5 - v0 (1-x)^3 ?
wrong = [a - b for a, b in zip(powe(X, 5), mul(inv(powe(X, 3)), powe(one_minus, 3)))]
print('  exact: xi^5 - xi^-3 (1-xi)^3 == 0 ?', all(c == 0 for c in wrong), ' (value in basis 1,xi,xi^2:', [str(c) for c in wrong], ')')
xf = float(XI)
print('  xi=%.12f  xi^-3=%.10f  xi^-4=%.10f' % (xf, xf ** -3, xf ** -4))
for (al, be, v0) in [(1, 2, xf ** -3), (2, 3, xf ** -4)]:
    n = al + be
    co = np.zeros(n + 1)
    co[0] = 1.0
    for i in range(be + 1):
        co[n - i] -= v0 * math.comb(be, i) * (-1) ** i
    rts = np.roots(co)
    real = [r.real for r in rts if abs(r.imag) < 1e-9]
    print('  shape (%d,%d): v0=%.6f real fiber roots=%s' % (al, be, v0, ['%.10f' % r for r in real]))
print('  (1,2) disc of f\'=3x^2-2v0x+2v0: 4v0(v0-6)=%.4f (<0 => strictly increasing)' % (4 * xf ** -3 * (xf ** -3 - 6)))
print('  (2,3) f\'=5x^4+3v0(1-x)^2>0 for every v0>0 (monotonicity does not depend on the value of v0)')
print('  ratio check: report interval (3.04,3.18) contains xi^-3:', 3.04 < xf ** -3 < 3.18, '; contains xi^-4:', 3.04 < xf ** -4 < 3.18)

# ---------------------------------------------------------------- #4
print('=' * 72)
print('[#4] rho_0')
for mm in range(0, 4):
    r = np.roots([1, -1, 0, -mm])
    print('  m=%d real roots of y^3-y^2-m: %s' % (mm, sorted(set(round(z.real, 10) for z in r if abs(z.imag) < 1e-7))))
U0 = core.U_list(0, 30)
print('  U_k(0) == 1 for k<=30:', all(u == 1 for u in U0), '=> G_0=1/(1-x), radius 1 = 1/rho_0 needs rho_0=1')
rho1 = [z.real for z in np.roots([1, -1, 0, -1]) if abs(z.imag) < 1e-9][0]
print('  x_1 = 1/rho_1 = %.6f < 1 (so the proof step works with rho_0=1)' % (1 / rho1))
print('  06_C5 inequality at m=1: rho_0^2 + m - 1 >= m  <=> rho_0^2 >= 1 : rho_0=1 ->', 1 + 0 >= 1, '; rho_0=0 ->', 0 + 0 >= 1)
c1p = rd(os.path.join(PARTS, '02_C1.md'))
print('  02_C1 states rho_0 convention anywhere:', ('ρ_0' in c1p))
c1n = rd(os.path.join(ROOT, 'notes', 'c1.md'))
print('  notes/c1.md has convention rho_0:=1 :', '约定 ρ_0:=1' in c1n)
c5n = rd(os.path.join(ROOT, 'notes', 'c5a.md'))
print('  notes/c5a.md has convention rho_0 := 1 :', 'ρ_0 := 1' in c5n)
print('  02_C1 T1.3(4) proof uses 1/rho_{m-1} with m>=1:', '收敛半径 1/ρ_{m−1}>x_m' in c1p and 'm≥1 时 y³−y²−m 只有一个实根' in c1p)
print('DONE')
