# -*- coding: utf-8 -*-
"""s2：用独立 N 表（s1 生成，锚定到原始定义）复核 c4 第 (i) 部分关于 D(k,d)、p_d 的全部数值结论。
p_d 直接由 DP 数据在 k=2d+2..4d+2 处插值（与被复核者「递推 + 基点」构造法无关），再在更大范围核对。
用法：py -3.14 s2_pd.py [K]   （需要先运行 s1_build_N.py K）
"""
import sys, os, time, pickle, re
from fractions import Fraction
from math import comb, factorial
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, HERE)
from rlib import (ptrim, padd, psub, pmul, pscale, peval, pshift, interp, newton_coeffs, dfact)

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
K = int(sys.argv[1]) if len(sys.argv) > 1 else 100
t0 = time.time()
with open(os.path.join(HERE, 'N_K%d.pkl' % K), 'rb') as fh:
    N = pickle.load(fh)['N']


def Nv(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


def D(k, d):
    return Nv(k, k - d)


RES = []


def rep(tag, ok, msg):
    RES.append(ok)
    print(('OK  ' if ok else 'BAD ') + tag + ' ' + msg, flush=True)


# ---- C4-1 三角递推（k>=3,q>=1）与 k=2 的缺陷
ok = True
for k in range(3, K + 1):
    for q in range(1, k + 1):
        r = Nv(k - 1, q - 1) + Nv(k - 1, q) + (q - 1) * (Nv(k - 3, q - 2) + 2 * Nv(k - 3, q - 1) + Nv(k - 3, q))
        if r != Nv(k, q):
            ok = False
k2 = Nv(1, 1) + Nv(1, 2) + 1 * (0)  # k=2,q=2 公式值
rep('C4-1', ok and Nv(2, 2) == 2 and k2 == 1 and Nv(2, 1) == 1,
    '三角递推对独立 N 表 3<=k<=%d 全部成立；k=2 时公式给 N(2,2)=1 而真值 2（缺陷确认）' % K)

# ---- C4-3 D 递推
ok = True
for k in range(3, K + 1):
    for d in range(0, k):
        r = D(k - 1, d) + D(k - 1, d - 1) + (k - d - 1) * (D(k - 3, d - 1) + 2 * D(k - 3, d - 2) + D(k - 3, d - 3))
        if r != D(k, d):
            ok = False
rep('C4-3', ok, 'D 递推 3<=k<=%d, 0<=d<=k-1' % K)

# ---- C4-4
ok = all(D(k, 0) == 2 for k in range(2, K + 1)) and D(1, 0) == 1 and D(0, 0) == 1
ok = ok and all(D(k, 1) == k * k - k - 4 for k in range(4, K + 1)) and D(3, 1) == 4 and D(2, 1) == 1
rep('C4-4', ok, 'D(k,0)=2 (k>=2), D(k,1)=k^2-k-4 (4<=k<=%d)，例外值确认' % K)

# ---- p_d 由插值得到（独立于被复核者的构造）
MARGIN = 6
DMAX = (K - 2 - MARGIN) // 4
PD = {}
for d in range(0, DMAX + 1):
    xs = list(range(2 * d + 2, 4 * d + 3))
    PD[d] = interp(xs, [D(k, d) for k in xs])
print('p_d interpolated for d<=%d (K=%d, margin>=%d extra points)' % (DMAX, K, MARGIN))

ok_thr, ok_deg, ok_lead, ok_e1, ok_e0, ok_exc = True, True, True, True, True, True
first_bad = []
for d in range(0, DMAX + 1):
    p = PD[d]
    for k in range(2 * d + 2, K + 1):
        if peval(p, k) != D(k, d):
            ok_thr = False
            first_bad.append((d, k))
            break
    if len(p) - 1 != 2 * d:
        ok_deg = False
    if p[-1] != Fraction(2, 2 ** d * factorial(d)):
        ok_lead = False
    if D(2 * d + 1, d) - peval(p, 2 * d + 1) != (-1) ** (d + 1) * factorial(d + 1):
        ok_e1 = False
    if D(2 * d, d) - peval(p, 2 * d) != Fraction((-1) ** (d + 1) * factorial(d + 2), 2):
        ok_e0 = False
    for k in range(d + 1, 2 * d + 2):
        if peval(p, k) == D(k, d):
            ok_exc = False
            print('   equality below threshold at d=%d k=%d' % (d, k))
rep('C4-5a', ok_thr, 'D(k,d)=p_d(k) 对 2d+2<=k<=%d 全成立，d<=%d（p_d 由 2d+1 个点插值，其余点独立核对）%s' % (K, DMAX, first_bad[:3]))
rep('C4-5b', ok_deg and ok_lead, 'deg p_d=2d 且首项 2/(2^d d!)，d<=%d' % DMAX)
rep('C4-5c', ok_e1 and ok_e0, '缺陷闭式 e_d(2d+1)=(-1)^{d+1}(d+1)!, e_d(2d)=(-1)^{d+1}(d+2)!/2，d<=%d' % DMAX)
rep('C4-7', ok_exc, '门槛以下 d+1<=k<=2d+1 每点 D!=p_d，d<=%d' % DMAX)

# ---- 缺陷递推 (‡) 在 3<=k<=2d+2、k-d>=1 处成立（d<=DMAX）
ok = True


def e(d, k):
    if d < 0:
        return 0
    return D(k, d) - peval(PD[d], k)


for d in range(1, DMAX + 1):
    for k in range(max(3, d + 1), 2 * d + 3):
        lhs = e(d, k) - e(d, k - 1)
        rhs = e(d - 1, k - 1) + (k - d - 1) * (e(d - 1, k - 3) + 2 * e(d - 2, k - 3) + e(d - 3, k - 3))
        if lhs != rhs:
            ok = False
rep('C4-5d', ok, '缺陷递推 (‡) 在 max(3,d+1)<=k<=2d+2 全部成立，1<=d<=%d' % DMAX)

# ---- C4-6 逻辑：p_d(k)-p_d(k-1) == R_d(k) 作为多项式（用插值得到的 p_d）
ok = True
for d in range(0, DMAX + 1):
    pm1 = PD.get(d - 1, [])
    pm2 = PD.get(d - 2, [])
    pm3 = PD.get(d - 3, [])
    inner = padd(padd(pshift(pm1, -3), pscale(pshift(pm2, -3), 2)), pshift(pm3, -3))
    R = padd(pshift(pm1, -1), pmul([Fraction(-(d + 1)), Fraction(1)], inner))
    if psub(PD[d], pshift(PD[d], -1)) != R:
        ok = False
rep('C4-6a', ok, '插值得到的 p_d 满足 p_d(k)-p_d(k-1) ≡ R_d(k)（多项式恒等），d<=%d' % DMAX)

# ---- C4-8 次首项
ok = all(PD[d][-2] == -(4 * d * d - 3 * d) * PD[d][-1] for d in range(1, DMAX + 1))
rep('C4-8', ok, '次首项 = -(4d^2-3d)*首项，1<=d<=%d' % DMAX)

# ---- C4-9 平移后单项式系数正、[m^{2d-1}]=5d[m^{2d}]
ok, bad9 = True, []
for d in range(0, DMAX + 1):
    ps = pshift(PD[d], 2 * d + 1)
    if not all(c > 0 for c in ps) or len(ps) != 2 * d + 1:
        ok = False
        bad9.append(d)
    if d >= 1 and ps[-2] != 5 * d * ps[-1]:
        ok = False
        bad9.append(('5d', d))
rep('C4-9', ok, 'p_d(2d+1+m) 的 m 单项式系数全正，d<=%d %s' % (DMAX, bad9[:5]))

# ---- C4-10 / C4-11 Newton
ok10, ok11, bad11 = True, True, []
for d in range(0, DMAX + 1):
    n2 = newton_coeffs(PD[d], 2 * d + 2, 2 * d)
    n1 = newton_coeffs(PD[d], 2 * d + 1, 2 * d)
    if not all(c.denominator == 1 and c > 0 for c in n2) or n2[-1] != 2 * dfact(2 * d - 1):
        ok10 = False
    if not all(c.denominator == 1 and c > 0 for c in n1):
        ok11 = False
        bad11.append(d)
rep('C4-10', ok10, '基点 2d+2 Newton 系数全为正整数，末项 2(2d-1)!!，d<=%d' % DMAX)
rep('C4-11', ok11, '基点 2d+1 Newton 系数全为正整数，d<=%d %s' % (DMAX, bad11[:5]))
ok = all(D(2 * d + 1, d) > factorial(d + 1) for d in range(1, DMAX + 1, 2))
mins = min(Fraction(D(2 * d + 1, d), factorial(d + 1)) for d in range(1, DMAX + 1, 2))
rep('C4-11r', ok, '归约条件 D(2d+1,d)>(d+1)! 对奇数 d<=%d 成立（最小比值 %s）' % (DMAX, mins))

# ---- 分母 2^{d-1} d! 与首一整系数
ok, badden = True, []
for d in range(1, DMAX + 1):
    sc = [c * 2 ** (d - 1) * factorial(d) for c in PD[d]]
    if not all(c.denominator == 1 for c in sc) or sc[-1] != 1:
        ok = False
        badden.append(d)
rep('INFO-den', ok, '2^{d-1}d!*p_d 为首一整系数，1<=d<=%d；不成立的 d：%s' % (DMAX, badden[:10]))

# ---- 与 c4.md 表 1（两列）、表 2、表 3 比较
T1 = {0: (1, [2]), 1: (1, [1, -1, -4]), 2: (4, [1, -10, 43, -98, 164]),
      3: (24, [1, -27, 331, -2225, 8560, -17392, 11088]),
      4: (192, [1, -52, 1242, -17280, 151217, -845644, 2926356, -5702176, 5014464]),
      5: (1920, [1, -85, 3350, -79370, 1241073, -13308173, 98708360, -498528820, 1637903536, -3158022432, 2686170240])}
T1m = {0: (1, [2]), 1: (1, [1, 5, 2]), 2: (4, [1, 10, 43, 82, 124]),
       3: (24, [1, 15, 121, 673, 2554, 6212, 4200]),
       4: (192, [1, 20, 234, 2160, 15137, 75452, 244500, 411488, 405312]),
       5: (1920, [1, 25, 380, 4890, 50653, 398817, 2340990, 9829580, 28039016, 54223968, 40805760])}
ok = True
for d in range(0, 6):
    den, cs = T1[d]
    if ptrim([Fraction(c, den) for c in reversed(cs)]) != PD[d]:
        ok = False
        print('   table1 k-col mismatch d=%d' % d)
    den, cs = T1m[d]
    if ptrim([Fraction(c, den) for c in reversed(cs)]) != pshift(PD[d], 2 * d + 1):
        ok = False
        print('   table1 m-col mismatch d=%d' % d)
rep('TAB1', ok, 'c4.md 表 1 两列（k 与 m=k-2d-1）d<=5 与独立插值一致')

T2 = {0: [(1, 1, 2, -1)], 1: [(2, 1, -2, 3), (3, 4, 2, 2)],
      2: [(3, 1, 17, -16), (4, 7, 19, -12), (5, 25, 31, -6)],
      3: [(4, 1, -114, 115), (5, 12, -78, 90), (6, 59, -1, 60), (7, 199, 175, 24)],
      4: [(5, 1, 1052, -1051), (6, 19, 879, -860), (7, 124, 742, -618), (8, 557, 917, -360), (9, 1991, 2111, -120)],
      5: [(6, 1, -11679, 11680), (7, 29, -9843, 9872), (8, 253, -7247, 7500), (9, 1416, -3504, 4920),
          (10, 6051, 3531, 2520), (11, 21973, 21253, 720)]}
ok = True
for d, rows in T2.items():
    for (k, Dv, pvv, ev) in rows:
        if not (D(k, d) == Dv and peval(PD[d], k) == pvv and Dv - pvv == ev):
            ok = False
            print('   table2 mismatch', d, k)
ok = ok and peval(PD[1], 0) == -4 and peval(PD[1], 1) == -4 and [peval(PD[2], k) for k in range(3)] == [41, 25, 19]
rep('TAB2', ok, 'c4.md 表 2 (d<=5) 及 p_1(0),p_1(1),p_2(0..2) 与独立计算一致')

T3 = {0: [2], 1: [8, 8, 2], 2: [65, 74, 64, 30, 6], 3: [574, 872, 939, 802, 486, 180, 30],
      4: [6012, 10337, 14196, 15341, 13531, 9400, 4710, 1470, 210],
      5: [70674, 134661, 211267, 278625, 306255, 282432, 215295, 129150, 55860, 15120, 1890]}
ok = all(newton_coeffs(PD[d], 2 * d + 2, 2 * d) == [Fraction(c) for c in T3[d]] for d in T3)
ok = ok and newton_coeffs(PD[2], 5, 4) == [31, 34, 40, 24, 6] and newton_coeffs(PD[3], 7, 6) == [175, 399, 473, 466, 336, 150, 30]
ok = ok and [D(2 * d + 2, d) for d in range(6)] == [2, 8, 65, 574, 6012, 70674]
rep('TAB3', ok, 'c4.md 表 3（Newton，基点 2d+2，d<=5）与基点 2d+1 的两例、锚点序列 一致')

# ---- 与 logs/c4_tables.log 中 d<=12 的 p_d 系数、Newton 系数比较
logp = os.path.join(ROOT, 'logs', 'c4_tables.log')
txt = open(logp, encoding='utf-8').read()
ok, nd = True, 0
for mm in re.finditer(r'^d=(\d+) den=(\d+) : \[([^\]]*)\]', txt, re.M):
    d, den = int(mm.group(1)), int(mm.group(2))
    cs = [int(x) for x in mm.group(3).split(',')]
    if d > DMAX:
        continue
    nd += 1
    if den != 2 ** d * factorial(d) or ptrim([Fraction(c, den) for c in reversed(cs)]) != PD[d]:
        ok = False
        print('   log p_d mismatch d=%d' % d)
rep('LOG-pd', ok and nd >= 13, 'logs/c4_tables.log 中 d=0..12 的 p_d 系数（分母 2^d d!）与独立插值一致（比较了 %d 个）' % nd)
ok, nn = True, 0
for mm in re.finditer(r'^d=(\d+) base=(\d+): \[([^\]]*)\]', txt, re.M):
    d, base = int(mm.group(1)), int(mm.group(2))
    cs = [int(x) for x in mm.group(3).split(',')]
    if d > DMAX:
        continue
    nn += 1
    if newton_coeffs(PD[d], base, 2 * d) != [Fraction(c) for c in cs]:
        ok = False
        print('   log newton mismatch d=%d base=%d' % (d, base))
rep('LOG-newton', ok and nn >= 26, 'logs/c4_tables.log 中 Newton 系数（两个基点，d<=12）一致（比较了 %d 行）' % nn)

# ---- §3.3 两个例子（d=1,2 的展开式）对一切 k>=d 成立
def Cp(n, r):
    return comb(n, r) if (n >= 0 and 0 <= r <= n) else 0


ok = True
for k in range(1, K + 1):
    q = k - 1
    v = Cp(q, 1) + Cp(q, 2) + Cp(q - 2, 0) + Cp(q - 2, 1) + Cp(q - 2, 2) + 2 * Cp(q - 3, 1)
    if v != D(k, 1):
        ok = False
for k in range(2, K + 1):
    q = k - 2
    v = (Cp(q, 1) + 4 * Cp(q, 2) + 3 * Cp(q, 3) + 3 * Cp(q, 4)
         + Cp(q - 2, 0) + 4 * Cp(q - 2, 1) + 5 * Cp(q - 2, 2) + 3 * Cp(q - 2, 3) + 3 * Cp(q - 2, 4)
         + 2 * Cp(q - 3, 0) + 6 * Cp(q - 3, 1) + 4 * Cp(q - 3, 2) + 6 * Cp(q - 3, 3) + 6 * Cp(q - 4, 2))
    if v != D(k, 2):
        ok = False
rep('EX-3.3', ok, 'c4.md §3.3 中 d=1、d=2 的模式展开显式式对一切 d<=k<=%d 成立' % K)

print('SUMMARY s2 ok=%d bad=%d runtime=%.1fs' % (sum(RES), len(RES) - sum(RES), time.time() - t0))
