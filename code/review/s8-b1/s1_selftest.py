# -*- coding: utf-8 -*-
"""s8-b1 第 1 步：先检验两种交错判定本身（手算例子 + 随机对照），再在带公共根、重根、根在 0 与 -1 的
随机例子上检验 notes/05 的引理 1、3、4、5（这些是对抗性的边界情形）。全部精确运算。"""
import random
import sys
import time
from fractions import Fraction as Fr

from px import (trim, deg, add, mul, scal, deriv, mulz, mul1z, T, Phi, from_roots,
                interlace_A, interlace_B)

t0 = time.time()
fails = []


def check(name, cond, extra=""):
    if not cond:
        fails.append(name + " " + extra)
        print("FAIL", name, extra)


# ------------------------------------------------------------ 1. 手算例子
H = Fr(1, 2)
cases = [
    # (名称, g 的根, f 的根, 期望 g<<f)
    ("deg-1 strict", [-H - 1, -H - 2], [-1, -2, -3], True),
    ("g root too large", [-H, -H - 2], [-1, -2, -3], False),
    ("same deg strict", [-3 - H, -2 - H, -1 - H], [-3, -2, -1], True),
    ("same deg, largest is g", [-3 + H, -2 + H, -1 + H], [-3, -2, -1], False),
    ("weak with double root at 0", [-1, 0], [-1, 0, 0], True),
    ("deg diff 2", [0], [0, 0, 0], False),
    ("all at 0, deg-1", [0, 0], [0, 0, 0], True),
    ("identical", [0, 0, 0], [0, 0, 0], True),
    ("triple root needs two g-roots", [-2, -1], [-1, -1, -1], False),
    ("triple vs double", [-1, -1], [-1, -1, -1], True),
    ("weak mixed", [-2, -1], [-3, -1, -1], True),
    ("weak mixed bad", [-2, -H], [-3, -1, -1], False),
    ("constants", [], [], True),
    ("const vs linear", [], [-1], True),
    ("linear vs const", [-1], [], False),
    ("multiplicity gap 2", [-1], [-1, -1, -1], False),
]
for name, gr, fr, exp in cases:
    g, f = from_roots(gr), from_roots(fr)
    a, ma = interlace_A(g, f)
    b, mb = interlace_B(g, f)
    check("hand:" + name, a == exp and b == exp, "A=%s(%s) B=%s(%s) expected %s" % (a, ma, b, mb, exp))

# 非实根与无理根
f = [2, 4, 1]            # z^2+4z+2，根 -2±√2 = -3.414.., -0.586..
for g, exp, nm in [([2, 1], True, "z+2"), ([7, 2], False, "2z+7 (root -3.5)"),
                   ([17, 5], True, "5z+17 (root -3.4)"), ([1, 0, 1], False, "z^2+1"),
                   ([3, 4, 1], False, "(z+1)(z+3): b1=-3 > a1=-3.414"),
                   ([5, 6, 1], True, "(z+1)(z+5)"),
                   ([7, 6, 1], True, "z^2+6z+7: roots -3±√2"),
                   ([1, 3, 1], False, "z^2+3z+1: roots (-3±√5)/2"), ([1, 1], True, "z+1")]:
    a, ma = interlace_A(g, f)
    b, mb = interlace_B(g, f)
    check("irr:" + nm, a == exp and b == exp, "A=%s(%s) B=%s(%s) expected %s" % (a, ma, b, mb, exp))
# 非实根的 f
a, _ = interlace_A([1], [1, 0, 1])
b, _ = interlace_B([1], [1, 0, 1])
check("f=z^2+1 rejected", (not a) and (not b))
a, _ = interlace_A([1, 1], [1, 1, 1])
b, _ = interlace_B([1, 1], [1, 1, 1])
check("f=z^2+z+1 rejected", (not a) and (not b))

# ------------------------------------------------------------ 2. 随机生成
ITER = int(sys.argv[1]) if len(sys.argv) > 1 else 400
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 20261007
print('ITER=%d NMAX=%d SEED=%d' % (ITER, NMAX, SEED))
rng = random.Random(SEED)
GRID = [Fr(-j, 6) for j in range(0, 37)]          # [-6, 0] 上步长 1/6，故意让根常常重合
FINE = [Fr(-j, 6) for j in range(0, 25)]          # [-4, 0]


def pick(lo, hi):
    c = [x for x in GRID if lo <= x <= hi]
    return rng.choice(c)


def rand_f(n):
    return sorted(rng.choice(FINE) for _ in range(n))


def below(a1):
    return max(GRID[-1], a1 - 2)


def rand_lower(a, same_degree):
    """g << f 的根：same_degree 时 b1<=a1<=b2<=...<=bn<=an；否则 a1<=b1<=...<=b_{n-1}<=an。"""
    n = len(a)
    if n == 0:
        return []
    if same_degree:
        b = [pick(below(a[0]), a[0])]
        for i in range(1, n):
            b.append(pick(a[i - 1], a[i]))
    else:
        b = [pick(a[i], a[i + 1]) for i in range(n - 1)]
    return b


def rand_upper(a, plus_one):
    """f << G 的根：G 与 f 同次时 a1<=c1<=a2<=...<=an<=cn<=0；G 高一次时 c1<=a1<=c2<=...<=an<=c_{n+1}<=0。"""
    n = len(a)
    c = []
    if plus_one:
        c.append(pick(below(a[0]) if n else Fr(-6), a[0] if n else Fr(0)))
    for i in range(n - 1):
        c.append(pick(a[i], a[i + 1]))
    if n:
        c.append(pick(a[-1], Fr(0)))
    return c


def P(roots, c=None):
    return from_roots(roots, c if c is not None else rng.choice([1, 2, 3]))


n_pos = n_negctl = 0
agree_neg = {True: 0, False: 0}
for it in range(ITER):
    n = rng.randint(0, NMAX)
    a = rand_f(n)
    f = P(a)
    same = (n == 0) or rng.random() < 0.5
    gr = rand_lower(a, same)
    g = P(gr)
    # 判定 A、B 一致且为真
    A1, mA = interlace_A(g, f)
    B1, mB = interlace_B(g, f)
    check("rand-pos A==B==True #%d" % it, A1 and B1, "f-roots %s g-roots %s A=%s B=%s" % (a, gr, mA, mB))
    n_pos += 1
    # 引理 1：乘一个只有实根的 p
    p = P(rand_f(rng.randint(0, 3)))
    check("L1 #%d" % it, interlace_A(mul(p, g), mul(p, f))[0])
    # 引理 3(a)：g,h << f ⇒ c1 g + c2 h << f
    h = P(rand_lower(a, (n == 0) or rng.random() < 0.5))
    s = add(scal(rng.randint(1, 5), g), scal(rng.randint(1, 5), h))
    check("L3a #%d" % it, interlace_A(s, f)[0], "f %s" % a)
    # 引理 3(b)：f << G1, f << G2 ⇒ f << c1 G1 + c2 G2
    G1 = P(rand_upper(a, rng.random() < 0.5))
    G2 = P(rand_upper(a, rng.random() < 0.5))
    check("L3b-pre #%d" % it, interlace_A(f, G1)[0] and interlace_A(f, G2)[0])
    check("L3b #%d" % it, interlace_A(f, add(scal(rng.randint(1, 5), G1), scal(rng.randint(1, 5), G2)))[0])
    # 引理 4(i)
    check("L4i-a #%d" % it, interlace_A(f, mul1z(f))[0])
    if deg(f) >= 1:
        check("L4i-b #%d" % it, interlace_A(deriv(f), f)[0])
    # 引理 4(ii)：g<<f ⇒ f << z g
    check("L4ii #%d" % it, interlace_A(f, mulz(g))[0], "f %s g %s" % (a, gr))
    # 引理 4(iii)：g<<f, deg g>=1 ⇒ g' << f'
    if deg(g) >= 1:
        ok = interlace_A(deriv(g), deriv(f))[0]
        check("L4iii #%d" % it, ok, "f %s g %s" % (a, gr))
        if it % 4 == 0:
            check("L4iii-B #%d" % it, interlace_B(deriv(g), deriv(f))[0])
    # 引理 5(ii)(iii)
    check("L5ii-T #%d" % it, interlace_A(T(g), T(f))[0], "f %s g %s" % (a, gr))
    check("L5ii-Phi #%d" % it, interlace_A(Phi(g), Phi(f))[0])
    check("L5iii #%d" % it, interlace_A(mul1z(f), T(f))[0])
    if it % 4 == 0:
        check("L5ii-T-B #%d" % it, interlace_B(T(g), T(f))[0])
        check("L5iii-B #%d" % it, interlace_B(mul1z(f), T(f))[0])
    # 负对照：根随意取的 (f, g)，A 与 B 必须一致
    n2 = max(0, n - rng.randint(0, 1))
    gr2 = sorted(rng.choice(GRID) for _ in range(n2))
    g2 = P(gr2)
    A2 = interlace_A(g2, f)[0]
    B2 = interlace_B(g2, f)[0]
    check("negctl A==B #%d" % it, A2 == B2, "f %s g %s A=%s B=%s" % (a, gr2, A2, B2))
    agree_neg[A2] += 1
    n_negctl += 1
    # 非实根：乘 z^2+z+1 再去掉 f 的两个根位置——直接构造 g3 = (z^2+z+1)·(n-2 个根)
    if n >= 2:
        g3 = mul([1, 1, 1], P(sorted(rng.choice(FINE) for _ in range(n - 2))))
        check("nonreal A,B false #%d" % it, (not interlace_A(g3, f)[0]) and (not interlace_B(g3, f)[0]))

# 引理 5(iv) 恒等式：对任意整数多项式
for it in range(200):
    nn = [rng.randint(-9, 9) for _ in range(rng.randint(1, 8))]
    lhs = T(mul1z(nn))
    rhs = mul1z(add(T(nn), mulz(nn)))
    check("L5iv #%d" % it, trim(lhs) == trim(rhs))

print("random positive pairs: %d; negative-control pairs: %d (A=B=True %d, A=B=False %d)"
      % (n_pos, n_negctl, agree_neg[True], agree_neg[False]))
print("selftest: %d failures; %.1fs" % (len(fails), time.time() - t0))
sys.exit(1 if fails else 0)
