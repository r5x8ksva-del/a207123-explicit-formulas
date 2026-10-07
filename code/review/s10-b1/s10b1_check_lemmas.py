# -*- coding: utf-8 -*-
"""s10-b1 核对 4：笔记 05 §1 的引理 1、3、4、5 以及定理 2、§4 用到的几条交错性质，
在随机的「边界」例子上（根取自 1/4 格点，故意制造公共根、重根、根在 0）精确测试。

每个例子都同时用方法 R（按定义）与方法 C（Cauchy 指标）判定，并要求两者一致。
"""
import os
import random
import sys
import time
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s10b1_poly import (add, mul, mulz, mul1z, deriv, scal, T, Phi, L, norm, deg, ev_frac,
                        interlace_R, interlace_C, is_real_rooted)

random.seed(20261007)
t0 = time.time()
PASS = 0
FAIL = 0
DIS = 0
stats = {}


def check(name, ok, detail=''):
    global PASS, FAIL
    st = stats.setdefault(name, [0, 0])
    if ok:
        PASS += 1
        st[0] += 1
    else:
        FAIL += 1
        st[1] += 1
        if st[1] <= 3:
            print('FAIL', name, detail, flush=True)
    return ok


def il(g, f):
    """g ≪ f，两种方法；不一致计入 DIS。"""
    global DIS
    r = interlace_R(g, f)
    c = interlace_C(g, f)
    if r != c:
        DIS += 1
        print('DISAGREE R=%s C=%s g=%s f=%s' % (r, c, g, f), flush=True)
    return r


GRID = [Fraction(-i, 4) for i in range(0, 25)]          # 0, −1/4, …, −6


def poly_from_roots(roots, c=None):
    p = [c if c is not None else random.randint(1, 3)]
    for r in roots:
        r = Fraction(r)
        p = mul(p, [-r.numerator, r.denominator])        # den·z − num，系数非负（r≤0）
    return p


def rand_roots(n):
    return sorted(random.choice(GRID) for _ in range(n))


def pick(lo, hi):
    """[lo, hi] ∩ GRID 中随机取一个（常取端点）。"""
    cands = [x for x in GRID if lo <= x <= hi]
    if random.random() < 0.35:
        return random.choice([lo, hi]) if lo in GRID and hi in GRID else random.choice(cands)
    return random.choice(cands)


def make_g_below(a, same_degree):
    """给定 f 的根 a（升序），造 g 的根使 g ≪ f。"""
    n = len(a)
    if same_degree:
        b = [pick(GRID[-1], a[0])] + [pick(a[i - 1], a[i]) for i in range(1, n)]
    else:
        b = [pick(a[i], a[i + 1]) for i in range(n - 1)]
    return b


def make_g_above(a, plus_one):
    """给定 f 的根 a，造 g 的根使 f ≪ g（g 的最大根最大）。"""
    n = len(a)
    if plus_one:
        b = [pick(GRID[-1], a[0])] + [pick(a[i - 1], a[i]) for i in range(1, n)] + [pick(a[-1], Fraction(0))]
    else:
        b = [pick(a[i], a[i + 1]) for i in range(n - 1)] + [pick(a[-1], Fraction(0))]
    return b


NTRIAL = 1500
for trial in range(NTRIAL):
    n = random.randint(1, 6)
    a = rand_roots(n)
    f = poly_from_roots(a)
    sd = random.random() < 0.5
    b = make_g_below(a, sd)
    g = poly_from_roots(b)
    check('construction g<<f', il(g, f))
    # 引理 1：乘公共实根因子（⇒），以及随机对的 ⇔
    p = poly_from_roots(rand_roots(random.randint(1, 3)))
    check('L1 =>', il(mul(p, g), mul(p, f)))
    n2 = random.randint(0, 5)
    g2 = poly_from_roots(rand_roots(n2))
    f2 = poly_from_roots(rand_roots(random.choice([n2, n2 + 1])))
    check('L1 <=> on random pair', il(mul(p, g2), mul(p, f2)) == il(g2, f2))
    # 引理 3(a)：g≪f，h≪f ⇒ g+h≪f
    h = poly_from_roots(make_g_below(a, random.random() < 0.5))
    check('L3a', il(add(g, h), f))
    # 引理 3(b)：f≪g1，f≪h1 ⇒ f≪g1+h1
    g1 = poly_from_roots(make_g_above(a, random.random() < 0.5))
    h1 = poly_from_roots(make_g_above(a, random.random() < 0.5))
    check('construction f<<g', il(f, g1) and il(f, h1))
    check('L3b', il(f, add(g1, h1)))
    # 引理 4
    check('L4i f<<(1+z)f', il(f, mul1z(f)))
    check('L4i f\'<<f', il(deriv(f), f))
    check('L4ii f<<zg', il(f, mulz(g)))
    if deg(g) >= 1:
        check('L4iii g\'<<f\'', il(deriv(g), deriv(f)))
    # 引理 5
    check('L5i Tf, Phi f real-rooted', is_real_rooted(T(f)) and is_real_rooted(Phi(f))
          and deg(T(f)) == deg(f) + 1 and deg(Phi(f)) == deg(f) + 2)
    check('L5ii Tg<<Tf', il(T(g), T(f)))
    check('L5ii Phi g<<Phi f', il(Phi(g), Phi(f)))
    check('L5iii (1+z)f<<Tf', il(mul1z(f), T(f)))
    check('L5iv', T(mul1z(f)) == mul1z(add(T(f), mulz(f))))
    # 定理 2 情形 A：g≪f，α 是 f 的单根且 g(α)≠0 ⇒ g(α) f'(α) > 0
    for al in set(a):
        if a.count(al) == 1:
            gv = ev_frac(g, al)
            if gv != 0:
                check('Thm2 caseA sign', gv * ev_frac(deriv(f), al) > 0)
    # §4 的计数：deg 差 1 时，#{f 根 < x} − #{g 根 < x} ∈ {0,1}（<、≤ 都对）
    if not sd:
        for x in GRID + [Fraction(1, 8) - Fraction(i, 4) for i in range(25)]:
            d1 = sum(1 for t in a if t < x) - sum(1 for t in b if t < x)
            d2 = sum(1 for t in a if t <= x) - sum(1 for t in b if t <= x)
            check('Sec4 count', d1 in (0, 1) and d2 in (0, 1))
    # 一致性：随机（多半不交错）的对，两种方法必须一致
    gg = poly_from_roots(rand_roots(random.randint(0, 5)))
    ff = poly_from_roots(rand_roots(random.choice([deg(gg), deg(gg) + 1])))
    res = il(gg, ff)
    st = stats.setdefault('random pair outcome', [0, 0])
    st[0 if res else 1] += 1

print('elapsed %.1fs' % (time.time() - t0))
for k, (p, f_) in stats.items():
    if k == 'random pair outcome':
        print('%-28s (not a check) judged interlacing=%d, non-interlacing=%d' % (k, p, f_))
    else:
        print('%-28s PASS=%d FAIL=%d' % (k, p, f_))
print('method disagreements:', DIS)
print('TOTAL PASS=%d FAIL=%d' % (PASS, FAIL))
