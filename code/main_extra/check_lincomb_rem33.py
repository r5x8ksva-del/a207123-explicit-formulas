# -*- coding: utf-8 -*-
"""在随机有理点上检验注记 3.3 形式化里用到的 linear_combination 恒等式（多项式恒等式，与约束无关）。
每个恒等式写成 goal.lhs − goal.rhs − Σ coeff_i·(h_i.lhs − h_i.rhs)，应恒为 0。
用法：py -3.14 code/main_extra/check_lincomb_rem33.py
"""
import random
from fractions import Fraction as F

random.seed(20261010)


def rnd():
    return F(random.randint(-40, 40), random.randint(1, 13))


def check(name, fn, nvars, trials=200):
    for _ in range(trials):
        vals = [rnd() for _ in range(nvars)]
        r = fn(*vals)
        if r != 0:
            print('FAIL', name, vals, r)
            return False
    print('PASS', name)
    return True


# cm_one：goal (ρ^6 + ρ)·31 = (10 + 15ρ + 17ρ²)(ρ² + 3)，h : ρ³ − ρ² = 1
def cm_one(r):
    goal = (r**6 + r) * 31 - (10 + 15 * r + 17 * r**2) * (r**2 + 3)
    h = r**3 - r**2 - 1
    return goal - (31 * r**3 + 31 * r**2 + 14 * r + 30) * h


# cm_one 的 key：goal ρ^6(1 + I) = ρ^6 + ρ，h5 : ρ^5·I = 1（I 是 (ρ^5)⁻¹ 的原子）
def cm_one_key(r, I):
    goal = r**6 * (1 + I) - (r**6 + r)
    h5 = r**5 * I - 1
    return goal - r * h5


# theta：goal m(1 − b x)(1 + b x + (b x)² − x − b x·x) = 1 − x
# hd : (a − b)(a² + ab + b² − a − b) = 1；hm : a³ − a² = m；hinv : a·x = 1
def theta_id(a, b, x, m):
    goal = m * (1 - b * x) * (1 + b * x + (b * x)**2 - x - b * x * x) - (1 - x)
    D = a**2 + a * b + b**2 - a - b
    S = 1 + a * x + b * x - x
    T = x * (a - b) * S + x**2 * D + (1 - a * x) * S
    hd = (a - b) * D - 1
    hm = a**3 - a**2 - m
    hinv = a * x - 1
    c_inv = (a * x)**2 + a * x + 1 - x * (a * x + 1) - m * T
    return goal - (m * x**3 * hd - x**3 * hm + c_inv * hinv)


# hd 本身：(a³ − a²) − (b³ − b²) − (a − b)(a² + ab + b² − a − b) ≡ 0
def hd_id(a, b):
    return (a**3 - a**2) - (b**3 - b**2) - (a - b) * (a**2 + a * b + b**2 - a - b)


ok = all([check('cm_one', cm_one, 1), check('cm_one_key', cm_one_key, 2), check('theta_id', theta_id, 4),
          check('hd_id', hd_id, 2)])
print('ALL PASS' if ok else 'SOME FAIL')
