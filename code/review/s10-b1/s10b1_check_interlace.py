# -*- coding: utf-8 -*-
"""s10-b1 核对 2：笔记 05 定理 1 的四条交错关系、归纳步里的全部中间关系、定理 2 的公共根结论。

两种互相独立的精确判定（见 s10b1_poly.py）：方法 R（按定义：隔离实根后比较不等式链）、
方法 C（Cauchy 指标）。四条关系：方法 R 到 k≤KR，方法 C 到 k≤KC。
N 取自三角递推（核对 1 已对照「按定义 DP + 容斥」的 N 到 k≤60）。
用法：py s10b1_check_interlace.py [KR] [KC]
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s10b1_poly import (add, sub, mul, mulz, mul1z, deriv, scal, T, Phi, L, norm, ev_int, pgcd, divexact,
                        interlace_R, interlace_C, is_real_simple, is_real_rooted, mult_at, deg, prim_pos)
from s10b1_data import N_tri, nrow

KR = int(sys.argv[1]) if len(sys.argv) > 1 else 40
KC = int(sys.argv[2]) if len(sys.argv) > 2 else 80
t0 = time.time()
N = N_tri(KC + 2)
n = {k: nrow(N, k) for k in range(1, KC + 2)}

PASS = 0
FAIL = 0
stats = {}


def check(name, ok, detail=''):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        print('FAIL', name, detail, flush=True)
    return ok


def rel(tag, g, f, k, use_R=True):
    """记录 g ≪ f；两种方法都要通过（use_R=False 时只用方法 C）。"""
    c = interlace_C(g, f)
    r = interlace_R(g, f) if use_R else None
    ok = c and (r if use_R else True)
    if use_R and (c != r):
        print('DISAGREE', tag, 'k=%d' % k, 'C=', c, 'R=', r, flush=True)
    st = stats.setdefault(tag, [0, 0, None, None])
    if ok:
        st[0] += 1
    else:
        st[1] += 1
    st[2] = k if st[2] is None else min(st[2], k)
    st[3] = k if st[3] is None else max(st[3], k)
    check('%s k=%d' % (tag, k), ok)
    return ok


# ---------------- 基例（精确）
check('n1,n2,n3', n[1] == [1] and n[2] == [1, 2] and n[3] == [1, 4, 2])
check('T n1 = 2z', T(n[1]) == [0, 2])
check('T n2 = 2z(2+3z)', T(n[2]) == mul([0, 2], [2, 3]))
check('Phi n1 = 2z(1+z)', Phi(n[1]) == mul([0, 2], [1, 1]))
check('T n3 = 2z(2z+1)(2z+3)', T(n[3]) == mul(mul([0, 2], [1, 2]), [3, 2]))
# 引理 5(iv)：T((1+z)p) = (1+z)(Tp + zp)
for k in range(1, min(40, KC + 2)):
    p = n[k]
    check('L5(iv) k=%d' % k, T(mul1z(p)) == mul1z(add(T(p), mulz(p))))

# ---------------- 四条关系
for k in range(2, KC + 1):
    useR = k <= KR
    rel('alpha', n[k - 1], n[k], k, useR)                 # n_{k−1} ≪ n_k
    rel('beta', n[k], T(n[k - 1]), k, useR)               # n_k ≪ T n_{k−1}
    if k >= 3:
        rel('delta', n[k], Phi(n[k - 2]), k, useR)        # n_k ≪ Φ n_{k−2}
        rel('eps', Phi(n[k - 2]), T(n[k]), k, useR)       # Φ n_{k−2} ≪ T n_k
    if k % 10 == 0:
        print('four relations up to k=%d  %.1fs' % (k, time.time() - t0), flush=True)

# ---------------- 归纳步的中间关系（A=n_k, B=n_{k−1}, C=n_{k−2}，3≤k，k+1≤KR）
for k in range(3, KR):
    A, B, C = n[k], n[k - 1], n[k - 2]
    TA, TB, TC = T(A), T(B), T(C)
    PA, PB, PC = Phi(A), Phi(B), Phi(C)
    nk1 = n[k + 1]
    check('step: n_{k+1} = (1+z)(A+TC) k=%d' % k, nk1 == mul1z(add(A, TC)) and nk1 == add(mul1z(A), PC))
    Tn1 = T(nk1)
    expand = add(add(PA, mul([0, 1, 1], A)), add(mul1z(T(TC)), mul([0, 1, 1], TC)))
    check('step: T n_{k+1} 4-term expansion k=%d' % k, Tn1 == expand)
    rel('s01 A<<(1+z)A', A, mul1z(A), k)
    rel('s02 A<<PhiC', A, PC, k)
    rel('s03 A<<n_{k+1}', A, nk1, k)
    rel('s04 (1+z)A<<TA', mul1z(A), TA, k)
    rel('s05 PhiC<<TA', PC, TA, k)
    rel('s06 n_{k+1}<<TA', nk1, TA, k)
    rel('s07 A<<TB', A, TB, k)
    rel('s08 C<<B', C, B, k)
    rel('s09 TC<<TB', TC, TB, k)
    rel('s10 A+TC<<TB', add(A, TC), TB, k)
    rel('s11 n_{k+1}<<PhiB', nk1, PB, k)
    rel('s12 B<<A', B, A, k)
    rel('s13 PhiB<<PhiA', PB, PA, k)
    rel('s14 TB<<zA', TB, mulz(A), k)
    rel('s15 PhiB<<z(1+z)A', PB, mul([0, 1, 1], A), k)
    rel('s16 B<<TC', B, TC, k)
    rel('s17 TB<<T(TC)', TB, T(TC), k)
    rel('s18 PhiB<<(1+z)T^2C', PB, mul1z(T(TC)), k)
    rel('s19 TB<<z TC', TB, mulz(TC), k)
    rel('s20 PhiB<<z(1+z)TC', PB, mul([0, 1, 1], TC), k)
    rel('s21 PhiB<<T n_{k+1}', PB, Tn1, k)
    # 引理 5(iii) 的中间步：L n ≪ (1+z)n
    rel('s22 L A<<(1+z)A', L(A), mul1z(A), k)
    if k % 10 == 0:
        print('step relations up to k=%d  %.1fs' % (k, time.time() - t0), flush=True)

# ---------------- 定理 2：公共根、重数
for k in range(2, KC + 1):
    g = pgcd(n[k], n[k - 1])
    e = -(-(k - 1) // 3) - 1          # ⌈(k−1)/3⌉ − 1
    target = [1]
    for _ in range(e):
        target = mul1z(target)
    check('gcd(n_k,n_{k-1}) = (1+z)^(ceil((k-1)/3)-1) k=%d' % k, g == target, 'got deg %d' % deg(g))
for k in range(1, KC + 1):
    a, core = mult_at(n[k], -1)
    check('mult_{-1}(n_k) = ceil(k/3)-1 k=%d' % k, a == -(-k // 3) - 1, 'got %d' % a)
    check('core(n_k) real & simple k=%d' % k, is_real_simple(core))
    check('core(n_k)(0) != 0', ev_int(core, 0) != 0)
# 定理 2 证明里用到的两件事：T n_j 除 0、−1 外只有单根；(1+z)^2 n_j 的导数在 P≠0 处只有单根
for j in range(1, KR + 1):
    Tj = T(n[j])
    b0, c0 = mult_at(Tj, 0)
    a1, c1 = mult_at(c0, -1)
    check('T n_j: root 0 simple, core simple j=%d' % j, b0 == 1 and is_real_simple(c1))
print('theorem 2 checks done %.1fs' % (time.time() - t0), flush=True)

# ---------------- 反向检查（这些应当判为「不交错」）
rev = {}
for k in range(3, KR + 1):
    cases = {
        'T n_{k-1} << n_k (wrong side)': (T(n[k - 1]), n[k]),
        'Phi n_{k-2} << n_k (wrong side)': (Phi(n[k - 2]), n[k]),
        'n_{k-2}*z << n_k': (mulz(n[k - 2]), n[k]),
        'n_{k-1}(perturbed) << n_k': (add(n[k - 1], [0] * ((k - 2) // 2) + [N[k - 1][(k - 2) // 2 + 1] * 3]), n[k]),
    }
    for name, (g, f) in cases.items():
        c = interlace_C(g, f)
        r = interlace_R(g, f)
        st = rev.setdefault(name, [0, 0, 0])
        st[0] += 1
        st[1] += (not c)
        st[2] += (not r)
        if c != r:
            print('DISAGREE (reverse)', name, k, c, r)
for name, (tot, fc, fr) in rev.items():
    print('REVERSE %-34s cases=%d  judged non-interlacing: C=%d R=%d' % (name, tot, fc, fr))
# 用错的 T（2zn → zn）重跑四条关系，看是否有 FAIL
def T_bad(p):
    return add(mul([0, 1, 1], deriv(p)), mulz(p))
nb = 0
tot = 0
for k in range(3, KR + 1):
    for g, f in ((n[k], T_bad(n[k - 1])), (mul1z(T_bad(n[k - 2])), T_bad(n[k]))):
        tot += 1
        nb += (not interlace_C(g, f))
print('REVERSE with T replaced by z(1+z)n\'+zn: beta/eps fail in %d of %d cases' % (nb, tot))

print('\n== summary of relations ==')
for tag, (p, f, lo, hi) in stats.items():
    print('%-28s k=%d..%d  PASS=%d FAIL=%d' % (tag, lo, hi, p, f))
print('elapsed %.1fs' % (time.time() - t0))
print('TOTAL PASS=%d FAIL=%d' % (PASS, FAIL))
