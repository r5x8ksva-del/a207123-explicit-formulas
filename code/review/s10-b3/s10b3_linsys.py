# -*- coding: utf-8 -*-
"""s10-b3 检查 2：截断线性方程组（直接按定义，不经过任何母函数或纤维论证）。

对形状 (α,β)、参数 (c,d,k0[,s0]) 与 m，未知数是 A(s)，方程是
    sum_s A(s) C(k+c-αs, βs+d) = U_k(m)，   max(k0,0) <= k <= max(k0,0)+R-1。
β>=1 时 βs+d<0 的项恒为 0，s0 无关紧要（取 s >= ceil(-d/β)，这是最一般的）；
β=0 时 s0 可以吸收进 c（s -> s+s0 把 c 变成 c-α s0），这里另取 s0∈{-3,0} 两种。
真表示存在 => 截断方程组可解；所以截断方程组无解是「该参数下不存在」的严格证据。

判定：
  * 快速路径：[A|b] 模 p=2^61-1 的秩 = 列数+1  => 有理数上 rank[A|b] = 列数+1 > rank A => 无解（严格）；
  * 否则用 Fraction 精确消元判定；可解时给出一个解并逐个方程精确代回验证。
  * 抽样：对一部分无解的方程组另求显式整数证书 y（y^T A = 0、y^T b ≠ 0），用整数精确核对。

PASS 标准：
  L1 α+β>=2 的全部形状（含 (2,1)）在全部参数下无解；
  L2 对照组 (1,0)、(0,1)：可解 <=> 我自己推出的条件
        (0,1)（s0 自由）：max(k0,0)+c >= 0；
        (1,0)（s0 固定）：d >= 0 且 max(k0,0)+c-d-s0 >= 0；
  L3 抽样证书全部通过整数核对；
  L4 正对照（反向检查）：把 U 换成真有某形状表示的序列，判定器必须报「可解」：
        (a) U-U^up（(2,1) 形状，A(s)=S(m+s,m)，c=d=m）；
        (b) 随机系数构造的 (2,0)、(1,2)、(0,3)、(3,3)、(4,1) 形状序列。
"""
import sys
import random
import time
from fractions import Fraction
from s10b3_common import binom, U_dp, U_up_dp

PMOD = (1 << 61) - 1
R_ROWS = 40


def ceil_div(a, b):
    return -((-a) // b)


def build_system(alpha, beta, c, d, k0, s0, seq, R=R_ROWS):
    """返回 (rows, rhs, slist)。seq 是函数 k -> 目标值（k>=0）。"""
    kstart = max(k0, 0)
    ks = list(range(kstart, kstart + R))
    K = ks[-1]
    if beta == 0:
        if d < 0:
            return None  # 全部项为 0
        s_lo = s0
    else:
        s_lo = ceil_div(-d, beta)
    # e_s=(α+β)s+d-c <= K
    s_hi = (K + c - d) // (alpha + beta)
    slist = list(range(s_lo, s_hi + 1))
    rows = [[binom(k + c - alpha * s, beta * s + d) for s in slist] for k in ks]
    rhs = [seq(k) for k in ks]
    return rows, rhs, slist


def rank_mod_p(rows, rhs):
    M = [[x % PMOD for x in r] + [b % PMOD] for r, b in zip(rows, rhs)]
    n = len(M)
    ncol = len(M[0]) if M else 0
    rank = 0
    for col in range(ncol):
        piv = None
        for i in range(rank, n):
            if M[i][col]:
                piv = i
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], PMOD - 2, PMOD)
        pr = [(x * inv) % PMOD for x in M[rank]]
        M[rank] = pr
        for i in range(rank + 1, n):
            f = M[i][col]
            if f:
                Mi = M[i]
                M[i] = [(a - f * b) % PMOD for a, b in zip(Mi, pr)]
        rank += 1
        if rank == n:
            break
    return rank


def exact_decide(rows, rhs, want_cert=False):
    """Fraction 精确消元。返回 ('sol', x) 或 ('nosol', y)；y 为整数左核证书（want_cert 时）。"""
    n = len(rows)
    ncol = len(rows[0]) if rows else 0
    M = []
    for i, (r, b) in enumerate(zip(rows, rhs)):
        row = [Fraction(x) for x in r] + [Fraction(b)]
        if want_cert:
            row += [Fraction(1) if j == i else Fraction(0) for j in range(n)]
        M.append(row)
    piv_cols = []
    rk = 0
    for col in range(ncol):
        piv = None
        for i in range(rk, n):
            if M[i][col] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        pv = M[rk][col]
        M[rk] = [x / pv for x in M[rk]]
        for i in range(n):
            if i != rk and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        piv_cols.append(col)
        rk += 1
    for i in range(rk, n):
        if M[i][ncol] != 0:
            if want_cert:
                y = M[i][ncol + 1:]
                # 化成整数
                from math import lcm
                L = 1
                for q in y:
                    L = lcm(L, q.denominator)
                yi = [int(q * L) for q in y]
                return ("nosol", yi)
            return ("nosol", None)
    x = [Fraction(0)] * ncol
    for i, col in enumerate(piv_cols):
        x[col] = M[i][ncol]
    for r, b in zip(rows, rhs):
        if sum(Fraction(a) * xi for a, xi in zip(r, x)) != b:
            raise AssertionError("solution does not verify")
    return ("sol", x)


def check_cert(rows, rhs, y):
    ncol = len(rows[0])
    for j in range(ncol):
        if sum(y[i] * rows[i][j] for i in range(len(rows))) != 0:
            return False
    return sum(y[i] * rhs[i] for i in range(len(rows))) != 0


def decide(rows, rhs):
    ncol = len(rows[0]) if rows else 0
    if ncol == 0:
        return ("nosol-trivial", None) if any(rhs) else ("sol", [])
    if rank_mod_p(rows, rhs) == ncol + 1:
        return ("nosol-modp", None)
    return exact_decide(rows, rhs)


def main():
    t0 = time.time()
    random.seed(20261007)
    Kmax = 80
    Ucol = {m: U_dp(m, Kmax) for m in (1, 2, 3)}
    import os
    if os.environ.get("S10B3_CORRUPT", "") == "seq":
        # 反向检查：把 U 换成 U-U^up（它有 (2,1) 形状的表示），L1 必须报 FAIL
        for m in (1, 2, 3):
            up = U_up_dp(m, Kmax)
            Ucol[m] = [a - b for a, b in zip(Ucol[m], up)]
        print("!! S10B3_CORRUPT=seq: U replaced by U-U^up (reverse check)")
    shapes = [(a, b) for n in range(2, 8) for a in range(0, n + 1) for b in [n - a]]
    shapes += [(6, 3), (8, 4), (9, 0), (0, 9), (1, 8), (4, 5), (10, 2)]
    controls = [(1, 0), (0, 1)]
    cs = range(-3, 4)
    ds = range(-2, 4)
    k0s = (0, 7)
    nfail = 0
    stats = {}
    sample = []
    n_sys = 0
    # L1
    for (al, be) in shapes:
        for m in (1, 2, 3):
            seq = (lambda k, m=m: Ucol[m][k])
            for c in cs:
                for d in ds:
                    for k0 in k0s:
                        for s0 in ((-3, 0) if be == 0 else (None,)):
                            sysd = build_system(al, be, c, d, k0, s0, seq)
                            if sysd is None:
                                verdict = "nosol-allzero"
                            else:
                                rows, rhs, sl = sysd
                                verdict, _ = decide(rows, rhs)
                                if verdict.startswith("nosol") and random.random() < 0.02:
                                    sample.append((al, be, c, d, k0, s0, m))
                            n_sys += 1
                            stats[verdict] = stats.get(verdict, 0) + 1
                            if not verdict.startswith("nosol"):
                                nfail += 1
                                print("FAIL L1 solvable: shape=(%d,%d) m=%d c=%d d=%d k0=%d s0=%s" % (al, be, m, c, d, k0, s0))
    print("L1 systems=%d verdicts=%s" % (n_sys, stats))
    print(("PASS" if nfail == 0 else "FAIL") + " L1 every shape with alpha+beta>=2 (%d shapes incl. (2,1)) unsolvable in all %d systems" % (len(shapes), n_sys))
    res = [("L1", nfail == 0)]

    # L2
    nf2 = 0
    n2 = 0
    for (al, be) in controls:
        for m in (1, 2, 3):
            seq = (lambda k, m=m: Ucol[m][k])
            for c in cs:
                for d in ds:
                    for k0 in k0s:
                        for s0 in ((-3, 0) if be == 0 else (None,)):
                            sysd = build_system(al, be, c, d, k0, s0, seq)
                            if sysd is None:
                                verdict = "nosol-allzero"
                            else:
                                rows, rhs, sl = sysd
                                verdict, _ = decide(rows, rhs)
                            solv = (verdict == "sol")
                            kk = max(k0, 0)
                            if (al, be) == (0, 1):
                                pred = (kk + c >= 0)
                            else:
                                pred = (d >= 0 and kk + c - d - s0 >= 0)
                            n2 += 1
                            if solv != pred:
                                nf2 += 1
                                print("FAIL L2 shape=(%d,%d) m=%d c=%d d=%d k0=%d s0=%s solvable=%s predicted=%s" % (al, be, m, c, d, k0, s0, solv, pred))
    print(("PASS" if nf2 == 0 else "FAIL") + " L2 controls (1,0),(0,1): solvable exactly when predicted (%d systems)" % n2)
    res.append(("L2", nf2 == 0))

    # L3 抽样证书
    nf3 = 0
    for (al, be, c, d, k0, s0, m) in sample:
        rows, rhs, sl = build_system(al, be, c, d, k0, s0, lambda k, m=m: Ucol[m][k])
        verdict, y = exact_decide(rows, rhs, want_cert=True)
        if verdict != "nosol" or not check_cert(rows, rhs, y):
            nf3 += 1
            print("FAIL L3 certificate shape=(%d,%d) m=%d c=%d d=%d k0=%d s0=%s" % (al, be, m, c, d, k0, s0))
    print(("PASS" if nf3 == 0 else "FAIL") + " L3 explicit integer left-kernel certificates verified for %d sampled systems" % len(sample))
    res.append(("L3", nf3 == 0 and len(sample) > 0))

    # L4 正对照（反向检查）
    nf4 = 0
    # (a) U-U^up 的 (2,1) 表示：C(k+m-2s, m+s) 即 c=m, d=m
    for m in (1, 2, 3):
        up = U_up_dp(m, Kmax)
        seq = (lambda k, m=m, up=up: Ucol[m][k] - up[k])
        for k0 in (0, 7):
            rows, rhs, sl = build_system(2, 1, m, m, k0, None, seq)
            verdict, x = decide(rows, rhs)
            if verdict != "sol":
                nf4 += 1
                print("FAIL L4a (2,1) control m=%d k0=%d verdict=%s" % (m, k0, verdict))
            # 同一参数下真 U 必须无解（说明是 U^up 那一族造成的差别）
            rowsU, rhsU, _ = build_system(2, 1, m, m, k0, None, lambda k, m=m: Ucol[m][k])
            vU, _ = decide(rowsU, rhsU)
            if not vU.startswith("nosol"):
                nf4 += 1
                print("FAIL L4a U itself solvable m=%d k0=%d" % (m, k0))
    # (b) 合成序列
    for (al, be) in [(2, 0), (1, 2), (0, 3), (3, 3), (4, 1)]:
        for trial in range(3):
            c = random.randint(-2, 2)
            d = random.randint(0, 3)
            s_lo = 0 if be == 0 else ceil_div(-d, be)
            A = {s: random.randint(-5, 5) for s in range(s_lo, s_lo + 40)}
            seq = (lambda k, A=A, al=al, be=be, c=c, d=d: sum(a * binom(k + c - al * s, be * s + d) for s, a in A.items()))
            rows, rhs, sl = build_system(al, be, c, d, 0, 0 if be == 0 else None, seq)
            verdict, x = decide(rows, rhs)
            if verdict != "sol":
                nf4 += 1
                print("FAIL L4b synthetic shape=(%d,%d) c=%d d=%d verdict=%s" % (al, be, c, d, verdict))
    print(("PASS" if nf4 == 0 else "FAIL") + " L4 reverse checks: sequences that do have a representation are reported solvable")
    res.append(("L4", nf4 == 0))

    nf = sum(1 for _, o in res if not o)
    print("SUMMARY linsys: %d PASS, %d FAIL  (%.1f s)" % (len(res) - nf, nf, time.time() - t0))
    return nf


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
