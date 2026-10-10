# -*- coding: utf-8 -*-
r"""注记 3.5 的行递推阶的最小性与不同乘积个数（Lean 续作第十六项）：在 Python 里核对，并生成
`lean/A207123/OeisRowOrders.lean` 里的系数表、Hankel 矩阵模 97 的逆的各列与各行定理。

论文注记 3.5：「by the Berlekamp–Massey algorithm their orders 10, 22, 28, 49, 55, 85 are minimal, and they are the
numbers of distinct products of a characteristic root of the first factor with one of the second」。
Lean 里的证明（本脚本逐项镜像其中要在内核里求值的部分）：
  ①最小性：k ↦ a_k(n) 从 k = 0 起满足常数项非零的 rowPoly 递推（第十一项 row_rec），所以一个只对 k ≥ k0 成立的
    d 阶递推可以向后延拓到 k ≥ 0；d < e 时 e×e 的 Hankel 矩阵 H = (a_{i+j}(n)) 就退化。行列式非零的证书是 H 模
    p = 97 的逆 W。核对用 Kronecker 代换（kronCheck）：S = Σ_k (a_k(n) mod p)·B^k（k ≤ 2e − 1，B = 2^20），第 j 列
    倒序打包 C_j = Σ_t W[e−1−t][j]·B^t；S·C_j 的第 e − 1 + i 位就是 (H·W)_{ij}（没有进位，因为
    (p − 1)·Σ_t W[t][j] < B），模 p 应为 δ_{ij}。
  ②不同乘积个数：每个根 σ ∈ sig m 在某一层 i ≤ m（i = 0 时 σ = 1，否则 σ³ − σ² = i）。σ^l 写成 A + Bσ + Cσ²
    （lvStep：(A, B, C) ↦ (iC, A, B + C)；i = 0 时不变）。lvCheck 核对每一对层 (i, j) 上 Σ_l γ_l (στ)^l 约化后的
    9 个系数都为 0，于是每个乘积都是 OEIS 特征多项式 Σ_l γ_l X^l（e 次）的根，个数 ≤ e；反过来 k ↦ a_k(n) 满足
    ∏_λ (X − λ)（λ 取遍不同乘积）给出的递推，由①个数 ≥ e。
γ 由第十四项的脚本 code/main_extra/oeis_rows_lean.py 从 OEIS 快照读出（前向形式 Σ_j γ_j a_{k+j}(n) = 0，γ_e = 1）。
另外：用 Berlekamp–Massey（模 1000003）核对线性复杂度就是 e；用 numpy（有的话）粗数不同乘积个数。
用法（在任务 C 根目录）：py -3.14 code/main_extra/oeis_row_orders_lean.py [--lean]
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('oeis_rows_lean', os.path.join(HERE, 'oeis_rows_lean.py'))
orl = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(orl)

P = 97
B = 2 ** 20
NAMES = {2: 'two', 3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven'}


def inv_mod(M, p):
    """M 模 p 的逆（Gauss–Jordan）；不可逆时返回 None。"""
    n = len(M)
    A = [[x % p for x in r] + [1 if i == j else 0 for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c]), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        iv = pow(A[c][c], p - 2, p)
        A[c] = [x * iv % p for x in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]
                A[r] = [(x - f * y) % p for x, y in zip(A[r], A[c])]
    return [r[n:] for r in A]


def of_dig(b, ds):
    """镜像 Lean 的 ofDig：d0 + b·(d1 + b·(…))。"""
    x = 0
    for d in reversed(ds):
        x = d + b * x
    return x


def kron_check(p, b, e, S, cols):
    """镜像 Lean 的 kronCheck p b e S cols 0。"""
    for j, c in enumerate(cols):
        if len(c) != e or not (p - 1) * sum(c) < b:
            return False
        x = S * of_dig(b, c) // b ** (e - 1)
        digs = []
        for _ in range(e):
            digs.append(x % b)
            x //= b
        if [d % p for d in digs] != [1 if i == j else 0 for i in range(e)]:
            return False
    return True


def bm_mod(s, p):
    C, Bc = [1], [1]
    L, m, b = 0, 1, 1
    for n_ in range(len(s)):
        d = s[n_] % p
        for i in range(1, L + 1):
            d = (d + C[i] * s[n_ - i]) % p
        if d == 0:
            m += 1
            continue
        T = C[:]
        coef = d * pow(b, p - 2, p) % p
        C = C + [0] * (len(Bc) + m - len(C))
        for i, x in enumerate(Bc):
            C[i + m] = (C[i + m] - coef * x) % p
        if 2 * L <= n_:
            L, Bc, b, m = n_ + 1 - L, T, d, 1
        else:
            m += 1
    return L


def pw_step(i, x):
    """镜像 Lean 的 lvStep：σ^{l+1} 的 (A, B, C)；i = 0 时 σ = 1，不变。"""
    if i == 0:
        return x
    A, Bq, C = x
    return (i * C, A, Bq + C)


def macc(i, j, u, v, gamma):
    """镜像 Lean 的 lvAcc i j u v γ (1,0,0) (1,0,0)：Σ_l γ_l·x_l[u]·y_l[v]。"""
    x, y, s = (1, 0, 0), (1, 0, 0), 0
    for g in gamma:
        s += g * x[u] * y[v]
        x, y = pw_step(i, x), pw_step(j, y)
    return s


def root_check(gamma, a, b):
    return all(macc(i, j, u, v, gamma) == 0 for i in range(a + 1) for j in range(b + 1)
               for u in range(3) for v in range(3))


def lean_list(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    ok = True
    gen = []
    for n, (aid, fn) in orl.ROWS.items():
        rhs, coef = orl.empirical(aid, fn)
        e = max(coef)
        gamma = [-coef.get(e - j, 0) for j in range(e)] + [1]
        K = 2 * e - 1
        vals = orl.row_vals(n, K)
        H = [[vals[i + j] for j in range(e)] for i in range(e)]
        W = inv_mod(H, P)
        cols = [[W[e - 1 - t][j] for t in range(e)] for j in range(e)] if W is not None else None
        S = of_dig(B, [v % P for v in vals])
        inv_ok = cols is not None and kron_check(P, B, e, S, cols)
        a1, b1 = (n + 1) // 2, n // 2
        rc = root_check(gamma, a1, b1)
        L = bm_mod(orl.row_vals(n, 2 * e + 40), 1000003)
        good = inv_ok and rc and gamma[0] != 0 and L == e and e == orl.ORDERS[n] and len(vals) == K + 1
        ok &= good
        print('%s row n=%d e=%d  Hankel inverse mod %d (kronCheck, B=2^20, max (p-1)*sum=%d) %s  '
              'lvCheck(levels <=%d,<=%d) %s  BM(mod 1000003)=%d  gamma_0=%d  %s'
              % (aid, n, e, P, max((P - 1) * sum(c) for c in cols) if cols else -1, 'PASS' if inv_ok else 'FAIL',
                 a1, b1, 'PASS' if rc else 'FAIL', L, gamma[0], 'PASS' if good else 'FAIL'))
        gen.append((n, aid, e, gamma, K, cols, a1, b1))
    try:
        import numpy as np
        for n, aid, e, gamma, K, cols, a1, b1 in gen:
            def roots(m):
                r = [1.0 + 0j]
                for i in range(1, m + 1):
                    r += list(np.roots([1, -1, 0, -i]))
                return r
            prods = [x * y for x in roots(a1) for y in roots(b1)]
            dist = []
            for z in prods:
                if all(abs(z - w) > 1e-7 for w in dist):
                    dist.append(z)
            good = len(dist) == e
            ok &= good
            print('row n=%d numeric distinct products %d of %d  %s' % (n, len(dist), len(prods), 'PASS' if good else 'FAIL'))
    except ImportError:
        print('numpy not available: numeric count skipped')
    print('ALL PASS' if ok else 'SOME FAIL')
    if '--lean' in sys.argv:
        for n, aid, e, gamma, K, cols, a1, b1 in gen:
            nm = NAMES[n]
            seq_thm = 'oeis_%s' % aid
            print()
            print('/-! ### 第 n = %d 行（%s，阶 %d） -/' % (n, aid, e))
            print()
            print('/-- 第 %d 行的 OEIS 递推的系数（前向形式，`γ_%d = 1`）。 -/' % (n, e))
            print('def rowGam%d : List ℤ := %s' % (n, lean_list(gamma)))
            print()
            print('set_option maxRecDepth 100000 in')
            print('/-- 第 %d 行 %d×%d Hankel 矩阵模 %d 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{%d,j}, …, W_{0,j}]`；'
                  '由脚本算出，`hankel_row_%s` 里核对）。 -/' % (n, e, e, P, e - 1, nm))
            print('def rowCols%d : List (List ℕ) := [' % n)
            for idx, c in enumerate(cols):
                print('  %s%s' % (lean_list(c), ',' if idx < len(cols) - 1 else ']'))
            print()
            print('/-- 辅助引理（注记 3.5）：第 %d 行的 OEIS 递推（`%s`）写成 `Σ_i γ_i·a_{k+i}(%d) = 0`。 -/' % (n, seq_thm, n))
            print('theorem row_rec_%s (k : ℕ) : ∑ i ∈ range (%d + 1), (rowGam%d.getD i 0 : ℂ) * (a (k + i) %d : ℂ) = 0 := by'
                  % (nm, e, n, n))
            print('  refine (sum_getD_eq_lsumC (fun j => (a (k + j) %d : ℂ)) rowGam%d 0).trans ?_' % (n, n))
            print('  have h2 := congrArg (Int.cast : ℤ → ℂ) (%s k)' % seq_thm)
            if n <= 3:
                print('  simp only [%s] at h2' % ('aAlt_two' if n == 2 else 'aAlt_three'))
            print('  push_cast at h2')
            print('  simp only [rowGam%d, lsumC, add_zero]' % n)
            print('  push_cast')
            print('  linear_combination h2')
            print()
            print('/-- 辅助引理（注记 3.5）：第 %d 行 %d×%d 的 Hankel 行列式 `det (a_{i+j}(%d))` 非零（模 %d 的逆作证书）。 -/'
                  % (n, e, e, n, P))
            print('theorem hankel_row_%s : (Matrix.of fun i j : Fin %d => (a (i + j) %d : ℂ)).det ≠ 0 :=' % (nm, e, n))
            print('  hankel_det_ne_zero_of_kron (p := %d) (B := 2 ^ 20) (K := %d) rowCols%d (by norm_num) (by norm_num) rfl'
                  % (P, K, n))
            print('    (by norm_num) (by decide +kernel)')
            print()
            print('/-- **注记 3.5**（第 %d 行递推的最小阶）：`k ↦ a_k(%d)` 的常系数递推（对一切充分大的 `k` 成立、首项系数'
                  '非零）的阶最小是 %d：OEIS 的 %d 阶递推（%s）从 `k = 0` 起成立，更低阶的都不成立。 -/' % (n, n, e, e, aid))
            print('theorem row_min_order_%s : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧' % nm)
            print('    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) %d : ℂ) = 0} %d :=' % (n, e))
            print('  row_isLeast (γ := rowGam%d) rfl row_rec_%s hankel_row_%s' % (n, nm, nm))
            print()
            print('/-- **注记 3.5**（第 %d 行：不同乘积的个数）：`σ ∈ sig %d`、`τ ∈ sig %d` 的乘积 `στ` 恰有 %d 个不同的值，'
                  '等于第 %d 行递推的最小阶。 -/' % (n, a1, b1, e, n))
            print('theorem card_row_products_%s : #((sig %d ×ˢ sig %d).image fun p => p.1 * p.2) = %d :=' % (nm, a1, b1, e))
            print('  le_antisymm (card_products_le (e := %d) (γ := rowGam%d) rfl rfl (by decide +kernel))' % (e, n))
            print('    (card_products_ge (n := %d) row_min_order_%s.2)' % (n, nm))


if __name__ == '__main__':
    main()
