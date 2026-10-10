# -*- coding: utf-8 -*-
r"""注记 3.5 的行递推（Lean 续作第十四项）：从 OEIS 快照读出 A207123 第 n = 2,…,7 行（A207069、A207070、A207124–A207127）
的经验递推（%F … Empirical 一行），在 Python 里用精确整数核对，并生成 `lean/A207123/OeisRows.lean` 里的陈述与系数表。

快照（只读，2026-10 按 OEIS 只读规则取得）：data/oeis/A207069.txt、A207070.txt（条目原文），
data/oeis/search_ref_A207123.txt、search_ref_A207123_p2.txt（检索结果里的 A207124–A207127 条目原文）。

记号：a_k(n) = U_k(⌈n/2⌉)·U_k(⌊n/2⌋)（k 列 n 行的矩阵个数）；行条目的 a(N) 是 N 列矩阵的个数，即 a_N(n)。
OEIS 的经验递推 a(N) = Σ_{i=1}^{e} c_i a(N−i) 写成前向形式 Σ_{j=0}^{e} γ_j a_{k+j}(n) = 0（N = k + e），
γ_e = 1、γ_{e−i} = −c_i。论文注记 3.5 的判据：Δ_n = (3⌈n/2⌉+1)(3⌊n/2⌋+1)，前向递推只要在 Δ_n 个相邻的 k 上成立，
就对其后一切 k 成立。Lean 里在 k = k0, …, k0 + Δ_n − 1 上用 decide +kernel 核对（列表长 K + 1，K = k0 + Δ_n + e）。

本脚本核对：①递推在 Lean 要核的窗口上成立；②在更长的范围（到 k = 3K）上也成立（与判据一致）；③k0 取多少：
OEIS 从 N = 1 编号，递推本来只对 N ≥ e + 1（k ≥ 1）陈述；若在 k = 0（用到 a_0(n) = 1）也成立，就取 k0 = 0。
用法（在任务 C 根目录）：py -3.14 code/main_extra/oeis_rows_lean.py [--lean]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SNAP = os.path.join(ROOT, 'data', 'oeis')

ROWS = {2: ('A207069', 'A207069.txt'), 3: ('A207070', 'A207070.txt'), 4: ('A207124', 'search_ref_A207123.txt'),
        5: ('A207125', 'search_ref_A207123.txt'), 6: ('A207126', 'search_ref_A207123.txt'),
        7: ('A207127', 'search_ref_A207123_p2.txt')}
ORDERS = {2: 10, 3: 22, 4: 28, 5: 49, 6: 55, 7: 85}       # 论文注记 3.5 写的阶


def empirical(aid, fn):
    lines = [l for l in open(os.path.join(SNAP, fn), encoding='utf-8').read().splitlines()
             if l.startswith('%%F %s Empirical: a(n) = ' % aid)]
    assert len(lines) == 1, (aid, len(lines))
    rhs = lines[0].split(' = ', 1)[1].strip().rstrip('.')
    terms = re.findall(r'([+-]?)\s*(\d*)\*?a\(n-(\d+)\)', rhs)
    rebuilt = ''.join('%s%s%sa(n-%s)' % (s, c, '*' if c else '', i) for s, c, i in terms)
    assert rebuilt == re.sub(r'\s+', '', rhs), (aid, rebuilt[:80], rhs[:80])
    coef = {}
    for s, c, i in terms:
        v = int(c) if c else 1
        coef[int(i)] = -v if s == '-' else v
    return rhs, coef


def ucols(M, K):
    """cols[m] = [U_0(m), …, U_K(m)]，按引理 1：U_k(m+1) = U_k(m) + U_{k-1}(m+1) + (m+1)·U_{k-3}(m+1)（U_{-1}=1、U_{-2}=0；U_0 = 1）。"""
    cols = [[1] * (K + 1)]
    for m in range(M):
        p = cols[-1]
        v = [1]
        for k in range(1, K + 1):
            prev = v[k - 1]
            three = v[k - 3] if k >= 3 else (1 if k == 2 else 0)
            v.append(p[k] + prev + (m + 1) * three)
        cols.append(v)
    return cols


def row_vals(n, K):
    cols = ucols((n + 1) // 2, K)
    return [cols[(n + 1) // 2][k] * cols[n // 2][k] for k in range(K + 1)]


def rowOrd(n):
    return (3 * ((n + 1) // 2) + 1) * (3 * (n // 2) + 1)


def holds(vals, gamma, k):
    return sum(g * vals[k + j] for j, g in enumerate(gamma)) == 0


def wrap(first, pieces, indent, tail, width=110):
    lines, cur = [], first
    for idx, p in enumerate(pieces):
        piece = p if idx == 0 else ' ' + p
        if idx > 0 and len(cur) + len(piece) > width:
            lines.append(cur.rstrip())
            cur = indent + p
        else:
            cur += piece
    lines.append(cur + tail)
    return '\n'.join(lines)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    ok = True
    gen = []
    for n, (aid, fn) in ROWS.items():
        rhs, coef = empirical(aid, fn)
        e = max(coef)
        gamma = [-coef.get(e - j, 0) for j in range(e)] + [1]
        D = rowOrd(n)
        vals = row_vals(n, 3 * (D + e + 2))
        k0 = 0 if holds(vals, gamma, 0) else 1
        K = k0 + D + e
        win = all(holds(vals, gamma, k) for k in range(k0, k0 + D))
        far = all(holds(vals, gamma, k) for k in range(k0, len(vals) - e))
        good = win and far and e == ORDERS[n] and (k0 == 0 or holds(vals, gamma, 1))
        ok &= good
        print('%s  row n=%d  order %d (paper %d)  Delta_n=%d  k0=%d (holds at k=0: %s)  K=%d  window %s  up to k=%d %s  max|c|=%d digits'
              % (aid, n, e, ORDERS[n], D, k0, holds(vals, gamma, 0), K, 'PASS' if win else 'FAIL', len(vals) - e - 1,
                 'PASS' if far else 'FAIL', max(len(str(abs(v))) for v in coef.values())))
        gen.append((n, aid, rhs, coef, e, gamma, D, k0, K))
    print('ALL PASS' if ok else 'SOME FAIL')
    if '--lean' in sys.argv:
        for n, aid, rhs, coef, e, gamma, D, k0, K in gen:
            seq = 'aAlt' if n <= 3 else 'a'
            terms = []
            for i in sorted(coef):
                v = coef[i]
                t = '%s (k + %d) %d' % (seq, e - i, n) if e - i else '%s k %d' % (seq, n)
                if abs(v) != 1:
                    t = '%d * %s' % (abs(v), t)
                terms.append(t if not terms and v > 0 else ('-' + t if not terms else ('+ ' if v > 0 else '- ') + t))
            print()
            print('/-- **注记 3.5**（%s，第 n = %d 行）：OEIS 记的经验递推' % (aid, n))
            print(wrap('`a(n) = ', rhs.split(), '', '`'))
            print('（%s 的 `a(n)` 是 %d×n 矩阵的个数，即这里的 `%s n %d`）对一切 `n ≥ %d` 成立；这里写成 `n = k + %d`'
                  '（`k ≥ %d`）。 -/' % (aid, n, seq, n, k0 + e, e, k0))
            hyp = '' if k0 == 0 else ' (hk : %d ≤ k)' % k0
            print('theorem oeis_%s (k : ℕ)%s :' % (aid, hyp))
            print(wrap('    (%s (k + %d) %d : ℤ) = ' % (seq, e, n), terms, '      ', ' := by'))
            print('  have h := (sum_getD_eq_lsumC (fun j => (a (k + j) %d : ℂ)) _ 0).symm.trans' % n)
            print(wrap('    (row_rec_of_check (n := %d) (K := %d) (k0 := %d) (γ := [' % (n, K, k0),
                       [str(g) + (',' if j < len(gamma) - 1 else '') for j, g in enumerate(gamma)], '      ',
                       ']) (by decide)'))
            print('      (by norm_num [rowOrd]) (by decide +kernel) k %s)' % ('(Nat.zero_le k)' if k0 == 0 else 'hk'))
            print('  simp only [lsumC, add_zero] at h')
            print('  push_cast at h')
            if n <= 3:
                print('  simp only [%s]' % ('aAlt_two' if n == 2 else 'aAlt_three'))
            print('  apply Int.cast_injective (α := ℂ)')
            print('  push_cast')
            print('  linear_combination h')


if __name__ == '__main__':
    main()
