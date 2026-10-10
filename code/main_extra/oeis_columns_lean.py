# -*- coding: utf-8 -*-
r"""注记 3.5（Lean 续作第十一项）：从 OEIS 快照 data/lit/oeis/A207118.txt … A207122.txt 读出第 k = 3,…,7 列的
经验递推（%F Empirical 一行），核对其特征多项式恰为 (x−1)^{2k+1}(x+1)^{2k−1}（等价地：1 − Σ c_i x^i 等于
(1−x)^{2k+1}(1+x)^{2k−1}），并按原样生成 `lean/A207123/OeisRemark.lean` 里五个定理的陈述与系数表。

只读本地快照（快照是 2026-10 按 OEIS 只读规则取的原始页面），不联网。
用法（在任务 C 根目录）：py -3.14 code/main_extra/oeis_columns_lean.py [--lean]
不带参数只做核对；带 --lean 再把生成的 Lean 文本打印出来（贴进模块后由 Lean 编译核对）。
"""
import html
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SNAP = os.path.join(ROOT, 'data', 'lit', 'oeis')

COLS = {3: 'A207118', 4: 'A207119', 5: 'A207120', 6: 'A207121', 7: 'A207122'}


def empirical(aid):
    text = html.unescape(open(os.path.join(SNAP, aid + '.txt'), encoding='utf-8').read())
    lines = re.findall(r'%F Empirical: a\(n\) = ([^\n<]*)', text)
    assert len(lines) == 1, (aid, len(lines))
    rhs = lines[0].strip().rstrip('.')
    terms = re.findall(r'([+-]?)\s*(\d*)\*?a\(n-(\d+)\)', rhs)
    # 整行必须恰好由这些项组成
    rebuilt = re.sub(r'\s+', '', ''.join('%s%s%sa(n-%s)' % (s, c, '*' if c else '', i) for s, c, i in terms))
    assert rebuilt == re.sub(r'\s+', '', rhs), (aid, rebuilt, rhs)
    coef = {}
    for s, c, i in terms:
        v = int(c) if c else 1
        if s == '-':
            v = -v
        i = int(i)
        assert i not in coef
        coef[i] = v
    return rhs, coef


def poly_mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def pdenom(k):
    p = [1]
    for _ in range(2 * k + 1):
        p = poly_mul(p, [1, -1])
    for _ in range(2 * k - 1):
        p = poly_mul(p, [1, 1])
    return p


def lean_rhs(k, coef):
    out = []
    for i in sorted(coef):
        v = coef[i]
        term = 'a %d (n - %d)' % (k, i)
        if abs(v) != 1:
            term = '%d * %s' % (abs(v), term)
        if not out:
            out.append(term if v > 0 else '-' + term)
        else:
            out.append(('+ ' if v > 0 else '- ') + term)
    return out


def wrap(first, pieces, sep, indent, tail, width=110):
    """把 pieces 依次接在 first 后面（用 sep 连接），超过 width 就换行并缩进 indent，最后接 tail。"""
    lines = []
    cur = first
    for idx, p in enumerate(pieces):
        piece = p if idx == 0 else sep + p
        if idx > 0 and len(cur) + len(piece) > width:
            lines.append(cur.rstrip())
            cur = indent + (p if sep.strip() == '' else p)
        else:
            cur += piece
    lines.append(cur + tail)
    return '\n'.join(lines)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    ok = True
    gen = []
    for k, aid in COLS.items():
        rhs, coef = empirical(aid)
        d = 4 * k
        assert max(coef) == d, (aid, max(coef))
        lst = [1] + [-coef.get(i, 0) for i in range(1, d + 1)]
        good = lst == pdenom(k)
        ok &= good
        print('%s  k=%d  order %d  terms %d  1 - sum c_i x^i == (1-x)^%d (1+x)^%d: %s'
              % (aid, k, d, len(coef), 2 * k + 1, 2 * k - 1, 'PASS' if good else 'FAIL'))
        gen.append((k, aid, d, lst, lean_rhs(k, coef), rhs))
    print('ALL PASS' if ok else 'SOME FAIL')
    if '--lean' in sys.argv:
        names = {3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven'}
        for k, aid, d, lst, terms, rhs in gen:
            print()
            print('/-- 第 k = %d 列：`(1−x)^%d(1+x)^%d` 的系数（%s 的经验递推的系数取反，首项 1）。 -/' % (k, 2 * k + 1, 2 * k - 1, aid))
            print('theorem parDen_%s :' % names[k])
            items = [str(x) for x in lst]
            items = [x + ',' for x in items[:-1]] + [items[-1]]
            print(wrap('    parDen %d = ofList [' % k, items, ' ', '      ', '] := by'))
            print('  simp [parDen, ofList, Finset.sum_range_succ]')
            print('  ring')
            print()
            print('/-- **注记 3.5**（%s，第 k = %d 列）：OEIS 记的经验递推' % (aid, k))
            words = rhs.split()
            print(wrap('`a(n) = ', words, ' ', '', '`'))
            print('对一切 `n ≥ %d` 成立（OEIS 从 `n = 1` 编号；这里还含用到 `a_%d(0) = 1` 的 `n = %d`）。 -/' % (d, k, d))
            print('theorem oeis_%s (n : ℕ) (hn : %d ≤ n) :' % (aid, d))
            print(wrap('    (a %d n : ℤ) = ' % k, terms, ' ', '      ', ' := by'))
            print('  have h := col_rec (by norm_num) parDen_%s rfl hn' % names[k])
            print('  simp [Finset.sum_range_succ] at h')
            print('  qify')
            print('  linarith')


if __name__ == '__main__':
    main()
