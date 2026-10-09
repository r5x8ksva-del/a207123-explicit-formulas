# -*- coding: utf-8 -*-
"""猜想总表.md 表格行里没有转义的竖线（整除号 a | b、绝对值 |x|）会让 GitHub 把一行拆成多列。
2026-10-09 晚检查时发现 A25、A28、A29、B8 四行有这个问题（都是早先几轮写的），这里统一改成 \\|。
改完断言：表 A、表 B 每一行恰有 7 个未转义的竖线（6 列）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_tableB_2026-10-09_pipes.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
BS = chr(92)

REPS = [
    (r'|n|,|b|≤300', r'\|n\|,\|b\|≤300'),
    (r'所以 p^e | j 时 U_k(−j)≡1', r'所以 p^e \| j 时 U_k(−j)≡1'),
    (r'零点 −j 只能有 j | lcm(1..k)（p=2', r'零点 −j 只能有 j \| lcm(1..k)（p=2'),
    (r'恒等式与 p | C(p^e,i)', r'恒等式与 p \| C(p^e,i)'),
    (r'且 j | lcm(1..k) 的 71,660,856 个 j', r'且 j \| lcm(1..k) 的 71,660,856 个 j'),
    (r'limsup|h_{3n+r}(−1)/n!|^{1/n}', r'limsup\|h_{3n+r}(−1)/n!\|^{1/n}'),
    (r'：p^e | j、p^e>k 时', r'：p^e \| j、p^e>k 时'),
    (r'所以候选只剩 j | lcm(1..k)；', r'所以候选只剩 j \| lcm(1..k)；'),
]


def unescaped_pipes(line):
    return sum(1 for i, c in enumerate(line) if c == '|' and (i == 0 or line[i - 1] != BS))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    p = os.path.join(ROOT, '猜想总表.md')
    raw = open(p, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in REPS:
        c = s.count(old)
        assert c == 1, (c, old)
        s = s.replace(old, new)
    a = s.index('## 表 A')
    c_ = s.index('## 表 C')
    bad = [ln[:8] for ln in s[a:c_].split('\n')
           if (ln.startswith('| A') or ln.startswith('| B')) and unescaped_pipes(ln) != 7]
    assert not bad, bad
    open(p, 'wb').write(s.encode('utf-8'))
    print('猜想总表.md: %d edits; 表 A、B 的每一行都是 6 列' % len(REPS))


if __name__ == '__main__':
    main()
