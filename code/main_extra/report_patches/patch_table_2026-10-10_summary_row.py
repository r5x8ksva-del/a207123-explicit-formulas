# -*- coding: utf-8 -*-
r"""2026-10-10（Lean 续作第二十七至五十四项之后）：猜想总表「表 A 已证明」汇总行按各行现状更新形式化情况。
只改这一行的两处：括号里「A19–A31 都是书面证明 + 核对，未形式化」与「全部或主体 / 部分 / 只有书面证明」三组名单。
各组名单逐行对照了表 A 各行的「Lean」句子（2026-10-10 晚的状态）。每处替换断言原文出现一次；按字节读写（LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_table_2026-10-10_summary_row.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

TABLE = [
    ('2026-10-09 新增 A30、A31（都是书面证明 + 核对，未形式化；',
     '2026-10-09 新增 A30、A31（都是书面证明 + 核对；2026-10-10 的 Lean 续作之后，A19、A20 已主体形式化，A24、A25、'
     'A26、A28、A29 已部分形式化，范围见各行；'),
    ('全部或主体已机器检查的：A2、A3、A4、A6、A7、A9、A10、A13、A14，以及 A15 的列方向；部分机器检查的：A1、A5、A8、'
     'A11、A16、A18 的前半；只有书面证明 + 程序核对的：A12、A17、A18 的推论；',
     '全部或主体已机器检查的（2026-10-10 晚）：A1、A2、A3、A4、A6、A7、A9、A10、A11、A12、A13、A14、A15、A16、A19、A20；'
     '部分机器检查的：A5（(4) 与 A000262 组合定义的等同、(6) 的一般结构、(7) 未形式化）、A8（T3.2 的形式 Laplace 表示、'
     'T3.3 的 Kummer 单级数形式与 Humbert 闭式未形式化）、A18 的前半、A24（β≥0、α+β=1 一侧）、A25（(a)、(b) 与 (d) 的'
     '存在部分）、A26（(ii) 的三原子存在唯一与「每个 i 一个原子不存在」、(iii) 的存在例子）、A28（(i)–(iii)）、A29（(ii)、'
     '(iii) 的前两句与乘积式）；只有书面证明 + 程序核对的：A17、A18 的推论、A21、A22、A23、A27、A30、A31；'),
]


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    path = os.path.join(ROOT, '猜想总表.md')
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in TABLE:
        c = s.count(old)
        assert c == 1, (c, old[:60])
        s = s.replace(old, new)
    open(path, 'wb').write(s.encode('utf-8'))
    print('猜想总表.md: %d edits' % len(TABLE))


if __name__ == '__main__':
    main()
