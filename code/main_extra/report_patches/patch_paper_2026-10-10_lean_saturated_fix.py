# -*- coding: utf-8 -*-
"""patch_paper_2026-10-10_lean_saturated.py 的后续：表 5 第一列是 l 列（不换行），新加的「Corollary 5.5, with denominators
cleared」把表格撑宽约 20pt（Tectonic 报 Overfull hbox）。把「with denominators cleared」移到第二列（p 列，会换行）。
用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_saturated_fix.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
B = chr(92)
OLD = ('Corollary~' + B + 'ref{cor:saturated}, with denominators cleared & ' + B + 'lean{mul' + B + '_mem' + B + '_ideal'
       + B + '_of' + B + '_vanish}, ' + B + 'lean{mem' + B + '_ideal' + B + '_of' + B + '_mul' + B + '_mem' + B + '_ideal}' + B + B)
NEW = ('Corollary~' + B + 'ref{cor:saturated} & ' + B + 'lean{mul' + B + '_mem' + B + '_ideal' + B + '_of' + B + '_vanish}, '
       + B + 'lean{mem' + B + '_ideal' + B + '_of' + B + '_mul' + B + '_mem' + B + '_ideal} (with denominators cleared)' + B + B)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    p = os.path.join(ROOT, 'paper', 'main.tex')
    s = open(p, 'rb').read().decode('utf-8')
    assert s.count(OLD) == 1, s.count(OLD)
    open(p, 'wb').write(s.replace(OLD, NEW).encode('utf-8'))
    print('paper/main.tex: 1 edit')


if __name__ == '__main__':
    main()
