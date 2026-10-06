# -*- coding: utf-8 -*-
"""2026-10-07 更新 T3.9(3) 中「Kauers 定义怎么读」的说明。

主 Agent 对照 Kauers 2007 §2.2–§3（RISC 公开版，来源与哈希见 data/lit/read_papers.md）：序列取为 f: Z²→C，零化子是 Q·f≡0 的算子全体，
比「在象限上零化」更强；所以 U 的任何延拓若是 Stirling-like，其三项生成元就在 N² 的某个象限上零化 U，T3.9(3) 覆盖 Kauers 的定义。
原文里担心的「每个象限里都有无穷多个例外点」的情形在 Kauers 的定义下不出现。
用法：py -3.14 code/main_extra/report_patches/patch_kauers_reading.py [--dry]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
DRY = '--dry' in sys.argv
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

NOTE = 'notes/04-主Agent-U不是Stirling-like.md'
name = '04_C3.md'
path = os.path.join(PARTS, name)
t = open(path, encoding='utf-8').read()
old = '(3) 对 Kauers 定义的读法（零化在哪些点成立）是书面的，例外点若在每个象限里都有无穷多个，论证需要修改，见 ' + NOTE + ' §3。'
new = ('(3) 对 Kauers 定义的读法：Kauers 2007 §2.2 把序列取在整个 Z² 上，零化子要求 Q·f≡0（主 Agent 2026-10-07 对照 RISC 公开版原文），'
       '比「在象限上零化」更强；U 的任何延拓若是 Stirling-like，其三项生成元就在 N² 的某个象限上（系数有定义处）零化 U，所以 (3) 覆盖 Kauers 的定义。'
       '这一步是书面论证，人还没核对，见 ' + NOTE + ' §3。')
n = t.count(old)
assert n == 1, '锚点出现 %d 次' % n
t = t.replace(old, new)
if DRY:
    print('would patch', name)
else:
    with open(path, 'w', encoding='utf-8') as f:
        f.write(t)
    print('patched', name)
