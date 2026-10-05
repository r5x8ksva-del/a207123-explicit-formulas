# -*- coding: utf-8 -*-
"""一键重跑 r-c4ii 的全部复核脚本（从任意目录：py -3.14 <本文件路径>）。
各脚本的日志：logs/review_r-c4ii_<name>.log。r1 必须先跑（生成 numdp.json）。"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = ['r1_anchor.py', 'r2_positivity.py', 'r3_gcd.py', 'r4_lowhigh.py', 'r5_egf.py', 'r6_structure.py', 'r7_gcd_proof.py']
tot_fail = 0
for s in SCRIPTS:
    t = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, s)], cwd=HERE, capture_output=True, text=True, encoding='utf-8')
    last = [ln for ln in r.stdout.splitlines() if ln.startswith('SUMMARY')]
    print('%-18s %-28s exit=%d  %.1fs' % (s, last[-1] if last else 'NO SUMMARY', r.returncode, time.time() - t), flush=True)
    if r.returncode != 0 or not last or 'fail=0' not in last[-1]:
        tot_fail += 1
        print(r.stdout[-2000:], r.stderr[-2000:])
print('ALL OK' if tot_fail == 0 else 'SOME FAILED (%d scripts)' % tot_fail)
sys.exit(0 if tot_fail == 0 else 1)
