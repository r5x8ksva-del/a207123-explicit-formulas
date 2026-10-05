# -*- coding: utf-8 -*-
"""审计 a1-formulas：依次运行本目录全部审计脚本，汇总 PASS/FAIL（py -3.14 run_all.py）。"""
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = ['audit_c1.py', 'audit_c2.py', 'audit_c3.py', 'audit_c3b.py', 'audit_c3_extra.py', 'audit_c3_num.py',
           'audit_c3_K.py', 'audit_c4.py', 'audit_c4_patterns.py', 'audit_c5.py', 'audit_c5_extra.py', 'audit_misc.py']
try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
tp = tf = 0
t0 = time.time()
for s in SCRIPTS:
    t1 = time.time()
    out = subprocess.run([sys.executable, os.path.join(HERE, s)], cwd=HERE, env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.decode('utf-8', 'replace')
    print('=' * 70)
    print('>>> %s' % s)
    print(out.rstrip())
    m = re.search(r'SUMMARY \S+ pass=(\d+) fail=(\d+)', out)
    if m:
        tp += int(m.group(1))
        tf += int(m.group(2))
    else:
        tf += 1
        print('!! no SUMMARY line')
    print('(%.1fs)' % (time.time() - t1))
print('=' * 70)
print('TOTAL pass=%d fail=%d (%.1fs)' % (tp, tf, time.time() - t0))
