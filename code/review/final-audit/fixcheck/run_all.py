# -*- coding: utf-8 -*-
"""fixcheck 汇总：依次运行本目录的只读核对脚本，输出合并到 logs/final_audit_fixcheck.log。"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(HERE))))
LOG = os.path.join(ROOT, 'logs', 'final_audit_fixcheck.log')
JOBS = [('f1_applied.py', []), ('f2_numeric_labels.py', []), ('f3_newton_2d1.py', ['101']),
        ('f3b_newton_detail.py', []), ('f4_tailbound.py', []), ('f5_math.py', [])]
env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
with open(LOG, 'w', encoding='utf-8') as out:
    out.write('# fixcheck（最终审计修订逐条复查）%s\n' % time.strftime('%Y-%m-%d %H:%M:%S'))
    for script, args in JOBS:
        t = time.time()
        p = subprocess.run([sys.executable, os.path.join(HERE, script)] + args, cwd=ROOT, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out.write('=' * 72 + '\n>>> %s %s (rc=%d, %.1fs)\n' % (script, ' '.join(args), p.returncode, time.time() - t))
        out.write(p.stdout.decode('utf-8', errors='replace'))
print('written', LOG)
