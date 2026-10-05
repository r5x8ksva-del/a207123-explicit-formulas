# -*- coding: utf-8 -*-
"""verify-fixcheck：运行本目录的核对脚本，输出写到 logs/final_audit_verify-fixcheck.log。"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
OUT = os.path.join(ROOT, 'logs', 'final_audit_verify-fixcheck.log')
JOBS = [('v0_newton_2d1.py', ['101']), ('v_misc.py', [])]

with open(OUT, 'w', encoding='utf-8') as f:
    f.write('# verify-fixcheck（对 fixcheck 发现 #0–#9 的对抗性复核）%s\n' % time.strftime('%Y-%m-%d %H:%M:%S'))
    for script, args in JOBS:
        t = time.time()
        env = dict(os.environ, PYTHONUTF8='1', PYTHONIOENCODING='utf-8')
        p = subprocess.run([sys.executable, os.path.join(HERE, script)] + args, cwd=ROOT, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        f.write('=' * 72 + '\n>>> %s %s (rc=%d, %.1fs)\n' % (script, ' '.join(args), p.returncode, time.time() - t))
        f.write(p.stdout.decode('utf-8', errors='replace'))
print('written', OUT)
