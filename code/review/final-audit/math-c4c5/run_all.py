# -*- coding: utf-8 -*-
"""final-audit math-c4c5：依次运行 s1..s10，汇总输出到 logs/final_audit_math-c4c5.log。"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
SCRIPTS = ['s1_T41.py', 's2_patterns.py', 's3_num.py', 's4_num2.py', 's5_c5.py', 's6_misc.py',
           's7_oeis.py', 's8_bij3.py', 's9_stirling_assoc.py', 's10_nk.py', 's11_quotes.py']
lines = []
t0 = time.time()
npass = nfail = 0
for s in SCRIPTS:
    env = dict(os.environ, PYTHONUTF8='1', PYTHONIOENCODING='utf-8')
    t = time.time()
    p = subprocess.run([sys.executable, os.path.join(HERE, s)], cwd=HERE, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode('utf-8', errors='replace')
    lines.append('=' * 72)
    lines.append('>>> %s  (rc=%d, %.1fs)' % (s, p.returncode, time.time() - t))
    lines.extend(out.rstrip('\n').splitlines())
    npass += sum(1 for ln in out.splitlines() if ln.startswith('PASS '))
    nfail += sum(1 for ln in out.splitlines() if ln.startswith('FAIL ')) + (1 if p.returncode else 0)
lines.append('=' * 72)
lines.append('TOTAL pass=%d fail=%d (%.1fs)' % (npass, nfail, time.time() - t0))
text = '\n'.join(lines) + '\n'
with open(os.path.join(ROOT, 'logs', 'final_audit_math-c4c5.log'), 'w', encoding='utf-8') as f:
    f.write(text)
print(text)
sys.exit(0 if nfail == 0 else 1)
