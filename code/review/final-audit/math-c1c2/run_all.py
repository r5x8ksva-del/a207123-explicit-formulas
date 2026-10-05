# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 : run every audit script of this direction and write one combined log
logs/final_audit_math-c1c2.log  (scripts import only the self-written mylib.py; no core/polylib)."""
import os, sys, subprocess, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
SCRIPTS = ['a1_refined.py', 'a1b_extended.py', 'a2_numfield.py', 'a3_skeleton.py', 'a4_c1.py', 'a5_formula.py', 'a6_ids.py', 'a7_quotes.py']
env = dict(os.environ, PYTHONUTF8='1', PYTHONIOENCODING='utf-8')
out = ['# final audit math-c1c2 (02_C1.md, 03_C2.md, 07_formula.md) -- %s' % time.strftime('%Y-%m-%d %H:%M:%S')]
tp = tf = 0
for s in SCRIPTS:
    t = time.time()
    p = subprocess.run([sys.executable, os.path.join(HERE, s)], cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    txt = p.stdout.decode('utf-8', errors='replace').rstrip()
    out.append('=' * 72)
    out.append('>>> %s (rc=%d, %.1fs)' % (s, p.returncode, time.time() - t))
    out.append(txt)
    tp += sum(1 for l in txt.splitlines() if l.startswith('PASS '))
    tf += sum(1 for l in txt.splitlines() if l.startswith('FAIL '))
out.append('=' * 72)
out.append('TOTAL PASS=%d FAIL=%d' % (tp, tf))
open(os.path.join(ROOT, 'logs', 'final_audit_math-c1c2.log'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('TOTAL PASS=%d FAIL=%d' % (tp, tf))
