# -*- coding: utf-8 -*-
"""Final audit (consistency): does verify_all really run on the standard library alone?
Runs the two x1 scripts that check_rv2.py calls, with numpy blocked via a fake package on PYTHONPATH.
Output goes only to stdout (no project files are written; the x1 scripts themselves write nothing)."""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
X1 = os.path.join(ROOT, 'code', 'review', 'x1-single-sum')
sys.stdout.reconfigure(encoding='utf-8')
env = dict(os.environ, PYTHONPATH=os.path.join(HERE, 'nonumpy'), PYTHONUTF8='1', PYTHONIOENCODING='utf-8')
for script, args in (('r1_numfield_residues.py', []), ('r2_two_family.py', ['50', '50'])):
    p = subprocess.run([sys.executable, os.path.join(X1, script)] + args, cwd=X1, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode('utf-8', 'replace').strip().splitlines()
    print('[numpy blocked] %s rc=%d last line: %s' % (script, p.returncode, out[-1] if out else ''))
