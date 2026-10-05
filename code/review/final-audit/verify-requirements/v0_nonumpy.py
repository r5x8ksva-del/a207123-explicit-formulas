# -*- coding: utf-8 -*-
"""verify-requirements / finding #0：在「没有 numpy」的环境下，哪些核对模块还能跑通？

做法：把 nonumpy_shadow/ 放到 PYTHONPATH 最前面，其中的假 numpy 包一 import 就抛 ModuleNotFoundError，
这样子进程（verify_all -> check_*.py -> check_rv2 再起的子进程）也都看不到 numpy。
  (1) sanity：shadow 下 import numpy 必须失败；
  (2) 直接运行 rv2 调用的两个复核脚本 r1/r2（cwd 与参数同 check_rv2；不经过 check_rv2，以免覆盖 logs/rv2_x1_*.log）；
  (3) 用 verify_all.py 跑除 rv2 以外的 10 个模块（verify_all 只往 stdout 打印，不写文件）。
只读：不改动任何报告/笔记/核对模块文件。
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
SHADOW = os.path.join(HERE, 'nonumpy_shadow')
X1 = os.path.join(ROOT, 'code', 'review', 'x1-single-sum')
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
env['PYTHONPATH'] = SHADOW + (os.pathsep + env['PYTHONPATH'] if env.get('PYTHONPATH') else '')


def run(args, cwd, tag, tail=12):
    t = time.time()
    p = subprocess.run([sys.executable] + args, cwd=cwd, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode('utf-8', errors='replace')
    lines = out.splitlines()
    print('---- %s  rc=%d  (%.1fs)  PASS=%d FAIL=%d' % (
        tag, p.returncode, time.time() - t,
        sum(1 for ln in lines if ln.startswith('PASS ')),
        sum(1 for ln in lines if ln.startswith('FAIL '))))
    for ln in lines[-tail:]:
        print('    | ' + ln)
    return p.returncode, out


print('== finding #0: no-numpy runs (shadow=%s)' % SHADOW)
rc, out = run(['-c', 'import numpy'], ROOT, 'sanity: import numpy under shadow', tail=3)
print('sanity ok (import must fail):', rc != 0)
rc1, _ = run([os.path.join(X1, 'r1_numfield_residues.py')], X1, 'rv2 sub-script r1_numfield_residues.py', tail=4)
rc2, _ = run([os.path.join(X1, 'r2_two_family.py'), '6000', '1500'], X1, 'rv2 sub-script r2_two_family.py 6000 1500', tail=6)
mods = ['c0', 'c1', 'c2a', 'c2b', 'c3a', 'c3b', 'c4', 'c5a', 'c5b', 'rv']
rc3, out3 = run([os.path.join(ROOT, 'verify_all.py')] + mods, ROOT, 'verify_all.py ' + ' '.join(mods), tail=18)
c3b_np = [ln for ln in out3.splitlines() if 'numpy=' in ln]
print('c3b numpy flag line:', c3b_np)
print('RESULT #0: r1 rc=%d, r2 rc=%d (nonzero => rv2 would FAIL without numpy); other 10 modules rc=%d' % (rc1, rc2, rc3))
