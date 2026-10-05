# -*- coding: utf-8 -*-
"""最终审计（requirements）r2：检验报告 00_head 的说法「只依赖 Python 标准库；装有 numpy 时 c3b 与 rv2 会用它加速」。
做法：在屏蔽 numpy 的解释器里（sys.modules['numpy']=None 使 import numpy 抛 ImportError）
  (a) 运行 rv2 调用的子脚本 code/review/x1-single-sum/r2_two_family.py（小参数 20 20，只打印，不写文件）；
  (b) 运行 code/checks/check_c3b.py 的导入部分是否有回退（只看源码里的 try/except，不运行，因它不写文件但耗时）。
只读：不修改任何文件，子进程输出只打印到 stdout。
"""
import os
import subprocess
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
X1 = os.path.join(ROOT, 'code', 'review', 'x1-single-sum')
script = os.path.join(X1, 'r2_two_family.py')
src = open(script, encoding='utf-8').read()
print('[a] r2_two_family.py has unconditional "import numpy as np":', '\nimport numpy as np' in src,
      '; has try/except around it:', 'except ImportError' in src or 'except Exception' in src)
code = ("import sys; sys.modules['numpy']=None; sys.argv=[%r,'20','20']; "
        "__file__=%r; exec(compile(open(%r,encoding='utf-8').read(), %r, 'exec'))") % (script, script, script, script)
env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
p = subprocess.run([sys.executable, '-c', code], cwd=X1, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out = p.stdout.decode('utf-8', errors='replace')
print('[a] return code without numpy:', p.returncode)
print('[a] last lines:')
for ln in out.strip().splitlines()[-6:]:
    print('     ', ln)
c3b = open(os.path.join(ROOT, 'code', 'checks', 'check_c3b.py'), encoding='utf-8').read()
print('[b] check_c3b.py wraps numpy import in try/except (fallback HAVE_NP):', 'HAVE_NP = False' in c3b)
# 其他 check 模块与 core/polylib 是否导入 numpy
for d in ('code/checks', 'code'):
    for fn in sorted(os.listdir(os.path.join(ROOT, d))):
        if fn.endswith('.py'):
            s = open(os.path.join(ROOT, d, fn), encoding='utf-8').read()
            if 'import numpy' in s:
                print('[c] %s/%s imports numpy' % (d, fn))
