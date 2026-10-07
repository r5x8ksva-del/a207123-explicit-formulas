# -*- coding: utf-8 -*-
"""表 B 新结论中已并入论文的三项（2026-10-08 登记进 verify_all）：依次运行
  code/tableB/check_b1.py（A19：h_k 全实根且根互异，论文第 8 节），
  code/tableB/check_b3.py（A20：单族二项式形状的分类，论文定理 6.3），
  code/tableB/check_b2.py（A21：两族 u 型和不存在，论文第 6.2 节；含 T=5040 的筛法与 l 进证书计算），
原样转印各条 PASS / FAIL，最后一行「SUMMARY tb pass=<n> fail=<n>」。子脚本异常退出或缺少 SUMMARY 时记一条 FAIL。
A22（B7，check_b7.py、check_b7_borel.py）与 B11（check_b11.py）没有进论文，仍只在 code/tableB/run_all.py 里。
需要 numpy（check_b2.py 的筛法；其余只用来求近似根，判定都是精确运算）。实测峰值约 0.4 GB，用时约半分钟。
"""
import os
import subprocess
import sys
import time

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
TABLEB = os.path.join(ROOT, 'code', 'tableB')
PARTS = ['b1', 'b3', 'b2']

t0 = time.time()
env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
n_pass = n_fail = 0
for part in PARTS:
    proc = subprocess.run([sys.executable, os.path.join(TABLEB, 'check_%s.py' % part)], cwd=ROOT, env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = proc.stdout.decode('utf-8', errors='replace')
    lines = out.splitlines()
    for ln in lines:
        if ln.startswith('SUMMARY '):
            print('INFO tb sub-' + ln)          # the sub-script's own summary; the module summary is the last line
        else:
            print(ln)
    p = sum(1 for ln in lines if ln.startswith('PASS '))
    f = sum(1 for ln in lines if ln.startswith('FAIL '))
    n_pass += p
    n_fail += f
    if proc.returncode != 0 or not any(ln.startswith('SUMMARY ') for ln in lines) or p == 0:
        n_fail += 1
        print('FAIL tb-%s-run 子脚本退出码 %d，PASS %d 条，SUMMARY %s' %
              (part, proc.returncode, p, '有' if any(ln.startswith('SUMMARY ') for ln in lines) else '缺'))
print('SUMMARY tb pass=%d fail=%d  (%.1fs)' % (n_pass, n_fail, time.time() - t0))
sys.exit(0 if n_fail == 0 else 1)
