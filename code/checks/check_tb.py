# -*- coding: utf-8 -*-
"""表 B 新结论的核对（2026-10-08 登记 b1、b3、b2；2026-10-09 并入报告时扩到 code/tableB/run_all.py 的全部 13 个部分）：依次运行
  code/tableB/check_b1.py（A19：h_k 全实根且根互异，报告 T5.3(6)、论文第 8 节），
  code/tableB/check_b3.py（A20：单族二项式形状的分类，报告 T2.6(i)、论文定理 6.3），
  code/tableB/check_b2.py（A21：两族 u 型和不存在，报告 T2.6(iii)、论文第 6.2 节；含 T=5040 的筛法与 l 进证书计算），
  code/tableB/check_b7.py、check_b7_borel.py（A22：f_k 的 Gevrey-1/3 上界与 t<0 时的 3-可和性，报告 T3.4(5)；后者是数值佐证），
  code/tableB/check_b11.py（B11：二阶 Euler 型非负展开 d<=100 不存在，报告 T4.2(2)），
  code/tableB/check_b6.py（A23：只用一元 1F1 / 不完全 Gamma 的整表闭式不存在，报告 T3.3(3)），
  code/tableB/check_b4.py、check_b5.py、check_b5_skel.py（A24–A27：更短公式的精确化、N 的单和与骨架型两层和，报告 T2.5(3)、T2.6、T2.8(3)），
  code/tableB/check_b8.py、check_b9.py（A28、A29：U_k 的负整数零点、h_k 的系数，报告 T5.3(2)(5)(7)；默认模式），
  code/tableB/check_b13.py（A30：t<0 时 f_k(t) 的精确 Gevrey 常数与 (★)，报告 T3.4(5)、T5.3(7)），
原样转印各条 PASS / FAIL，最后一行「SUMMARY tb pass=<n> fail=<n>」。子脚本异常退出或缺少 SUMMARY 时记一条 FAIL。
check_b8.py、check_b9.py 的完整范围（k<=300、i<=40）用 --full 单独运行（约 13 分钟、2 分钟），不在这里，日志见 logs/tableB_check_b8_full.log、
logs/tableB_check_b9_full.log。需要 numpy。实测峰值约 0.4 GB，用时约 4–5 分钟（主要是 check_b11.py 与 check_b5.py）。
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
PARTS = ['b1', 'b3', 'b2', 'b7', 'b7_borel', 'b11', 'b6', 'b4', 'b5', 'b5_skel', 'b8', 'b9', 'b13']

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
