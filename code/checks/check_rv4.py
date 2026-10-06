# -*- coding: utf-8 -*-
"""check_rv4：T2.6(ii)（截断块部分对一切 m≥2 没有 u 型单和）的主 Agent 独立重推所依赖的计算（2026-10-07 加入）。

  rv4-t26ii-a   E 部分的母函数：以上升结尾的合法序列数 E(k,m) 的母函数等于 (W_m−1)/P_m（自写 DP，1≤m≤6，0≤k≤30）
  rv4-t26ii-b   在 b_i 的根 η 处：b_v(η)=(i−v)η³、η·b_i′(η)=2η−3（1≤i≤8，0≤v≤44）
  rv4-t26ii-c   留数闭式 Res_η E_m·u′(η) = (−1)^{m−i+1}(W̃_i(η)−1)η^{−3m−3}/((m−i)!·i!·i²) 在 Q[x]/(b_i) 中精确成立（1≤i≤8，i≤m≤40）
  rv4-t26ii-d1  K_2=Q[x]/(2x³+x−1) 中 N(η)=1/2、N(4−2η)=68
  rv4-t26ii-d2  W̃_2(η)−1 = η⁵(4−2η)
  rv4-t26ii-d3  N(W̃_2(η)−1) = 17/8
  rv4-t26ii-d4  对 −60≤n≤60，N((4−2η)η^n) 的 17-进赋值都是 1（不是有理数的立方）
  rv4-t26ii-e1  b_1、b_2 在 Q 上不可约（有理根检验）
  rv4-t26ii-e2  b_4 可约（有根 1/2）；证明只用 i=1、2
子脚本 code/review/main-t26ii/check_t26ii.py 不导入 core、不复用复核者 x1 的脚本，只用 Python 标准库，
逐条打印「PASS <字母>.<描述>」或「FAIL …」，最后一行是「结果： 全部通过」。这里按出现顺序给每条配 id，
只检查退出码与这些行，完整输出写进 logs/rv4_main_t26ii.log。
"""
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SCRIPT = os.path.join(ROOT, 'code', 'review', 'main-t26ii', 'check_t26ii.py')
IDS = ['a', 'b', 'c', 'd1', 'd2', 'd3', 'd4', 'e1', 'e2']
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

t0 = time.time()
env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
proc = subprocess.run([sys.executable, SCRIPT], cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out = proc.stdout.decode('utf-8', errors='replace')
with open(os.path.join(ROOT, 'logs', 'rv4_main_t26ii.log'), 'w', encoding='utf-8', newline='\n') as f:
    f.write(out)
lines = [ln for ln in out.splitlines() if re.match(r'(PASS|FAIL) [a-e]\.', ln)]
n_pass = n_fail = 0
for k, cid in enumerate(IDS):
    if k < len(lines) and lines[k].split(' ', 1)[1].startswith(cid[0] + '.'):
        ok = lines[k].startswith('PASS ') and proc.returncode == 0
        desc = lines[k].split(' ', 1)[1]
    else:
        ok, desc = False, '子脚本缺少这一条或顺序不符'
    n_pass += ok
    n_fail += (not ok)
    print('%s rv4-t26ii-%s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)
if len(lines) != len(IDS):
    n_fail += 1
    print('FAIL rv4-t26ii-count 子脚本打印了 %d 条，应为 %d 条' % (len(lines), len(IDS)))
print('SUMMARY rv4 pass=%d fail=%d  (%.1fs, 子脚本退出码 %d)' % (n_pass, n_fail, time.time() - t0, proc.returncode))
sys.exit(0 if n_fail == 0 else 1)
