# -*- coding: utf-8 -*-
"""c1 的扩展范围核对（一次性运行，日志 logs/c1_extended.log）。

这些范围超出 check_c1.py 的约 120 秒预算，所以单独运行；陈述本身都已在 notes/c1.md 中证明，
check_c1.py 覆盖了任务要求的全部范围。这里只是把三处原始定义级的对照再扩大：
  E1  core.U_fast_column == core.U_list（第 1 节参考实现）对 m=21..62 的每一整列（k<=60）
  E2  core.a_direct == U 乘积公式：k=10,11（n<=13）以及 k<=7（14<=n<=20）
  E3  core.N_brute（DFS 定义）== 容斥 N(k,q)：k=10,11
全部精确整数。
"""
import os
import sys
import time

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_list, U_fast_column, U_fast_table, a_direct, N_brute, N_from_U  # noqa: E402

t0 = time.time()
KMAX = 60
TF = U_fast_table(KMAX, 62)

t = time.time()
bad = [m for m in range(21, 63) if U_list(m, KMAX) != U_fast_column(m, KMAX)]
print('%s E1 U_fast_column == U_list（参考实现），每个 m=21..62 的整列 k<=60 [%.1fs] %s'
      % ('PASS' if not bad else 'FAIL', time.time() - t, bad[:4] if bad else ''), flush=True)

t = time.time()
pairs = [(k, n) for k in (10, 11) for n in range(0, 14)] + [(k, n) for k in range(1, 8) for n in range(14, 21)]
bad = [(k, n) for (k, n) in pairs if a_direct(n, k) != TF[k][(n + 1) // 2] * TF[k][n // 2]]
print('%s E2 a_direct == U_k(ceil(n/2))U_k(floor(n/2))：k=10,11 (0<=n<=13)；1<=k<=7 (14<=n<=20) [%.1fs] %s'
      % ('PASS' if not bad else 'FAIL', time.time() - t, bad[:4] if bad else ''), flush=True)

t = time.time()
bad = []
for k in (10, 11):
    br = N_brute(k)
    if [br.get(q, 0) for q in range(0, k + 2)] != [N_from_U(TF, k, q) for q in range(0, k + 2)]:
        bad.append(k)
print('%s E3 N_brute（DFS 定义）== 容斥 N(k,q)，k=10,11 [%.1fs] %s'
      % ('PASS' if not bad else 'FAIL', time.time() - t, bad if bad else ''), flush=True)

print('TIME c1-extended total %.1fs' % (time.time() - t0))
