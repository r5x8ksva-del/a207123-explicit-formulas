# -*- coding: utf-8 -*-
"""最终审计（requirements）r4：对报告文本做只读的定点核对，给出每条发现的机器可复现证据。
  (a) T5.4(6)「k>=5 没有类似对应」：data/oeis/INDEX.md 中实际搜索过哪些 U_k（k>=5）；
  (b) 10_uncertain「22 个盒子」：verify_all 日志里 N 的盒子数（C3B-E3B/E3S）与 U 的盒子数；
  (c) T2.6(i) 的【已验证（数值，浮点…）】与 00_head 的等级定义「【已验证】= 只有精确程序核对」；
  (d) 00_head「已在相应条目注明『不在 verify_all 中』并给出日志路径」：列出提到复核者扩展范围但没有日志路径的条目；
  (e) 记号：06_C5 中 P_3（偏序集）与全局 P_m；c_2/c_3（序列）与 T5.1 的增长常数 c_2/c_3；02_C1 T1.4(1) 的 C(x+1,q)/Q[x]；
  (f) 【已证明】但既无证明也无笔记小节指针的条目：T4.3(5)(7)、T5.3(5)，以及笔记中对应小节是否存在；
  (g) T3.7 核对「C3B-RES（留数非零）」与日志中 C3B-RES 的实际内容；
  (h) T5.4 核对行是否引用 c5b.diag / c5b.rows；
  (i) 09_code 表头「每个都从 core.py 取真值」与 rv2 行「不导入 core」；子脚本是否 import core。
只读，不修改任何文件。
"""
import os
import re
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
P = os.path.join(ROOT, 'notes', 'report_parts')
T = {n: open(os.path.join(P, n), encoding='utf-8').read() for n in sorted(os.listdir(P)) if n.endswith('.md')}
LOG = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read()


def has(fn, s):
    ok = s in T[fn]
    print('   [%s] 含「%s」: %s' % (fn, s if len(s) < 70 else s[:70] + '…', ok))
    return ok


print('(a) T5.4(6) 搜索覆盖')
idx = open(os.path.join(ROOT, 'data', 'oeis', 'INDEX.md'), encoding='utf-8').read()
ks = sorted(set(int(k) for k in re.findall(r'search_U(\d+)_m\d+\.txt', idx)))
print('   INDEX.md 中按 m 搜索过的 U_k：k =', ks, '；k>=8 的 U_k(m) 窗口搜索：', [k for k in ks if k >= 8] or '无')
has('06_C5.md', '(6)【已验证】k≥5 没有类似对应')
has('01_summary.md', 'k≥5 没有对应')
has('06_C5.md', '而且 k≥5 在 OEIS 中没有任何对应')
has('08_failed.md', 'k≥5 在 OEIS 中没有对应')
has('10_uncertain.md', 'k≥5（无对应）')

print('(b) 22 个盒子')
def boxes(tag):
    ln = next(l for l in LOG.splitlines() if l.startswith('PASS ' + tag + ' '))
    return len(re.findall(r'ker=\d+ pred=\d+', ln))
nU = boxes('C3B-E2') + boxes('C3B-E2S')
nN = boxes('C3B-E3B') + boxes('C3B-E3S')
print('   verify_all 中 U 的 (k,m) 多项式系数盒子 =', nU, '；N 的 =', nN, '；合计 =', nU + nN)
has('10_uncertain.md', '数据上 22 个盒子（verify_all）加上复核者新增的盒子全部吻合')

print('(c) T2.6(i) 等级')
has('00_head.md', '【已验证】= 只有精确程序核对，写明范围')
has('03_C2.md', '其余奇数形状【已验证（数值，浮点纤维检验')
rv = open(os.path.join(ROOT, 'notes', 'review', 'r-c2a-review.md'), encoding='utf-8').read()
print('   r-c2a-review 自述：', '只做了浮点检验（容差 1e−7），没有做区间算术，只能算证据' in rv)
print('   verify_all 日志里是否有奇数形状纤维检验：', any(w in LOG for w in ('odd shape', 'fiber_numeric', '奇数形状')))

print('(d) 复核者扩展范围但未给日志路径/未注明不在 verify_all')
for fn, needle in [('02_C1.md', '第二轮复核者 r-c1 另以精确 gcd（i≤150）'), ('02_C1.md', '复核者 r-c1 用与 U 无关的序型 DP 扩到 k≤28'),
                   ('06_C5.md', '复核者 r-c5b 用同法确认到 k≤70'), ('04_C3.md', '复核者 x2 用自写 DP 另算了 44 个新盒子')]:
    i = T[fn].find(needle)
    seg = T[fn][i:i + 160] if i >= 0 else ''
    print('   [%s] 「%s」 found=%s；后 160 字内含 logs/：%s；含「不在 verify_all」：%s' % (fn, needle, i >= 0, 'logs/' in seg, '不在 verify_all' in seg))
for f in ['review_r-c1_r3_C2_final.log', 'review_r-c1_r4_C3_C6_C7_final.log', 'review_r-c5b_negzeros_exact.log', 'review_x2-dfinite_kernel.log', 'review_r-c3b_r2_rank.log']:
    print('   日志存在 logs/%s: %s' % (f, os.path.exists(os.path.join(ROOT, 'logs', f))))

print('(e) 记号')
has('02_C1.md', '> 记号（全文统一）：good(a,b,c)')
has('02_C1.md', 'P_m=∏_{i=0}^{m} b_i')
has('06_C5.md', 'Q_3 与 P_3 不同构')
print('   06_C5 中是否另有 P_3 的定义：', bool(re.search(r'P_3\s*[:：]?=|P_3 为|记 P_3', T['06_C5.md'])))
has('06_C5.md', 'c_2≈7.8411192294')
has('06_C5.md', '命中的只有 c_2=A077949、c_3=A084386')
has('06_C5.md', '可写成 c_j 的形式')
has('02_C1.md', '{C(x+1,q)} 是 Q[x] 的基')
has('02_C1.md', '如基 C(y+1,q)')

print('(f) 【已证明】缺证明/指针')
for fn, needle in [('05_C4.md', '(5)【已证明，一切 j】'), ('05_C4.md', '(7)【已证明】反转分子'), ('06_C5.md', '(5)【已证明】h_k 在 [0,1] 上无根')]:
    i = T[fn].find(needle)
    j = T[fn].find('\n', i)
    seg = T[fn][i:j]
    print('   [%s] %s：本段含「证明」=%s，含 notes/ 或 § 指针=%s' % (fn, needle, '证明' in seg, ('notes/' in seg) or ('§' in seg)))
c4 = open(os.path.join(ROOT, 'notes', 'c4.md'), encoding='utf-8').read()
c5a = open(os.path.join(ROOT, 'notes', 'c5a.md'), encoding='utf-8').read()
print('   notes/c4.md §4.7 存在：', '### 4.7 低次系数' in c4, '；§4.9 定理 4.9 存在：', '### 4.9 定理 4.9' in c4)
print('   notes/c5a.md §4.6/§4.8/§4.9 存在：', '### 4.6 [t¹]' in c5a, '### 4.8 二元母函数' in c5a, '### 4.9 实根性' in c5a)

print('(g) C3B-RES')
ln = next(l for l in LOG.splitlines() if l.startswith('PASS C3B-RES '))
print('   日志：', ln)
has('04_C3.md', 'c3b.C3B-RES（留数非零）')
for tag in ('C3B-PX', 'C3B-INT'):
    l2 = next(l for l in LOG.splitlines() if l.startswith('PASS ' + tag + ' '))
    print('   日志：', l2[:160])

print('(h) T5.4 核对行')
i = T['06_C5.md'].find('核对：c5b.col-data')
seg = T['06_C5.md'][i:T['06_C5.md'].find('\n', i)]
print('   引用 c5b.diag：', 'c5b.diag' in seg, '；引用 c5b.rows：', 'c5b.rows' in seg)
print('   日志有 c5b.diag / c5b.rows：', 'PASS c5b.diag ' in LOG, 'PASS c5b.rows ' in LOG)

print('(i) 09_code 表头 vs rv2')
has('09_code.md', '**11 个核对模块**（每个都从 `code/core.py` 的原始定义程序取「真值」）')
has('09_code.md', '复核者 x1 的两个独立脚本（不导入 core）')
for fn in ('r1_numfield_residues.py', 'r2_two_family.py'):
    s = open(os.path.join(ROOT, 'code', 'review', 'x1-single-sum', fn), encoding='utf-8').read()
    print('   %s import core：%s' % (fn, bool(re.search(r'^\s*(import core|from core import)', s, re.M))))
