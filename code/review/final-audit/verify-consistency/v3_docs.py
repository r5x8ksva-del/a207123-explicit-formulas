# -*- coding: utf-8 -*-
"""对抗性验证 consistency 审计：文档类发现的证据整理（只读）。"""
import os, re, io

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
def rd(p):
    with io.open(os.path.join(ROOT, p), encoding='utf-8') as f:
        return f.read()

rep = rd('报告.md')
out = []
def log(s):
    print(s); out.append(s)

# #0 numpy
r2 = rd('code/review/x1-single-sum/r2_two_family.py')
c3b = rd('code/checks/check_c3b.py')
log('#0 r2_two_family 无条件 import numpy: %s；check_c3b 用 try/except: %s'
    % ('\nimport numpy as np' in r2, 'HAVE_NP = False' in c3b))
nn = rd('code/review/final-audit/verify-consistency/c3b_nonumpy.out')
log('   屏蔽 numpy 运行 check_c3b：%s' % [l for l in nn.splitlines() if l.startswith('SUMMARY') or 'numpy=' in l])

# #5 OEIS 单行搜索
names = sorted(os.listdir(os.path.join(ROOT, 'data', 'oeis')))
log('#5 data/oeis 中 search_U<k>_* 文件：%s' % [n for n in names if re.match(r'search_U\d', n)])

# #8 盒子计数
fl = rd('logs/verify_all_final.log')
for cid in ('C3B-E2 ', 'C3B-E2S', 'C3B-E3B', 'C3B-E3S'):
    line = [l for l in fl.splitlines() if l.startswith('PASS ' + cid)][0]
    boxes = re.findall(r'\(([\d, ]+)\):\d+u/\d+eq ker=(\d+)', line)
    log('#8 %s 盒子数=%d，其中 ker=0 的 %d 个' % (cid.strip(), len(boxes), sum(1 for b in boxes if b[1] == '0')))
r = rd('notes/review/r-c3b-review.md'); x = rd('notes/review/x2-dfinite-review.md')
log('   r-c3b 判 T3N minor_gap（角点需取最大 β′）: %s；x2 同判: %s'
    % ('T3N：N 的维数公式里的「角点」论证要选列内最大的 β′' in r, '两份报告在 T3N 上给出了同一个 minor_gap' in x))

# #9 rv2 不导入 core
r1 = rd('code/review/x1-single-sum/r1_numfield_residues.py')
log('#9 r1/r2 是否 import core: %s / %s' % (bool(re.search(r'^\s*(from|import) core', r1, re.M)), bool(re.search(r'^\s*(from|import) core', r2, re.M))))

# #10 复核者范围与日志
for p, pat in [('logs/review_r-c1_r3_C2_final.log', 'G4c-reducible'), ('logs/review_r-c1_r4_C3_C6_C7_final.log', '序型 DP（k<=28'),
               ('logs/review_r-c5b_negzeros_exact.log', '1<=k<=70'), ('logs/review_x2-dfinite_kernel.log', 'X2-C-N'),
               ('logs/review_r-c3b_r2_rank.log', 'R-E3B'), ('logs/review_r-c3b_r5_extra.log', 'PASS N (A,B)=(3,12)')]:
    log('#10 %s 含「%s」: %s' % (p, pat, pat in rd(p)))
for frag in ('i≤3000', '扩到 k≤28', '确认到 k≤70', '另算了 44 个新盒子'):
    i = rep.find(frag)
    log('   报告「%s」附近 120 字是否含 log/不在 verify_all: %s' % (frag, ('logs/' in rep[i:i+120]) or ('不在 verify_all' in rep[i:i+120])))

# #11 / #14 / #15 / #18 / #19 / #20 / #21 / #23 记号
log('#14 报告中 R_k 的出现处是否有定义（「R_k=U_k(1)」或「R_k:=」）: %s' % (('R_k=U_k(1)' in rep) or ('R_k:=' in rep)))
log('#15 报告中 N_i 的定义（「N_i:=」或「N_i=」）: %s' % (('N_i:=' in rep) or ('N_i=' in rep)))
log('#18 报告中 c_d 的定义: %s' % ('c_d:=' in rep))
log('#20 报告中「初等对称」字样: %s' % ('初等对称' in rep))
log('#21 报告中 Λ_k 出现: %s；「P_3」出现次数 %d' % ('Λ_k' in rep, rep.count('P_3')))
log('#23 T3.6 说明「用 𝓗 以免与 r-Stirling 数 H(m,s,j) 混淆」: %s；⑤ 表写「𝒩 与 H」: %s' % ('用 𝓗 以免与 r-Stirling 数 H(m,s,j) 混淆' in rep, '𝒩 与 H |' in rep))

# #16 r4b 日志
log('#16 r4b_full.log 是否含 k<=60 结论: %s；r4b_k60.log 含「k<=60 上仍相容 0 对」: %s'
    % ('k<=60' in rd('logs/review_r-c2b_r4b_full.log'), 'k<=60 上仍相容 0 对' in rd('logs/review_r-c2b_r4b_k60.log')))

# #22 数值标注
line = [l for l in fl.splitlines() if 'c5a-prompt-k40' in l][0]
log('#22 c5a-prompt-k40 在日志里以 [numeric] 开头: %s；c5a 笔记 §2.7 标【已验证，数值】: %s'
    % ('[numeric]' in line, '2.7 提示词"m=2、3 在 k=40 时相差 <0.4%"【已验证，数值】' in rd('notes/c5a.md')))

with io.open(os.path.join(ROOT, 'logs', 'final_audit_verify_consistency.log'), 'a', encoding='utf-8') as f:
    f.write('\n===== v3_docs.py =====\n' + '\n'.join(out) + '\n')
