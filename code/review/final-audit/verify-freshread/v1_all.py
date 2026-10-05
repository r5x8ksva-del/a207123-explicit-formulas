# -*- coding: utf-8 -*-
"""verify-freshread：对 freshread 的 14 条发现逐条独立复核（只读；输出到 stdout，由 run_all 重定向到日志）。"""
import json
import os
import re
import sys
from fractions import Fraction

ROOT = 'C:/Users/Michael Song/Desktop/私人办公/A207123-任务C-显式公式与母函数'
P = ROOT + '/notes/report_parts/'
L = ROOT + '/logs/'
sys.path.insert(0, ROOT + '/code')
import core  # noqa: E402


def rd(path):
    return open(path, encoding='utf-8').read()


def part(name):
    return rd(P + name)


def hdr(s):
    print('\n' + '=' * 30 + ' ' + s + ' ' + '=' * 30)


def grep(path, pat, maxn=20):
    out = []
    for i, line in enumerate(rd(path).splitlines(), 1):
        if re.search(pat, line):
            out.append((i, line))
    return out[:maxn]


# ---------------------------------------------------------------- #0
hdr('#0 01_summary N(k,q) 组合意义的核对范围')
for i, l in grep(L + 'c1_extended.log', r'E3'):
    print('c1_extended.log:%d %s' % (i, l))
for i, l in grep(L + 'review_r-c1_rerun_c1_extended.log', r'E3'):
    print('review_r-c1_rerun_c1_extended.log:%d %s' % (i, l))
for i, l in grep(L + 'verify_all_final.log', r'C3-brute|c3a-N-def|c4-N-dfs|C3B-PSI N:|rv-Ntri-vs-def'):
    print('verify_all_final.log:%d %s' % (i, l[:200]))
for i, l in grep(L + 'review_r-c1_r4_C3_C6_C7_final.log', r'C3a-basis'):
    print('review_r-c1_r4:%d %s' % (i, l[:160]))
s = part('01_summary.md')
print('01_summary 含「按定义直接计数只核到 k≤9」:', '按定义直接计数只核到 k≤9' in s, '; 含「k≤11」:', 'k≤11' in s)
print('02_C1 T1.4 含「扩展脚本到 11」:', '扩展脚本到 11' in part('02_C1.md'))
print('10_uncertain 含「扩展脚本到 k≤11」:', '扩展脚本到 k≤11' in part('10_uncertain.md'))

# ---------------------------------------------------------------- #1
hdr('#1 08_failed ④B.11「对 m=5,6 需要 k≤60」')
for f in ['review_r-c2b_r4b_full.log', 'review_r-c2b_r4b_k60.log']:
    for i, l in grep(L + f, r'm=5|m=6'):
        print('%s:%d %s' % (f, i, l))
for i, l in grep(L + 'review_r-c2b_r4c_example.log', r'K=30|K=35'):
    print('r4c_example:%d %s' % (i, l))
c2 = part('03_C2.md')
print('T2.6(iv) 现文含「改用 k≤60 的数据后全部被反驳」:', '改用 k≤60 的数据后全部被反驳' in c2)
print('T2.6(iv) 现文含「要用 k≤60 才」:', '要用 k≤60 才' in c2)
print('08_failed 现文含「需要 k≤60」:', '需要 k≤60' in part('08_failed.md'))

# ---------------------------------------------------------------- #2
hdr('#2 09_code 总表 vs logs/verify_all_final.log')
st = os.stat(L + 'verify_all_final.log')
import time
print('verify_all_final.log mtime(UTC):', time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(st.st_mtime)), 'size', st.st_size)
print('09_code.md mtime(UTC):', time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(os.stat(P + '09_code.md').st_mtime)))
row = re.compile(r'^(c0|c1|c2a|c2b|c3a|c3b|c4|c5a|c5b|rv|rv2)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\w+)\s+([\d.]+)\s+(\w+)\s*$')
def table(text):
    d = {}
    tot = None
    for line in text.splitlines():
        m = row.match(line.strip())
        if m:
            d[m.group(1)] = (int(m.group(2)), int(m.group(3)), float(m.group(6)))
        m2 = re.search(r'TOTAL pass=(\d+) fail=(\d+) modules=(\d+) failed_modules=-\s+\(([\d.]+)s\)', line)
        if m2:
            tot = (int(m2.group(1)), int(m2.group(2)), float(m2.group(4)))
    return d, tot
rep_t, rep_tot = table(part('09_code.md'))
log_t, log_tot = table(rd(L + 'verify_all_final.log'))
print('报告表 TOTAL', rep_tot, '; 日志 TOTAL', log_tot)
for k in rep_t:
    a, b = rep_t[k], log_t.get(k)
    print('  %-4s 报告 pass=%d fail=%d secs=%.1f | 日志 pass=%d fail=%d secs=%.1f %s' % (
        k, a[0], a[1], a[2], b[0], b[1], b[2], '' if (a[0], a[1]) == (b[0], b[1]) else 'PASS数不同!'))
print('PASS/FAIL 计数全部一致:', all(rep_t[k][:2] == log_t[k][:2] for k in rep_t), '; secs 全部一致:',
      all(rep_t[k][2] == log_t[k][2] for k in rep_t))
others = {}
for f in ['verify_all_run1.log', 'audit_a3-requirements_verify_rerun.log']:
    others[f] = table(rd(L + f))[1]
print('其他全量运行 TOTAL:', others, '(正常负载约 216–232 s)')
print('00_head 运行时长说法:', re.findall(r'约 [0-9–\-]+ 分钟', part('00_head.md')), '; 09_code 是否写了分钟:',
      bool(re.findall(r'分钟', part('09_code.md'))))

# ---------------------------------------------------------------- #3
hdr('#3 T2.9「各显式公式约 0.2–2.4 s」与所引 6 次运行')
six = ['c2a_check_run.log', 'review_x2-dfinite_check_c2a_run.log', 'verify_all_run1.log', 'verify_all_final.log',
       'audit_a3-requirements_verify_rerun.log']
allmin, allmax, rmin, rmax = 9e9, 0, 9e9, 0
for f in six:
    line = [l for _, l in grep(L + f, r'bench_k200_m30')][0]
    vals = dict((k, float(v)) for k, v in re.findall(r'(\w+) ([\d.]+)', line.split('noisy):')[1]))
    ex = {k: vals[k] for k in ['H', 'F3', 'Theta', 'ThetaH', 'F4']}
    lo, hi, lem = min(ex.values()), max(ex.values()), vals['Lemma1']
    allmin, allmax = min(allmin, lo), max(allmax, hi)
    rmin, rmax = min(rmin, lo / lem), max(rmax, hi / lem)
    print('  %-42s Lemma1=%.3f 显式 %.3f–%.3f (最快 %s, 最慢 %s) 倍数 %.0f–%.0f' % (
        f, lem, lo, hi, min(ex, key=ex.get), max(ex, key=ex.get), lo / lem, hi / lem))
e5 = rd(L + 'c2a_e5_bench_K200_M30.log')
e5v = [float(x) for x in re.findall(r'\s([\d.]+)s\s+equal', e5)]
lem5 = 0.003
ex5 = [1.098, 1.517, 1.217, 0.945, 0.863, 0.737]
print('  c2a_e5_bench_K200_M30.log Lemma1=0.003 显式 %.3f–%.3f 倍数 %.0f–%.0f' % (min(ex5), max(ex5), min(ex5) / lem5,
                                                                              max(ex5) / lem5))
allmin, allmax = min(allmin, min(ex5)), max(allmax, max(ex5))
rmin, rmax = min(rmin, min(ex5) / lem5), max(rmax, max(ex5) / lem5)
print('6 次合计：显式公式 %.3f–%.3f s，与引理 1 之比 %.0f–%.0f' % (allmin, allmax, rmin, rmax))
print('若排除当前 verify_all_final.log：显式公式 0.227–2.405 s（见上各行）')

# ---------------------------------------------------------------- #4
hdr('#4 00_head「三轮多 Agent 工作流」')
for name in ['00_head.md', '08_failed.md', '09_code.md']:
    for i, l in enumerate(part(name).splitlines(), 1):
        for pat in ['三轮', '两轮', '最终一轮', 'phase']:
            if pat in l:
                print('%s:%d [%s] %s' % (name, i, pat, l[:150]))
                break
for f in ['phase1_workflow_output.json', 'phase2_review_output.json', 'phase3_audit_output.json',
          'phase4_final_audit_output.json']:
    print('  logs/%s 存在: %s; 报告中被引用: %s' % (f, os.path.exists(L + f), f in rd(ROOT + '/报告.md')))
d4 = json.load(open(L + 'phase4_final_audit_output.json', encoding='utf-8'))
print('phase4 审计视角:', [o['lens'] for o in d4['out']], '发现数', sum(len(o['findings']) for o in d4['out']),
      'confirmed', len(d4['confirmed']), 'real=True 计数',
      sum(1 for o in d4['out'] for f in o['findings'] if f['verdict']['real']))
print('patch_final_audit.py 文件头:', rd(ROOT + '/code/main_extra/report_patches/patch_final_audit.py').splitlines()[1])
print('第四轮复核日志:', sorted(x for x in os.listdir(L) if x.startswith('final_audit_verify_')))

# ---------------------------------------------------------------- #5
hdr('#5 00_head「少数扩展范围只由第二轮复核脚本跑过…已注明并给出日志路径」')
for i, l in grep(L + 'c1_extended.log', r'E2'):
    print('c1_extended.log:%d %s' % (i, l))
print('c4_explore9b_d4.log:', rd(L + 'c4_explore9b_d4.log').strip())
for i, l in grep(L + 'verify_all_final.log', r'B3-direct-vs-product|c4-pattern-brute'):
    print('verify_all_final.log:%d %s' % (i, l[:200]))
for i, l in grep(L + 'review_r-c3a_r3_growth.log', r'k=75|k=150'):
    print('review_r-c3a_r3_growth.log:%d %s' % (i, l[:120]))
checks = [('02_C1.md', '扩展脚本另核对 a_direct 到 k=11。'),
          ('05_C4.md', 'c4.c4-pattern-brute（按定义暴力枚举 d≤3；探索中 d=4）'),
          ('04_C3.md', '精确计算 |f_k(−1/2)|^{1/k} 在 k=75、150 为 1.669、2.036（比值 1.22），与 (k!)^{1/3} 型增长相容，未证。'),
          ('05_C4.md', '审计者 a1 算到 d≤60'),
          ('04_C3.md', 'c3b 探索脚本 explore_relations2')]
for name, q in checks:
    s = part(name)
    idx = s.find(q)
    seg = s[idx: idx + len(q) + 160] if idx >= 0 else ''
    print('  %s 找到=%s；该处后 160 字内含 logs/: %s | 片段: %s' % (name, idx >= 0, 'logs/' in seg[:len(q) + 160],
                                                         seg[:len(q) + 60].replace('\n', ' ')))

# ---------------------------------------------------------------- #6
hdr('#6 T5.1 核对行 c5a-roots、c5a-cm-repr 的「数值」标注')
for i, l in grep(L + 'verify_all_final.log', r'PASS c5a-roots|PASS c5a-cm-repr'):
    print('verify_all_final.log:%d %s' % (i, l))
c5 = part('06_C5.md')
m = re.search(r'核对：c5a\.c5a-roots[^\n]*', c5)
line = m.group(0)
for cid in ['c5a.c5a-roots', 'c5a.c5a-cm-repr', 'c5a.c5a-asym-m1..m8', 'c5a.c5a-prompt-k40', 'c0.c0-cm']:
    j = line.find(cid)
    nxt = line[j + len(cid): j + len(cid) + 40]
    print('  %-22s 紧随其后: %s' % (cid, nxt))
print('00_head 规则:', '凡是用 decimal 做的高精度数值检查，一律注明「数值」' in part('00_head.md'))

# ---------------------------------------------------------------- #7
hdr('#7 T5.3(1) 基本事实：独立重算 + 证明出处')
K, M = 30, 40
T = core.U_fast_table(K, M)
ok_ref = all(core.U_list(m, 20)[k] == T[k][m] for m in range(0, 9) for k in range(0, 21))
print('U_fast_table 与参考实现 U_list 一致 (m<=8,k<=20):', ok_ref)
binom = core.binom
def hcoef(k, i):
    return sum((-1) ** (i - j) * binom(k + 1, i - j) * T[k][j] for j in range(0, i + 1))
H = {k: [hcoef(k, i) for i in range(0, k + 4)] for k in range(0, K + 1)}
ok_deg = all(all(c == 0 for c in H[k][max(k, 1):]) for k in range(0, K + 1))
print('h_k 由 (1−t)^{k+1}ΣU_k(m)t^m 截断得到，deg h_k ≤ max(k−1,0)（k≤30）:', ok_deg)
print('h_k(0)=1 (k≤30):', all(H[k][0] == 1 for k in range(K + 1)))
print('h_k(1)=2 (2≤k≤30):', all(sum(H[k]) == 2 for k in range(2, K + 1)), '; h_0(1),h_1(1)=', sum(H[0]), sum(H[1]))
R = [T[k][1] for k in range(K + 1)]
print('[t^1]h_k = R_k−k−1 (k≤30):', all(H[k][1] == R[k] - k - 1 for k in range(K + 1)),
      '; >0 for 2≤k≤30:', all(H[k][1] > 0 for k in range(2, K + 1)), '; k=0,1 值', H[0][1], H[1][1])
# g.f. x^2(1-x+x^2)/((1-x)^2(1-x-x^3)) 的系数
def series_div(num, den, n):
    out = []
    num = num + [0] * (n + 5)
    for i in range(n + 1):
        c = Fraction(num[i]) - sum(den[j] * out[i - j] for j in range(1, min(i, len(den) - 1) + 1))
        out.append(c / den[0])
    return out
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r
den = pmul(pmul([1, -1], [1, -1]), [1, -1, 0, -1])
gf = series_div([0, 0, 1, -1, 1], den, K)
print('Σ h_{k,1}x^k = x²(1−x+x²)/((1−x)²(1−x−x³)) (k≤30):', all(gf[k] == H[k][1] for k in range(K + 1)))
N = {(k, q): core.N_from_U(T, k, q) for k in range(0, K + 1) for q in range(0, K + 2)}
def poly_N_rep(k):
    acc = [0] * (k + 2)
    for q in range(1, k + 1):
        p = [1]
        for _ in range(k - q):
            p = pmul(p, [1, -1])
        p = [0] * (q - 1) + p
        for i, c in enumerate(p):
            acc[i] += N[(k, q)] * c
    return acc
print('h_k = Σ_q N(k,q)t^{q−1}(1−t)^{k−q} (1≤k≤30):',
      all(poly_N_rep(k)[:k + 1] == H[k][:k + 1] for k in range(1, K + 1)))
# h_k^{(d)}(1)
from math import factorial
def deriv_at1(c, d):
    return sum(Fraction(factorial(i), factorial(i - d)) * c[i] for i in range(d, len(c)))
okd = True
for k in range(1, K + 1):
    for d in range(0, 4):
        rhs = factorial(d) * sum((-1) ** e * binom(k - 1 - e, d - e) * N[(k, k - e)] for e in range(0, d + 1)
                                 if k - e >= 0)
        if deriv_at1(H[k], d) != rhs:
            okd = False
print('h_k^{(d)}(1)=d!Σ_e(−1)^eC(k−1−e,d−e)N(k,k−e) (d≤3, 1≤k≤30):', okd)
print("h_k'(1)=−(k²−3k−2) (4≤k≤30):", all(deriv_at1(H[k], 1) == -(k * k - 3 * k - 2) for k in range(4, K + 1)),
      "; k=3 时 h_3'(1)=", deriv_at1(H[3], 1), '公式给', -(9 - 9 - 2))
# n_k(z) := Σ_q N(k,q) z^{q-1} == (1+z)^{k-1} h_k(z/(1+z)) = Σ_i h_{k,i} z^i (1+z)^{k-1-i}
okn = True
for k in range(1, K + 1):
    lhs = [N[(k, q)] for q in range(1, k + 1)]
    rhs = [0] * k
    for i in range(0, k):
        p = [1]
        for _ in range(k - 1 - i):
            p = pmul(p, [1, 1])
        p = [0] * i + p
        for j, c in enumerate(p):
            if j < k:
                rhs[j] += H[k][i] * c
    if lhs != rhs:
        okn = False
print('n_k(z):=Σ_q N(k,q)z^{q−1} == (1+z)^{k−1}h_k(z/(1+z)) (1≤k≤30):', okn)
s5 = part('06_C5.md')
t531 = s5[s5.find('(1)【已证明】基本事实'): s5.find('(2)【已证明】负整数处的值')]
print('T5.3(1) 段内含 notes/ 或 § 指针:', ('notes/' in t531) or ('§' in t531), '; 含「证明」:', '证明' in t531)
print('T5.3(1) 段内含 Σ_qN(k,q)z^{q−1}:', 'z^{q−1}' in t531)
c5a = rd(ROOT + '/notes/c5a.md')
for h in ['### 4.1 基本事实', '### 4.6 [t¹] 与固定位置的系数', '### 4.7 t=1 处的各阶导数与 N 的关系',
          'N 行多项式 n_k(z) := Σ_q N(k,q)z^{q−1}']:
    print('  notes/c5a.md 含 %s: %s' % (h, h in c5a))

# ---------------------------------------------------------------- #8
hdr('#8 T3.8 角点句中的记号')
s3 = part('04_C3.md')
allrep = ''.join(part(x) for x in sorted(os.listdir(P)) if x.endswith('.md'))
for sym in ['α′', 'β*', 'α*', 'β′', 'q_{α*b}', 'q_{ab}', 'q_{α′β*}']:
    print('  报告各节中「%s」出现次数: %d' % (sym, allrep.count(sym)))
c3b = rd(ROOT + '/notes/c3b.md')
j = c3b.find('取 β*=Q 中最大的 b')
print('notes/c3b.md §6 定义:', c3b[j - 80: j + 170].replace('\n', ' '))
print('T3.8 中 N 的下标 q 用法:', re.findall(r'Y: q↦q−1|\(q−1\)X³\(1\+Y\)²', s3))

# ---------------------------------------------------------------- #9
hdr('#9 01_summary 第 7 条与 T3.8')
print(re.findall(r'Rel\(U\)=O_U·L1|Rel\(N\)=O_N·L_N，L_N=1−X−XY−\(q−1\)X³\(1\+Y\)²|L1=1−E\^\{−1\}−X−mX³', s3))
print('01_summary 第 7 条:', [l for l in part('01_summary.md').splitlines() if l.startswith('7.')][0])

# ---------------------------------------------------------------- #10
hdr('#10「m=5,6 各有 59/1024 个零检验形状对」')
big = rd(L + 'review_r-c2b_r4_twoterm_big.log')
exE5 = re.search(r'E m=5 k0=0:.*?examples (\[.*?\])\n', big).group(1)
exU5 = re.search(r'U m=5 k0=0:.*?examples (\[.*?\])\n', big).group(1)
exE6 = re.search(r'E m=6 k0=0:.*?examples (\[.*?\])\n', big).group(1)
exU6 = re.search(r'U m=6 k0=0:.*?examples (\[.*?\])\n', big).group(1)
print('E、U 在 m=5 的零检验形状对示例完全相同:', exE5 == exU5, '; m=6:', exE6 == exU6)
print('（零检验 = 未知数等于方程数，任何数列都相容，所以形状对集合与目标数列 E/U 无关；计数 59/1024 对 E、U 都成立）')
for i, l in grep(L + 'review_r-c2b_r4b_full.log', r'consistent'):
    print('  r4b_full:%d %s' % (i, l[:90]))

# ---------------------------------------------------------------- #11
hdr('#11 T2.6 (i) 与 (iv) 的 α、β')
for pat in ['形状 C(k+c−αs, βs+d)', '取 v=x^{α+β}/(1−x)^β', '形状 Σ_s A(m,s)C(k+αm+β−γs, δm+εs+ζ)']:
    print('  03_C2 含「%s」: %s' % (pat, pat in c2))
for i, l in grep(L + 'verify_all_final.log', r'T7\.box'):
    print('  verify_all_final.log:%d %s' % (i, l[:220]))

# ---------------------------------------------------------------- #12
hdr('#12 T5.4(2) 的 E 与 m_1、m_2')
print('  报告中 m_1 出现次数:', allrep.count('m_1'), '; T3.8 中 E 的定义:', re.findall(r'E\^\{−1\}: m↦m−1', s3))
for i, l in grep(L + 'verify_all_final.log', r'c5b\.emp-row'):
    bounds = re.findall(r'\(行(\d)\):(\d+)阶,界(\d+)', l)
    print('  emp-row 界:', bounds)
    print('  (⌈n/2⌉+1)²(⌊n/2⌋+1)²:', [(n, ((n + 1) // 2 + 1) ** 2 * (n // 2 + 1) ** 2) for n in range(2, 8)])
c5bn = rd(ROOT + '/notes/c5b.md')
j = c5bn.find('**T4（行）')
print('  notes/c5b.md T4:', c5bn[j: j + 200].replace('\n', ' '))

# ---------------------------------------------------------------- #13
hdr('#13 ④C.15 的文献只读访问记录')
j = c3b.find('**文献核实（只读）**')
for l in c3b[j: j + 1600].splitlines()[:5]:
    print('  c3b:', l[:200])
print('  x2 文献日志 GET 行:', [l for l in rd(L + 'review_x2-dfinite_literature.log').splitlines() if 'GET' in l])
print('  00_head 第 9 行:', part('00_head.md').splitlines()[8][:120])
