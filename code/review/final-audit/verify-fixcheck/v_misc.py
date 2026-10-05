# -*- coding: utf-8 -*-
"""verify-fixcheck：#1–#9 的文本/日志/小计算核对（只读）。"""
import os
import re
import sys

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
RP = os.path.join(ROOT, 'notes', 'report_parts')
LG = os.path.join(ROOT, 'logs')
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402


def rd(p):
    return open(p, encoding='utf-8').read()


def part(name):
    return rd(os.path.join(RP, name))


# ---------- quotes present?
QUOTES = [
    ('01_summary.md', '基点 2d+1 的 Newton 正性在 d=69 首次失效，奇数 69≤d≤101 为负'),
    ('03_C2.md', '各显式公式约 0.2–2.4 s'),
    ('00_head.md', 'r2 只对由已证明的 G_m=W_m/P_m 推出的留数–范数条件做精确穷举'),
    ('00_head.md', '另做了三轮多 Agent 工作流'),
    ('01_summary.md', 'N(k,q) 的组合意义按定义直接计数只核到 k≤9'),
    ('06_C5.md', 'c0.c0-cm（数值）、c1.C2-cm。'),
    ('08_failed.md', '（对 m=5,6 需要 k≤60）'),
    ('04_C3.md', '复核者 r-c3a 的更紧的界给出 ≤6.6·10^{−121}）'),
    ('05_C4.md', 'ν_j(q)=Σ_{i≤j}π_i(q)·D(q+j−i,j−i)（π_i=[x^i]P_{q−1}）'),
    ('06_C5.md', '(5)（数值结果，不属于 T5.1 已证明的部分：decimal 90 位计算，核对 c5a.c5a-prompt-k40（数值））'),
]
for i, (f, q) in enumerate(QUOTES):
    print('#%d quote count in %s: %d' % (i, f, part(f).count(q)))

# ---------- #1 bench ranges
print('\n[#1] bench_k200_m30 ranges in the 6 cited runs + reviewer runs')
FORM = ['H', 'F3', 'Theta', 'ThetaH', 'F4']
runs = ['c2a_check_run.log', 'review_x2-dfinite_check_c2a_run.log', 'verify_all_run1.log',
        'verify_all_final.log', 'audit_a3-requirements_verify_rerun.log',
        'review_r-c2a_checkrun.log', 'review_x1-single-sum_check_c2a.log']
allmin, allmax, ratios = 9e9, 0, []
for r in runs:
    s = rd(os.path.join(LG, r))
    m = re.search(r'bench_k200_m30.*?seconds \(this run, noisy\): (.*)', s)
    d = dict((a, float(b)) for a, b in re.findall(r'(\w+) ([0-9.]+)', m.group(1)))
    vals = [d[k] for k in FORM]
    lo, hi = min(vals), max(vals)
    tag = 'reviewer(loaded)' if r.startswith('review_r-c2a') or r.startswith('review_x1') else 'cited'
    if tag == 'cited':
        allmin, allmax = min(allmin, lo), max(allmax, hi)
        ratios += [lo / d['Lemma1'], hi / d['Lemma1']]
    print('  %-42s %-16s explicit %.3f–%.3f  Lemma1 %.3f' % (r, tag, lo, hi, d['Lemma1']))
e5 = rd(os.path.join(LG, 'c2a_e5_bench_K200_M30.log'))
e5v = [float(x) for x in re.findall(r'(?:H form[^\n]*?|F3 form|Theta form[^\n]*?|H-outer \+ c_i inner|F4 c_i partial fractions)\s+([0-9.]+)s', e5)]
e5l = float(re.search(r'Lemma1 recurrence\s+([0-9.]+)s', e5).group(1))
print('  %-42s %-16s explicit %.3f–%.3f  Lemma1 %.3f' % ('c2a_e5_bench_K200_M30.log', 'cited', min(e5v), max(e5v), e5l))
allmin, allmax = min(allmin, min(e5v)), max(allmax, max(e5v))
ratios += [min(e5v) / e5l, max(e5v) / e5l]
print('  cited 6 runs: explicit range %.3f–%.3f s; within-run ratio to Lemma1 %.0f–%.0f' % (allmin, allmax, min(ratios), max(ratios)))
print('  report text says 约 0.2–2.4 s:', '各显式公式约 0.2–2.4 s' in part('03_C2.md'))

# 09_code table vs verify_all_final.log summary table
s = rd(os.path.join(LG, 'verify_all_final.log'))
tot = re.search(r'TOTAL pass=(\d+) .*\(([0-9.]+)s\)', s)
tbl09 = re.search(r'TOTAL pass=(\d+) .*\(([0-9.]+)s\)', part('09_code.md'))
print('  verify_all_final.log TOTAL: pass=%s %ss ; 09_code table TOTAL: pass=%s %ss' % (tot.group(1), tot.group(2), tbl09.group(1), tbl09.group(2)))
st = os.stat(os.path.join(LG, 'verify_all_final.log')).st_mtime
st2 = os.stat(os.path.join(RP, '03_C2.md')).st_mtime
print('  verify_all_final.log mtime later than 03_C2.md mtime by %.0f s' % (st - st2))

# ---------- #2 r2 does no norm computation; r1 does
r2 = rd(os.path.join(ROOT, 'code', 'review', 'x1-single-sum', 'r2_two_family.py'))
r1 = rd(os.path.join(ROOT, 'code', 'review', 'x1-single-sum', 'r1_numfield_residues.py'))
print('\n[#2] r2: occurrences of norm/范数/N(:', len(re.findall(r'norm|范数', r2, re.I)),
      '; det( occurrences:', r2.count('det3('), '; r1 norm/范数 occurrences:', len(re.findall(r'norm|范数', r1, re.I)))
print('  09_code describes r2 as:', re.search(r'r2 只做[^）]*', part('09_code.md')).group(0))

# ---------- #3 rounds
print('\n[#3] 00_head 三轮:', '另做了三轮多 Agent 工作流' in part('00_head.md'),
      '; 08_failed 最终一轮对抗审计:', '最终一轮对抗审计' in part('08_failed.md'),
      '; patch docstring says 第四轮:', '第四轮' in rd(os.path.join(ROOT, 'code', 'main_extra', 'report_patches', 'patch_final_audit.py')))
import json  # noqa: E402
ph4 = json.load(open(os.path.join(LG, 'phase4_final_audit_output.json'), encoding='utf-8'))
print('  phase4 lenses:', [o['lens'] for o in ph4['out']], ' confirmed:', len(ph4['confirmed']))
print('  any mention of 四轮/phase4 in report parts:', any(('四轮' in part(f) or 'phase4' in part(f)) for f in os.listdir(RP) if f.endswith('.md')))

# ---------- #4 c1_extended E3
c1e = rd(os.path.join(LG, 'c1_extended.log'))
print('\n[#4] c1_extended E3 line:', [ln for ln in c1e.splitlines() if ln.startswith('PASS E3')])
print('  verify_all C3-brute line mentions 0<=k<=9:', '0<=k<=9（k=10,11 见 extended_checks.py 的 E3）' in s)

# ---------- #5 C2-cm decimal
print('\n[#5] C2-cm log line:', [ln[:120] for ln in s.splitlines() if ln.startswith('PASS C2-cm')])
t51 = part('06_C5.md')
line = [ln for ln in t51.splitlines() if ln.startswith('核对：c5a.c5a-roots')][0]
print('  T5.1 check line tail:', line[-60:])

# ---------- #6 r4c example
ex = rd(os.path.join(LG, 'review_r-c2b_r4c_example.log'))
print('\n[#6] K=35 INCONSISTENT lines:', sum(1 for ln in ex.splitlines() if 'K=35' in ln and 'INCONSISTENT' in ln),
      'of', sum(1 for ln in ex.splitlines() if 'K=35' in ln))
print('  03_C2 T2.6(iv) now says 改用 k≤60 的数据后全部被反驳:', '改用 k≤60 的数据后全部被反驳' in part('03_C2.md'))

# ---------- #7 r-c3a bound source
rc = rd(os.path.join(LG, 'review_r-c3a_r1_exact.log'))
print('\n[#7] review_r-c3a_r1_exact.log has 6.6e-121:', '6.6e-121' in rc,
      '; report gives that log path:', 'review_r-c3a_r1_exact.log' in ''.join(part(f) for f in os.listdir(RP) if f.endswith('.md')))

# ---------- #8 nu_j identity
print('\n[#8] occurrences of ν in report parts:', {f: part(f).count('ν') for f in os.listdir(RP) if f.endswith('.md') and part(f).count('ν')})
K = 60
T = core.U_fast_table(K, 20)


def Nkq(k, q):
    return core.N_from_U(T, k, q)


def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


ok = True
for q in range(1, 15):
    P = [1]
    for v in range(q):
        P = polymul(P, [1, -1, 0, -v])        # b_v = 1 - x - v x^3
    F = [Nkq(k, q) for k in range(0, 3 * q + 2)]
    Num = polymul(P, F)[:3 * q - 1]           # degree 3q-2
    for j in range(0, min(6, 2 * q - 1)):
        lhs = Num[q + j] if q + j < len(Num) else 0
        rhs = sum((P[i] if i < len(P) else 0) * Nkq(q + j - i, q) for i in range(j + 1))
        if lhs != rhs:
            ok = False
print('  [x^{q+j}]Num_q == sum_{i<=j} [x^i]P_{q-1} * D(q+j-i, j-i)  (1<=q<=14, j<=5):', ok)
print('  05_C4 (6) uses pi_{j,i}:', 'π_{j,i}' in part('05_C4.md'))

# ---------- #9 grade of T5.1(5)
print('\n[#9] T5.1(5) has a 【…】 grade label:', bool(re.search(r'\(5\)【', t51.split('**T5.2')[0])))
print('  00_head grade list:', re.search(r'等级：[^\n]*', part('00_head.md')).group(0)[:200])
