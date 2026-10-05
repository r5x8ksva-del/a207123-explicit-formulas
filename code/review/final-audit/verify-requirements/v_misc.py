# -*- coding: utf-8 -*-
"""verify-requirements：用程序从日志 / 快照 / 笔记中抽取事实，独立复核审计者 #1 #2 #4 #5 #6 #7 #8 #9 #10 #11 #12 #13 #14 #15。
只读：只读取 logs/、data/、notes/、code/ 下的文件。
"""
import os
import re
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))


def rd(*p):
    with open(os.path.join(ROOT, *p), encoding='utf-8') as f:
        return f.read()


VA = rd('logs', 'verify_all_final.log')
PARTS = {fn: rd('notes', 'report_parts', fn) for fn in sorted(os.listdir(os.path.join(ROOT, 'notes', 'report_parts')))}
ALL = ''.join(PARTS.values())


def line_of(cid):
    for ln in VA.splitlines():
        if ln.startswith('PASS ' + cid + ' ') or ln.startswith('FAIL ' + cid + ' '):
            return ln
    return None


print('== #1 odd shapes: evidence type')
ln = [l for l in rd('logs', 'review_r-c2a_r4_negative.log').splitlines() if 'odd_shapes_fiber' in l]
print('  r-c2a log:', ln[0][:200] if ln else None)
print('  in verify_all_final.log? odd_shapes / fiber-point:', ('odd_shapes' in VA) or ('fiber-point' in VA))
rv = rd('notes', 'review', 'r-c2a-review.md')
print('  r-c2a-review §5 says 只能算证据:', '只能算证据' in rv)
print('  00_head grade def contains 【已验证】= 只有精确程序核对:', '【已验证】= 只有精确程序核对' in PARTS['00_head.md'])

print('== #2 OEIS U_k-in-m windows actually queried')
idx = rd('data', 'oeis', 'INDEX.md')
ks = sorted(set(int(k) for k in re.findall(r'search_U(\d+)_m\d\.txt', idx)))
print('  U_k(m) (as sequence in m) searched for k =', ks)
print('  verify_all c5b.k567-nohit:', (line_of('c5b.k567-nohit') or '')[:90])
for fn, s in PARTS.items():
    for m in re.finditer(r'k≥5', s):
        ctx = s[max(0, m.start() - 25):m.end() + 25].replace('\n', ' ')
        print('  %s: ...%s...' % (fn, ctx))

print('== #4 c3b relation-space boxes in verify_all (U vs N)')
for cid in ('C3B-E2', 'C3B-E2S', 'C3B-E3B', 'C3B-E3S'):
    l = line_of(cid)
    n = len(re.findall(r'\(\d+(?:, \d+){2,3}\):\d+u', l))
    print('  %-8s boxes=%d  (%s)' % (cid, n, 'U' if cid.startswith('C3B-E2') else 'N'))
x2 = rd('logs', 'review_x2-dfinite_kernel.log').splitlines()
print('  x2 U boxes:', len(re.findall(r'U\(A,B,[^)]*\)=\([^)]*\)', x2[3])), ' x2 N boxes:', len(re.findall(r'N\(A,B,[^)]*\)=\([^)]*\)', x2[4])))

print('== #5 checks of N(k,q) against its combinatorial definition (max k)')
for cid in ('C3-brute', 'c3a-N-def', 'c4-N-dfs', 'N_inversion', 'C3B-PSI', 'rv-Ntri-vs-def', 'c5a-anchor'):
    l = line_of(cid) or ''
    print('  %-14s %s' % (cid, l[:150]))
print('  r-c1 order-type DP:', [l[:120] for l in rd('logs', 'review_r-c1_r4_C3_C6_C7_final.log').splitlines() if '序型' in l][:1])
print('  completion row / summary contain unqualified claim:',
      '核对扩到 k≤60、m≤20（多处更远）' in PARTS['10_uncertain.md'], '核对扩到 k≤60、m≤20。' in PARTS['01_summary.md'])

print('== #6 reviewer-only ranges cited without 「不在 verify_all 中」/log path')
probes = [('02_C1.md', '第二轮复核者 r-c1 另以精确 gcd（i≤150）'), ('02_C1.md', '复核者 r-c1 用与 U 无关的序型 DP 扩到 k≤28'),
          ('04_C3.md', '复核者 x2 用自写 DP 另算了 44 个新盒子'), ('06_C5.md', '复核者 r-c5b 用同法确认到 k≤70')]
for fn, p in probes:
    s = PARTS[fn]
    i = s.find(p)
    seg = s[i:i + 160]
    end = seg.find('。')
    seg = seg[:end + 1 if end >= 0 else len(seg)]
    print('  %s found=%s  logs/ in sentence=%s  不在 verify_all in sentence=%s  | %s' % (
        fn, i >= 0, 'logs/' in seg, '不在 verify_all' in seg, seg[:110]))
for lg in ('review_r-c1_r3_C2_final.log', 'review_r-c1_r4_C3_C6_C7_final.log', 'review_r-c3b_r2_rank.log',
           'review_x2-dfinite_kernel.log', 'review_r-c5b_negzeros_exact.log'):
    print('  exists logs/%s: %s; cited in report: %s' % (lg, os.path.exists(os.path.join(ROOT, 'logs', lg)), lg in ALL))

print('== #7 r-c2b r4b logs')
for lg in ('review_r-c2b_r4b_full.log', 'review_r-c2b_r4b_full_small.log', 'review_r-c2b_r4b_k60.log'):
    s = rd('logs', lg)
    print('  %s: k<=60 mentioned=%s; lines: %s' % (lg, 'k<=60' in s, ' | '.join(l[:60] for l in s.splitlines()[1:6])))

print('== #8 rv2 scripts import core?')
for sc in ('r1_numfield_residues.py', 'r2_two_family.py'):
    s = rd('code', 'review', 'x1-single-sum', sc)
    print('  %s: "import core"/"from core" present: %s' % (sc, bool(re.search(r'^\s*(import core|from core)', s, re.M))))
print('  09_code rv2 row says 不导入 core:', '不导入 core' in PARTS['09_code.md'])

print('== #9/#10 proofs / pointers')
c4 = rd('notes', 'c4.md')
c5a = rd('notes', 'c5a.md')
print('  c4.md has §4.7 低次系数 【已证明，一切 j】:', '### 4.7 低次系数' in c4, ' §4.9 定理 4.9:', '### 4.9 定理 4.9' in c4)
print('  c5a.md has 4.6 / 4.8 / 4.9 sections:', '### 4.6 [t¹]' in c5a, '### 4.8 二元母函数' in c5a, '### 4.9 实根性' in c5a)
for fn, start, stop in (('05_C4.md', '(5)【已证明，一切 j】', '(6)【已证明】'), ('05_C4.md', '(7)【已证明】', '(8)【已证明】'),
                        ('06_C5.md', '(5)【已证明】h_k', '(6)【猜想')):
    s = PARTS[fn]
    seg = s[s.find(start):s.find(stop)]
    print('  %s %s : contains notes/ or §: %s' % (fn, start, ('notes/' in seg) or ('§' in seg)))

print('== #11 what C3B-RES / C3B-PX / C3B-INT check; C3B-INT cited?')
for cid in ('C3B-PX', 'C3B-INT', 'C3B-RES'):
    print('  %-8s %s' % (cid, (line_of(cid) or '')[5:150]))
print('  C3B-INT cited in report:', 'C3B-INT' in ALL)

print('== #12 c5b.diag / c5b.rows')
for cid in ('c5b.diag', 'c5b.rows'):
    print('  %-9s cited=%s  %s' % (cid, cid in ALL, (line_of(cid) or '')[5:120]))

print('== #13 P_3 / Λ notation')
print('  02_C1 notation defines P_m=∏b_i:', 'P_m=∏_{i=0}^{m} b_i' in PARTS['02_C1.md'], '; T1.0(c) uses Λ_k:', '允许行偏序集 Λ_k' in PARTS['02_C1.md'])
print('  06_C5 defines P_3 anywhere (\"P_3 为\"/\"P_3:=\"/\"记 P_3\"):', any(t in PARTS['06_C5.md'] for t in ('P_3 为', 'P_3:=', '记 P_3', 'P_3（')))

print('== #14 c_2 / c_3 double use in 06_C5')
s = PARTS['06_C5.md']
print('  constant c_2≈7.84 present:', 'c_2≈7.8411192294' in s, '; sequence use "c_2=A077949":', 'c_2=A077949' in s, '; c_j 的形式:', 'c_j 的形式' in s)

print('== #15 polynomial-variable convention')
s = PARTS['02_C1.md']
print('  notation block uses 基 C(y+1,q):', '基 C(y+1,q)' in s, '; T1.2 y-remark:', '这里用 y 作 m 的多项式变量' in s, '; T1.4(1) uses C(x+1,q)/Q[x]:', '{C(x+1,q)} 是 Q[x] 的基' in s)
