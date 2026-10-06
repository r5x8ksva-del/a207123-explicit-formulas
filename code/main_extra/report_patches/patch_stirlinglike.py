# -*- coding: utf-8 -*-
"""2026-10-07 新增 T3.9（T3.8 的推论：U 不是 Kauers 意义下的 Stirling-like，Lean：NotStirlingLike.lean）之后，同步报告各节。

改动：
  - 04_C3：T3.8 之后插入 T3.9（陈述、证明、Lean 名）；
  - 09_code ⑤：Lean 表加 NotStirlingLike.lean 一行；Axioms.lean 一行的条数与声明数（从 logs/lean_axioms_2026-10-07.log 抽取）；
  - 00_head：Lean 形式化清单加 T3.9；
  - 01_summary：第 7 条加 T3.9；第 10 条的模块数（原文 11 个，已过时）；第 11 条加 T3.9。
每处替换都断言锚点恰好出现一次。运行前提：logs/lean_axioms_2026-10-07.log 是加入 NotStirlingLike 之后的公理检查，且全量扫描没有其他公理。
用法：py -3.14 code/main_extra/report_patches/patch_stirlinglike.py [--dry]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))   # report_patches → main_extra → code → 根目录
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
DRY = '--dry' in sys.argv
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

NOTE = 'notes/04-主Agent-U不是Stirling-like.md'
texts = {}


def load(name):
    if name not in texts:
        texts[name] = open(os.path.join(PARTS, name), encoding='utf-8').read()
    return texts[name]


def rep(name, old, new):
    t = load(name)
    n = t.count(old)
    assert n == 1, '%s：锚点出现 %d 次：%s' % (name, n, old[:60])
    texts[name] = t.replace(old, new)


# ---------------------------------------------------------------- 公理检查日志
ax = open(os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-07.log'), encoding='utf-8').read()
assert '[lean_one exit code 0]' in ax, 'Axioms.lean 没有通过'
assert 'sorryAx' not in ax
NEW = ['TU_three_points', 'relU_support_det', 'relU_card_support', 'not_mem_relU_of_support_subset']
for nm in NEW:
    assert ("'A207123.%s' depends on axioms: [propext, Classical.choice, Quot.sound]" % nm) in ax, nm
N_PRINT = len(re.findall(r"^'A207123\.[^']+' depends on axioms", ax, re.M))
m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个', ax)
assert m, '全量扫描结果不对'
N_DECL = int(m.group(1))
print('axioms: %d #print lines, %d declarations' % (N_PRINT, N_DECL))

# ---------------------------------------------------------------- 04_C3：插入 T3.9
T39 = ('**T3.9（U 不是 Kauers 意义下的 Stirling-like；T3.8 的推论；2026-10-07 新增）【已证明；(1)(2) 已在 Lean 中形式化：'
       '`A207123.relU_support_det`、`relU_card_support`、`not_mem_relU_of_support_subset`（核心引理 `TU_three_points`）；'
       '(3) 中从 Kauers 的定义到 (2) 的一步是书面论证，未形式化】**\n'
       '陈述：把 Rel(U) 中的算子写成正规形 Σ r_{ab}(k,m)X^aE^{−b}，支撑 Supp={(a,b): r_{ab}≠0}，det(p,p′,p″):=det(p′−p,p″−p)（绝对值是三角形面积的两倍）。'
       '(1) 每个非零 R∈Rel(U) 的支撑里有三个点 p_0,p_1,p_2，det(p_0,p_1,p_2)≥3；特别地 R 至少有三项，U 没有一项或两项的象限递推。'
       '(2) 若正规形 r≠0 的支撑含于三点 {p_0,p_1,p_2} 且 |det(p_0,p_1,p_2)|≤2，则它不在 Rel(U) 中。'
       '(3) 推论：设 T=Σ_{i=0}^{2}c_i(k,m)S^{(s_i,t_i)}（S^{(s,t)}: f(k,m)↦f(k+s,m+t)，(s_i,t_i)∈Z²，c_i 为不全为 0 的有理函数），三个位移点的 |det|≤2，则 T 不在任何象限上（在系数有定义处）零化 U。'
       'Kauers 2007 定义 3 的 Stirling-like 要求零化理想由一条三项算子生成、两条位移向量构成 Z² 的基（|det|=1），所以 **U 不是 Stirling-like**，Kauers 关于 Stirling-like 序列的现成结论不能直接用于 U；新颖性核查（notes/新颖性核查_2026-10-07.md §3.1）原来只有「L1 是四项」的观察，这里补上了证明。\n'
       '证明（' + NOTE + '）：由 T3.8，R=Q·L1，Q 的正规形 q≠0，R 的正规形 r(a,b)=q(a,b)−q(a,b−1)−q(a−1,b)−(m−b)q(a−3,b)（越界取 0）。'
       '取 Supp(Q) 中第二个下标的最小值 b_0、最大值 B（所在点 (a_B,B)），第 b_0 行第一个下标的最小值 a⁻、最大值 a⁺，'
       '则 r(a⁻,b_0)=q(a⁻,b_0)、r(a⁺+3,b_0)=−(m−b_0)q(a⁺,b_0)、r(a_B,B+1)=−q(a_B,B) 都非零（C[k,m] 是整环），det=(a⁺−a⁻+3)(B−b_0+1)≥3。'
       '(2) 由 (1) 的三点是 p_0,p_1,p_2 的排列得到。(3)：在 (k−c,m−d)（c≥max s_i，d≥max t_i）处用这条关系，系数通分为 n_i/D，'
       'R′=Σ n_iX^{c−s_i}E^{−(d−t_i)} 在象限上 D≠0 处零化 U，R=D·R′ 在整个象限上零化 U，R≠0，支撑是原位移点经 (s,t)↦(c−s,d−t) 的像，|det| 不变，与 (2) 矛盾。∎ '
       '这是「L1 的牛顿三角形 (0,0)、(3,0)、(0,1) 面积 3/2，乘积的牛顿多边形含它的平移」的组合版本。'
       '(3) 对 Kauers 定义的读法（零化在哪些点成立）是书面的，例外点若在每个象限里都有无穷多个，论证需要修改，见 ' + NOTE + ' §3。只有主 Agent 一人推导，证明由 Lean 检查。\n'
       '核对：proof-only（Lean 编译与公理检查：logs/lean_notstirling_run2.log、logs/lean_axioms_2026-10-07.log）。')
rep('04_C3.md',
    '核对：c3b.C3B-E1、c3b.C3B-E2、c3b.C3B-E2S、c3b.C3B-E3A、c3b.C3B-E3B、c3b.C3B-E3S、c3b.C3B-ISO、c3b.C3B-L1。',
    '核对：c3b.C3B-E1、c3b.C3B-E2、c3b.C3B-E2S、c3b.C3B-E3A、c3b.C3B-E3B、c3b.C3B-E3S、c3b.C3B-ISO、c3b.C3B-L1。\n\n' + T39)

# ---------------------------------------------------------------- 09_code：Lean 表
t = load('09_code.md')
lines = t.split('\n')
idx = [i for i, ln in enumerate(lines) if ln.startswith('| `A207123/HStruct.lean` |')]
assert len(idx) == 1
lines.insert(idx[0] + 1, '| `A207123/NotStirlingLike.lean` | T3.9（2026-10-07） | `det2`（三个格点的二倍有向面积）；`TU_three_points`（Q≠0 时 Q·L1 的正规形支撑里有三个点，二倍面积 ≥3）；`relU_support_det`、`relU_card_support`（Rel(U) 的非零元至少有三项）、`not_mem_relU_of_support_subset`（支撑含于二倍面积 ≤2 的三点时不在 Rel(U) 中）；从 Kauers 的定义到这里的一步是书面论证，写在文件头 |')
texts['09_code.md'] = '\n'.join(lines)
rep('09_code.md',
    '| `Axioms.lean` | — | 对 252 条定理（报告各条标签与上表中列出的定理）',
    '| `Axioms.lean` | — | 对 %d 条定理（报告各条标签与上表中列出的定理）' % N_PRINT)
rep('09_code.md',
    '另对 A207123 各模块的全部 2649 个声明（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个',
    '另对 A207123 各模块的全部 %d 个声明（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个'
    '（2026-10-07 加入 NotStirlingLike.lean 后重跑：新模块单独编译、根模块重编、`Axioms.lean` 与 `Checks.lean` 重跑都通过，'
    '日志 logs/lean_notstirling_run2.log、logs/lean_root_2026-10-07.log、logs/lean_axioms_2026-10-07.log、logs/lean_checks_2026-10-07.log；'
    '其余 26 个模块沿用当天早些时候全量构建的结果，没有重编）' % N_DECL)

# ---------------------------------------------------------------- 00_head
rep('00_head.md',
    'T5.4(2) 的列方向与 (3)–(5) 的代数部分（逐条范围见各条标签与 ⑤ 的表）。',
    'T5.4(2) 的列方向与 (3)–(5) 的代数部分（逐条范围见各条标签与 ⑤ 的表）。2026-10-07 又形式化了 T3.9（T3.8 的推论：U 不是 Kauers 意义下的 Stirling-like）。')

# ---------------------------------------------------------------- 01_summary
rep('01_summary.md',
    '（N 的则恰为三角递推算子 L_N 生成的左理想，见 T3.8）',
    '（N 的则恰为三角递推算子 L_N 生成的左理想，见 T3.8）；由此 U 不是 Kauers 意义下的 Stirling-like（T3.9）')
rep('01_summary.md',
    '`verify_all.py` 的 11 个模块全部 PASS（见 ⑤）',
    '`verify_all.py` 的 13 个模块全部 PASS（见 ⑤）')
rep('01_summary.md',
    'T5.3(1)–(5) 的主体等（范围见各条标签）',
    'T5.3(1)–(5) 的主体等（范围见各条标签），2026-10-07 又加上 T3.9')

# ---------------------------------------------------------------- 写回
for name, txt in sorted(texts.items()):
    if DRY:
        print('would patch', name)
    else:
        with open(os.path.join(PARTS, name), 'w', encoding='utf-8') as f:
            f.write(txt)
        print('patched', name)
print('dry run' if DRY else 'done')
