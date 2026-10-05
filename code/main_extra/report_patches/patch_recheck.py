# -*- coding: utf-8 -*-
"""最终复查（第四轮的后半段）确认的问题；计时范围、⑤ 结果表与运行时间在空闲重跑后另行同步。"""
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


patch(P + '00_head.md', [
(r"另做了三轮多 Agent 工作流：第一轮 8 个方向并行研究；第二轮 11 个对抗性复核者逐条复核；第三轮 3 个审计者用独立程序逐条核对本报告里的公式、核对与笔记的一致性、交付要求是否齐全。",
 r"另做了四轮多 Agent 工作流：第一轮 8 个方向并行研究；第二轮 11 个对抗性复核者逐条复核；第三轮 3 个审计者用独立程序逐条核对本报告里的公式、核对与笔记的一致性、交付要求是否齐全；第四轮是最终对抗审计，5 个审计者分别从交付要求、C-1/C-2、C-3、C-4/C-5、全文一致性复查，每条发现再由独立复核者核实，修订后又由 2 个复查者（逐条核对修订、通读全文）各配复核者再查一遍，确认属实的问题都已改正（原始输出 logs/phase4_final_audit_output.json、logs/phase4b_recheck_output.json；见 ④B.13）。"),
(r"少数扩展范围只由第二轮复核脚本跑过，都不在 verify_all 中；已在相应条目注明并给出日志路径。",
 r"少数扩展范围只由第一轮的扩展/探索脚本、第二轮复核脚本或第三、四轮审计脚本跑过，都不在 verify_all 中；已在相应条目注明并给出日志路径。"),
(r"- 等级：【已证明】= 附完整证明（另有程序核对）；【已验证】= 只有精确程序核对，写明范围；【猜想】= 只有数据；",
 r"- 等级：【已证明】= 附完整证明（另有程序核对）；【已验证】= 只有精确程序核对，写明范围；【已验证（数值）】= 用 decimal 高精度计算得到的具体数值结论，写明精度与范围；【猜想】= 只有数据（包括只有浮点或容差判断支持的一般性结论）；"),
(r"r2 只对由已证明的 G_m=W_m/P_m 推出的留数–范数条件做精确穷举。",
 r"r2 只对由已证明的 G_m=W_m/P_m 推出的纤维留数条件（留数元与 x^a、x^b 在 K_i 中 Q-线性相关，即 det(R_i,x^a,x^b)=0）做精确穷举（范数计算在 r1）。"),
(r"另有子 Agent 对 Lipshitz 1989 做了几次文献元数据只读查询（见 ④C）。",
 r"另有子 Agent 为核实 D-finite 的定义做了几次只读文献查询（见 ④C）。"),
])

patch(P + '01_summary.md', [
(r"（例外：N(k,q) 的组合意义按定义直接计数只核到 k≤9，复核者用独立 DP 到 k≤28）",
 r"（例外：N(k,q) 的组合意义按定义直接计数，在 verify_all 中只核到 k≤9，扩展脚本到 k≤11，复核者用独立 DP 到 k≤28）"),
(r"全部多项式系数象限递推恰为引理 1 算子生成的左理想。",
 r"U 的全部多项式系数象限递推恰为引理 1 算子生成的左理想（N 的则恰为三角递推算子 L_N 生成的左理想，见 T3.8）。"),
(r"基点 2d+1 的 Newton 正性在 d=69 首次失效，奇数 69≤d≤101 为负",
 r"基点 2d+1 的第 0 个 Newton 系数 p_d(2d+1) 在 d=69 首次为负，奇数 69≤d≤101 都为负（偶数 d 时第 0 个系数已证明为正）"),
])

patch(P + '02_C1.md', [
(r"扩展脚本另核对 a_direct 到 k=11。",
 r"扩展脚本另核对 a_direct 到 k=11（k=10,11 时 n≤13，另 k≤7 时 n≤20；logs/c1_extended.log 的 E2，不在 verify_all 中）。"),
])

patch(P + '04_C3.md', [
(r"复核者 r-c3a 的更紧的界给出 ≤6.6·10^{−121}）",
 r"复核者 r-c3a 的更紧的界给出 ≤6.6·10^{−121}，见 logs/review_r-c3a_r1_exact.log 的 r1-counterex，不在 verify_all 中）"),
(r"在 k=75、150 为 1.669、2.036（比值 1.22）",
 r"在 k=75、150 为 1.669、2.036（比值 1.22；复核者 r-c3a 的数据，logs/review_r-c3a_r3_growth.log，不在 verify_all 中）"),
(r"维数公式的计数：U 的情形看角点 (α′,β*+1) 与 (α*+3,β′)；N 的情形必须取 β′=max{b:q_{α*b}≠0}",
 r"维数公式的计数：把 Q 写成 Σ_{a,b}Q_{ab}X^aE^{−b}（N 的情形把 E^{−b} 换成 Y^b；Q_{ab} 为 Q 的多项式系数），令 β* 为出现的最大 b、α′ 为满足 Q_{α′β*}≠0 的某个 a，α* 为出现的最大 a、β′ 为满足 Q_{α*β′}≠0 的某个 b；U 的情形看角点 (α′,β*+1) 与 (α*+3,β′)；N 的情形必须取 β′=max{b:Q_{α*b}≠0}"),
])

patch(P + '05_C4.md', [
(r"ν_j(q)=Σ_{i≤j}π_i(q)·D(q+j−i,j−i)（π_i=[x^i]P_{q−1}）",
 r"ν_j(q):=[x^{q+j}]Num_q=Σ_{i≤j}π_i(q)·D(q+j−i,j−i)（π_i(q):=[x^i]P_{q−1}，与 (6) 的 π_{j,i} 无关）"),
(r"c4.c4-pattern-brute（按定义暴力枚举 d≤3；探索中 d=4）",
 r"c4.c4-pattern-brute（按定义暴力枚举 d≤3；探索脚本另做 d=4，logs/c4_explore9b_d4.log，不在 verify_all 中）"),
(r"例如 d=69 时等于 N(139,70)−70!≈−1.74·10^{99}（第二轮复核者 r-c4i 发现，主 Agent 独立重算确认）。",
 r"例如 d=69 时等于 N(139,70)−70!≈−1.74·10^{99}（第二轮复核者 r-c4i 发现，主 Agent 独立重算确认）。最终复查中两位审计者另用两条独立路线算出：d≤68 时基点 2d+1 的全部 Newton 系数都为正，偶数 d=74,76,…,100 时第 1 个系数为负，d=77、79、81 时第 2 个系数也为负（logs/final_audit_fixcheck.log、logs/final_audit_verify-fixcheck.log，不在 verify_all 中）。"),
])

patch(P + '06_C5.md', [
(r"(5)（数值结果，不属于 T5.1 已证明的部分：decimal 90 位计算，核对 c5a.c5a-prompt-k40（数值））",
 r"(5)【已验证（数值）：decimal 90 位计算，核对 c5a.c5a-prompt-k40；这一小条不属于 T5.1 的已证明部分】"),
(r"核对：c5a.c5a-roots、c5a.c5a-binet（Lagrange 形式 m≤20、k≤60 精确相等）、c5a.c5a-filter（单独抽出 b_m 的极点分量，1≤m≤20）、c5a.c5a-cm-form、c5a.c5a-cm-repr、",
 r"核对：c5a.c5a-roots（实根唯一用 Sturm 精确核对；ρ_j 单调与复根模长不等式为 decimal 数值核对，j≤30，一般证明见 T1.3(4) 与上文 (2) 的关键不等式）、c5a.c5a-binet（Lagrange 形式 m≤20、k≤60 精确相等）、c5a.c5a-filter（单独抽出 b_m 的极点分量，1≤m≤20）、c5a.c5a-cm-form、c5a.c5a-cm-repr（Q(ρ_m) 中的表示为精确计算；与闭式的比较为 decimal 数值，m≤8）、"),
(r"c0.c0-cm（数值）、c1.C2-cm。",
 r"c0.c0-cm（数值）、c1.C2-cm（数值）。"),
(r"(1)【已证明】基本事实：h_k(0)=1，h_k(1)=2（k≥2）",
 r"(1)【已证明；证明见 notes/c5a.md §4.1、§4.6、§4.7：h_k(0)、h_k(1)、h_{k,i} 的反演式、h_k^{(d)}(1) 与 n_k(z) 都由 T1.7 的两个表示 Σ_mU_k(m)t^m=h_k/(1−t)^{k+1} 与 h_k=Σ_qN(k,q)t^{q−1}(1−t)^{k−q} 直接得到；[t¹]h_k 的母函数与正性另用 T1.3(1) 的 G_1=W_1/P_1】基本事实：h_k(0)=1，h_k(1)=2（k≥2）"),
(r"N 行多项式 n_k(z)=(1+z)^{k−1}h_k(z/(1+z))。",
 r"N 行多项式 n_k(z):=Σ_qN(k,q)z^{q−1}=(1+z)^{k−1}h_k(z/(1+z))。"),
(r"（论证：列方向 (E²−1)^{2k+1} 零化 a_k(n)，所以有限个初值核对即足够；行方向由 (m_1+1)²(m_2+1)² 阶转移矩阵给出先验阶界；",
 r"（论证：列方向（固定 k）记 E 为 n 方向的移位算子（Ea(n)=a(n+1)，与 T3.8 中 m 方向的 E 无关），(E²−1)^{2k+1} 零化 a_k(n)，所以有限个初值核对即足够；行方向（固定 n）由 (m_1+1)²(m_2+1)² 阶转移矩阵（m_1=⌈n/2⌉、m_2=⌊n/2⌋，即两个 (m+1)² 阶高度转移矩阵的 Kronecker 积）给出先验阶界；"),
])

patch(P + '08_failed.md', [
(r"**B. 两轮工作中出过的错（都已更正，记在这里便于复核）**",
 r"**B. 各轮工作中出过的错（都已更正，记在这里便于复核）**"),
(r"（对 m=5,6 需要 k≤60）",
 r"（对 m=5,6，k≤30 时仍有「零检验」形状对，改用 k≤60 的数据后全部被反驳）"),
(r"另有子 Agent 为查 Lipshitz 1989 读了几次文献元数据（Crossref、Semantic Scholar API、ar5iv、Wikipedia；ScienceDirect 返回 403）。",
 r"另有子 Agent 为核实 D-finite 的定义做了几次只读文献查询：Lipshitz 1989 的元数据与引言（Crossref、Semantic Scholar API；ScienceDirect 返回 403），以及 ar5iv 上 Bousquet-Mélou–Petkovšek、Bousquet-Mélou–Mishna 两篇论文与 Melczer 学位论文的相关文本、Wikipedia「Holonomic function」页面。"),
(r"更正「verify_all 只依赖标准库」（rv2 必须有 numpy）。",
 r"更正「verify_all 只依赖标准库」（rv2 必须有 numpy）。修订后的复查又补了：摘要中丢失的限定词（N(k,q) 组合意义的核对范围、只指第 0 个 Newton 系数、U 与 N 各自的生成元）、T5.1(5) 的等级【已验证（数值）】（并在开头的等级说明中补上这一档）、几处数值核对的「数值」标注与日志出处、ν_j 与 T3.8 角点记号的定义、轮数与文献查询记录的描述。"),
])

patch(P + '09_code.md', [
(r"- 两轮工作流的原始返回值：`logs/phase1_workflow_output.json`、`logs/phase2_review_output.json`；",
 r"- 各轮工作流的原始返回值：`logs/phase1_workflow_output.json`、`logs/phase2_review_output.json`、`logs/phase3_audit_output.json`、`logs/phase4_final_audit_output.json`、`logs/phase4b_recheck_output.json`；第四轮各审计者的独立脚本在 `code/review/final-audit/`，输出为 `logs/final_audit_*.log`；报告各轮修订的补丁脚本在 `code/main_extra/report_patches/`；"),
(r"r2 只做纤维条件的精确代数穷举）",
 r"r2 只做纤维留数条件的精确代数穷举）"),
])

patch(ROOT + r'\README.md', [
(r"6. 整合报告，运行 verify_all.py 做最终核对。",
 r"6. 第四轮工作流：最终对抗审计（5 个审计方向，各配一个反驳验证者，确认 58 条），修订后再由 2 个复查者各配验证者复查一遍；据此再修订报告（`logs/phase4_final_audit_output.json`、`logs/phase4b_recheck_output.json`，补丁脚本在 `code/main_extra/report_patches/`）。" + "\n" +
 r"7. 整合报告，运行 verify_all.py 做最终核对。"),
(r"（`phase1_workflow_output.json`、`phase2_review_output.json`、`phase3_audit_output.json`）",
 r"（`phase1_workflow_output.json`、`phase2_review_output.json`、`phase3_audit_output.json`、`phase4_final_audit_output.json`、`phase4b_recheck_output.json`）"),
(r"三轮工作流的原始返回值",
 r"四轮工作流的原始返回值"),
])
