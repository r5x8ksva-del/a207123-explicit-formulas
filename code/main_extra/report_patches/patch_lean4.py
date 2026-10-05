# -*- coding: utf-8 -*-
"""Lean 形式化第四轮（2026-10-05）完成后同步报告分节：给新形式化的条目加 Lean 标签，更新 ⑤ 的 Lean 表、
00_head、① 第 11 条、⑥ 与完成度表。

用法（顺序不能换）：
  1. 在 lean/ 下运行 ./run_lean_checks.sh（逐个模块串行构建，再跑 Axioms.lean、Checks.lean）；
  2. py -3.14 code/main_extra/report_patches/patch_lean4.py
     （从 logs/lean_build.log 读取结果：断言三步退出码都是 0、全量扫描中依赖其他公理的声明为 0 个、
     `#print axioms` 的条数与 lean/Axioms.lean 一致；每处替换都断言原文恰好出现一次）；
  3. py -3.14 code/main_extra/assemble_report.py 重新拼接报告。
"""
import re
import sys

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

STD = {'propext', 'Classical.choice', 'Quot.sound'}
DRY = '--dry' in sys.argv  # 只检查每处原文是否恰好出现一次，不读日志、不写文件

# ---------- 从构建日志读取结果 ----------
if not DRY:
    log = open(ROOT + r'\logs\lean_build.log', encoding='utf-8').read()
    codes = re.findall(r'^\[exit code (\d+)\]', log, flags=re.M)
    assert codes == ['0', '0', '0'], codes
    m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[([^\]]*)\]；依赖其他公理的声明：(\d+) 个', log)
    assert m, 'sweep line not found'
    NDECL, AXS, NBAD = m.group(1), m.group(2), m.group(3)
    assert NBAD == '0', NBAD
    assert set(a.strip() for a in AXS.split(',')) == STD, AXS
    assert 'sorry' not in log.lower(), 'sorry in build log'

    axiom_src = open(ROOT + r'\lean\Axioms.lean', encoding='utf-8').read()
    printed = re.findall(r'^#print axioms (\S+)', axiom_src, flags=re.M)
    assert len(printed) == len(set(printed)), 'duplicate #print axioms lines'
    dep = dict(re.findall(r"^'(A207123\.[^']*)' depends on axioms: \[([^\]]*)\]", log, flags=re.M))
    nodep = re.findall(r"^'(A207123\.[^']*)' does not depend on any axioms", log, flags=re.M)
    assert len(dep) + len(nodep) == len(printed), (len(dep), len(nodep), len(printed))
    assert set(dep) | set(nodep) == set(printed)
    fewer = []  # 只用到三条标准公理中一部分的定理
    for name, axs in dep.items():
        s = set(a.strip() for a in axs.split(','))
        assert s <= STD, (name, s)
        if s != STD:
            fewer.append((name, sorted(s)))
    fewer += [(n, []) for n in nodep]
    NPRINT = len(printed)
    print('sweep:', NDECL, 'declarations;', NPRINT, '#print axioms lines; fewer axioms:', fewer)


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    if DRY:
        print('dry ok', path[-28:], len(pairs))
        return
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


# ====================================================================================================
# 一、正文标签（已完成并核对过陈述的模块）
# ====================================================================================================

# ---------- 02_C1：T1.2、T1.3(3)(4)、T1.5–T1.9 ----------
C1 = [
    (r"**T1.2（(C1)）【已证明】**",
     r"**T1.2（(C1)）【已证明；已在 Lean 中形式化：`A207123.T1_2`（汇总）、`C1_sum`、`existsUnique_upoly`、"
     r"`natDegree_upoly`、`leadingCoeff_upoly_eq`、`upoly_eval_neg_one`、`upoly_sub_comp`】**"),
    (r"(3)【已证明】P_m 无重因子（",
     r"(3)【已证明；已在 Lean 中形式化：`A207123.T1_3_3`（汇总）、`isCoprime_bpoly`、`separable_bpoly`、"
     r"`squarefree_Ppoly`、`simple_root_Ppoly`（P_m 的每个复根都是单根且 W_m 在该处非零）、"
     r"`discr_reverse_bpoly`（判别式 −i(4+27i)，i≥1 时为负）】P_m 无重因子（"),
    (r"(4)【已证明，提示词标为「未证」】增长率：",
     r"(4)【已证明，提示词标为「未证」；根的部分已在 Lean 中形式化：`A207123.existsUnique_rho`、`one_lt_rho`、"
     r"`rho_strictMono`、`normSq_eq_of_root`、`norm_lt_rho_of_root`、`root_P_min`（x_m=1/ρ_m 是 P_m 唯一的模最小根）；"
     r"渐近式 U_k(m)=c_mρ_m^k+O(r^k) 与 c_m>0 未形式化】增长率："),
    (r"**T1.5（(C4) 两个系数公式与 Θ 公式）【已证明】**",
     r"**T1.5（(C4) 两个系数公式与 Θ 公式）【已证明；已在 Lean 中形式化：(1) `A207123.ci_formula`；"
     r"(2) `coeff_inv_Ppoly`；(3) `factorial_mul_coeff_inv_Ppoly`；(4) `U_eq_Theta`（k≥0）、`Theta_eq_coeff_prod`、"
     r"`Theta_eq_coeff_Ppoly_div`；注中的两个反例 `T15_note_P`、`T15_note_c`】**"),
    (r"**T1.6（(C5) PDE）【已证明】**",
     r"**T1.6（(C5) PDE）【已证明；已在 Lean 中形式化：`A207123.FK_pde`（Q[[x,t]] 中）；逐项形式 `pde_coeff`"
     r"（越界取 0）与反例 `pde_coeff_needs_zero_convention`；注中「齐次方程只有零解、形式解唯一」"
     r"`pde_homogeneous`、`pde_unique`】**"),
    (r"**T1.7（(C6) h 多项式）【已证明】**",
     r"**T1.7（(C6) h 多项式）【已证明；已在 Lean 中形式化：`A207123.hpoly_spec`、`hpoly_formula_zero`"
     r"（k=0 须单列）、`hpoly_rec`（k≥3）、`hrec_eq_hpoly`（三个初值恰好生成全部 h_k）、`hrec_bad_ne`"
     r"（取 h_2=1 的反例）、`hpoly_three`…`hpoly_six`、`hpoly_eval_one_eq_two`】**"),
    (r"**T1.8（(C7) 分子）【已证明】**",
     r"**T1.8（(C7) 分子）【已证明；已在 Lean 中形式化：`A207123.P_mul_Nser`（Num_q 是多项式）、"
     r"`natDegree_Numq`、`leadingCoeff_Numq`、`Numq_lowest`（q≥2）、`Numq_one`、`prompt_numerators`】**"),
    (r"**T1.9（(C8) 与 A、B 的推导链）【已证明（推导链）；A、B 的正式工作不在本任务】**",
     r"**T1.9（(C8) 与 A、B 的推导链）【已证明（推导链）；A、B 的正式工作不在本任务；推导链已在 Lean 中形式化："
     r"`A207123.T1_9`（汇总）、`a_eq_parity`、`existsUnique_parity`、`natDegree_parP`、`leadingCoeff_parP`、"
     r"`natDegree_parQ`、`leadingCoeff_parQ`、`gf_aSer`、`parDen_dvd_of_mul_aSer`、`parity_min_order`（k≥1），"
     r"k=0 的反例 `parity_min_order_zero`】**"),
]
patch(P + '02_C1.md', C1)

# ---------- 03_C2：T2.5、T2.7、T2.8(1) ----------
C2 = [
    (r"**T2.5（其他等价形式，及与 (C4) 的关系）【已证明】**",
     r"**T2.5（其他等价形式，及与 (C4) 的关系）【已证明；公式部分已在 Lean 中形式化：(1) `A207123.U_F3`"
     r"（另有自然数形式 `U_F3_nat`；Lean 走系数提取的代数路线，组合证明中的映射 φ 未形式化）；(2) `Theta_eq_H`、"
     r"`Theta_eq_F3_term`（逐项相同）、反例 `Theta_vs_H_example`；(3) `U_F4`、`R_formula`】**"),
    (r"**T2.7（j 求和的结构性原因）【已证明】**",
     r"**T2.7（j 求和的结构性原因）【已证明；第一句（Σ_{j<m}P_j 不是 Gosper 可和的）已在 Lean 中形式化："
     r"`A207123.partialSum_P_not_hypergeometric`（超几何项按「对充分大的 m 满足 q(m)T(m+1)=p(m)T(m)，q≠0」"
     r"定义，比通常的定义宽，所以结论更强）、核心引理 `no_gosper_solution`；依赖文献的推论未形式化】**"),
    (r"(1)【已证明】k≥1 时 N(k,q)=Σ_{i=1}^{q}",
     r"(1)【已证明；已在 Lean 中形式化：`A207123.N_explicit`（三层和）；反演式本身是 T1.4 的 `N_inv`】"
     r"k≥1 时 N(k,q)=Σ_{i=1}^{q}"),
]
patch(P + '03_C2.md', C2)

# ---------- 04_C3：T3.5、T3.6、T3.7(3)、T3.8 维数公式 ----------
C3 = [
    (r"**T3.5（N 的二元母函数 𝒩(x,y)=Σ N(k,q)x^ky^q）【已证明；Humbert 部分同 T3.3(2)】**",
     r"**T3.5（N 的二元母函数 𝒩(x,y)=Σ N(k,q)x^ky^q）【已证明；Humbert 部分同 T3.3(2)；已在 Lean 中形式化："
     r"(1) 的第一种写法 `A207123.one_add_X_mul_FK_eq_subst`、`subst_NKser`（代换用 Mathlib 的 `PowerSeries.subst`）；"
     r"(2) `NK_pde`；(3) 中的 [y^q]𝒩=Σ_i(−1)^{q−i}C(q,i)G_{i−1} 即 `Nser_eq_sum`；(3) 的其余部分未形式化】**"),
    (r"**T3.6（h 多项式的二元母函数）【已证明】**",
     r"**T3.6（h 多项式的二元母函数）【已证明；已在 Lean 中形式化：`A207123.HH_eq_F`（z↦z(1−t) 用 Mathlib 的 "
     r"`PowerSeries.rescale`）、`HH_eq_N`、`HH_pde`】**"),
    (r"；(2) `A207123.no_k_only_recurrence`（p_ab∈C[k]）；(3) 未形式化】**",
     r"；(2) `A207123.no_k_only_recurrence`（p_ab∈C[k]）；(3) 全部——「𝒩 不是 D-finite」`not_isDFinite_NKser`"
     r"（对任何系数域 K⊆C；ODE 部分 `no_x_ODE_NK` 用下面 (3) 证明中的代换 y=t/(1−t)），「N 没有 k-only 象限递推」"
     r"`no_k_only_recurrence_N`（Lean 中不用极点论证，而是沿用 T3.8 中 N 的二项式变换搬运，归结到 (2)）】**"),
    (r"【已证明；Rel(U)=O_U·L1 与 Rel(N)=O_N·L_N 已在 Lean 中形式化：",
     r"【已证明；已在 Lean 中形式化（全部）。Rel(U)=O_U·L1 与 Rel(N)=O_N·L_N："),
    (r"饱和引理 (i)(ii)：`saturation_Y`、`saturation_one_add_Y`；维数公式未形式化】**",
     r"饱和引理 (i)(ii)：`saturation_Y`、`saturation_one_add_Y`。维数公式：`finrank_relU_tot`、`finrank_relU_gr`、"
     r"`finrank_relN_tot`、`finrank_relN_gr`（关系空间取为盒子与 Rel(U)、Rel(N) 之交，`mem_relBoxU_iff`、"
     r"`mem_relBoxN_iff`；盒子里的关系恰为 Q·L1、Q·L_N 且 Q 在小盒子里：`relU_box_tot_iff`、`relN_box_tot_iff`）】**"),
    (r"（第一轮原文「与 §6 同法」按字面不成立，例 Q=1+Y；复核已补正，公式不变，新增 14 个盒子的数据一致）。",
     r"（第一轮原文「与 §6 同法」按字面不成立，例 Q=1+Y；复核已补正，公式不变，新增 14 个盒子的数据一致）。"
     r"Lean 形式化（`lean/A207123/OreDim.lean`）同样用角点论证：在 Q 的正规形支撑中按字典序取极大项，说明 Q·L 的"
     r"支撑超出盒子，从而 Q 必须在小盒子里；再用正规形单项式线性无关与右乘 L 的单射计数。"),
]
patch(P + '04_C3.md', C3)

# ---------- 05_C4：T4.1、T4.2(3)、T4.3(1)–(5) ----------
C4 = [
    (r"**T4.1（N(k,k−d) 最终是 2d 次多项式，门槛恰为 2d+2）【已证明，对一切 d】**",
     r"**T4.1（N(k,k−d) 最终是 2d 次多项式，门槛恰为 2d+2）【已证明，对一切 d；已在 Lean 中形式化："
     r"`A207123.T4_1_a`（存在唯一）、`T4_1`（次数、首项、次首项、两个缺陷值）、`T4_1_threshold`（门槛精确）、"
     r"`ndPoly_zero_one`（p_0、p_1；p_2 见 `N_sub_two`）；与 S(k,k−d) 首项的比较、p_3–p_5 的显式式、"
     r"以 m 展开时系数符号的观察与例外值表未形式化】**"),
    (r"(3)【已证明，一切 d】以门槛 2d+2 为基点的 Newton 系数",
     r"(3)【已证明，一切 d；已在 Lean 中形式化：`A207123.T4_2_3`】以门槛 2d+2 为基点的 Newton 系数"),
    (r"(1)【已证明】三项递推（含边界缺陷）",
     r"(1)【已证明；已在 Lean 中形式化：`A207123.Nser_three_term` 与反例 `Nser_three_term_needs_boundary`、"
     r"`Numq_three_term`、`Numq_three_term_boundary`、`Numq_three_term_fails_at_two`、`leadingCoeff_Numq_rec`、"
     r"`Numq_deg_lead_low`】三项递推（含边界缺陷）"),
    (r"(2)【已证明】容斥闭式",
     r"(2)【已证明；已在 Lean 中形式化：`A207123.Num_eq_IE_closed_form`、`P_mul_Nser_eq_IE`】容斥闭式"),
    (r"(3)【已证明】系数全非负",
     r"(3)【已证明；已在 Lean 中形式化：`A207123.Numq_full_history` 与反例 `full_history_at_two`、"
     r"`Numq_hasNonnegCoeffs`、`Numq_coeff_gap`、`Numq_coeff_pos_iff`、`Numq_coeff_ne_zero_iff`】系数全非负"),
    (r"(4)【已证明】Num_q(1)=A000262(q)",
     r"(4)【已证明；x=1 处的递推与初值已在 Lean 中形式化：`A207123.Numq_eval_one_rec`、`Numq_eval_one_init`；"
     r"与 A000262（OEIS 按「集合划分为有序块」组合定义）的等同未形式化】Num_q(1)=A000262(q)"),
    (r"(5)【已证明，一切 j；证明见 notes/c4.md §4.7：",
     r"(5)【已证明，一切 j；一般恒等式 ν_j(q)=Σ_{i≤j}π_i(q)·N(q+j−i,q)、j=1,2 的显式式与 j≤2 的门槛已在 Lean 中"
     r"形式化：`A207123.Numq_coeff_q_add`、`Numq_coeff_q_add_one`、`Numq_coeff_q_add_two`、"
     r"`Numq_coeff_exception_zero`、`Numq_coeff_exception_one`、`Numq_coeff_exception_two`（一般 j 的次数、首项与门槛"
     r"未形式化）；证明见 notes/c4.md §4.7："),
]
patch(P + '05_C4.md', C4)

# ---------- 06_C5：T5.2、T5.4(2)–(5) ----------
C5 = [
    (r"**T5.2（固定 k、m→∞：m 的次首项系数）【已证明】**",
     r"**T5.2（固定 k、m→∞：m 的次首项系数）【已证明；已在 Lean 中形式化：B_d(k) 的公式 `A207123.T5_2_formula`、"
     r"[m^k]U_k=2/k! `T5_2_top`、[m^{k−1}]U_k `T5_2_sub` 与 k=3 的例外 `T5_2_sub_three`；「k≥2d+2 时是 2d 次多项式、"
     r"门槛精确」、[m^{k−2}]、[m^{k−3}] 的显式式与渐近形式未形式化】**"),
    (r"(2)【已证明】OEIS 里这一族的全部 Empirical 递推",
     r"(2)【已证明；列方向（4k 阶、特征多项式 (x−1)^{2k+1}(x+1)^{2k−1}、阶数最小）就是 T1.9，已在 Lean 中形式化："
     r"`A207123.parDen_dvd_of_mul_aSer`、`parity_min_order`（k≥1）；行方向的阶数（对精确数据做 BM）与 Barker 的猜想"
     r"未形式化】OEIS 里这一族的全部 Empirical 递推"),
    (r"(3)【已证明，证明见 notes/c5b.md §3 的 T6、T7】**R_k=A038718(k+2)**",
     r"(3)【已证明，证明见 notes/c5b.md §3 的 T6、T7；母函数部分已在 Lean 中形式化：`A207123.gf_R`、`gf_R_shift`、"
     r"`gf_R_prompt_wrong`；R_k=A038718(k+2) 与 Hamilton 路双射未形式化（A038718 按排列的组合条件定义）】"
     r"**R_k=A038718(k+2)**"),
    (r"(4)【已证明】U_3(m)=",
     r"(4)【已证明；三个等号已在 Lean 中形式化：`A207123.U_three`、`U_three_choose`、`U_three_eq_A084990`"
     r"（A084990 照条目的定义 a(n)=n(n²+3n−1)/3）；双射与 Q_3 的结构未形式化】U_3(m)="),
    (r"(5)【已证明】U_4(m)=",
     r"(5)【已证明；前两个等号已在 Lean 中形式化：`A207123.U_four`、`U_four_choose`；=A326247(m+2)（该条目按"
     r"「不交叉也不嵌套的边对」组合定义）与双射 Φ 未形式化】U_4(m)="),
]
patch(P + '06_C5.md', C5)

# ====================================================================================================
# 二、⑤（09_code）的 Lean 表
# ====================================================================================================
ROWS = [
    r"| `A207123/Poly.lean` | T1.2、T1.3(3) | `upoly k`（u_k，取为二项式基展开 Σ_q N(k,q)·C(y+1,q)；`existsUnique_upoly` 说明任何"
    r"插值多项式都等于它）；`T1_2`（汇总）：`C1_sum`（(C1)，越界下标按 T1.1 的约定 `Uext`）、`natDegree_upoly`、"
    r"`leadingCoeff_upoly_eq`、`upoly_eval_neg_one`、`upoly_sub_comp`（u_{−1}=1、u_{−2}=0 由 `uext` 实现）；"
    r"`T1_3_3`（汇总）：`isCoprime_bpoly`、`separable_bpoly`、`squarefree_Ppoly`、`simple_root_Ppoly`、"
    r"`discr_reverse_bpoly` |",
    r"| `A207123/Growth.lean` | T1.3(4) 的根的部分 | `rho m`（m≥1 时 y³−y²−m 的唯一实根）：`existsUnique_rho`、"
    r"`one_lt_rho`、`rho_spec`、`rho_strictMono`；复根 `normSq_eq_of_root`（\|w\|²=m/ρ_m）、`norm_lt_rho_of_root`；"
    r"`root_P_min`（x_m=1/ρ_m 是 P_m 唯一的模最小根） |",
    r"| `A207123/Coeffs.lean` | T1.5、T2.5 | `ci i n`（c_i(n):=[x^n]1/b_i）与 `ci_formula`；`coeff_inv_Ppoly`、"
    r"`factorial_mul_coeff_inv_Ppoly`；`Theta m t n`（照抄 c1.md §6.4）与 `U_eq_Theta`（k≥0）、`Theta_eq_coeff_prod`、"
    r"`Theta_eq_coeff_Ppoly_div`；求和约定的两个反例 `T15_note_P`、`T15_note_c`（用 Mathlib 的广义二项式 "
    r"`Ring.choose`）；F3 型 `U_F3`、`U_F3_nat`；`Theta_eq_H`、`Theta_eq_F3_term`、`Theta_vs_H_example`；"
    r"`U_F4`、`R_formula`（n<0 时 c_i(n)=0 由 `ciZ` 实现） |",
    r"| `A207123/HNum.lean` | T1.6、T1.7、T1.8 | `FK_pde`（Q[[x,t]] 写成 Q[[x]][[t]]，1/(1−t)² 为 `Ring.inverse`）、"
    r"逐项形式 `pde_coeff` 与 `pde_coeff_needs_zero_convention`、`pde_homogeneous`、`pde_unique`；`hpoly k`"
    r"（h_0=1，k≥1 时按 N 表达式）与 `hpoly_spec`、`hpoly_formula_zero`、`hpoly_rec`、`hrec_eq_hpoly`、`hrec_bad_ne`、"
    r"`hpoly_three`…`hpoly_six`、`hpoly_eval_one_eq_two`；`Numq q`（按 T4.3(2) 的容斥闭式定义）与 `P_mul_Nser`"
    r"（它等于 P_{q−1}·Σ_kN(k,q)x^k）、`Nser_eq_sum`、`natDegree_Numq`、`leadingCoeff_Numq`、`Numq_lowest`、"
    r"`Numq_one`、`prompt_numerators` |",
    r"| `A207123/Parity.lean` | T1.9 | `parP k`、`parQ k`（p=(E+O)/2、q=(E−O)/2）；`T1_9`（汇总）：`a_eq_parity`、"
    r"`existsUnique_parity`、`natDegree_parP`、`leadingCoeff_parP`、`natDegree_parQ`、`leadingCoeff_parQ`（k≥1）、"
    r"`gf_aSer`、`parDen_dvd_of_mul_aSer`（最简分母恰为 (1−x)^{2k+1}(1+x)^{2k−1}）、`parity_min_order`"
    r"（最小递推阶恰为 4k）；k=0 的反例 `parity_min_order_zero` |",
    r"| `A207123/Gosper.lean` | T2.7 第一句 | `IsHyperTerm`（ℚ(x) 上的超几何项：对充分大的 m 满足 q(m)T(m+1)=p(m)T(m)，"
    r"q≠0）；`no_gosper_solution`（Gosper 方程没有有理解：约成最简分式后分母只能是常数，再比较次数）；"
    r"`partialSum_P_not_hypergeometric` |",
    r"| `A207123/SmallK.lean` | T2.8(1)、T5.4(3)(4)(5) 的公式部分 | `N_explicit`（N 的三层和，k≥1）；`gf_R`、"
    r"`gf_R_shift`、`gf_R_prompt_wrong`；`U_three`、`U_three_choose`、`U_three_eq_A084990`（`A084990` 照 OEIS 条目"
    r"的定义 a(n)=n(n²+3n−1)/3）；`U_four`、`U_four_choose` |",
    r"| `A207123/DFiniteN.lean` | T3.5(1)、T3.7(3) 前半 | `NKser`（𝒩∈K[[x]][[y]]）、`tFrac`（t/(1−t)）；代换用 Mathlib 的 "
    r"`PowerSeries.subst`：`subst_NKser`、`one_add_X_mul_FK_eq_subst`；`no_x_ODE_NK`（代换把 𝒩 的 x-ODE 变成 F 的"
    r"非齐次 x-ODE）、`not_isDFinite_NKser`（任何系数域 K⊆C）、`not_isDFinite_NK` |",
    r"| `A207123/NPDE.lean` | T3.5(2) | `NK_pde`：逐系数比较，k≥3、q≥1 时就是 `N_tri`，其余是 4 个边界修正项 |",
    r"| `A207123/HGen.lean` | T3.6 | 𝓗 写成 Q[[t]][[z]]；`HH_eq_F`（x↦z(1−t) 用 Mathlib 的 `PowerSeries.rescale`）、"
    r"`HH_eq_N`、`HH_pde` |",
    r"| `A207123/NoKOnlyN.lean` | T3.7(3) 后半 | `no_k_only_recurrence_N`：沿用 `OreRelN.lean` 的二项式变换搬运，把 N 的"
    r" k-only 关系变成 U 的 k-only 关系，再用 T3.7(2)，不用极点论证 |",
    r"| `A207123/OreDim.lean` | T3.8 维数公式 | 盒子空间 `boxSp`（正规形单项 k^i m^j X^a E^{−b} 张成）与「在某个象限上零化」"
    r"的子空间之交；`mem_relBoxU_iff`、`mem_relBoxN_iff`（它就是盒子与 Rel(U)、Rel(N) 之交）；`relU_box_tot_iff`、"
    r"`relN_box_tot_iff`（盒子里的关系恰为 Q·L1、Q·L_N，Q 在小盒子里）；`finrank_relU_tot`、`finrank_relU_gr`、"
    r"`finrank_relN_tot`、`finrank_relN_gr` |",
]
ROWS_AGENT = [
    r"| `A207123/NumStruct.lean` | T4.3(1)–(5)（(4)(5) 部分） | `Nser_three_term`（F_q 的递推，含边界项 [q=2]x²）与反例 "
    r"`Nser_three_term_needs_boundary`；`Numq_three_term`、`Numq_three_term_boundary`、`leadingCoeff_Numq_rec`；容斥闭式 "
    r"`Num_eq_IE_closed_form`；正项全历史递推 `Numq_full_history`（反例 `full_history_at_two`）、`Numq_hasNonnegCoeffs`、"
    r"`Numq_coeff_gap`、`Numq_coeff_pos_iff`（支撑）；`Numq_eval_one_rec`、`Numq_eval_one_init`；`Numq_coeff_q_add`、"
    r"`Numq_coeff_q_add_one`、`Numq_coeff_q_add_two` 与 j≤2 的门槛；`N_six_four`（N(6,4)=65，写法见其说明：不能让内核"
    r"去核对含具体数字的 `N a b` 之间的定义相等） |",
    r"| `A207123/NearDiag.lean` | T4.1、T4.2(3)、T5.2（部分） | `ndPoly d`（p_d，Newton 形式）；`T4_1_a`、`T4_1`、"
    r"`T4_1_threshold`、`ndPoly_zero_one`；`T4_2_3`（基点 2d+2 的 Newton 系数为正整数，末项 2(2d−1)!!）；"
    r"`T5_2_formula`、`T5_2_top`、`T5_2_sub`、`T5_2_sub_three` |",
]  # 待补：HStruct 及后续模块

OLD_ANCHOR = r"| `Axioms.lean` | — | "
s09 = open(P + '09_code.md', encoding='utf-8').read()
assert s09.count(OLD_ANCHOR) == 1
i0 = s09.index(OLD_ANCHOR)
i1 = s09.index('\n', i0)
OLD_AXROW = s09[i0:i1]
if DRY:
    NPRINT, NDECL, fewer = 0, 0, [('A207123.rowRule_iff_allowed', ['Quot.sound', 'propext'])]
parts = []
for name, axs in fewer:
    short = name.replace('A207123.', '')
    parts.append(f"`{short}` " + ("只用到 " + '、'.join(axs) if axs else "不依赖任何公理"))
FEWER = ('（其中 ' + '；'.join(parts) + '）') if parts else ''
NEW_AXROW = (f"| `Axioms.lean` | — | 对 {NPRINT} 条定理（报告各条标签与上表中列出的定理）`#print axioms`：全部只依赖 "
             f"propext、Classical.choice、Quot.sound{FEWER}；另对 A207123 各模块的全部 {NDECL} 个声明"
             f"（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个 |")
NEW_TABLE_ROWS = '\n'.join(ROWS + ROWS_AGENT) + '\n' + NEW_AXROW
OLD_RUN = (r"| `run_lean_checks.sh` | — | 依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`，"
           r"输出写入 `logs/lean_build.log` |")
NEW_RUN = (r"| `run_lean_checks.sh` | — | 按依赖顺序逐个模块 `lake build`（顺序由 `topo_order.py` 给出），再整体 `lake build` "
           r"一次，然后依次运行 `lake env lean Axioms.lean`、`lake env lean Checks.lean`；每一步都经 `lean_one.sh` 串行执行"
           r"（先拿锁，再等机器上没有其他 lean.exe），输出写入 `logs/lean_build.log` |" "\n"
           r"| `lean_one.sh`、`topo_order.py` | — | 串行锁（同一时间只运行一个 Lean 进程；退出码 127 且没有输出说明进程被杀）"
           r"与模块拓扑排序 |")
OLD_RERUN = r"重跑：在 `lean/` 下运行 `./run_lean_checks.sh`，或依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`（"
NEW_RERUN = (r"重跑：在 `lean/` 下运行 `./run_lean_checks.sh`。本机（16 GB 内存）上单个 Lean 进程峰值超过 7.5 GB，"
             r"两个同时运行会被系统杀掉，所以不要直接整体 `lake build`（它会并行编译多个模块），也不要同时开两个编译；"
             r"内存充足的机器可以直接依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`（")
patch(P + '09_code.md', [(OLD_AXROW, NEW_TABLE_ROWS), (OLD_RUN, NEW_RUN), (OLD_RERUN, NEW_RERUN)])

# ====================================================================================================
# 三、待补（Agent 完成后）：T4.1、T4.2(3)、T4.3、T5.2、T5.3 的标签；00_head；① 第 11 条；⑥ 与完成度表
# ====================================================================================================

# ====================================================================================================
# 四、一致性检查：标签与表中引用的 Lean 名字要么在 Axioms.lean 的 #print axioms 里，要么是定义 / Mathlib 名字
# ====================================================================================================
NOT_THEOREMS = {
    # 定义（def / 记号），不是定理
    'upoly', 'Uext', 'uext', 'rho', 'ci', 'Theta', 'ciZ', 'hpoly', 'Numq', 'parP', 'parQ', 'IsHyperTerm',
    'A084990', 'NKser', 'tFrac', 'boxSp', 'IsDFinite',
    # Mathlib
    'Ring.choose', 'Ring.inverse', 'PowerSeries.subst', 'PowerSeries.rescale',
}
cited = set()
for _, new in C1 + C2 + C3 + C4 + C5:
    cited |= set(re.findall(r'`([A-Za-z][A-Za-z0-9_.\']*)`', new))
for row in ROWS + ROWS_AGENT:
    cited |= set(re.findall(r'`([A-Za-z][A-Za-z0-9_.\']*)`', row.split('|')[3]))
axiom_names = set(n.replace('A207123.', '') for n in
                  re.findall(r'^#print axioms (\S+)', open(ROOT + r'\lean\Axioms.lean', encoding='utf-8').read(),
                             flags=re.M))
missing = sorted(n for n in (c.replace('A207123.', '') for c in cited)
                 if n not in axiom_names and n not in NOT_THEOREMS and not n.endswith('.lean'))
assert not missing, ('cited but not in Axioms.lean:', missing)
print('cited names all in Axioms.lean or whitelisted:', len(cited))
print('done (part 1)')
