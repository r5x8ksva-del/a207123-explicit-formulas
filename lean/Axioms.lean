import A207123

/-! 打印主要定理所依赖的公理：只应出现 Lean 的标准公理（propext、Classical.choice、Quot.sound），不应出现 sorryAx。 -/

-- T1.1 引理 1（Basic.lean）
#print axioms A207123.lemma1
#print axioms A207123.lemma1_one
#print axioms A207123.lemma1_two
#print axioms A207123.U_zero_left
#print axioms A207123.U_zero_right
#print axioms A207123.legal_iff_getElem
#print axioms A207123.L_split
#print axioms A207123.L_split_disjoint
-- T1.0(a)(b) 原题归约（Reduction.lean）
#print axioms A207123.a_eq
-- T1.0(c) 多重链（Multichain.lean）
#print axioms A207123.U_eq_multichains
#print axioms A207123.card_Lam
#print axioms A207123.card_antitone_rows
#print axioms A207123.rowRule_iff_allowed
-- T1.3(1)(2) 母函数、互素、最小递推阶（Recurrence.lean）
#print axioms A207123.G_zero
#print axioms A207123.G_rec
#print axioms A207123.P_mul_G
#print axioms A207123.X_mul_W
#print axioms A207123.isCoprime_W_P
#print axioms A207123.natDegree_P
#print axioms A207123.coeff_zero_P
#print axioms A207123.P_recurrence
#print axioms A207123.order_lower_bound
#print axioms A207123.min_order
#print axioms A207123.P_dvd_of_mul_G_poly
-- T1.4 二项式基与 N 的三角递推（Binomial.lean）
#print axioms A207123.mem_NW
#print axioms A207123.U_eq_sum_N
#print axioms A207123.N_inv
#print axioms A207123.N_inv_zero
#print axioms A207123.N_eq_zero_of_lt
#print axioms A207123.N_succ_zero
#print axioms A207123.N_tri
#print axioms A207123.N_init
#print axioms A207123.N_tri_fails_at_two
#print axioms A207123.N_tri_one
#print axioms A207123.N_tri_two
#print axioms A207123.N_diag
#print axioms A207123.N_subdiag
#print axioms A207123.N_three_two
-- T2.4 主公式（Formula.lean）
#print axioms A207123.U_eq_F
#print axioms A207123.hc_vars_zero
#print axioms A207123.U_explicit
-- T2.2 按上升数细化的引理 1、T2.4 第二式（Ascent.lean）
#print axioms A207123.asc_eq_card
#print axioms A207123.sum_Us
#print axioms A207123.Us_zero_left
#print axioms A207123.Us_zero_right
#print axioms A207123.lemma1_asc_one
#print axioms A207123.lemma1_asc_two
#print axioms A207123.lemma1_asc
#print axioms A207123.lemma1_asc_s0
#print axioms A207123.Us_eq_Fs
#print axioms A207123.Us_explicit
-- 论文定理 4.4 与引理 4.5（按 y 细化）：二元母函数 G_m(x,y)（GenFunXY.lean）
#print axioms A207123.Gxy_zero
#print axioms A207123.Gxy_rec
#print axioms A207123.Gxy_prod
#print axioms A207123.coef_formula_xy
-- 论文定理 4.2（唯一分解）与例 4.3 之后一段的上升数（Blocks.lean）
#print axioms A207123.blocks_bijOn
#print axioms A207123.asc_concatBlk
-- T3.7(1) 的 ODE 部分、T3.7(2)（NonDFinite.lean）
#print axioms A207123.no_x_ODE
#print axioms A207123.no_x_ODE_poly
#print axioms A207123.no_k_only_recurrence
-- T3.7(1) 最后一步：D-finite 的定义、引理 D1、F 不是 D-finite（DFinite.lean）
#print axioms A207123.not_isDFinite_FK
#print axioms A207123.not_isDFinite_F
#print axioms A207123.not_isDFinite_Fxt
#print axioms A207123.exists_x_ODE_of_isDFinite
#print axioms A207123.exists_t_ODE_of_isDFinite
#print axioms A207123.mem_ratFn_iff
#print axioms A207123.isFractionRing_ratFn
#print axioms A207123.dXK_dTK_comm
#print axioms A207123.isDFinite_one
-- 论文注记 5.2：不以上升结尾的序列与 ₁F₁（EndAscent.lean）
#print axioms A207123.P_mul_NAser
#print axioms A207123.sum_inv_P_eq_hyp1F1
#print axioms A207123.remark_1F1
-- T3.8 中 U 的部分：Rel(U) = O_U·L1，O_U 的正规形（OreRel.lean）
#print axioms A207123.RelU_eq
#print axioms A207123.RelU_iff_mem_span
-- 论文推论 5.5：有理系数的零化算子，分母乘掉的形式（Saturated.lean）
#print axioms A207123.mul_mem_ideal_of_vanish
#print axioms A207123.mem_ideal_of_mul_mem_ideal
-- 论文推论 5.5：有理函数系数的原样陈述，𝒪(k,m)·L1 用正规形与式 (4)描述，取公分母化到上面两条（SaturatedRat.lean）
#print axioms A207123.TUrat_algebraMap
#print axioms A207123.exists_common_den
#print axioms A207123.saturated_one_rat
#print axioms A207123.saturated_two_rat
#print axioms A207123.pure_ann_zero
#print axioms A207123.col_zero
#print axioms A207123.red_of_mem
#print axioms A207123.L1_U
#print axioms A207123.exists_normal_form
#print axioms A207123.normal_form_unique
#print axioms A207123.opX_mul_mulOp
#print axioms A207123.opEinv_mul_mulOp
-- T3.8 中 N 的部分：Rel(N) = O_N·L_N 与饱和引理（OreRelN.lean）
#print axioms A207123.RelN_eq
#print axioms A207123.RelN_iff_mem_span
#print axioms A207123.saturation_Y
#print axioms A207123.saturation_one_add_Y
#print axioms A207123.LN_N
#print axioms A207123.L1V_P
#print axioms A207123.relV
#print axioms A207123.exists_N_to_V
#print axioms A207123.exists_V_to_N
#print axioms A207123.opD_pow_P_vanish
-- T1.2 与 T1.3(3)（Poly.lean）
#print axioms A207123.T1_2
#print axioms A207123.C1_sum
#print axioms A207123.existsUnique_upoly
#print axioms A207123.natDegree_upoly
#print axioms A207123.leadingCoeff_upoly_eq
#print axioms A207123.upoly_eval_neg_one
#print axioms A207123.upoly_sub_comp
#print axioms A207123.T1_3_3
#print axioms A207123.squarefree_Ppoly
#print axioms A207123.simple_root_Ppoly
#print axioms A207123.isCoprime_bpoly
#print axioms A207123.separable_bpoly
#print axioms A207123.discr_reverse_bpoly
-- T1.6–T1.8（HNum.lean）
#print axioms A207123.FK_pde
#print axioms A207123.pde_coeff
#print axioms A207123.pde_coeff_needs_zero_convention
#print axioms A207123.pde_homogeneous
#print axioms A207123.pde_unique
#print axioms A207123.hpoly_spec
#print axioms A207123.hpoly_formula_zero
#print axioms A207123.hpoly_rec
#print axioms A207123.hrec_eq_hpoly
#print axioms A207123.hrec_bad_ne
#print axioms A207123.hpoly_three
#print axioms A207123.hpoly_four
#print axioms A207123.hpoly_five
#print axioms A207123.hpoly_six
#print axioms A207123.hpoly_eval_one_eq_two
#print axioms A207123.P_mul_Nser
#print axioms A207123.Nser_eq_sum
#print axioms A207123.natDegree_Numq
#print axioms A207123.leadingCoeff_Numq
#print axioms A207123.Numq_lowest
#print axioms A207123.Numq_one
#print axioms A207123.prompt_numerators
-- T3.7(3) 与 T3.5(1)（DFiniteN.lean、NoKOnlyN.lean）
#print axioms A207123.not_isDFinite_NKser
#print axioms A207123.not_isDFinite_NK
#print axioms A207123.no_x_ODE_NK
#print axioms A207123.subst_NKser
#print axioms A207123.one_add_X_mul_FK_eq_subst
#print axioms A207123.no_k_only_recurrence_N
-- T3.8 的维数公式（OreDim.lean）
#print axioms A207123.finrank_relU_tot
#print axioms A207123.finrank_relU_gr
#print axioms A207123.finrank_relN_tot
#print axioms A207123.finrank_relN_gr
#print axioms A207123.relU_box_tot_iff
#print axioms A207123.relN_box_tot_iff
#print axioms A207123.mem_relBoxU_iff
#print axioms A207123.mem_relBoxN_iff
#print axioms A207123.finrank_spanBox
-- T3.8 的推论：U 不是 Kauers 意义下的 Stirling-like（NotStirlingLike.lean，2026-10-07）
#print axioms A207123.TU_three_points
#print axioms A207123.relU_support_det
#print axioms A207123.relU_card_support
#print axioms A207123.not_mem_relU_of_support_subset
-- 论文推论 5.7 与注 5.8：三项算子不零化 U 的任何延拓，分母乘掉的形式（ThreeTerm.lean）
#print axioms A207123.not_annihilate_three_terms
#print axioms A207123.not_annihilate_two_terms
#print axioms A207123.not_annihilate_kauers
-- 论文推论 5.7：有理函数系数的原样陈述，取公分母化到上面三条（ThreeTermRat.lean）
#print axioms A207123.HasValueAt.unique
#print axioms A207123.not_annihilate_three_terms_rat
#print axioms A207123.not_annihilate_two_terms_rat
#print axioms A207123.not_annihilate_kauers_rat
-- T2.7 的前半：Σ_{j<m} P_j 不是 Gosper 可和的（Gosper.lean）
#print axioms A207123.partialSum_P_not_hypergeometric
#print axioms A207123.no_gosper_solution
-- T1.3(4) 的根的部分（Growth.lean）
#print axioms A207123.existsUnique_rho
#print axioms A207123.one_lt_rho
#print axioms A207123.rho_spec
#print axioms A207123.rho_strictMono
#print axioms A207123.normSq_eq_of_root
#print axioms A207123.norm_lt_rho_of_root
#print axioms A207123.rho_mul_rho_sub_one_strictMono
#print axioms A207123.normSq_lt_rho_pred_sq
#print axioms A207123.root_P_min
-- 论文定理 3.2(2)：U_k(m) 按 (y − 1)∏(y³ − y² − i) 的根展开，系数非零、唯一，α_m 与 α_j 的关系（RootExpansion.lean）
#print axioms A207123.thm_asym_two
#print axioms A207123.alpha_unique
#print axioms A207123.alpha_eq
-- 论文定理 3.2(3)：c_m = α_m(ρ_m) 的两个表达式、c_m > 0、τ_m < ρ_{m−1} 与 U_k(m) 的渐近式（RootAsymp.lean）
#print axioms A207123.thm_asym_three
#print axioms A207123.cm_zero
#print axioms A207123.U_asymp_bound
-- 论文注记 3.3 的精确部分：比值渐近与速率不能改进、c_1 闭式、ρ_m 为整数的情形、c_4、U_k(4)、1 − θ_m ~ 1/(3m)（AsympRemark.lean）
#print axioms A207123.tendsto_ratio
#print axioms A207123.kappaConst_pos
#print axioms A207123.rate_not_improvable
#print axioms A207123.cm_one
#print axioms A207123.rho_int_iff
#print axioms A207123.cm_rat_of_rho_int
#print axioms A207123.cm_four
#print axioms A207123.U_four_asymp
#print axioms A207123.tendsto_one_sub_theta
-- 论文注记 3.3 的数值：区间算术，ρ_m、c_m、κ_m 的有理区间与 U 的精确值（AsympNumerics.lean）
#print axioms A207123.lt_rho_of_cubic
#print axioms A207123.rho_lt_of_cubic
#print axioms A207123.cm_eq_frac
#print axioms A207123.cm_bounds
#print axioms A207123.cmNQ_cast
#print axioms A207123.rho_one_approx
#print axioms A207123.cm_one_approx
#print axioms A207123.cm_two_approx
#print axioms A207123.cm_three_approx
#print axioms A207123.kappa_one_approx
#print axioms A207123.kappa_four_approx
#print axioms A207123.kappa_twentyfour_approx
#print axioms A207123.kappa_increasing
#print axioms A207123.relerr_two_six
#print axioms A207123.relerr_two_twenty
#print axioms A207123.relerr_twentyfour_seventytwo
#print axioms A207123.relerr_twentyfour_twoforty
-- 论文注记 3.5 后半句：行递推阶的最小性（Hankel 行列式模 97 的证书）与不同乘积的个数（OeisRowOrders.lean）
#print axioms A207123.eq_zero_of_rec_of_eventually
#print axioms A207123.hankel_det_eq_zero
#print axioms A207123.order_ge_of_hankel
#print axioms A207123.hankel_det_ne_zero_of_kron
#print axioms A207123.card_products_le
#print axioms A207123.card_products_ge
#print axioms A207123.hankel_row_two
#print axioms A207123.hankel_row_three
#print axioms A207123.hankel_row_four
#print axioms A207123.hankel_row_five
#print axioms A207123.hankel_row_six
#print axioms A207123.hankel_row_seven
#print axioms A207123.row_min_order_two
#print axioms A207123.row_min_order_three
#print axioms A207123.row_min_order_four
#print axioms A207123.row_min_order_five
#print axioms A207123.row_min_order_six
#print axioms A207123.row_min_order_seven
#print axioms A207123.card_row_products_two
#print axioms A207123.card_row_products_three
#print axioms A207123.card_row_products_four
#print axioms A207123.card_row_products_five
#print axioms A207123.card_row_products_six
#print axioms A207123.card_row_products_seven
-- 论文引理 4.5 最后一句：H(m,s,j) 是集合划分个数（r-Stirling 数；RStirling.lean）
#print axioms A207123.card_setParts_single
#print axioms A207123.card_setParts_join
#print axioms A207123.partCount_succ_succ
#print axioms A207123.partCount_succ_succ_of_le
#print axioms A207123.hc_vars_eq_partCount
#print axioms A207123.stirlingSecond_eq_partCount
#print axioms A207123.partCount_one
#print axioms A207123.lemma_coef_partitions
-- 论文命题 4.7：双射的存在（两边计数相等；Bijection.lean）
#print axioms A207123.NAs_split
#print axioms A207123.NAs_rec
#print axioms A207123.NAs_two
#print axioms A207123.NAs_eq_g
#print axioms A207123.NAs_explicit
#print axioms A207123.prop_bijection
-- T5.4(3)(4)(5) 的代数部分与 T2.8(1) 的三层和（SmallK.lean）
#print axioms A207123.gf_R
#print axioms A207123.gf_R_shift
#print axioms A207123.gf_R_prompt_wrong
#print axioms A207123.U_three
#print axioms A207123.U_three_choose
#print axioms A207123.U_three_eq_A084990
#print axioms A207123.U_four
#print axioms A207123.U_four_choose
#print axioms A207123.N_explicit
-- T1.5 与 T2.5（Coeffs.lean）
#print axioms A207123.ci_formula
#print axioms A207123.coeff_inv_Ppoly
#print axioms A207123.factorial_mul_coeff_inv_Ppoly
#print axioms A207123.U_eq_Theta
#print axioms A207123.Theta_eq_coeff_prod
#print axioms A207123.Theta_eq_coeff_Ppoly_div
#print axioms A207123.T15_note_P
#print axioms A207123.T15_note_c
#print axioms A207123.U_F3
#print axioms A207123.U_F3_nat
#print axioms A207123.Theta_eq_H
#print axioms A207123.Theta_eq_F3_term
#print axioms A207123.Theta_vs_H_example
#print axioms A207123.U_F4
#print axioms A207123.R_formula
-- T1.9（Parity.lean）
#print axioms A207123.T1_9
#print axioms A207123.a_eq_parity
#print axioms A207123.existsUnique_parity
#print axioms A207123.natDegree_parP
#print axioms A207123.leadingCoeff_parP
#print axioms A207123.natDegree_parQ
#print axioms A207123.leadingCoeff_parQ
#print axioms A207123.gf_aSer
#print axioms A207123.parDen_dvd_of_mul_aSer
#print axioms A207123.parity_min_order
#print axioms A207123.parity_min_order_zero
-- 论文注记 3.5：A207118–A207122 的经验递推、行递推的阶与核对判据、A207069/A207070 标题的列规则（OeisRemark.lean）
#print axioms A207123.parDen_three
#print axioms A207123.parDen_four
#print axioms A207123.parDen_five
#print axioms A207123.parDen_six
#print axioms A207123.parDen_seven
#print axioms A207123.oeis_A207118
#print axioms A207123.oeis_A207119
#print axioms A207123.oeis_A207120
#print axioms A207123.oeis_A207121
#print axioms A207123.oeis_A207122
#print axioms A207123.row_rec
#print axioms A207123.row_rec_of_consecutive
#print axioms A207123.aAlt_two
#print axioms A207123.aAlt_three
-- 论文注记 3.5：行 n = 2,…,7 的经验递推对一切 k 成立（经证明的 U 求值器 + decide +kernel 核对；OeisRows.lean）
#print axioms A207123.Ucol_eq
#print axioms A207123.rowList_eq
#print axioms A207123.row_rec_of_check
#print axioms A207123.oeis_A207069
#print axioms A207123.oeis_A207070
#print axioms A207123.oeis_A207124
#print axioms A207123.oeis_A207125
#print axioms A207123.oeis_A207126
#print axioms A207123.oeis_A207127
-- T3.5(2)（NPDE.lean）
#print axioms A207123.NK_pde
-- T3.6（HGen.lean）
#print axioms A207123.HH_eq_F
#print axioms A207123.HH_eq_N
#print axioms A207123.HH_pde
-- T4.3(1)–(5)（NumStruct.lean）
#print axioms A207123.Nser_three_term
#print axioms A207123.Nser_three_term_needs_boundary
#print axioms A207123.Numq_three_term
#print axioms A207123.Numq_three_term_boundary
#print axioms A207123.Numq_three_term_fails_at_two
#print axioms A207123.leadingCoeff_Numq_rec
#print axioms A207123.Numq_deg_lead_low
#print axioms A207123.Num_eq_IE_closed_form
#print axioms A207123.P_mul_Nser_eq_IE
#print axioms A207123.Numq_full_history
#print axioms A207123.full_history_at_two
#print axioms A207123.Numq_hasNonnegCoeffs
#print axioms A207123.Numq_coeff_nonneg
#print axioms A207123.Numq_coeff_gap
#print axioms A207123.Numq_coeff_pos_iff
#print axioms A207123.Numq_coeff_ne_zero_iff
#print axioms A207123.Numq_eval_one_rec
#print axioms A207123.Numq_eval_one_init
#print axioms A207123.Numq_coeff_q_add
#print axioms A207123.Numq_coeff_q_add_one
#print axioms A207123.Numq_coeff_q_add_two
#print axioms A207123.Numq_coeff_exception_zero
#print axioms A207123.Numq_coeff_exception_one
#print axioms A207123.Numq_coeff_exception_two
#print axioms A207123.N_six_four
#print axioms A207123.N_sub_two
-- T4.1、T4.2(3)、T5.2（NearDiag.lean）
#print axioms A207123.T4_1_a
#print axioms A207123.T4_1
#print axioms A207123.T4_1_threshold
#print axioms A207123.ndPoly_zero_one
#print axioms A207123.T4_2_3
#print axioms A207123.T5_2_formula
#print axioms A207123.T5_2_top
#print axioms A207123.T5_2_sub
#print axioms A207123.T5_2_sub_three
-- T5.3(1)–(5)（HStruct.lean）
#print axioms A207123.hpoly_eval_zero_eq_one
#print axioms A207123.hpoly_eval_one_two
#print axioms A207123.hpoly_coeff_one
#print axioms A207123.hpoly_coeff_one_pos
#print axioms A207123.hpoly_coeff_one_eq_zero
#print axioms A207123.hpoly_coeff_one_gf
#print axioms A207123.hpoly_coeff_eq_sum
#print axioms A207123.iterate_derivative_hpoly_eval_one
#print axioms A207123.iterate_derivative_hpoly_eval_one_k_zero
#print axioms A207123.hpoly_derivative_eval_one
#print axioms A207123.nrowPoly_eval
#print axioms A207123.nrowPoly_eq
#print axioms A207123.Gneg_one
#print axioms A207123.Gneg_succ
#print axioms A207123.Gneg_isPoly
#print axioms A207123.coeff_gnegPoly_top
#print axioms A207123.coeff_gnegPoly_top_one
#print axioms A207123.coeff_gnegPoly_top_two
#print axioms A207123.upoly_eval_neg_eq_zero
#print axioms A207123.upoly_eval_neg_ne_zero
#print axioms A207123.prod_dvd_upoly
#print axioms A207123.upoly_three_mul_eval
#print axioms A207123.upoly_eval_neg_recip
#print axioms A207123.natDegree_hpoly
#print axioms A207123.leadingCoeff_hpoly_eq
#print axioms A207123.leadingCoeff_hpoly_three_mul
#print axioms A207123.leadingCoeff_hpoly_three_mul_add_one
#print axioms A207123.leadingCoeff_hpoly_three_mul_add_two
#print axioms A207123.leadingCoeff_hpoly_sign
#print axioms A207123.sum_neg_one_pow_N
#print axioms A207123.sum_neg_one_pow_N_eq_zero
#print axioms A207123.sum_neg_one_pow_N_small
#print axioms A207123.rootMultiplicity_nrowPoly
#print axioms A207123.rootMultiplicity_nrowPoly_ceil
#print axioms A207123.hpoly_aeval_eq_tsum
#print axioms A207123.hpoly_pos_of_mem_Icc
#print axioms A207123.hpoly_ne_zero_of_mem_Icc

/-! 全量扫描：`A207123` 各模块中的每一个声明（含辅助引理与编译器自动生成的声明）所依赖的公理，
只应是 `propext`、`Classical.choice`、`Quot.sound`。 -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  let mut seen : Std.HashSet Name := {}
  for (modName, modData) in env.header.moduleNames.zip env.header.moduleData do
    if (`A207123).isPrefixOf modName then
      for n in modData.constNames do
        count := count + 1
        let axs ← collectAxioms n
        for a in axs do
          seen := seen.insert a
          unless std.contains a do
            bad := bad.push (n, a)
  logInfo m!"A207123 各模块共 {count} 个声明；出现过的公理：{seen.toList}；依赖其他公理的声明：{bad.size} 个 {bad}"
