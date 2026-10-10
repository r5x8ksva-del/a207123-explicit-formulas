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
-- T3.1 的 Kummer 形式与下不完全 Gamma 形式、T3.3(1) 的整表 ₁F₁ 和式（Kummer.lean）
#print axioms A207123.sum_choose_div_sub
#print axioms A207123.kummer_1F1
#print axioms A207123.remark_kummer
#print axioms A207123.sum_inv_P_eq_lowerGamma
#print axioms A207123.remark_lowerGamma
#print axioms A207123.W_div_P_eq_sum
#print axioms A207123.coeff_hyp1F1_shift
#print axioms A207123.T3_3_one_coeff
#print axioms A207123.T3_3_one
#print axioms A207123.remark_T3_3_one
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
-- 论文 §8.1 交错的工具（Interlace.lean）
#print axioms A207123.interlaces_mul_iff
#print axioms A207123.sign_eval
#print axioms A207123.alt_points
#print axioms A207123.interlaces_coneSum
#print axioms A207123.interlaces_uconeSum
#print axioms A207123.cone_of_interlaces
#print axioms A207123.ucone_of_interlaces
#print axioms A207123.Interlaces.add_left
#print axioms A207123.Interlaces.add_right
#print axioms A207123.interlaces_derivative
#print axioms A207123.interlaces_X_sub_C_mul
#print axioms A207123.Interlaces.X_mul
-- 论文引理 8.8、8.9 与命题 8.10：行多项式只有实根（RealRoots.lean）
#print axioms A207123.opDz_interlaces
#print axioms A207123.lemma_il_T_one
#print axioms A207123.Interlaces.opDz
#print axioms A207123.Interlaces.opTz
#print axioms A207123.Interlaces.opPsiz
#print axioms A207123.interlaces_one_add_X_mul_opTz
#print axioms A207123.opTz_one_add_X_mul
#print axioms A207123.nR_rec
#print axioms A207123.alpha_two
#print axioms A207123.beta_two
#print axioms A207123.prop_four_relations
#print axioms A207123.realRooted_nR
#print axioms A207123.nrowPoly_root_im_eq_zero
-- 论文命题 8.11 与定理 8.1：n_k 除 −1 外只有单根；h_k 的根都是实数且互不相同（SimpleRoots.lean）
#print axioms A207123.N_one_right
#print axioms A207123.nR_eval_zero
#print axioms A207123.Interlaces.eval_mul_derivative_nonneg
#print axioms A207123.count_roots_of_derivative
#print axioms A207123.alpha_rel
#print axioms A207123.beta_rel
#print axioms A207123.nR_no_common_root
#print axioms A207123.count_roots_nR_le_one
#print axioms A207123.rootMultiplicity_nrowPoly_le_one
#print axioms A207123.nR_eval_hR
#print axioms A207123.count_neg_one_nR
#print axioms A207123.card_roots_nR_ne
#print axioms A207123.hR_realRooted_nodup
#print axioms A207123.hpoly_root_im_eq_zero
#print axioms A207123.separable_hpoly
#print axioms A207123.thm_realroots
-- 论文推论 8.2：N 的每一行为正、严格对数凹、单峰（LogConcave.lean）
#print axioms A207123.prod_X_add_C_coeff_props
#print axioms A207123.root_neg_nR
#print axioms A207123.nR_eq_prod
#print axioms A207123.coeff_nR_eq_rowProd
#print axioms A207123.rowProd_props
#print axioms A207123.unimodal_of_pos_logconcave
#print axioms A207123.cor_logconcave
-- 论文引理 8.12 中 λ_k 的符号与推论 8.13：h_k 的根的位置与系数的变号次数（RootLocation.lean）
#print axioms A207123.nrowPoly_eq_mul_mPoly
#print axioms A207123.mPoly_eval_neg_one
#print axioms A207123.div_three_identities
#print axioms A207123.lemma_minusone_sign_alt
#print axioms A207123.lemma_minusone_sign
#print axioms A207123.lemma_minusone
#print axioms A207123.nAbove_nR_parity
#print axioms A207123.nBelow_add_count_add_nAbove
#print axioms A207123.Interlaces.nBelow_le
#print axioms A207123.nBelow_nR_parity
#print axioms A207123.nBelow_nR
#print axioms A207123.hR_roots_toFinset
#print axioms A207123.card_roots_hR_gt_one
#print axioms A207123.card_roots_hR_neg
#print axioms A207123.signVariations_add_comp_neg_X_le
#print axioms A207123.signVariations_map_rat
#print axioms A207123.signVariations_hR
#print axioms A207123.signVariations_hpoly
#print axioms A207123.cor_hk_signs
-- 论文引理 8.7(3)：g ≪ f、deg g ≥ 1 推出 g′ ≪ f′（InterlaceDeriv.lean）
#print axioms A207123.Interlaces.of_C_mul
#print axioms A207123.inCone_derivative_of_eq_mul
#print axioms A207123.interlaces_derivative_of_interlaces_pos
#print axioms A207123.interlaces_derivative_of_interlaces
-- 论文引理 8.5：交错关系与上半平面上虚部的符号（Pick 判据）（Pick.lean）
#print axioms A207123.aeval_ne_zero_of_im_pos
#print axioms A207123.im_div_coneSum_nonpos
#print axioms A207123.im_div_uconeSum_nonneg
#print axioms A207123.exists_im_pos_of_local
#print axioms A207123.exists_omega_of_two_le
#print axioms A207123.isRoot_of_im_nonpos
#print axioms A207123.weight_nonneg_of_im_nonpos
#print axioms A207123.cone_of_im_nonpos
#print axioms A207123.ucone_of_im_nonneg
#print axioms A207123.lemma_il_pick_one
#print axioms A207123.lemma_il_pick_two
#print axioms A207123.realRooted_of_im_nonpos
#print axioms A207123.realRooted_of_im_nonneg
-- 论文推论 8.14：不同取值个数的中心极限定理（CLT.lean）
#print axioms A207123.sum_cltWords
#print axioms A207123.isProbabilityMeasure_cltLaw
#print axioms A207123.card_cltWords_eq
#print axioms A207123.linProd_moments
#print axioms A207123.cltMean_eq
#print axioms A207123.cltVar_eq
#print axioms A207123.cltVar_eq_sum
#print axioms A207123.cltVar_ge
#print axioms A207123.tendsto_cltVar
#print axioms A207123.charFun_cltLaw
#print axioms A207123.charFun_cltLaw_eq_prod
#print axioms A207123.norm_multiset_prod_sub_prod_le
#print axioms A207123.exp_I_taylor_bound
#print axioms A207123.bernoulli_factor_bound
#print axioms A207123.factor_eq
#print axioms A207123.charFun_cltLaw_bound
#print axioms A207123.tendsto_charFun_cltLaw
#print axioms A207123.cor_clt
-- 论文注记 8.16：链多项式与序复形（Chains.lean）
#print axioms A207123.surjective_iff_colMat
#print axioms A207123.numChainsBar_eq_card_heights
#print axioms A207123.card_legalF_surjective
#print axioms A207123.numChainsBar_eq_N
#print axioms A207123.N_eq_numChainsBar
#print axioms A207123.numChainsBar_eq_zero
#print axioms A207123.numChainsBar_pos
#print axioms A207123.nR_eq_chainPoly
#print axioms A207123.hpoly_eq_hPoly_orderComplex
#print axioms A207123.eval_pos_of_coeff_nonneg
#print axioms A207123.no_root_lt_neg_one
#print axioms A207123.hpoly_exists_coeff_neg
-- 论文定理 6.1：U_k(m) 没有 (2,1) 形状的单族和（SingleSum.lean）
#print axioms A207123.substU_coords_unique
#print axioms A207123.coe_eq_coords
#print axioms A207123.eval_eq_coords
#print axioms A207123.coe_Ppoly_uS
#print axioms A207123.eval_Wpoly_root
#print axioms A207123.cubic_roots
#print axioms A207123.powsum_rat
#print axioms A207123.not_rat_cube_81
#print axioms A207123.no_common_value
#print axioms A207123.binomZ_sub_two_mul
#print axioms A207123.coeff_uS_pow_mul_mk_one
#print axioms A207123.coeff_substU_mk_mul_mk_one
#print axioms A207123.thm_S
-- 论文定理 6.2：以上升结尾的部分也没有 (2,1) 形状的单族和（SingleSumAsc.lean）
#print axioms A207123.eval_eq_coords_at
#print axioms A207123.single_sum_cross
#print axioms A207123.NUp_add_NA
#print axioms A207123.P_mul_GUp
#print axioms A207123.Dpoly_eval_half
#print axioms A207123.eval_Wpoly_sub_one_root
#print axioms A207123.cubic_roots_half
#print axioms A207123.powsum_rat_half
#print axioms A207123.not_rat_cube_17
#print axioms A207123.no_common_value_b2
#print axioms A207123.thm_Spart
-- 论文定理 6.3 的第 1–3 步：一般形状的母函数、坐标与纤维（ShapeFibre.lean）
#print axioms A207123.vanish_substV
#print axioms A207123.vanish_mul_Xw_pow
#print axioms A207123.subst_coords_unique_gen
#print axioms A207123.qV_monic
#print axioms A207123.aeval_eq_coordsV
#print axioms A207123.eval_eq_coordsV
#print axioms A207123.cross_of_eq
#print axioms A207123.coeff_mk_one_pow_mul_substV
#print axioms A207123.binomZ_shape
#print axioms A207123.shape_gf
#print axioms A207123.U_pos
#print axioms A207123.shape_main_identity
#print axioms A207123.shape_fibre_x
#print axioms A207123.aeval_homogY
#print axioms A207123.eval_homogY
#print axioms A207123.shape_fibre_y
-- 论文定理 6.3：单族二项式形状的分类（ShapeNT.lean、ShapeCases.lean）
#print axioms A207123.irreducible_fQ
#print axioms A207123.minpoly_root_b1
#print axioms A207123.eq_zero_of_aeval_root_b1
#print axioms A207123.quad_rel_root_b1
#print axioms A207123.aeval_root_b1_eq_zero
#print axioms A207123.exists_real_root_b1
#print axioms A207123.complex_root_b1
#print axioms A207123.real_root_pow_not_rat
#print axioms A207123.exists_b_root_of_Ppoly
#print axioms A207123.not_shape_a
#print axioms A207123.not_shape_b
#print axioms A207123.not_shape_c
#print axioms A207123.not_shape_d
#print axioms A207123.not_shape_21
#print axioms A207123.shape_10
#print axioms A207123.shape_01
#print axioms A207123.thm_shapes
-- 论文第 6.1 节其余的断言：m = 0、不以上升结尾的部分、m = 1 的 U^↑、注记 6.4 的第一句（ShapeRemarks.lean）
#print axioms A207123.binomZ_natCast
#print axioms A207123.NA_eq_sum
#print axioms A207123.NA_single_sum
#print axioms A207123.NA_excluded_form
#print axioms A207123.U_zero_single_sum
#print axioms A207123.NUp_explicit
#print axioms A207123.NUp_one_single_sum
#print axioms A207123.NUp_one_excluded_form
#print axioms A207123.shapeRepZ_natCast
#print axioms A207123.sum_triA
#print axioms A207123.shape_neg
#print axioms A207123.shape_sum_one
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
-- T5.4(2)：Barker 在 A207118、A207069 的 g.f. 与闭式猜想（Barker.lean）
#print axioms A207123.coeff_ofList_of_le
#print axioms A207123.coeff_ofList_getD
#print axioms A207123.gf_of_rec
#print axioms A207123.U_three_rat
#print axioms A207123.barker_A207118_even
#print axioms A207123.barker_A207118_odd
#print axioms A207123.a_three_eq
#print axioms A207123.barker_A207118_gf
#print axioms A207123.barker_A207069_gf
-- T5.4(2)(4)：OEIS A326247（按条目定义）、U_4(m) = A326247(m+2) 与 Barker 的三条猜想（A326247.lean）
#print axioms A207123.A326247_small
#print axioms A207123.sum_range_choose_eq
#print axioms A207123.inc2_eq
#print axioms A207123.inc3_eq
#print axioms A207123.inc4_eq
#print axioms A207123.card_edgePairs
#print axioms A207123.edge_split
#print axioms A207123.A326247_add
#print axioms A207123.A326247_eq_U_four
#print axioms A207123.barker_A326247_formula
#print axioms A207123.barker_A326247_rec
#print axioms A207123.barker_A326247_gf
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
-- T4.3(5) 一般 j 的低次系数：2j 次多项式、首项与门槛（NumLow.lean）
#print axioms A207123.piSeq_succ
#print axioms A207123.piSeq_poly
#print axioms A207123.piPoly_eval
#print axioms A207123.piPoly_zero
#print axioms A207123.numLowPoly_spec
#print axioms A207123.numLowPoly_natDegree
#print axioms A207123.numLowPoly_threshold
#print axioms A207123.T4_3_five
#print axioms A207123.T4_3_five_threshold
#print axioms A207123.numLowPoly_one
#print axioms A207123.numLowPoly_two
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
-- T5.2 的其余部分：B_d(k) 的多项式性与门槛、[m^{k−2}]、[m^{k−3}]、m → ∞ 的形状（MCoeff.lean）
#print axioms A207123.exists_poly_of_fwdDiff_iter
#print axioms A207123.fwdDiff_iter_poly_eq_zero
#print axioms A207123.ndEsym_poly
#print axioms A207123.descPochhammer_dvd_of_eval
#print axioms A207123.esQ_eval
#print axioms A207123.esQ_natDegree_le
#print axioms A207123.B_eq_bPoly
#print axioms A207123.bPoly_natDegree
#print axioms A207123.B_threshold
#print axioms A207123.B_threshold_exact
#print axioms A207123.ndEsym_one
#print axioms A207123.ndEsym_two
#print axioms A207123.ndEsym_three
#print axioms A207123.N_eight_five
#print axioms A207123.N_sub_three
#print axioms A207123.N_table
#print axioms A207123.N_ten_six_twelve_seven
#print axioms A207123.N_sub_four
#print axioms A207123.N_sub_five
#print axioms A207123.ndPoly_two
#print axioms A207123.ndPoly_three
#print axioms A207123.table_exc
#print axioms A207123.T5_2_coeff_two
#print axioms A207123.T5_2_coeff_three
#print axioms A207123.upoly_sub_shape_natDegree
#print axioms A207123.T5_2_asymp
#print axioms A207123.upoly_top_three
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
-- T5.3(4) 的 Möbius 解释：Philip Hall 定理与 Λ_k 的 Möbius 函数（Mobius.lean）
#print axioms A207123.chainsIn_zero
#print axioms A207123.chainsIn_eq_zero
#print axioms A207123.chainsIn_succ
#print axioms A207123.mu_eq_sum_chains
#print axioms A207123.chainsIn_lam
#print axioms A207123.lamBot_lt_lamTop
#print axioms A207123.mobius_lam
#print axioms A207123.mobius_lam_eq_upoly
#print axioms A207123.mobius_lam_eq_zero
#print axioms A207123.mobius_lam_small
-- T5.3(2)(a)(b)(c)：负整数零点的同余、显式根界与顶端两层（NegZeros.lean）
#print axioms A207123.upoly_eval_int
#print axioms A207123.uInt_add_prime_pow
#print axioms A207123.uInt_neg_modEq_one
#print axioms A207123.upoly_eval_neg_ne_zero_of_prime_pow
#print axioms A207123.dvd_lcm_of_upoly_eval_neg_eq_zero
#print axioms A207123.N_ratio_ge
#print axioms A207123.alt_sum_pos
#print axioms A207123.upoly_eval_neg_sign
#print axioms A207123.coeff_gnegPoly_top_three
#print axioms A207123.coeff_gnegPoly_top_four
#print axioms A207123.coeff_gnegPoly_top_five
#print axioms A207123.factorial_lt_stirlingFirst_two
#print axioms A207123.upoly_eval_neg_ne_zero_two
-- T5.3(2)(a) 中 p = 2 的放宽：2^e ≥ k − 1（k ≥ 4）即可（NegZerosTwo.lean）
#print axioms A207123.N_even_top
#print axioms A207123.uInt_add_two_pow
#print axioms A207123.uInt_add_mul_two_pow
#print axioms A207123.uInt_neg_modEq_one_two
#print axioms A207123.upoly_eval_neg_ne_zero_of_two_pow
#print axioms A207123.two_pow_factorization_lt_of_upoly_eval_neg_eq_zero
-- T5.3(7)（A29 (ii)）：h_k 次高项的闭式与它和首项的符号关系（HSecond.lean）
#print axioms A207123.upoly_eval_neg_second
#print axioms A207123.hpoly_coeff_second
#print axioms A207123.hpoly_second_three_mul
#print axioms A207123.hpoly_second_three_mul_add_one
#print axioms A207123.hpoly_second_three_mul_add_two
#print axioms A207123.hB2_pos
#print axioms A207123.hB1_table
#print axioms A207123.hB1_fiftyfive
#print axioms A207123.hE_pos
#print axioms A207123.hB1_neg
#print axioms A207123.hB1_pos
#print axioms A207123.hpoly_second_sign
-- T5.3(7)（A29 (iii) 的前两句）：h_k(−1) 的公式与符号（HNegOne.lean）
#print axioms A207123.hpoly_eval_neg_one
#print axioms A207123.hpoly_eval_neg_one_nrow
#print axioms A207123.hpoly_two_eval_neg_one
#print axioms A207123.prod_mul_add_one_sign
#print axioms A207123.hpoly_eval_neg_one_sign
-- T4.3(8) 证明中引用的 Laguerre 零点定理（α 为自然数）：首一 Laguerre 多项式只有实根（Laguerre.lean）
#print axioms A207123.lagM_monic_natDegree
#print axioms A207123.lagM_interlaces
#print axioms A207123.realRooted_lagM
#print axioms A207123.lagM_aeval_ne_zero
#print axioms A207123.coeff_lagS
#print axioms A207123.lagS_key
#print axioms A207123.lagS_rec
#print axioms A207123.lagS_aeval
#print axioms A207123.lagS_aeval_ne_zero
#print axioms A207123.lagS_aeval_ofReal_ne_zero
-- T4.3(8)：对一切 q，gcd(Num_q, P_{q−1}) = 1，最简分母恰为 P_{q−1}（NumGcd.lean）
#print axioms A207123.numS_eq_comp
#print axioms A207123.bpoly_eq_add
#print axioms A207123.prod_Ico_sub_eq
#print axioms A207123.term_modEq
#print axioms A207123.Numq_modEq
#print axioms A207123.numS_aeval_ne_zero
#print axioms A207123.Numq_isCoprime_Ppoly
#print axioms A207123.Nser_denom_dvd
-- T5.4(3)：R_k = A038718(k+2)（A038718 按 OEIS 条目的置换定义）与允许行到 Hamilton 路的显式双射（A038718.lean）
#print axioms A207123.IsHam.mem
#print axioms A207123.mem_hamSet
#print axioms A207123.isHam_hamA
#print axioms A207123.isHam_hamB
#print axioms A207123.isHam_zz
#print axioms A207123.ham_end_one
#print axioms A207123.ham_cases
#print axioms A207123.card_hamSet_add_four
#print axioms A207123.A038718_eq_card_hamSet
#print axioms A207123.A038718_add_four
#print axioms A207123.A038718_rec
#print axioms A207123.A038718_one
#print axioms A207123.A038718_two
#print axioms A207123.A038718_three
#print axioms A207123.A038718_four
#print axioms A207123.U_one_eq_A038718
#print axioms A207123.isHam_rowPath
#print axioms A207123.rowPath_surj
#print axioms A207123.rowPath_bijOn

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
