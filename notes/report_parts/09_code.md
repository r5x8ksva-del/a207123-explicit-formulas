## ⑤ 代码与输出

**运行方式**：在本文件夹下执行 `py -3.14 verify_all.py`（需要 numpy：rv2 调用的复核脚本没有纯 Python 回退）。它依次运行 `code/checks/check_*.py`，逐条打印 `PASS <id> <描述（含范围）>` 或 `FAIL …`，最后给出总表；任何 FAIL、子模块异常退出或缺少 SUMMARY 行都会使退出码为 1。

**12 个核对模块**（除 check_rv2.py、check_rv3.py 外，每个都从 `code/core.py` 的原始定义程序取「真值」；check_rv2.py 运行复核者 x1 的两个独立脚本，不导入 core：r1 用自写的三元组 DP 作真值，r2 只做纤维留数条件的精确代数穷举；check_rv3.py 运行复核者 r-c4ii、r-c3a、s6-t436、s6-t342 的脚本，同样不导入 core，各脚本按定义自算真值：Num_q 的递推，K、I、𝒮 的定义）

| 模块 | 内容 | 检查数 |
|---|---|---|
| `check_c0.py` | 主 Agent 补充：基线数据、W_m、推荐显式公式（H 型）、H 的显式式与递推、最小阶逐因子检验（v≤300）、c_4 的数值收敛与 c_m 闭式（数值，m≤8；c_4=215/2 的精确核对在 c5a）、U_3 单调三元组双射 | 13 |
| `check_c1.py` | C-1：归约 (a)(b)(c)、引理 1、(C1)–(C8) 全部（k≤60、m≤20，多处更远） | 45 |
| `check_c2a.py` | C-2 代数路线：r-Stirling 识别、Θ/H/F3/F4 各形式、定理 S 的代数事实与线性方程组佐证、两族范围、计时 | 23 |
| `check_c2b.py` | C-2 组合路线：块分解（全部 (m+1)^k 个序列，k≤10,m≤4）、按上升数细化、竖线模型、u 型证书、参数盒、N^c/N^E | 33 |
| `check_c3a.py` | C-3 母函数：₁F₁、Kummer、形式 Laplace（k≤60,m≤30 精确展开）、Humbert 闭式、解析版本的反例与数值、𝒩 与 𝓗 | 34 |
| `check_c3b.py` | C-3 D-finite：极点与留数事实、gcd、模素数精确线性代数（只依赖 k 的递推无解；关系空间维数 = 公式） | 22 |
| `check_c4.py` | C-4：D(k,d) 的递推、p_d（d≤12）计算机辅助证明、门槛与缺陷、模式展开、Num_q 的递推/容斥/非负性/低高次系数/e.g.f. | 41 |
| `check_c5a.py` | C-5 渐近与 h_k：谱分解、c_m、m=4/18 精确常数、m 的次首项系数、deg h_k、负整数值、Möbius、实根（k≤60 Sturm） | 37 |
| `check_c5b.py` | C-5 OEIS：离线解析 68 个快照，核对家族条目、经验递推、R_k、U_3/U_4 双射、未命中记录 | 33 |
| `check_rv.py` | 第二轮复核的产物：N 三角对照定义、两个反例的范围（d≤46 全正、47≤d≤57 失效；奇数 d≤67 为正、69≤d≤101 为负）、Num_q 同余与 Laguerre 恒等式、负整数零点严格有限验证（k≤40）、恒等式补 s=0 | 7 |
| `check_rv2.py` | 复核者 x1 的两个独立脚本（不导入 core）：E 部分在 u=1/2 的统一阻碍（m=2..34）与证书复算；U 两族 \|指数\|≤6000、E 两项 ≤1500 无表示 | 2 |
| `check_rv3.py` | 报告 ⑥ 原有两处所依赖的复核者脚本（不导入 core）：T4.3(6) 由 (7) 的闭式推出 j≤14、按第二份证明构造到 j≤40 与拟合到 j≤24（真实系数 q≤300）；T3.4(2) K 的闭式与定义（两套实现，7 个与 13 个 x）、端到端 I−𝒮（4 组与 11 组 (x,t)）、推论在 105 个 x 上的扫描 | 6 |

**最终一次运行**（本地 2026-10-07，完整输出 `logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行；2026-10-05 的上一次最终运行（11 个模块、290 条，当时本机另有会话在跑基准测试，用时 630.7 s）另存为 `logs/verify_all_final_2026-10-05.log`）：

```
area     pass   fail    rc  summary     secs  status
c0         13      0     0      yes      4.1  PASS
c1         45      0     0      yes     39.5  PASS
c2a        23      0     0      yes     12.2  PASS
c2b        33      0     0      yes     32.9  PASS
c3a        34      0     0      yes     22.4  PASS
c3b        22      0     0      yes     20.0  PASS
c4         41      0     0      yes     21.7  PASS
c5a        37      0     0      yes     14.2  PASS
c5b        33      0     0      yes      5.2  PASS
rv          7      0     0      yes     14.7  PASS
rv2         2      0     0      yes      8.3  PASS
rv3         6      0     0      yes     78.0  PASS
------------------------------------------------------------------------
TOTAL pass=296 fail=0 modules=12 failed_modules=-  (273.3s)
OVERALL: PASS
```

**Lean 形式化**（`lean/`，Lean 4.34.1 + Mathlib v4.34.1；全部从原始定义出发，没有 sorry，只依赖三条标准公理）

| 文件 | 报告编号 | 内容 |
|---|---|---|
| `A207123/Basic.lean` | T1.1 | 按高度序列定义 `U k m`（`L k m` 的成员恰是长 k、取值 ≤ m、每个相邻三元组都好的列表；`legal_iff_getElem` 给出逐下标刻画）；引理 1：`lemma1`（k≥3）、`lemma1_one`、`lemma1_two`、`U_zero_left`、`U_zero_right`；引理 1 的三类分解抽成 `L_split`（`L_split_disjoint`、`L_split_inj`），供按上升数细化复用 |
| `A207123/Reduction.lean` | T1.0(a)(b) | 原题定义：`a k n` = 满足行规则（不含 001、010）与列规则（不含 001、011）的 n×k 0/1 矩阵个数；`a_eq : a k n = U k ((n+1)/2) * U k (n/2)` |
| `A207123/Multichain.lean` | T1.0(c) | 允许行 `AllowedRow`（`rowRule_iff_allowed`：原题行规则 ⇔ 每行都是允许行）、偏序集 `Lam k`（逐分量序）；`U_eq_multichains`：U_k(m) = Λ_k 中 m 元多重链 x_1≤⋯≤x_m 的个数；`card_Lam`：R_k=\|Λ_k\|=U_k(1) |
| `A207123/Recurrence.lean` | T1.3(1)(2) | b_i、P_m、W_m（任意交换环）与 G_m；`G_rec`、`P_mul_G`（P_m·G_m=W_m）、`X_mul_W`；`isCoprime_W_P`（Q[x] 中互素：W_m≡W_i (mod b_i)，再按不可约公因子的次数用正性、Gauss 引理、有理根定理排除）、`natDegree_P`、`P_recurrence`、`order_lower_bound`、`min_order`（最小递推阶恰为 3m+1）、`P_dvd_of_mul_G_poly`（既约分母恰为 P_m） |
| `A207123/Binomial.lean` | T1.4 | 组合定义 `N k q`（`mem_NW`：长 k、合法、值域恰为 {1..q}）；`U_eq_sum_N`（二项式基：按值域分类 + 严格增映射保持合法性）、`N_inv`/`N_inv_zero`（容斥式）、`N_tri`（三角递推，k≥3）、`N_init`、`N_tri_fails_at_two`、`N_tri_one`/`N_tri_two`（初值更正与 N(−1,·)、N(−2,·) 约定）、`N_diag`、`N_subdiag` |
| `A207123/Formula.lean` | T2.4 主公式 | 推荐显式公式 `U_explicit`：第一项用 Mathlib 的第二类 Stirling 数 `Nat.stirlingSecond`，第二项的 H(m,s,j) 写成 `hc s (vars j m)`（完全齐次对称多项式 h_s 在 m,m−1,…,j 处的值）；路线是闭式 `F` 满足与引理 1 相同的递推（`U_eq_F`） |
| `A207123/Ascent.lean` | T2.2、T2.4 第二式 | 上升数 `asc`（`asc_eq_card` 逐下标刻画）、`Us k m s`（`sum_Us`：按 s 求和回到 U）；按 s 细化的引理 1：`lemma1_asc`、`lemma1_asc_s0`、`lemma1_asc_one`、`lemma1_asc_two`、`Us_zero_left`、`Us_zero_right`；`Us_explicit`（T2.4 第二式，二项式约定由守卫条件实现） |
| `A207123/NonDFinite.lean` | T3.7(1) 的 ODE 部分、T3.7(2) | `no_x_ODE`（系数取 C[x][[t]]）、`no_x_ODE_poly`（系数取 C[x,t]）、`no_k_only_recurrence`（p_ab∈C[k]）：θ=x·d/dx 或 d/dx 作用在 W/P 上的分子递推及其模 P 的最高阶系数（`Bseq_mod`、`Dseq_mod`），在 b_m 的实根 x_m∈(0,1) 处比较「最高阶极点」系数；只用正性 W_m(x_m)≥1，不依赖 T1.3(2) 的互素性 |
| `A207123/DFinite.lean` | T3.7(1) 的最后一步 | `IsDFinite K f`（Lipshitz Def. 2.1，n=2：f 的全部偏导数 ∂_x^i∂_t^j f 在 Frac(K[[x,t]]) 中张成的 K(x,t)-子空间有限维；K(x,t) 取为 K[x,t] 的像生成的子域，`mem_ratFn_iff`、`isFractionRing_ratFn` 说明它就是 K(x,t)，`dXK_dTK_comm` 说明 ∂_x^i∂_t^j 穷尽全部偏导数，`isDFinite_one` 说明定义不是恒假的）；引理 D1 `exists_x_ODE_of_isDFinite`、`exists_t_ODE_of_isDFinite`；`not_isDFinite_FK`（任何域 K 与环同态 σ:K→C）、`not_isDFinite_Fxt`（K=C） |
| `A207123/OreRel.lean` | T3.8（U） | 算子作用在 C^{N×N} 上（负下标补 0）：乘法算子 `mulOp`、位移 `opX`、`opEinv`；`OU` 是它们生成的子代数，Ore 交换律 `opX_mul_mulOp`、`opEinv_mul_mulOp`，正规形存在且唯一 `exists_normal_form`、`normal_form_unique`；约化 `red_of_mem`（E^{−1}=1−X−mX³−L1）；命题 A `pure_ann_zero`（单列情形 `col_zero`：在 b_0..b_m 各一个单根处比较最高阶极点系数，W_m 在根处非零用 T1.3(2) 的互素性）；`RelU_eq`、`RelU_iff_mem_span` |
| `A207123/OreRelN.lean` | T3.8（N） | `LN`、`RelN`（O_N 与 O_U 是同一个 Ore 代数）；二项式变换 `opP` 与交换关系 `opD_P_Y`（ΔPY=YP）、`P_mul_cM`（Pq=mΔP）、`opD_P_one_add`；搬运恒等式 `L1V_P`（L1V·P=Δ·P·L_N）；`relV`（Rel(V)=O·L1V，由 `RelU_eq` 推出）；两个方向的交换引理 `exists_N_to_V`、`exists_V_to_N` 与边界消去 `opD_pow_P_vanish`；饱和引理 `saturation_Y`、`saturation_one_add_Y`；`RelN_eq`、`RelN_iff_mem_span` |
| `A207123/Poly.lean` | T1.2、T1.3(3) | `upoly k`（u_k，取为二项式基展开 Σ_q N(k,q)·C(y+1,q)；`existsUnique_upoly` 说明任何插值多项式都等于它）；`T1_2`（汇总）：`C1_sum`（(C1)，越界下标按 T1.1 的约定 `Uext`）、`natDegree_upoly`、`leadingCoeff_upoly_eq`、`upoly_eval_neg_one`、`upoly_sub_comp`（u_{−1}=1、u_{−2}=0 由 `uext` 实现）；`T1_3_3`（汇总）：`isCoprime_bpoly`、`separable_bpoly`、`squarefree_Ppoly`、`simple_root_Ppoly`、`discr_reverse_bpoly` |
| `A207123/Growth.lean` | T1.3(4) 的根的部分 | `rho m`（m≥1 时 y³−y²−m 的唯一实根）：`existsUnique_rho`、`one_lt_rho`、`rho_spec`、`rho_strictMono`；复根 `normSq_eq_of_root`（\|w\|²=m/ρ_m）、`norm_lt_rho_of_root`；`root_P_min`（x_m=1/ρ_m 是 P_m 唯一的模最小根） |
| `A207123/Coeffs.lean` | T1.5、T2.5 | `ci i n`（c_i(n):=[x^n]1/b_i）与 `ci_formula`；`coeff_inv_Ppoly`、`factorial_mul_coeff_inv_Ppoly`；`Theta m t n`（照抄 c1.md §6.4）与 `U_eq_Theta`（k≥0）、`Theta_eq_coeff_prod`、`Theta_eq_coeff_Ppoly_div`；求和约定的两个反例 `T15_note_P`、`T15_note_c`（用 Mathlib 的广义二项式 `Ring.choose`）；F3 型 `U_F3`、`U_F3_nat`；`Theta_eq_H`、`Theta_eq_F3_term`、`Theta_vs_H_example`；`U_F4`、`R_formula`（n<0 时 c_i(n)=0 由 `ciZ` 实现） |
| `A207123/HNum.lean` | T1.6、T1.7、T1.8 | `FK_pde`（Q[[x,t]] 写成 Q[[x]][[t]]，1/(1−t)² 为 `Ring.inverse`）、逐项形式 `pde_coeff` 与 `pde_coeff_needs_zero_convention`、`pde_homogeneous`、`pde_unique`；`hpoly k`（h_0=1，k≥1 时按 N 表达式）与 `hpoly_spec`、`hpoly_formula_zero`、`hpoly_rec`、`hrec_eq_hpoly`、`hrec_bad_ne`、`hpoly_three`…`hpoly_six`、`hpoly_eval_one_eq_two`；`Numq q`（按 T4.3(2) 的容斥闭式定义）与 `P_mul_Nser`（它等于 P_{q−1}·Σ_kN(k,q)x^k）、`Nser_eq_sum`、`natDegree_Numq`、`leadingCoeff_Numq`、`Numq_lowest`、`Numq_one`、`prompt_numerators` |
| `A207123/Parity.lean` | T1.9 | `parP k`、`parQ k`（p=(E+O)/2、q=(E−O)/2）；`T1_9`（汇总）：`a_eq_parity`、`existsUnique_parity`、`natDegree_parP`、`leadingCoeff_parP`、`natDegree_parQ`、`leadingCoeff_parQ`（k≥1）、`gf_aSer`、`parDen_dvd_of_mul_aSer`（最简分母恰为 (1−x)^{2k+1}(1+x)^{2k−1}）、`parity_min_order`（最小递推阶恰为 4k）；k=0 的反例 `parity_min_order_zero` |
| `A207123/Gosper.lean` | T2.7 第一句 | `IsHyperTerm`（ℚ(x) 上的超几何项：对充分大的 m 满足 q(m)T(m+1)=p(m)T(m)，q≠0）；`no_gosper_solution`（Gosper 方程没有有理解：约成最简分式后分母只能是常数，再比较次数）；`partialSum_P_not_hypergeometric` |
| `A207123/SmallK.lean` | T2.8(1)、T5.4(3)(4)(5) 的公式部分 | `N_explicit`（N 的三层和，k≥1）；`gf_R`、`gf_R_shift`、`gf_R_prompt_wrong`；`U_three`、`U_three_choose`、`U_three_eq_A084990`（`A084990` 照 OEIS 条目的定义 a(n)=n(n²+3n−1)/3）；`U_four`、`U_four_choose` |
| `A207123/DFiniteN.lean` | T3.5(1)、T3.7(3) 前半 | `NKser`（𝒩∈K[[x]][[y]]）、`tFrac`（t/(1−t)）；代换用 Mathlib 的 `PowerSeries.subst`：`subst_NKser`、`one_add_X_mul_FK_eq_subst`；`no_x_ODE_NK`（代换把 𝒩 的 x-ODE 变成 F 的非齐次 x-ODE）、`not_isDFinite_NKser`（任何系数域 K⊆C）、`not_isDFinite_NK` |
| `A207123/NPDE.lean` | T3.5(2) | `NK_pde`：逐系数比较，k≥3、q≥1 时就是 `N_tri`，其余是 4 个边界修正项 |
| `A207123/HGen.lean` | T3.6 | 𝓗 写成 Q[[t]][[z]]；`HH_eq_F`（x↦z(1−t) 用 Mathlib 的 `PowerSeries.rescale`）、`HH_eq_N`、`HH_pde` |
| `A207123/NoKOnlyN.lean` | T3.7(3) 后半 | `no_k_only_recurrence_N`：沿用 `OreRelN.lean` 的二项式变换搬运，把 N 的 k-only 关系变成 U 的 k-only 关系，再用 T3.7(2)，不用极点论证 |
| `A207123/OreDim.lean` | T3.8 维数公式 | 盒子空间 `boxSp`（正规形单项 k^i m^j X^a E^{−b} 张成）与「在某个象限上零化」的子空间之交；`mem_relBoxU_iff`、`mem_relBoxN_iff`（它就是盒子与 Rel(U)、Rel(N) 之交）；`relU_box_tot_iff`、`relN_box_tot_iff`（盒子里的关系恰为 Q·L1、Q·L_N，Q 在小盒子里）；`finrank_relU_tot`、`finrank_relU_gr`、`finrank_relN_tot`、`finrank_relN_gr` |
| `A207123/NumStruct.lean` | T4.3(1)–(5)（(4)(5) 部分） | `Nser_three_term`（F_q 的递推，含边界项 [q=2]x²）与反例 `Nser_three_term_needs_boundary`；`Numq_three_term`、`Numq_three_term_boundary`、`leadingCoeff_Numq_rec`；容斥闭式 `Num_eq_IE_closed_form`；正项全历史递推 `Numq_full_history`（反例 `full_history_at_two`）、`Numq_hasNonnegCoeffs`、`Numq_coeff_gap`、`Numq_coeff_pos_iff`（支撑）；`Numq_eval_one_rec`、`Numq_eval_one_init`；`Numq_coeff_q_add`、`Numq_coeff_q_add_one`、`Numq_coeff_q_add_two` 与 j≤2 的门槛；`N_six_four`（N(6,4)=65，写法见其说明：不能让内核去核对含具体数字的 `N a b` 之间的定义相等） |
| `A207123/NearDiag.lean` | T4.1、T4.2(3)、T5.2（部分） | `ndPoly d`（p_d，Newton 形式）；`T4_1_a`、`T4_1`、`T4_1_threshold`、`ndPoly_zero_one`；`T4_2_3`（基点 2d+2 的 Newton 系数为正整数，末项 2(2d−1)!!）；`T5_2_formula`、`T5_2_top`、`T5_2_sub`、`T5_2_sub_three` |
| `A207123/HStruct.lean` | T5.3(1)–(5) | `nrowPoly k`（N 行多项式 n_k，k≥1）、`Gneg j`（G_{−j}）、`gnegPoly n`（G_{−(n+1)} 作为多项式）、`recipPoly k i`（互反引理中的 C(y−i+k,k)）；(1) `hpoly_eval_zero_eq_one`、`hpoly_eval_one_two`、`hpoly_coeff_one`、`hpoly_coeff_one_pos`、`hpoly_coeff_one_eq_zero`、`hpoly_coeff_one_gf`、`hpoly_coeff_eq_sum`、`iterate_derivative_hpoly_eval_one`（k≥1）与反例 `iterate_derivative_hpoly_eval_one_k_zero`、`hpoly_derivative_eval_one`、`nrowPoly_eval`、`nrowPoly_eq`；(2) `Gneg_one`、`Gneg_succ`、`Gneg_isPoly`、`coeff_gnegPoly_top`、`coeff_gnegPoly_top_one`、`coeff_gnegPoly_top_two`、`upoly_eval_neg_eq_zero`、`upoly_eval_neg_ne_zero`、`prod_dvd_upoly`、`upoly_three_mul_eval`；(3) `upoly_eval_neg_recip`、`natDegree_hpoly`、`leadingCoeff_hpoly_three_mul`、`leadingCoeff_hpoly_three_mul_add_one`、`leadingCoeff_hpoly_three_mul_add_two`、`leadingCoeff_hpoly_sign`；(4) `sum_neg_one_pow_N`、`sum_neg_one_pow_N_eq_zero`、`sum_neg_one_pow_N_small`、`rootMultiplicity_nrowPoly`、`rootMultiplicity_nrowPoly_ceil`；(5) `hpoly_aeval_eq_tsum`、`hpoly_pos_of_mem_Icc`、`hpoly_ne_zero_of_mem_Icc` |
| `Axioms.lean` | — | 对 252 条定理（报告各条标签与上表中列出的定理）`#print axioms`：全部只依赖 propext、Classical.choice、Quot.sound（其中 `rowRule_iff_allowed` 只用到 Quot.sound、propext）；另对 A207123 各模块的全部 2649 个声明（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个 |
| `Checks.lean` | — | 用 `native_decide` 把定义与数据对照：任务说明第 2 节（k=7、10 两行，R_1..R_10，a_3(1..6)）、(C3) 的 N 三角形 k=7、10 两行（经 `N_inv`、`U_eq_F` 计算）、U_6(3,s) 与 U_7(2,s)（经 `Us_explicit` 计算，对照 Python 按定义暴力枚举的数据）；这是计算核对，依赖编译器，不是证明的一部分 |
| `run_lean_checks.sh` | — | 按依赖顺序逐个模块 `lake build +A207123.X`（顺序由 `topo_order.py` 给出；任何一步失败就停止），再整体 `lake build` 一次（这时只剩根模块），然后依次运行 `lake env lean Axioms.lean`、`lake env lean Checks.lean`；每一步都经 `lean_one.sh` 串行执行（先拿锁，再等机器上没有其他 lean.exe），输出写入 `logs/lean_build.log` |
| `run_lean_checks_direct.sh` | — | 同样三步、同样的日志格式，但第 1 步按依赖顺序直接 `lake env lean A207123/X.lean -o … -i …` 从源码编译每个模块，最后编根模块（不经 lake 的构建记录核对：本机内存紧时那一步核对每次要 7–10 分钟）；lakefile 没有额外的编译选项，所以与 lake build 编译的是同一套设置。2026-10-07 的全量构建用的是它 |
| `lean_one.sh`、`lean_watchdog.ps1`、`mem_status.ps1`、`topo_order.py` | — | 串行锁与内存保护（同一时间只运行一个 Lean 进程；启动前要求系统提交余量与可用内存足够，运行中 Lean 私有内存超过上限或系统提交余量过低就结束进程树，退出码 137；2026-10-07 起，单次内存查询失败时改用备用数据源，连续 5 秒都读不到才结束，不再把查询失败误当成余量为 0）与模块拓扑排序 |

重跑：在 `lean/` 下运行 `./run_lean_checks.sh`，内存紧时改用 `./run_lean_checks_direct.sh`。本机（16 GB 内存）上单个 Lean 进程峰值超过 7.5 GB，两个同时运行会被系统杀掉，所以不要直接整体 `lake build`（它会并行编译多个模块），也不要同时开两个编译；内存充足的机器可以直接依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`（首次需要下载 Mathlib 缓存，约 5–7 GB；之后 `lake build` 每次要核对全部 Mathlib 构建记录，约 3–6 分钟，单个文件编译约 0.5–1 分钟，冷启动时加载 Mathlib 可能要十几分钟）。输出见 `logs/lean_build.log`。

**其他重要文件**

- `code/core.py`：参考实现 `U_list`（照抄第 1 节）、后缀和高度 DP `U_fast_table`、多重链 `U_multichain`、原题矩阵直接计数 `a_direct`、暴力 `a_brute`、`N_brute`（DFS）、`N_from_U`（容斥）、Stirling 表、`h_complete`。
- `code/step0_baseline.py`（`logs/step0_baseline.log`）：开工时用三种独立方法核对第 2 节数据。
- `code/main_extra/gcd_minimal_order.py`：最小阶逐因子检验（v≤300）。
- 各方向的探索脚本在 `code/<area>/`，复核者的独立脚本在 `code/review/<reviewer>/`，对应日志在 `logs/`（文件名带 area 或 `review_` 前缀）。
- 各轮工作流的原始返回值：`logs/phase1_workflow_output.json`、`logs/phase2_review_output.json`、`logs/phase3_audit_output.json`、`logs/phase4_final_audit_output.json`、`logs/phase4b_recheck_output.json`；第四轮各审计者的独立脚本在 `code/review/final-audit/`，输出为 `logs/final_audit_*.log`；报告各轮修订的补丁脚本在 `code/main_extra/report_patches/`；逐条结论清单 `notes/review/claims_<area>.md`，逐条复核意见 `notes/review/<reviewer>-review.md`。
- 全量运行记录：`logs/verify_all_run1.log`（第一轮后，9 个模块 278 条）、`logs/verify_all_final_2026-10-05.log`（第四轮修订后，11 个模块 290 条）、`logs/verify_all_2026-10-07.log`（修好 c5b 之后，11 个模块 290 条）、`logs/verify_all_final.log`（最终，2026-10-07 加固 ⑥ 之后，12 个模块 296 条）。报告拼接与核对 id 交叉检查：`code/main_extra/assemble_report.py`。
