## ⑤ 代码与输出

**运行方式**：在本文件夹下执行 `py -3.14 verify_all.py`（需要 numpy：rv2 调用的复核脚本没有纯 Python 回退）。它依次运行 `code/checks/check_*.py`，逐条打印 `PASS <id> <描述（含范围）>` 或 `FAIL …`，最后给出总表；任何 FAIL、子模块异常退出或缺少 SUMMARY 行都会使退出码为 1。

**11 个核对模块**（除 check_rv2.py 外，每个都从 `code/core.py` 的原始定义程序取「真值」；check_rv2.py 运行复核者 x1 的两个独立脚本，不导入 core：r1 用自写的三元组 DP 作真值，r2 只做纤维留数条件的精确代数穷举）

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

**最终一次运行**（2026-10-05，完整输出 `logs/verify_all_final.log`；这次运行时本机另有一个会话在跑基准测试，耗时约为空闲时的 3 倍（此前保存的全量运行：logs/verify_all_run1.log 232.1 s，logs/audit_a3-requirements_verify_rerun.log 216.4 s），检查结果不受影响）：

```
area     pass   fail    rc  summary     secs  status
c0         13      0     0      yes      6.3  PASS
c1         45      0     0      yes    174.2  PASS
c2a        23      0     0      yes     76.2  PASS
c2b        33      0     0      yes     99.0  PASS
c3a        34      0     0      yes     35.2  PASS
c3b        22      0     0      yes     51.2  PASS
c4         41      0     0      yes     77.0  PASS
c5a        37      0     0      yes     28.5  PASS
c5b        33      0     0      yes      6.9  PASS
rv          7      0     0      yes     53.6  PASS
rv2         2      0     0      yes     22.6  PASS
------------------------------------------------------------------------
TOTAL pass=290 fail=0 modules=11 failed_modules=-  (630.7s)
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
| `Axioms.lean` | — | 对上述 83 条定理 `#print axioms`：全部只依赖 propext、Classical.choice、Quot.sound（其中 `rowRule_iff_allowed` 只用到 propext、Quot.sound）；另对 A207123 各模块的全部 1131 个声明（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个 |
| `Checks.lean` | — | 用 `native_decide` 把定义与数据对照：任务说明第 2 节（k=7、10 两行，R_1..R_10，a_3(1..6)）、(C3) 的 N 三角形 k=7、10 两行（经 `N_inv`、`U_eq_F` 计算）、U_6(3,s) 与 U_7(2,s)（经 `Us_explicit` 计算，对照 Python 按定义暴力枚举的数据）；这是计算核对，依赖编译器，不是证明的一部分 |
| `run_lean_checks.sh` | — | 依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`，输出写入 `logs/lean_build.log` |

重跑：在 `lean/` 下运行 `./run_lean_checks.sh`，或依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`（首次需要下载 Mathlib 缓存，约 5–7 GB；之后 `lake build` 每次要核对全部 Mathlib 构建记录，约 3–6 分钟，单个文件编译约 0.5–1 分钟，冷启动时加载 Mathlib 可能要十几分钟）。输出见 `logs/lean_build.log`。

**其他重要文件**

- `code/core.py`：参考实现 `U_list`（照抄第 1 节）、后缀和高度 DP `U_fast_table`、多重链 `U_multichain`、原题矩阵直接计数 `a_direct`、暴力 `a_brute`、`N_brute`（DFS）、`N_from_U`（容斥）、Stirling 表、`h_complete`。
- `code/step0_baseline.py`（`logs/step0_baseline.log`）：开工时用三种独立方法核对第 2 节数据。
- `code/main_extra/gcd_minimal_order.py`：最小阶逐因子检验（v≤300）。
- 各方向的探索脚本在 `code/<area>/`，复核者的独立脚本在 `code/review/<reviewer>/`，对应日志在 `logs/`（文件名带 area 或 `review_` 前缀）。
- 各轮工作流的原始返回值：`logs/phase1_workflow_output.json`、`logs/phase2_review_output.json`、`logs/phase3_audit_output.json`、`logs/phase4_final_audit_output.json`、`logs/phase4b_recheck_output.json`；第四轮各审计者的独立脚本在 `code/review/final-audit/`，输出为 `logs/final_audit_*.log`；报告各轮修订的补丁脚本在 `code/main_extra/report_patches/`；逐条结论清单 `notes/review/claims_<area>.md`，逐条复核意见 `notes/review/<reviewer>-review.md`。
- 全量运行记录：`logs/verify_all_run1.log`（第一轮后，9 个模块 278 条）、`logs/verify_all_final.log`（最终，11 个模块）。报告拼接与核对 id 交叉检查：`code/main_extra/assemble_report.py`。
