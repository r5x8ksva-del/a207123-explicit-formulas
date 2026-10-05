import A207123.Binomial
import A207123.DFinite

/-!
# 报告 T1.6（(C5) PDE）、T1.7（(C6) h 多项式）、T1.8（(C7) 分子）

本文件形式化报告 `notes/report_parts/02_C1.md` 的 T1.6、T1.7、T1.8（详细证明见 `notes/c1.md` §7–§9），
全部从 `Basic.lean` 中 `U k m` 的原始定义出发（经由已形式化的引理 1、T1.3(1)、T1.4）。

## 定义的取法

* **T1.6**：二元形式幂级数环 `ℚ[[x,t]]` 写成 `PS2 ℚ = ℚ[[x]][[t]]`（外层变量 `t`、内层变量 `x`，
  沿用 `DFinite.lean` 的约定；`ℚ[[x]][[t]] ≅ ℚ[[x,t]]` 的典范同构不形式化）。
  `F = Σ_{k,m} U_k(m)·x^k·t^m` 直接复用 `DFinite.lean` 的 `FK ℚ`（`[t^m]F = G_m`，`coeff_FK`），
  `∂_t` 复用 `dTK ℚ`。`x` 写成 `xvar = C X`（外层常数），`t` 写成 `tvar = X`。
  `1/(1−t)²` 写成 `Ring.inverse ((1 − t)²)`；`isUnit_one_sub_tvar_sq` 说明 `(1 − t)²` 是单位，
  所以 `Ring.inverse` 就是真正的逆（`inv_one_sub_tvar_sq_mul`），且等于 `Σ_n (n+1)·t^n`
  （`inv_one_sub_tvar_sq`）。
  逐项形式里越界的指标取 0（`notes/c1.md` §7 的约定；注意这里不是 T1.1 的 `U_{−1} ≡ 1`：
  `k = 2` 时 `m·U_{k−3}(m)` 一项必须取 0，等式才成立，见 `pde_coeff_needs_zero_convention`）。
* **T1.7**：`f_k = Σ_m U_k(m)·t^m` 记为 `fser k ∈ ℚ[[t]]`；`h_k` 记为 `hpoly k ∈ ℚ[t]`：
  `h_0 = 1`，`k ≥ 1` 时 `h_k = Σ_{q=1}^{k} N(k,q)·t^{q−1}·(1−t)^{k−q}`，正是报告的式子
  （`hpoly_of_one_le`）。`hrec a b c` 是按报告递推、从三个初值 `a, b, c` 生成的序列，用来陈述
  「递推需要三个初值」与「取 `h_2 = 1` 得到错误的 `h_3`」。
* **T1.8**：`Σ_k N(k,q)·x^k` 记为 `Nser q`；`Num_q` 记为 `Numq q`，按报告 T4.3(2) 的容斥闭式定义：
  `Num_q = Σ_{i=0}^{q} (−1)^{q−i}·C(q,i)·W_{i−1}·∏_{v=i}^{q−1} b_v`（`W_{−1} = 1`，即 `Wprev`）。
  报告把 `Num_q` 定义为乘积 `P_{q−1}·Σ_k N(k,q)x^k`；主定理 `P_mul_Nser` 说明该乘积（在 `ℚ[[x]]` 中）
  恰好等于多项式 `Numq q`，所以下面关于 `Numq q` 的次数、首项、最低项都是关于这个乘积的陈述
  （`ℚ[x] → ℚ[[x]]` 是单射，乘积对应的多项式唯一）。`G_{−1} = 1` 记为 `Gprev 0`。

## 与报告的对应

* T1.6：`FK_pde`（PDE 恒等式）；`coeff_pde_lhs`、`coeff_pde_rhs`、`pde_coeff`（逐项形式）；
  `pde_coeff_needs_zero_convention`（逐项形式必须「越界取 0」）；
  `pde_homogeneous`（`ℚ[[x,t]]` 中齐次方程只有零解，即报告 T3.2(i) 在 `A = 1 − x` 时的单射部分）；
  `pde_unique`（形式解唯一）。
* T1.7：`hpoly_spec`（`(1−t)^{k+1}·Σ_m U_k(m)t^m = h_k`）与 `fser_eq_div`（除法形式）；
  `hpoly_of_one_le`（k ≥ 1 的 N 表达式）；`X_mul_hpoly`、`hpoly_formula_zero`（k = 0 时 N 表达式给出
  `t^{−1}`，必须单列 `h_0 = 1`）；`hpoly_rec`（递推，k ≥ 3）；`hpoly_zero`、`hpoly_one`、`hpoly_two`
  （三个初值）；`hrec_eq_hpoly`（递推加这三个初值恰好生成 `h_k`）；`hrec_bad_three`、`hrec_bad_ne`
  （取 `h_2 = 1` 得 `h_3 = 1 + t − t² ≠ 1 + 2t − t²`）；`hpoly_three` … `hpoly_six`（与提示词一致）；
  `hpoly_eval_one`、`hpoly_eval_one_eq_two`（`h_k(1) = N(k,k) = 2`，k ≥ 2）；
  证明用到的 `fser_rec` 即报告的 `(1−t)f_k = f_{k−1} + t·f'_{k−3}`。
* T1.8：`P_mul_Nser`（`P_{q−1}·Σ_k N(k,q)x^k = Num_q`，q ≥ 1）；`natDegree_Numq`（次数 `3q−2`）；
  `leadingCoeff_Numq`（首项 `(q−1)!`）；`Numq_lowest`、`Numq_trailing`（q ≥ 2 时最低非零项是 `2x^q`）；
  `Numq_one`（q = 1 时 `Num_1 = x`，最低项不是 `2x`）；`Numq_two`、`Numq_three`、`Numq_four` 与
  `prompt_numerators`（提示词给的 q = 1..4 分子正确）。

## 证明路线

* T1.6：`coeff_Lop` 算出 `[t^m]((1−x−t)Y − x³t∂_tY) = b_m·Y_m − Y_{m−1}`（`b_m = 1 − x − m x³`）。
  对 `Y = F` 用 T1.3(1) 的 `G_zero`、`G_rec`（即报告「把 `(1−x)G_m − m x³G_m = G_{m−1} + m x²` 乘 `t^m`
  求和」）得到 PDE；逐项形式再取 `x^k` 系数（`coeff_b_mul`）。齐次方程：对 `m` 归纳，`b_m·Y_m = 0`，
  而 `ℚ[[x]]` 是整环、`b_m ≠ 0`。
* T1.7：由二项式基 `U_k(m) = Σ_q N(k,q)·C(m+1,q)`（`U_eq_sum_N`）与
  `Σ_m C(m+1,q)·t^m = t^{q−1}/(1−t)^{q+1}`（`one_sub_pow_mul_cser`，用 Mathlib 的
  `mk_add_choose_mul_one_sub_pow_eq_one`）得 `hpoly_spec`。递推：引理 1 乘 `t^m` 求和得 `fser_rec`，
  代入 `f_j = h_j/(1−t)^{j+1}`（先在 `ℚ[[t]]` 中证明，再用 `ℚ[t] → ℚ[[t]]` 的单射拉回）。
  h_3..h_6 由递推与初值直接计算。
* T1.8：由容斥式 `N(k,q) = Σ_i (−1)^{q−i}C(q,i)·U_k(i−1)`（`N_eq_inv_Vn`）得
  `Σ_k N(k,q)x^k = Σ_i (−1)^{q−i}C(q,i)·G_{i−1}`（`Nser_eq_sum`）；`P_{q−1} = P_{i−1}·∏_{v=i}^{q−1} b_v`
  与 `P_{i−1}·G_{i−1} = W_{i−1}`（`P_mul_G`）给出 `P_mul_Nser`。次数与首项：只有 `i = 0` 项
  `(−1)^q·P_{q−1}` 的次数达到 `3q−2`，其余各项次数 ≤ `3(i−1) + 3(q−i) = 3q−3`；
  `lc(P_{q−1}) = (−1)^q (q−1)!`（`leadingCoeff_P`）。最低项：比较 `P_{q−1}·Σ_k N(k,q)x^k` 的系数，
  `P_{q−1}(0) = 1`、`N(k,q) = 0`（k < q），所以 `[x^q]Num_q = N(q,q)`，再用 `N_diag`。
  q = 1..4 的分子直接展开计算。

## 没有形式化的部分

* T1.6 注中「`t^λ e^{−t/x³}`（`λ = (1−x)/x³`）只在解析意义下是齐次解」：`t^λ`、`e^{−t/x³}` 不是
  `ℚ[[x,t]]` 的元素，本文件不处理这类解析 / 非形式对象；只形式化了「在 `ℚ[[x,t]]` 里齐次方程只有零解、
  形式解唯一」。报告 T3.2 的一般情形（任意 `A ∈ ℚ[[x]]`、`A(0) = 1`，以及 `L_A` 的满射性与 Laplace
  表示）不在本文件中，这里只做了 `A = 1 − x` 时的单射。
* 报告在 T1.7、T1.8 末尾指向的 T5.3（h_k 的更多结构）与 T4.3（Num_q 的三项递推与一般系数结构）
  不在本文件中（`Numq` 的定义借用了 T4.3(2) 的容斥闭式，但其与乘积相等的证明在本文件中完成）。
* `ℚ[[x]][[t]]` 与 `ℚ[[x,t]]` 的典范同构（标准事实，沿用 `DFinite.lean` 的写法）。

## 对报告的一处补充（缺写的约定）

报告 02_C1.md 的 T1.6 逐项形式「`[x^k t^m]` 左边 `= U_k(m) − U_{k−1}(m) − U_k(m−1) − m·U_{k−3}(m)`」
没有写明越界指标怎么取。`notes/c1.md` §7 写了「指标越界取 0」，按这个约定等式成立（本文件即按此
陈述）；若沿用 T1.1 的
约定 `U_{−1} ≡ 1`，`k = 2`、`m = 1` 时左边为 `4 − 2 − 1 − 1 = 0`，右边为 1
（`pde_coeff_needs_zero_convention`）；若再用 T1.4 的 `U_0(−1) = 1`，`k = m = 0` 时左边为
`1 − 1 − 1 = −1`，右边为 1。PDE 本身与结论不受影响。除此之外没有发现 T1.6–T1.8 的陈述有误或缺条件。
-/

namespace A207123

open Polynomial Finset

/-! ## T1.6：`F` 满足的一阶 PDE -/

section PDE

/-- `x ∈ ℚ[[x,t]]`：在 `ℚ[[x]][[t]]` 中是外层（关于 `t`）的常数 `C X`。 -/
noncomputable def xvar : PS2 ℚ := PowerSeries.C (PowerSeries.X : PowerSeries ℚ)

/-- `t ∈ ℚ[[x,t]]`：`ℚ[[x]][[t]]` 的外层变量。 -/
noncomputable def tvar : PS2 ℚ := PowerSeries.X

/-- 辅助引理（T1.6）：`[t^m]F = G_m(x)`。 -/
theorem coeff_FK (m : ℕ) : PowerSeries.coeff m (FK ℚ) = Gser m := by
  rw [FK, PowerSeries.coeff_mk]; rfl

/-- 辅助引理（T1.6）：对任意 `Y ∈ ℚ[[x,t]]`，
`[t^m]((1 − x − t)·Y − x³·t·∂_t Y) = b_m·[t^m]Y − [t^{m−1}]Y`（`b_m = 1 − x − m x³`；`m = 0` 时没有
第二项）。 -/
theorem coeff_Lop (Y : PS2 ℚ) (m : ℕ) :
    PowerSeries.coeff m ((1 - xvar - tvar) * Y - xvar ^ 3 * tvar * dTK ℚ Y)
      = (↑(bpoly ℚ m) : PowerSeries ℚ) * PowerSeries.coeff m Y
        - (if m = 0 then 0 else PowerSeries.coeff (m - 1) Y) := by
  rw [coe_bpoly]
  have h1 : (1 - xvar - tvar) * Y
      = Y - PowerSeries.C (PowerSeries.X : PowerSeries ℚ) * Y - PowerSeries.X * Y := by
    simp only [xvar, tvar]; ring
  have h2 : xvar ^ 3 * tvar * dTK ℚ Y
      = PowerSeries.C ((PowerSeries.X : PowerSeries ℚ) ^ 3) * (PowerSeries.X * dTK ℚ Y) := by
    simp only [xvar, tvar, map_pow]; ring
  rw [h1, h2, map_sub, map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  cases m with
  | zero =>
    simp [PowerSeries.coeff_zero_X_mul]
    ring
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, dTK,
      PowerSeries.coeff_derivative]
    simp
    ring

/-- 辅助引理（T1.6）：`(1 − t)²` 是 `ℚ[[x,t]]` 中的单位，所以 `Ring.inverse ((1 − t)²)` 就是
`1/(1 − t)²`。 -/
theorem isUnit_one_sub_tvar_sq : IsUnit ((1 - tvar) ^ 2 : PS2 ℚ) := by
  have h : ((1 - tvar) ^ 2 : PS2 ℚ) = ↑(PowerSeries.invOneSubPow (PowerSeries ℚ) 2)⁻¹ := by
    rw [← Units.inv_eq_val_inv, PowerSeries.invOneSubPow_inv_eq_one_sub_pow]; rfl
  rw [h]; exact Units.isUnit _

/-- 辅助引理（T1.6）：`(1/(1 − t)²)·(1 − t)² = 1`。 -/
theorem inv_one_sub_tvar_sq_mul : Ring.inverse ((1 - tvar) ^ 2) * (1 - tvar) ^ 2 = 1 :=
  Ring.inverse_mul_cancel _ isUnit_one_sub_tvar_sq

/-- 辅助引理（T1.6）：`1/(1 − t)² = Σ_n (n+1)·t^n`。 -/
theorem inv_one_sub_tvar_sq :
    Ring.inverse ((1 - tvar) ^ 2) = PowerSeries.mk fun n => ((n : PowerSeries ℚ) + 1) := by
  have h : ((1 - tvar) ^ 2 : PS2 ℚ) = ↑(PowerSeries.invOneSubPow (PowerSeries ℚ) 2)⁻¹ := by
    rw [← Units.inv_eq_val_inv, PowerSeries.invOneSubPow_inv_eq_one_sub_pow]; rfl
  rw [h, Ring.inverse_unit, inv_inv,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ 2 (by norm_num)]
  ext n : 1
  simp [Nat.choose_one_right]
  ring

/-- 辅助引理（T1.6）：右边的 `t^m` 系数：`[t^m](1 + x²t/(1−t)²) = [m = 0] + m·x²`。 -/
theorem coeff_rhs (m : ℕ) :
    PowerSeries.coeff m (1 + xvar ^ 2 * tvar * Ring.inverse ((1 - tvar) ^ 2))
      = (if m = 0 then 1 else 0) + PowerSeries.C (m : ℚ) * PowerSeries.X ^ 2 := by
  rw [inv_one_sub_tvar_sq]
  have h2 : xvar ^ 2 * tvar * (PowerSeries.mk fun n => ((n : PowerSeries ℚ) + 1))
      = PowerSeries.C ((PowerSeries.X : PowerSeries ℚ) ^ 2)
        * (PowerSeries.X * PowerSeries.mk fun n => ((n : PowerSeries ℚ) + 1)) := by
    simp only [xvar, tvar, map_pow]; ring
  rw [h2, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  cases m with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    simp
    ring

/-- **T1.6（(C5) PDE）**：在 `ℚ[[x,t]]`（写成 `ℚ[[x]][[t]]`）中，
`F(x,t) = Σ_{k,m} U_k(m)·x^k·t^m` 满足 `(1 − x − t)·F − x³·t·∂_t F = 1 + x²·t/(1 − t)²`。
这里 `1/(1−t)²` 写成 `Ring.inverse ((1 − t)²)`（`(1 − t)²` 是单位，见 `isUnit_one_sub_tvar_sq`、
`inv_one_sub_tvar_sq_mul`）。证明：比较 `t^m` 系数，`m = 0` 用 `(1 − x)·G_0 = 1`（`G_zero`），
`m ≥ 1` 用 `(1 − x − m x³)·G_m = G_{m−1} + m x²`（`G_rec`），即报告「乘 `t^m` 求和」。 -/
theorem FK_pde :
    (1 - xvar - tvar) * FK ℚ - xvar ^ 3 * tvar * dTK ℚ (FK ℚ)
      = 1 + xvar ^ 2 * tvar * Ring.inverse ((1 - tvar) ^ 2) := by
  ext m : 1
  rw [coeff_Lop, coeff_rhs]
  cases m with
  | zero => simp [coeff_FK, G_zero]
  | succ n =>
    rw [coeff_FK, coeff_FK, G_rec]
    simp

/-- **T1.6**（逐项形式，左边）：`[x^k t^m]((1 − x − t)F − x³t∂_tF)
= U_k(m) − U_{k−1}(m) − U_k(m−1) − m·U_{k−3}(m)`，越界的指标（`k−1, k−3 < 0` 或 `m−1 < 0`）取 0。 -/
theorem coeff_pde_lhs (k m : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.coeff m ((1 - xvar - tvar) * FK ℚ - xvar ^ 3 * tvar * dTK ℚ (FK ℚ)))
      = (U k m : ℚ) - (if 1 ≤ k then (U (k - 1) m : ℚ) else 0)
        - (if 1 ≤ m then (U k (m - 1) : ℚ) else 0)
        - m * (if 3 ≤ k then (U (k - 3) m : ℚ) else 0) := by
  rw [coeff_Lop, map_sub, coe_bpoly, coeff_b_mul, coeff_FK]
  simp only [coeff_Gser]
  cases m with
  | zero => simp
  | succ n =>
    simp [coeff_FK, coeff_Gser]
    ring

/-- **T1.6**（逐项形式，右边）：`[x^k t^m](1 + x²t/(1−t)²) = [k = m = 0] + m·[k = 2]`。 -/
theorem coeff_pde_rhs (k m : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.coeff m (1 + xvar ^ 2 * tvar * Ring.inverse ((1 - tvar) ^ 2)))
      = ((if k = 0 ∧ m = 0 then 1 else 0) + (m : ℚ) * (if k = 2 then 1 else 0) : ℚ) := by
  rw [coeff_rhs, map_add, PowerSeries.coeff_C_mul_X_pow]
  by_cases hm : m = 0
  · subst hm
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]
  · simp [hm]

/-- **T1.6**（逐项形式）：对一切 `k, m ≥ 0`，
`U_k(m) − U_{k−1}(m) − U_k(m−1) − m·U_{k−3}(m) = [k = m = 0] + m·[k = 2]`（越界的指标取 0）；
`k ≥ 3`、`m ≥ 1` 时这就是引理 1。 -/
theorem pde_coeff (k m : ℕ) :
    (U k m : ℚ) - (if 1 ≤ k then (U (k - 1) m : ℚ) else 0)
        - (if 1 ≤ m then (U k (m - 1) : ℚ) else 0)
        - m * (if 3 ≤ k then (U (k - 3) m : ℚ) else 0)
      = ((if k = 0 ∧ m = 0 then 1 else 0) + (m : ℚ) * (if k = 2 then 1 else 0) : ℚ) := by
  rw [← coeff_pde_lhs, ← coeff_pde_rhs, FK_pde]

/-- **T1.6**（逐项形式的约定必不可少）：逐项形式必须把越界的指标取 0。若按 T1.1 的约定
`U_{−1} ≡ 1` 理解 `m·U_{k−3}(m)`，则 `k = 2`、`m = 1` 时左边
`U_2(1) − U_1(1) − U_2(0) − 1·U_{−1}(1) = 4 − 2 − 1 − 1 = 0`，而右边 `[k = m = 0] + m·[k = 2] = 1`。
（按「越界取 0」，左边为 `4 − 2 − 1 − 0 = 1`，与 `pde_coeff 2 1` 一致。） -/
theorem pde_coeff_needs_zero_convention :
    (U 2 1 : ℚ) - U 1 1 - U 2 0 - 1 * 1 ≠ (0 : ℚ) + 1 * 1 := by
  rw [U_of_le_two (by norm_num), U_of_le_two (by norm_num), U_of_le_two (by norm_num)]
  norm_num

/-- **T1.6**（注「在 `ℚ[[x,t]]` 里齐次方程只有零解」；这是报告 T3.2(i)「`L_A` 是 `𝓟` 上的双射」在
`A = 1 − x` 时的单射部分）：若 `Y ∈ ℚ[[x,t]]` 满足 `(1 − x − t)·Y − x³·t·∂_t Y = 0`，则 `Y = 0`。
证明：`[t^m]` 系数给出 `b_m·Y_m = Y_{m−1}`；对 `m` 归纳，`Y_{m−1} = 0`，而 `ℚ[[x]]` 是整环、
`b_m = 1 − x − m x³ ≠ 0`，故 `Y_m = 0`。 -/
theorem pde_homogeneous (Y : PS2 ℚ)
    (h : (1 - xvar - tvar) * Y - xvar ^ 3 * tvar * dTK ℚ Y = 0) : Y = 0 := by
  have hb : ∀ m, (↑(bpoly ℚ m) : PowerSeries ℚ) ≠ 0 := fun m hm =>
    bpoly_ne_zero m (Polynomial.coe_eq_zero_iff.mp hm)
  have key : ∀ m, PowerSeries.coeff m Y = 0 := by
    intro m
    induction m with
    | zero =>
      have h0 := congrArg (PowerSeries.coeff 0) h
      rw [coeff_Lop, map_zero, ite_eq_left rfl, sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hb 0)
    | succ n ih =>
      have h0 := congrArg (PowerSeries.coeff (n + 1)) h
      rw [coeff_Lop, map_zero, ite_eq_right (by omega), Nat.add_sub_cancel, ih, sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hb (n + 1))
  ext m : 1
  rw [key m, map_zero]

/-- **T1.6**（注「形式解唯一」）：`ℚ[[x,t]]` 中满足同一 PDE 的 `Y` 只有 `F`。 -/
theorem pde_unique (Y : PS2 ℚ)
    (h : (1 - xvar - tvar) * Y - xvar ^ 3 * tvar * dTK ℚ Y
      = 1 + xvar ^ 2 * tvar * Ring.inverse ((1 - tvar) ^ 2)) : Y = FK ℚ := by
  have hlin : (1 - xvar - tvar) * (Y - FK ℚ) - xvar ^ 3 * tvar * dTK ℚ (Y - FK ℚ)
      = ((1 - xvar - tvar) * Y - xvar ^ 3 * tvar * dTK ℚ Y)
        - ((1 - xvar - tvar) * FK ℚ - xvar ^ 3 * tvar * dTK ℚ (FK ℚ)) := by
    simp only [dTK, map_sub]; ring
  rw [h, FK_pde, sub_self] at hlin
  exact sub_eq_zero.mp (pde_homogeneous _ hlin)

end PDE

/-! ## T1.7：h 多项式 -/

section HPoly

/-- `f_k = Σ_m U_k(m)·t^m ∈ ℚ[[t]]`（报告 T1.7 证明中的 `f_k`）。 -/
noncomputable def fser (k : ℕ) : PowerSeries ℚ := PowerSeries.mk fun m => (U k m : ℚ)

/-- 报告 T1.7 的 `h_k ∈ ℚ[t]`：`h_0 = 1`；`k ≥ 1` 时 `h_k = Σ_{q=1}^{k} N(k,q)·t^{q−1}·(1−t)^{k−q}`
（`k = 0` 时这个式子给出 `t^{−1}`，所以单列 `h_0 = 1`，见 `hpoly_formula_zero`）。 -/
noncomputable def hpoly : ℕ → ℚ[X]
  | 0 => 1
  | k + 1 => ∑ q ∈ Icc 1 (k + 1), C (N (k + 1) q : ℚ) * X ^ (q - 1) * (1 - X) ^ (k + 1 - q)

/-- 辅助引理（T1.7）：`hpoly` 在 `k + 1` 处的展开（定义）。 -/
theorem hpoly_succ (k : ℕ) :
    hpoly (k + 1)
      = ∑ q ∈ Icc 1 (k + 1), C (N (k + 1) q : ℚ) * X ^ (q - 1) * (1 - X) ^ (k + 1 - q) := rfl

/-- **T1.7**：`k ≥ 1` 时 `h_k = Σ_{q=1}^{k} N(k,q)·t^{q−1}·(1−t)^{k−q}`。 -/
theorem hpoly_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    hpoly k = ∑ q ∈ Icc 1 k, C (N k q : ℚ) * X ^ (q - 1) * (1 - X) ^ (k - q) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- 辅助定义（T1.7）：`Σ_m C(m+1,q)·t^m ∈ ℚ[[t]]`。 -/
noncomputable def cser (q : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (((m + 1).choose q : ℕ) : ℚ)

/-- 辅助引理（T1.7）：`q = p + 1 ≥ 1` 时 `Σ_m C(m+1,q)·t^m = t^{q−1}/(1−t)^{q+1}`，
写成 `(1−t)^{p+2}·Σ_m C(m+1,p+1)·t^m = t^p`。 -/
theorem one_sub_pow_mul_cser (p : ℕ) :
    (1 - PowerSeries.X) ^ (p + 2) * cser (p + 1) = (PowerSeries.X : PowerSeries ℚ) ^ p := by
  have h : cser (p + 1) = PowerSeries.X ^ p *
      PowerSeries.mk fun n => (((p + 1 + n).choose (p + 1) : ℕ) : ℚ) := by
    ext m
    rw [cser, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    split_ifs with hpm
    · rw [PowerSeries.coeff_mk, show p + 1 + (m - p) = m + 1 by omega]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have h2 := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℚ (p + 1)
  rw [h]
  calc (1 - PowerSeries.X) ^ (p + 2) * (PowerSeries.X ^ p *
        PowerSeries.mk fun n => (((p + 1 + n).choose (p + 1) : ℕ) : ℚ))
      = PowerSeries.X ^ p * ((PowerSeries.mk fun n => (((p + 1 + n).choose (p + 1) : ℕ) : ℚ))
          * (1 - PowerSeries.X) ^ (p + 1 + 1)) := by ring
    _ = PowerSeries.X ^ p := by rw [h2, mul_one]

/-- 辅助引理（T1.7）：由二项式基 `U_k(m) = Σ_q N(k,q)·C(m+1,q)`（`U_eq_sum_N`），
`f_k = Σ_{q=0}^{k} N(k,q)·Σ_m C(m+1,q)·t^m`。 -/
theorem fser_eq_sum (k : ℕ) :
    fser k = ∑ q ∈ range (k + 1), PowerSeries.C (N k q : ℚ) * cser q := by
  ext m
  rw [fser, PowerSeries.coeff_mk, map_sum]
  simp only [PowerSeries.coeff_C_mul, cser, PowerSeries.coeff_mk]
  rw [U_eq_sum_N]
  push_cast
  rfl

/-- **T1.7**：在 `ℚ[[t]]` 中 `(1 − t)^{k+1}·Σ_m U_k(m)·t^m = h_k(t)`，即
`Σ_m U_k(m)·t^m = h_k(t)/(1 − t)^{k+1}`（除法形式见 `fser_eq_div`）。对一切 `k ≥ 0` 成立。 -/
theorem hpoly_spec (k : ℕ) :
    (1 - PowerSeries.X) ^ (k + 1) * fser k = (↑(hpoly k) : PowerSeries ℚ) := by
  cases k with
  | zero =>
    have h : fser 0 = PowerSeries.mk 1 := by
      ext m; simp [fser, U_zero_left]
    rw [h, zero_add, pow_one, mul_comm, PowerSeries.mk_one_mul_one_sub_eq_one]
    simp [hpoly]
  | succ j =>
    rw [fser_eq_sum, Finset.mul_sum, Finset.sum_range_succ', N_succ_zero, Nat.cast_zero, map_zero,
      zero_mul, mul_zero, add_zero]
    rw [hpoly_succ, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, show j + 1 + 1 - 1 = j + 1 by omega]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [Polynomial.coeToPowerSeries.ringHom_apply]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X]
    rw [show 1 + p - 1 = p by omega, show j + 1 - (1 + p) = j - p by omega,
      show 1 + p = p + 1 by omega]
    have e : (1 - PowerSeries.X : PowerSeries ℚ) ^ (j + 1 + 1)
        = (1 - PowerSeries.X) ^ (j - p) * (1 - PowerSeries.X) ^ (p + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    calc (1 - PowerSeries.X) ^ (j - p) * (1 - PowerSeries.X) ^ (p + 2)
          * (PowerSeries.C (N (j + 1) (p + 1) : ℚ) * cser (p + 1))
        = PowerSeries.C (N (j + 1) (p + 1) : ℚ) * (1 - PowerSeries.X) ^ (j - p)
          * ((1 - PowerSeries.X) ^ (p + 2) * cser (p + 1)) := by ring
      _ = _ := by rw [one_sub_pow_mul_cser]; ring

/-- **T1.7**（除法形式）：`Σ_m U_k(m)·t^m = h_k(t)/(1 − t)^{k+1}`，`1/(1−t)^{k+1}` 写成
`Ring.inverse ((1 − t)^{k+1})`（`(1 − t)^{k+1}` 是单位）。 -/
theorem fser_eq_div (k : ℕ) :
    fser k = Ring.inverse ((1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1)) * ↑(hpoly k) := by
  have hu : IsUnit ((1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1)) := by
    have h : ((1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1))
        = ↑(PowerSeries.invOneSubPow ℚ (k + 1))⁻¹ := by
      rw [← Units.inv_eq_val_inv, PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    rw [h]; exact Units.isUnit _
  rw [← hpoly_spec, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- 辅助引理（T1.7）：`k ≥ 1` 时 `t·h_k = Σ_{q=0}^{k} N(k,q)·t^q·(1−t)^{k−q}`
（`q = 0` 项因 `N(k,0) = 0` 为零）。 -/
theorem X_mul_hpoly {k : ℕ} (hk : 1 ≤ k) :
    X * hpoly k = ∑ q ∈ range (k + 1), C (N k q : ℚ) * X ^ q * (1 - X) ^ (k - q) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', N_succ_zero, Nat.cast_zero, map_zero, zero_mul, zero_mul, add_zero,
    hpoly_succ, Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show j + 1 + 1 - 1 = j + 1 by omega]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show 1 + p - 1 = p by omega, show 1 + p = p + 1 by omega]
  ring

/-- **T1.7**（「`k = 0` 时此式给 `t^{−1}`，须单列 `h_0 = 1`」）：把 N 表达式乘以 `t`，
`k = 0` 时得到 `Σ_{q=0}^{0} N(0,q)·t^q·(1−t)^{0−q} = N(0,0) = 1`；没有多项式 `h` 满足 `t·h = 1`，
所以 N 表达式在 `k = 0` 不给出多项式（它给出 `t^{−1}`）。对比 `X_mul_hpoly`（`k ≥ 1`）。 -/
theorem hpoly_formula_zero :
    ¬ ∃ h : ℚ[X], X * h = ∑ q ∈ range (0 + 1), C (N 0 q : ℚ) * X ^ q * (1 - X) ^ (0 - q) := by
  rintro ⟨h, hh⟩
  have := congrArg (Polynomial.eval 0) hh
  simp [N_init.1] at this

/-- 辅助引理（T1.7）：引理 1 乘 `t^m` 对 `m` 求和：`(1 − t)·f_k = f_{k−1} + t·f'_{k−3}`
（此处 `k = j + 3`；`m = 0` 处用 `U_k(−1) = 0`，即 `U_k(0) = U_{k−1}(0) = 1`）。 -/
theorem fser_rec (j : ℕ) :
    (1 - PowerSeries.X) * fser (j + 3)
      = fser (j + 2) + PowerSeries.X * PowerSeries.derivative (R := ℚ) (fser j) := by
  ext m
  rw [sub_mul, one_mul, map_sub, map_add]
  cases m with
  | zero => simp [fser, U_zero_right, PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [fser, PowerSeries.coeff_mk]
    have h : (U (j + 3) (n + 1) : ℚ)
        = U (j + 3) n + U (j + 2) (n + 1) + (n + 1) * U j (n + 1) := by
      exact_mod_cast lemma1 j n
    rw [h]
    ring

/-- **T1.7（递推）**：`k ≥ 3` 时 `h_k = h_{k−1} + t(1−t)·[(1−t)·h'_{k−3} + (k−2)·h_{k−3}]`。
证明：`fser_rec` 两边乘 `(1−t)^k`，代入 `f_j = h_j/(1−t)^{j+1}`（`hpoly_spec`），在 `ℚ[[t]]` 中验证后
用 `ℚ[t] → ℚ[[t]]` 的单射拉回。 -/
theorem hpoly_rec (k : ℕ) (hk : 3 ≤ k) :
    hpoly k = hpoly (k - 1) + X * (1 - X) *
      ((1 - X) * derivative (hpoly (k - 3)) + C ((k : ℚ) - 2) * hpoly (k - 3)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  rw [show j + 3 - 1 = j + 2 by omega, Nat.add_sub_cancel]
  apply Polynomial.coe_injective ℚ
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_C, ← PowerSeries.derivative_coe]
  rw [← hpoly_spec (j + 3), ← hpoly_spec (j + 2), ← hpoly_spec j]
  have hc : PowerSeries.C ((↑(j + 3) : ℚ) - 2) = (j : PowerSeries ℚ) + 1 := by
    rw [show ((↑(j + 3) : ℚ) - 2) = (j : ℚ) + 1 by push_cast; ring, map_add, map_natCast,
      map_one]
  rw [hc]
  have hd : PowerSeries.derivative (R := ℚ) ((1 - PowerSeries.X) ^ (j + 1) * fser j)
      = -((j : PowerSeries ℚ) + 1) * (1 - PowerSeries.X) ^ j * fser j
        + (1 - PowerSeries.X) ^ (j + 1) * PowerSeries.derivative (R := ℚ) (fser j) := by
    rw [Derivation.leibniz, PowerSeries.derivative_pow, map_sub, PowerSeries.derivative_X,
      Derivation.map_one_eq_zero]
    simp [smul_eq_mul]
    ring
  rw [hd]
  linear_combination (1 - PowerSeries.X) ^ (j + 3) * fser_rec j

/-- **T1.7（初值）**：`h_0 = 1`。 -/
theorem hpoly_zero : hpoly 0 = 1 := rfl

/-- **T1.7（初值）**：`h_1 = 1`。 -/
theorem hpoly_one : hpoly 1 = 1 := by
  rw [hpoly_succ]; simp [N_init.2.1]

/-- **T1.7（初值）**：`h_2 = 1 + t`。 -/
theorem hpoly_two : hpoly 2 = 1 + X := by
  rw [hpoly_succ, Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton,
    N_init.2.2.1, N_init.2.2.2]
  simp [Polynomial.C_ofNat]
  ring

/-- **T1.7**：`h_3 = 1 + 2t − t²`（与提示词一致）。 -/
theorem hpoly_three : hpoly 3 = 1 + 2 * X - X ^ 2 := by
  rw [hpoly_rec 3 (by norm_num)]
  norm_num [hpoly_two, hpoly_zero, Polynomial.C_ofNat]
  ring

/-- **T1.7**：`h_4 = 1 + 4t − 3t²`（与提示词一致）。 -/
theorem hpoly_four : hpoly 4 = 1 + 4 * X - 3 * X ^ 2 := by
  rw [hpoly_rec 4 (by norm_num)]
  norm_num [hpoly_three, hpoly_one, Polynomial.C_ofNat]
  ring

/-- **T1.7**：`h_5 = 1 + 8t − 5t² − 2t³`（与提示词一致）。 -/
theorem hpoly_five : hpoly 5 = 1 + 8 * X - 5 * X ^ 2 - 2 * X ^ 3 := by
  rw [hpoly_rec 5 (by norm_num)]
  norm_num [hpoly_four, hpoly_two, Polynomial.C_ofNat]
  ring

/-- **T1.7**：`h_6 = 1 + 14t − 7t² − 8t³ + 2t⁴`（与提示词一致）。 -/
theorem hpoly_six : hpoly 6 = 1 + 14 * X - 7 * X ^ 2 - 8 * X ^ 3 + 2 * X ^ 4 := by
  rw [hpoly_rec 6 (by norm_num)]
  norm_num [hpoly_five, hpoly_three, Polynomial.C_ofNat]
  ring

/-- **T1.7**：`k ≥ 1` 时 `h_k(1) = N(k,k)`（`t = 1` 时只有 `q = k` 一项存活）。 -/
theorem hpoly_eval_one {k : ℕ} (hk : 1 ≤ k) : (hpoly k).eval 1 = N k k := by
  rw [hpoly_of_one_le hk, eval_finsetSum, Finset.sum_eq_single k]
  · simp
  · intro q hq hne
    rw [Finset.mem_Icc] at hq
    have h : k - q ≠ 0 := by omega
    simp [h]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩) h

/-- **T1.7**：`h_k(1) = N(k,k) = 2`（`k ≥ 2`）。 -/
theorem hpoly_eval_one_eq_two {k : ℕ} (hk : 2 ≤ k) : (hpoly k).eval 1 = 2 := by
  rw [hpoly_eval_one (by omega), N_diag k hk]; norm_num

/-- 辅助定义（T1.7）：按报告的递推 `h_k = h_{k−1} + t(1−t)·[(1−t)·h'_{k−3} + (k−2)·h_{k−3}]`
（`k ≥ 3`）从三个初值 `h_0 = a`、`h_1 = b`、`h_2 = c` 生成的序列。 -/
noncomputable def hrec (a b c : ℚ[X]) : ℕ → ℚ[X]
  | 0 => a
  | 1 => b
  | 2 => c
  | k + 3 => hrec a b c (k + 2) + X * (1 - X) *
      ((1 - X) * derivative (hrec a b c k) + C (((k + 3 : ℕ) : ℚ) - 2) * hrec a b c k)

/-- **T1.7**（「需要三个初值 `h_0 = 1`、`h_1 = 1`、`h_2 = 1 + t`」）：递推加这三个初值恰好生成
全部 `h_k`。 -/
theorem hrec_eq_hpoly (k : ℕ) : hrec 1 1 (1 + X) k = hpoly k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rfl
    | 1, _ => rw [hpoly_one]; rfl
    | 2, _ => rw [hpoly_two]; rfl
    | k + 3, ih =>
      rw [hrec, ih (k + 2) (by omega), ih k (by omega), hpoly_rec (k + 3) (by omega)]
      simp only [show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel]

/-- **T1.7**（反例）：若取 `h_2 = 1`（初值 `1, 1, 1`），递推给出 `h_3 = 1 + t − t²`。 -/
theorem hrec_bad_three : hrec 1 1 1 3 = 1 + X - X ^ 2 := by
  simp [hrec, Polynomial.C_ofNat]
  ring

/-- **T1.7**（反例）：初值取 `1, 1, 1` 时递推给出的 `h_3 = 1 + t − t²` 不等于真正的
`h_3 = 1 + 2t − t²`（两者在 `t = 1` 处取值 1 与 2）。 -/
theorem hrec_bad_ne : hrec 1 1 1 3 ≠ hpoly 3 := by
  rw [hrec_bad_three, hpoly_three]
  intro h
  have := congrArg (Polynomial.eval 1) h
  norm_num at this

end HPoly

/-! ## T1.8：固定 `q` 的分子 `Num_q` -/

section Numer

/-- `W_{i−1}`（`Wprev 0 = W_{−1} = 1`，`Wprev (i+1) = W_i`）。 -/
noncomputable def Wprev : ℕ → ℚ[X]
  | 0 => 1
  | i + 1 => Wpoly ℚ i

/-- `G_{i−1}`（`Gprev 0 = G_{−1} = 1`，`Gprev (i+1) = G_i`）。 -/
noncomputable def Gprev : ℕ → PowerSeries ℚ
  | 0 => 1
  | i + 1 => Gser i

/-- `Σ_k N(k,q)·x^k ∈ ℚ[[x]]`。 -/
noncomputable def Nser (q : ℕ) : PowerSeries ℚ := PowerSeries.mk fun k => (N k q : ℚ)

/-- 报告 T1.8 的分子 `Num_q`，按报告 T4.3(2) 的容斥闭式定义：
`Num_q = Σ_{i=0}^{q} (−1)^{q−i}·C(q,i)·W_{i−1}·∏_{v=i}^{q−1} b_v`（`W_{−1} = 1`）。
`P_mul_Nser` 证明它等于报告的定义 `P_{q−1}·Σ_k N(k,q)x^k`（q ≥ 1）。 -/
noncomputable def Numq (q : ℕ) : ℚ[X] :=
  ∑ i ∈ range (q + 1),
    C ((-1 : ℚ) ^ (q - i) * (q.choose i : ℚ)) * Wprev i * ∏ v ∈ Ico i q, bpoly ℚ v

/-- 辅助引理（T1.8）：`[x^k]G_{i−1} = Vn(k,i)`（`i ≥ 1` 时为 `U_k(i−1)`；`i = 0` 时为
`N(k,0) = [k = 0]`，即 `G_{−1} = 1`）。 -/
theorem coeff_Gprev (k i : ℕ) : PowerSeries.coeff k (Gprev i) = (Vn k i : ℚ) := by
  cases i with
  | zero =>
    rw [Gprev, PowerSeries.coeff_one]
    cases k with
    | zero => simp [Vn, N_init.1]
    | succ k => simp [Vn, N_succ_zero]
  | succ i => rw [Gprev, coeff_Gser, U_eq_Vn]

/-- 辅助引理（T1.8）：由容斥式（`N_eq_inv_Vn`），
`Σ_k N(k,q)·x^k = Σ_{i=0}^{q} (−1)^{q−i}·C(q,i)·G_{i−1}`（`G_{−1} = 1`）。 -/
theorem Nser_eq_sum (q : ℕ) :
    Nser q = ∑ i ∈ range (q + 1),
      PowerSeries.C ((-1 : ℚ) ^ (q - i) * (q.choose i : ℚ)) * Gprev i := by
  ext k
  rw [Nser, PowerSeries.coeff_mk, map_sum]
  simp only [PowerSeries.coeff_C_mul, coeff_Gprev]
  have h := congrArg (Int.cast : ℤ → ℚ) (N_eq_inv_Vn k q)
  push_cast at h
  exact h

/-- 辅助引理（T1.8）：`i ≤ q` 时 `P_{q−1}·G_{i−1} = W_{i−1}·∏_{v=i}^{q−1} b_v`
（`P_{q−1} = P_{i−1}·∏_{v=i}^{q−1} b_v`，`P_{i−1}·G_{i−1} = W_{i−1}`）；`P_{q−1}` 写成
`∏_{v<q} b_v`。 -/
theorem prod_mul_Gprev {i q : ℕ} (hiq : i ≤ q) :
    (↑(∏ v ∈ range q, bpoly ℚ v) : PowerSeries ℚ) * Gprev i
      = ↑(Wprev i * ∏ v ∈ Ico i q, bpoly ℚ v) := by
  cases i with
  | zero => rw [Gprev, Wprev, mul_one, one_mul, Finset.range_eq_Ico]
  | succ j =>
    rw [← Finset.prod_range_mul_prod_Ico _ hiq]
    have hP : ∏ v ∈ range (j + 1), bpoly ℚ v = Ppoly ℚ j := rfl
    rw [hP, Polynomial.coe_mul, Polynomial.coe_mul, Gprev, Wprev, mul_right_comm, P_mul_G]

/-- 辅助引理（T1.8）：`Num_q` 看成幂级数时逐项展开。 -/
theorem coe_Numq (q : ℕ) :
    (↑(Numq q) : PowerSeries ℚ) = ∑ i ∈ range (q + 1),
      PowerSeries.C ((-1 : ℚ) ^ (q - i) * (q.choose i : ℚ))
        * ↑(Wprev i * ∏ v ∈ Ico i q, bpoly ℚ v) := by
  rw [Numq, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeToPowerSeries.ringHom_apply, mul_assoc, Polynomial.coe_mul, Polynomial.coe_C]

/-- **T1.8**：对 `q ≥ 1`，`P_{q−1}·Σ_k N(k,q)·x^k = Num_q`（`ℚ[[x]]` 中），所以报告的
`Num_q := P_{q−1}·Σ_k N(k,q)x^k` 是多项式，并且等于容斥闭式 `Numq q`。 -/
theorem P_mul_Nser {q : ℕ} (hq : 1 ≤ q) :
    (↑(Ppoly ℚ (q - 1)) : PowerSeries ℚ) * Nser q = ↑(Numq q) := by
  have hP : Ppoly ℚ (q - 1) = ∏ v ∈ range q, bpoly ℚ v := by
    rw [Ppoly, Nat.sub_add_cancel hq]
  rw [coe_Numq, hP, Nser_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [mul_left_comm, prod_mul_Gprev (by omega)]

/-- 辅助引理（T1.8）：`b_0 = 1 − x` 的首项系数为 `−1`。 -/
theorem leadingCoeff_bpoly_zero : (bpoly ℚ 0).leadingCoeff = -1 := by
  rw [leadingCoeff, natDegree_bpoly_zero]; simp [bpoly, Polynomial.coeff_one, Polynomial.coeff_X]

/-- 辅助引理（T1.8）：`i ≥ 1` 时 `b_i = 1 − x − i x³` 的首项系数为 `−i`。 -/
theorem leadingCoeff_bpoly {i : ℕ} (hi : 1 ≤ i) : (bpoly ℚ i).leadingCoeff = -(i : ℚ) := by
  rw [leadingCoeff, natDegree_bpoly hi]; simp [bpoly, Polynomial.coeff_one, Polynomial.coeff_X]

/-- 辅助引理（T1.8）：`lc(P_m) = (−1)^{m+1}·m!`。 -/
theorem leadingCoeff_P (m : ℕ) :
    (Ppoly ℚ m).leadingCoeff = (-1) ^ (m + 1) * (m.factorial : ℚ) := by
  induction m with
  | zero => rw [Ppoly_zero, leadingCoeff_bpoly_zero]; simp
  | succ m ih =>
    rw [Ppoly_succ, leadingCoeff_mul, ih, leadingCoeff_bpoly (by omega), Nat.factorial_succ]
    push_cast
    ring

/-- 辅助引理（T1.8）：`i ≥ 1` 时 `deg ∏_{v=i}^{q−1} b_v ≤ 3(q−i)`。 -/
theorem natDegree_prod_Ico_le {i q : ℕ} (hi : 1 ≤ i) :
    (∏ v ∈ Ico i q, bpoly ℚ v).natDegree ≤ 3 * (q - i) := by
  refine (natDegree_prod_le _ _).trans ?_
  rw [Finset.sum_congr rfl (fun v hv => natDegree_bpoly (by rw [Finset.mem_Ico] at hv; omega)),
    Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_comm]

/-- 辅助引理（T1.8）：`1 ≤ i ≤ q` 时第 `i` 项 `c·W_{i−1}·∏_{v=i}^{q−1} b_v` 的次数
`≤ 3(i−1) + 3(q−i) = 3q − 3`。 -/
theorem natDegree_Numq_term_le {q i : ℕ} (hi : 1 ≤ i) (hiq : i ≤ q) (c : ℚ) :
    (C c * Wprev i * ∏ v ∈ Ico i q, bpoly ℚ v).natDegree ≤ 3 * q - 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  refine natDegree_mul_le.trans ?_
  have h1 : (C c * Wprev (j + 1)).natDegree ≤ 3 * j :=
    (natDegree_C_mul_le _ _).trans (natDegree_W_le j)
  have h2 := natDegree_prod_Ico_le (q := q) hi
  omega

/-- 辅助引理（T1.8）：把 `i = 0` 项 `(−1)^q·P_{q−1}` 单独分出。 -/
theorem Numq_split {q : ℕ} (hq : 1 ≤ q) :
    Numq q = C ((-1 : ℚ) ^ q) * Ppoly ℚ (q - 1)
      + ∑ i ∈ range q, C ((-1 : ℚ) ^ (q - (i + 1)) * (q.choose (i + 1) : ℚ)) * Wprev (i + 1)
          * ∏ v ∈ Ico (i + 1) q, bpoly ℚ v := by
  rw [Numq, Finset.sum_range_succ', add_comm]
  congr 1
  rw [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Wprev, mul_one, Ppoly,
    Nat.sub_add_cancel hq, Finset.range_eq_Ico]

/-- 辅助引理（T1.8）：`i ≥ 1` 各项之和的次数 `≤ 3q − 3`。 -/
theorem natDegree_Numq_rest_le (q : ℕ) :
    (∑ i ∈ range q, C ((-1 : ℚ) ^ (q - (i + 1)) * (q.choose (i + 1) : ℚ)) * Wprev (i + 1)
        * ∏ v ∈ Ico (i + 1) q, bpoly ℚ v).natDegree ≤ 3 * q - 3 :=
  natDegree_sum_le_of_forall_le _ _ fun _ hi =>
    natDegree_Numq_term_le (by omega) (by rw [Finset.mem_range] at hi; omega) _

/-- 辅助引理（T1.8）：`i = 0` 项 `(−1)^q·P_{q−1}` 的次数恰为 `3q − 2`。 -/
theorem natDegree_Numq_head {q : ℕ} (hq : 1 ≤ q) :
    (C ((-1 : ℚ) ^ q) * Ppoly ℚ (q - 1)).natDegree = 3 * q - 2 := by
  rw [natDegree_C_mul (pow_ne_zero _ (by norm_num)), natDegree_P]
  omega

/-- **T1.8**：`q ≥ 1` 时 `deg Num_q = 3q − 2`。 -/
theorem natDegree_Numq {q : ℕ} (hq : 1 ≤ q) : (Numq q).natDegree = 3 * q - 2 := by
  rw [Numq_split hq, natDegree_add_eq_left_of_natDegree_lt, natDegree_Numq_head hq]
  rw [natDegree_Numq_head hq]
  exact lt_of_le_of_lt (natDegree_Numq_rest_le q) (by omega)

/-- **T1.8**：`q ≥ 1` 时 `Num_q` 的首项系数为 `(−1)^q·lc(P_{q−1}) = (q−1)!`。 -/
theorem leadingCoeff_Numq {q : ℕ} (hq : 1 ≤ q) :
    (Numq q).leadingCoeff = ((q - 1).factorial : ℚ) := by
  rw [Numq_split hq, leadingCoeff_add_of_degree_lt', leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_P, Nat.sub_add_cancel hq, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  · norm_num
  · apply degree_lt_degree
    rw [natDegree_Numq_head hq]
    exact lt_of_le_of_lt (natDegree_Numq_rest_le q) (by omega)

/-- 辅助引理（T1.8）：`[x^j]Num_q = Σ_{i≤j} [x^i]P_{q−1}·N(j−i,q)`（由 `P_mul_Nser` 比较系数）。 -/
theorem coeff_Numq {q : ℕ} (hq : 1 ≤ q) (j : ℕ) :
    (Numq q).coeff j = ∑ i ∈ range (j + 1), (Ppoly ℚ (q - 1)).coeff i * (N (j - i) q : ℚ) := by
  rw [← Polynomial.coeff_coe, ← P_mul_Nser hq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe, Nser, PowerSeries.coeff_mk]

/-- 辅助引理（T1.8）：`j < q` 时 `[x^j]Num_q = 0`（`N(k,q) = 0`，`k < q`）。 -/
theorem coeff_Numq_of_lt {q j : ℕ} (hq : 1 ≤ q) (hj : j < q) : (Numq q).coeff j = 0 := by
  rw [coeff_Numq hq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [N_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- 辅助引理（T1.8）：`[x^q]Num_q = N(q,q)`（`P_{q−1}(0) = 1`）。 -/
theorem coeff_Numq_self {q : ℕ} (hq : 1 ≤ q) : (Numq q).coeff q = N q q := by
  rw [coeff_Numq hq, Finset.sum_eq_single 0]
  · rw [Nat.sub_zero, coeff_zero_P, one_mul]
  · intro i hi hi0
    rw [N_eq_zero_of_lt (by rw [Finset.mem_range] at hi; omega), Nat.cast_zero, mul_zero]
  · intro h; simp at h

/-- **T1.8**（最低项，q ≥ 2）：`x^j`（`j < q`）的系数全为 0，`x^q` 的系数为 `N(q,q) = 2`，
即最低非零项是 `2x^q`。（`q = 1` 时最低项是 `x`，见 `Numq_one`。） -/
theorem Numq_lowest {q : ℕ} (hq : 2 ≤ q) :
    (∀ j < q, (Numq q).coeff j = 0) ∧ (Numq q).coeff q = 2 := by
  refine ⟨fun j hj => coeff_Numq_of_lt (by omega) hj, ?_⟩
  rw [coeff_Numq_self (by omega), N_diag q hq]
  norm_num

/-- **T1.8**（最低项，q ≥ 2，用 Mathlib 的 trailing degree 表述）：`Num_q` 的最低次数为 `q`，
最低项系数为 2。 -/
theorem Numq_trailing {q : ℕ} (hq : 2 ≤ q) :
    (Numq q).natTrailingDegree = q ∧ (Numq q).trailingCoeff = 2 := by
  obtain ⟨h1, h2⟩ := Numq_lowest hq
  have hne : Numq q ≠ 0 := fun h => by
    rw [h, Polynomial.coeff_zero] at h2
    norm_num at h2
  have hdeg : (Numq q).natTrailingDegree = q :=
    le_antisymm (natTrailingDegree_le_of_ne_zero (by rw [h2]; norm_num))
      (le_natTrailingDegree hne h1)
  exact ⟨hdeg, by rw [trailingCoeff, hdeg, h2]⟩

/-- **T1.8**：`Num_1 = x`（所以 `q = 1` 时最低项是 `x` 而不是 `2x`）。 -/
theorem Numq_one : Numq 1 = X := by
  simp [Numq, Finset.sum_range_succ, Wprev, Wpoly_zero, bpoly]

/-- **T1.8**：`Num_2 = 2x² + x⁴`（与提示词一致）。 -/
theorem Numq_two : Numq 2 = 2 * X ^ 2 + X ^ 4 := by
  simp [Numq, Finset.sum_range_succ, Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ, Wprev,
    Wpoly_succ, Wpoly_zero, Ppoly_zero, bpoly, Nat.choose]
  ring

/-- **T1.8**：`Num_3 = 2x³ + 2x⁴ + 7x⁵ + 2x⁷`（与提示词一致）。 -/
theorem Numq_three : Numq 3 = 2 * X ^ 3 + 2 * X ^ 4 + 7 * X ^ 5 + 2 * X ^ 7 := by
  simp [Numq, Finset.sum_range_succ, Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ, Wprev,
    Wpoly_succ, Wpoly_zero, Ppoly_succ, Ppoly_zero, bpoly, Nat.choose]
  ring

/-- **T1.8**：`Num_4 = 2x⁴ + 8x⁵ + 13x⁶ + 15x⁷ + 29x⁸ + 6x¹⁰`（与提示词一致）。 -/
theorem Numq_four :
    Numq 4 = 2 * X ^ 4 + 8 * X ^ 5 + 13 * X ^ 6 + 15 * X ^ 7 + 29 * X ^ 8 + 6 * X ^ 10 := by
  simp [Numq, Finset.sum_range_succ, Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ, Wprev,
    Wpoly_succ, Wpoly_zero, Ppoly_succ, Ppoly_zero, bpoly, Nat.choose, Polynomial.C_ofNat]
  ring

/-- **T1.8**（「提示词给的 q = 1..4 分子正确」）：`P_{q−1}·Σ_k N(k,q)x^k` 依次等于提示词 (C7) 的
`x`、`2x² + x⁴`、`2x³ + 2x⁴ + 7x⁵ + 2x⁷`、`2x⁴ + 8x⁵ + 13x⁶ + 15x⁷ + 29x⁸ + 6x¹⁰`。 -/
theorem prompt_numerators :
    (↑(Ppoly ℚ 0) : PowerSeries ℚ) * Nser 1 = ↑(X : ℚ[X]) ∧
    (↑(Ppoly ℚ 1) : PowerSeries ℚ) * Nser 2 = ↑(2 * X ^ 2 + X ^ 4 : ℚ[X]) ∧
    (↑(Ppoly ℚ 2) : PowerSeries ℚ) * Nser 3
      = ↑(2 * X ^ 3 + 2 * X ^ 4 + 7 * X ^ 5 + 2 * X ^ 7 : ℚ[X]) ∧
    (↑(Ppoly ℚ 3) : PowerSeries ℚ) * Nser 4
      = ↑(2 * X ^ 4 + 8 * X ^ 5 + 13 * X ^ 6 + 15 * X ^ 7 + 29 * X ^ 8 + 6 * X ^ 10 : ℚ[X]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Numq_one]; exact P_mul_Nser (q := 1) le_rfl
  · rw [← Numq_two]; exact P_mul_Nser (q := 2) (by norm_num)
  · rw [← Numq_three]; exact P_mul_Nser (q := 3) (by norm_num)
  · rw [← Numq_four]; exact P_mul_Nser (q := 4) (by norm_num)

end Numer

end A207123
