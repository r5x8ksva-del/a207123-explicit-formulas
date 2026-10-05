import A207123.Formula
import A207123.Recurrence

/-!
# 系数公式：`1/P_m` 的系数、Θ 公式、F3 型与 `c_i` 偏分式型（报告 T1.5、T2.5）

记号同报告：`b_i = 1 − x − i·x³`，`P_m = ∏_{i=0}^{m} b_i`（`P_{−1} = 1`），`c_i(n) = [xⁿ] 1/b_i`，
`S(n,k)` 为第二类 Stirling 数，`H(m,s,j) = h_s(j, j+1, …, m)`，`G_m = Σ_k U_k(m) x^k`。

## 形式化了什么

* **T1.5(1)** `ci_formula`：`c_i(n) = Σ_{0≤j≤n/3} C(n−2j, j)·i^j`（`0^0 = 1`，所以 `c_0 ≡ 1`，见 `ci_zero`）。
* **T1.5(2)** `coeff_inv_Ppoly`：`[xⁿ] 1/P_m = Σ_{0≤s≤n/3} S(m+s, m)·C(n+m−2s, m+s)`。
* **T1.5(3)** `factorial_mul_coeff_inv_Ppoly`：`m!·[xⁿ] 1/P_m = Σ_{i=0}^{m} (−1)^{m−i}·C(m,i)·c_i(n+3m)`；
  另有笔记 c1.md §6.3 的附带结论 `alt_sum_ci_vanish`（`0 ≤ N < 3m` 时该交错和为 0）。
* **T1.5(4)** `U_eq_Theta`：对一切 `k ≥ 0`，`U_k(m) = Θ_m(k+1+3m) − Σ_{t=0}^{m−1} Θ_t(k+3t)`；
  `Theta_eq_coeff_prod`、`Theta_eq_coeff_div`、`Theta_eq_coeff_Ppoly_div`：对 `0 ≤ t ≤ m`，
  `Θ_t(n+3t) = [xⁿ] ∏_{i=m−t}^{m} b_i^{-1} = [xⁿ] P_{m−t−1}/P_m`。
* **T1.5 注** `T15_note_P`、`T15_note_c`：若按广义二项式（Mathlib 的 `Ring.choose`）求和到 `n/3` 之外，
  公式错误。反例：`m = 1, n = 0` 时 `s = 1` 项 `S(2,1)·C(−1,2) = 1 ≠ 0`（`s = 0, 1` 两项之和为 2，
  真值为 1）；`Σ_{j=0}^{1} C(1−2j, j)·5^j = −4`，而 `c_5(1) = 1`。
* **T2.5(1)** `U_F3`（`ℤ` 中的减法）、`U_F3_nat`（移项后的自然数等式）：
  `U_k(m) = Σ_s S(m+s,m)·C(k+1+m−2s, m+s) − Σ_{j=1}^{m} Σ_s H(m,s,j)·C(k+m−j−2s, m−j+s)`。
* **T2.5(2)** `Theta_eq_H`：`Θ_t(n+3t) = [xⁿ] ∏_{v=m−t}^{m} b_v^{-1} = Σ_s H(m,s,m−t)·C(n+t−2s, n−3s)`；
  `Theta_eq_F3_head`、`Theta_eq_F3_term`：Θ 公式的每一项就是 F3 型对应的一项（逐项相同）；
  `Theta_vs_H_example`：与推荐的 H 型（`Formula.lean` 的 `U_explicit`）外层不逐项相同的反例
  `m = 1, k = 3`（Θ 型两项 `(8, −2)`，H 型两项 `(5, 1)`，和都是 6）。
* **T2.5(3)** `U_F4`：`m!·U_k(m) = Σ_{i=0}^{m} (−1)^{m−i} C(m,i)·[c_i(k+3m) + Σ_{j=1}^{i} j·i^{\underline j}·c_i(k+3m−3j−2)]`，
  `n < 0` 时 `c_i(n) = 0`；推论 `R_formula`：`R_k := U_k(1) = c_1(k+3) + c_1(k−2) − 1`，
  以及把约定拆开写的 `R_formula_of_two_le`（`k ≥ 2`）与 `R_formula_of_lt_two`（`k < 2` 时 `R_k = c_1(k+3) − 1`）。

## 定义怎么取

* `b_i`、`P_m`、`W_m`、`G_m` 沿用 `Recurrence.lean` 的 `bpoly`、`Ppoly`、`Wpoly`、`Gser`；`bser i` 只是
  `bpoly ℚ i` 到 `ℚ⟦x⟧` 的强制转换。`1/b_i`、`1/P_m` 取 `ℚ⟦x⟧` 中的逆（常数项为 1，所以可逆）。
* `ci i n := [xⁿ] (b_i)⁻¹`，与报告记号表 `c_i(n) := [xⁿ]1/b_i` 一致；显式式是定理（T1.5(1)），不是定义。
* `ciZ i n`（`n : ℤ`）：`n ≥ 0` 时为 `c_i(n)`，`n < 0` 时为 0，即 T2.5(3) 的约定。
* `Theta m t n := (1/t!)·Σ_{r=0}^{t} (−1)^r·C(t,r)·c_{m−r}(n)`，照抄 c1.md §6.4（依赖 `m`）。报告只在 `t ≤ m`
  时使用 Θ，所有定理也都带 `t ≤ m`；`t > m` 时自然数减法 `m − r` 会截断，那里的值没有意义，也没有被用到。
* `S(n,k)` 是 Mathlib 的 `Nat.stirlingSecond`；`H(m,s,j) = hc s (vars j m)`（`Formula.lean`，`vars j m = [m, …, j]`）；
  下降阶乘 `i^{\underline j}` 是 `Nat.descFactorial i j`；`U` 是 `Basic.lean` 中按原始定义计数的 `U k m`。
* 二项式约定：报告中计数公式的 `Σ_s`、`Σ_j` 是「使二项式非零的有限和」。这里都写成显式范围：
  T1.5(1) 为 `j ≤ n/3`，T1.5(2) 为 `s ≤ n/3`，F3 型的单和为 `s ≤ (k+1)/3`、双和内层为 `s ≤ k/3`，
  T2.5(2) 为 `s ≤ n/3`；它们恰好是使对应二项式 `C(a,b)` 满足 `0 ≤ b ≤ a` 的指标。在这些范围内
  自然数减法都不截断，`Nat.choose` 就是普通二项式。
* T1.5 注里的广义二项式用 `Ring.choose`（在 `ℤ` 上就是多项式 `C(y,b) = y(y−1)⋯(y−b+1)/b!` 的值）。
* 辅助定义 `Wtil i = W̃_i = 1 + Σ_{j=1}^{i} j·i^{\underline j}·x^{3j+2}`（报告 T2.6 的术语）只出现在 F4 的证明里。

## 证明路线

* 内层：`Formula.lean` 的 `E l n`（按 `h_s(l)·multichoose(|l|+s, n−3s)` 定义的有限和）满足「加入最大变量」的
  递推 `E_cons`，它正好说明 `(1 − x − v x³)·Σ_n E(v::l, n)xⁿ = Σ_n E(l, n)xⁿ`。于是
  `∏_{v=j}^{m} b_v^{-1} = Σ_n E([m,…,j], n)xⁿ`（`prod_Icc_inv_eq_mkE`）。取 `l = [i]`（`h_s(i) = i^s`）得
  T1.5(1)；取 `l = [m,…,0]`（`h_s = S(m+s,m)`，即 `hc_vars_zero`）得 T1.5(2)；一般的 `[m,…,j]` 给出 F3 型
  与 T2.5(2) 的内层。
* 部分分式：用 Mathlib 的前向差分公式 `fwdDiff_iter_eq_sum_shift`，对 `f(i) = b_i^{-1}` 归纳证明
  `Δ^t f(a) = t!·x^{3t}·∏_{j=0}^{t} b_{a+j}^{-1}`（关键是 `b_a − b_{a+t+1} = (t+1)x³`），即
  `Σ_{k=0}^{t} (−1)^{t−k} C(t,k)/b_{a+k} = t!·x^{3t}/∏_{j=0}^{t} b_{a+j}`。取 `a = 0, t = m` 得 T1.5(3)；
  取 `a = m − t` 并把求和反向（`r = t − k`）得 `Θ_t(n+3t) = [xⁿ]∏_{i=m−t}^{m} b_i^{-1}`。
* 外层：由 T1.3(1) 的 `X_mul_W` 与 `P_mul_G` 得 `x·G_m = 1/P_m − 1 − x·Σ_{j<m} P_j/P_m`（`X_mul_Gser`），
  取 `x^{k+1}` 的系数（`k ≥ 0` 时常数 `−1` 没有贡献）得 `U_eq_outer`；代入内层即得 Θ 公式（T1.5(4)）与
  F3 型（T2.5(1)）。
* F4：把 `a = 0, t = m` 的部分分式乘以 `W_m`，得 `m!·x^{3m}·G_m = Σ_i (−1)^{m−i}C(m,i)·W_m/b_i`；再用
  `P_{j−1} ≡ i^{\underline j}·x^{3j} (mod b_i)` 推出 `W_m ≡ W̃_i (mod b_i)`（`bpoly_dvd_W_sub_Wtil`），而商的
  次数 `< 3m`（`natDegree_W_sub_Wtil_lt`），所以 `x^{k+3m}` 的系数里多项式部分没有贡献。

## 与报告证明写法的差别

* T1.5(2)：报告用代换 `u = x³/(1−x)` 与 `∏_{i=1}^{m}(1−iu)^{-1} = Σ_s S(m+s,m)u^s`；这里不做幂级数代换，
  而是借用 `Formula.lean` 中 `E` 的递推（相当于逐个乘上因子 `b_v`），再用 `hc_vars_zero` 换成 Stirling 数。
* T1.5(3)(4)：报告是「对节点 `0..m` 做部分分式，再代入 `z = (1−x)/x³`」；这里在 `ℚ⟦x⟧` 中用有限差分归纳直接
  证明同一个部分分式恒等式（即 c2a.md 定理 3(i) 的写法），不经过有理函数域。
* T2.5(1)：报告给出组合证明（末块分类与双射 φ），并指出代数上就是望远镜恒等式；这里只走代数路线
  （`X_mul_W` 在 `Recurrence.lean` 中对 `m` 归纳证明，每一步用的正是 `(m+1)x³P_m = (1−x)P_m − P_{m+1}`）。

## 没有形式化的部分

* T2.5(1) 的组合证明（双射 φ）：结论已经用代数路线证明，组合双射本身没有形式化。
* T2.5(3) 后的评注「它与 T5.1 的 Binet 型谱分解是同一组公式按极点重排」：属于 T5.1 的范围，没有形式化。

形式化过程中没有发现 T1.5、T2.5 的陈述有误或缺条件；T1.5 注中的两个反例、T2.5(2) 中 `m = 1, k = 3` 的
反例与 T2.5(3) 中 `k < 2` 时的约定都已在 Lean 中核对。
-/

namespace A207123

open Finset

/-! ## 定义 -/

/-- T1.5 的记号：`b_i = 1 − x − i·x³`，看作 `ℚ` 上的形式幂级数（就是 `bpoly ℚ i` 的强制转换）。 -/
noncomputable def bser (i : ℕ) : PowerSeries ℚ := (↑(bpoly ℚ i) : PowerSeries ℚ)

/-- `c_i(n) := [xⁿ] 1/b_i`（报告记号表；T1.5(1)、T2.5(3) 使用）；`1/b_i` 是 `b_i` 在 `ℚ⟦x⟧` 中的逆。 -/
noncomputable def ci (i n : ℕ) : ℚ := PowerSeries.coeff n (bser i)⁻¹

/-- 整数下标的 `c_i(n)`：`n < 0` 时取 `0`（报告 T2.5(3) 的约定「n<0 时 c_i(n)=0」）。 -/
noncomputable def ciZ (i : ℕ) (n : ℤ) : ℚ := if 0 ≤ n then ci i n.toNat else 0

/-- `Θ_t(n) := (1/t!)·Σ_{r=0}^{t} (−1)^r·C(t,r)·c_{m−r}(n)`（依赖 `m`；笔记 c1.md §6.4 的定义，
报告 T1.5(4) 只在 `t ≤ m` 时使用它）。 -/
noncomputable def Theta (m t n : ℕ) : ℚ :=
  (1 / (t.factorial : ℚ)) * ∑ r ∈ range (t + 1), (-1 : ℚ) ^ r * (t.choose r : ℚ) * ci (m - r) n

/-- `W̃_i = 1 + Σ_{j=1}^{i} j·i^{\underline j}·x^{3j+2}`（报告 T2.6 的术语，`i^{\underline j}` 是下降阶乘
`Nat.descFactorial i j`）。T2.5(3) 用到 `W_m ≡ W̃_i (mod b_i)`（`i ≤ m`）。 -/
noncomputable def Wtil (i : ℕ) : Polynomial ℚ :=
  1 + ∑ j ∈ Icc 1 i,
    Polynomial.C ((j : ℚ) * (i.descFactorial j : ℚ)) * Polynomial.X ^ (3 * j + 2)

/-! ## 基本引理 -/

/-- 辅助引理（T1.5）：`b_i = 1 − x − i·x³`（幂级数形式）。 -/
theorem bser_eq (i : ℕ) :
    bser i = 1 - PowerSeries.X - (i : PowerSeries ℚ) * PowerSeries.X ^ 3 := by
  rw [bser, coe_bpoly, map_natCast]

/-- 辅助引理（T1.5）：`b_i` 的常数项为 `1`。 -/
theorem constantCoeff_bser (i : ℕ) : PowerSeries.constantCoeff (bser i) = 1 := by
  rw [bser, Polynomial.constantCoeff_coe, coeff_zero_bpoly]

/-- 辅助引理（T1.5）：`b_i` 的常数项非零。 -/
theorem constantCoeff_bser_ne (i : ℕ) : PowerSeries.constantCoeff (bser i) ≠ 0 := by
  rw [constantCoeff_bser]; exact one_ne_zero

/-- 辅助引理（T1.5）：`b_i^{-1}·b_i = 1`。 -/
theorem inv_mul_bser (i : ℕ) : (bser i)⁻¹ * bser i = 1 :=
  PowerSeries.inv_mul_cancel _ (constantCoeff_bser_ne i)

/-- 辅助引理（T1.5）：`b_i·b_i^{-1} = 1`。 -/
theorem bser_mul_inv (i : ℕ) : bser i * (bser i)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (constantCoeff_bser_ne i)

/-- 辅助引理（T1.5）：逆元唯一（`A·P = 1 = B·P ⇒ A = B`）。 -/
theorem ps_inv_unique {A B P : PowerSeries ℚ} (hA : A * P = 1) (hB : B * P = 1) : A = B := by
  calc A = A * (B * P) := by rw [hB, mul_one]
    _ = B * (A * P) := by ring
    _ = B := by rw [hA, mul_one]

/-- 辅助引理（T1.5(4)、T2.5(3)）：多项式到幂级数的强制转换与有限和交换。 -/
theorem psCoe_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) :
    (↑(∑ j ∈ s, f j) : PowerSeries ℚ) = ∑ j ∈ s, (↑(f j) : PowerSeries ℚ) :=
  map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) f s

/-- 辅助引理（T1.5(2)(4)）：多项式到幂级数的强制转换与有限积交换。 -/
theorem psCoe_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) :
    (↑(∏ j ∈ s, f j) : PowerSeries ℚ) = ∏ j ∈ s, (↑(f j) : PowerSeries ℚ) :=
  map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) f s

/-- 辅助引理（T1.5(2)(4)）：`↑(∏_{i∈s} b_i) = ∏_{i∈s} b_i`（幂级数）。 -/
theorem coe_prod_bpoly (s : Finset ℕ) :
    (↑(∏ i ∈ s, bpoly ℚ i) : PowerSeries ℚ) = ∏ i ∈ s, bser i :=
  psCoe_prod s (bpoly ℚ)

/-- 辅助引理（T1.5(2)）：`P_m = ∏_{i=0}^{m} b_i`（幂级数）。 -/
theorem coe_Ppoly (m : ℕ) : (↑(Ppoly ℚ m) : PowerSeries ℚ) = ∏ i ∈ Icc 0 m, bser i := by
  rw [Ppoly, coe_prod_bpoly, Nat.range_succ_eq_Icc_zero]

/-- 辅助引理（T1.5(2)）：`P_m` 的常数项非零。 -/
theorem constantCoeff_Ppoly_ne (m : ℕ) :
    PowerSeries.constantCoeff (↑(Ppoly ℚ m) : PowerSeries ℚ) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, coeff_zero_P]; exact one_ne_zero

/-- 辅助引理（T1.5(2)）：`(∏_{i∈s} b_i^{-1})·∏_{i∈s} b_i = 1`。 -/
theorem prod_inv_mul_prod (s : Finset ℕ) : (∏ i ∈ s, (bser i)⁻¹) * ∏ i ∈ s, bser i = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ => inv_mul_bser i

/-- 辅助引理（T1.5(2)(3)）：`1/P_m = ∏_{i=0}^{m} b_i^{-1}`。 -/
theorem Ppoly_inv_eq_prod (m : ℕ) :
    (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ = ∏ i ∈ Icc 0 m, (bser i)⁻¹ := by
  refine ps_inv_unique (PowerSeries.inv_mul_cancel _ (constantCoeff_Ppoly_ne m)) ?_
  rw [coe_Ppoly]
  exact prod_inv_mul_prod _

/-- 辅助引理（T1.5(4)）：对 `j ≤ m+1`，`(∏_{i<j} b_i)/P_m = ∏_{i=j}^{m} b_i^{-1}`
（`∏_{i<j} b_i = P_{j−1}`，`P_{−1} = 1`）。 -/
theorem coe_prod_range_mul_Ppoly_inv (j m : ℕ) (h : j ≤ m + 1) :
    (↑(∏ i ∈ range j, bpoly ℚ i) : PowerSeries ℚ) * (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ =
      ∏ i ∈ Icc j m, (bser i)⁻¹ := by
  have hsplit : (↑(Ppoly ℚ m) : PowerSeries ℚ) =
      (↑(∏ i ∈ range j, bpoly ℚ i) : PowerSeries ℚ) * ∏ i ∈ Icc j m, bser i := by
    rw [coe_Ppoly, coe_prod_bpoly, ← Nat.range_succ_eq_Icc_zero,
      ← Finset.Ico_add_one_right_eq_Icc, prod_range_mul_prod_Ico _ h]
  refine ps_inv_unique ?_ (prod_inv_mul_prod (Icc j m))
  calc (↑(∏ i ∈ range j, bpoly ℚ i) : PowerSeries ℚ) * (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ *
        ∏ i ∈ Icc j m, bser i
      = ((↑(∏ i ∈ range j, bpoly ℚ i) : PowerSeries ℚ) * ∏ i ∈ Icc j m, bser i) *
          (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ := by ring
    _ = 1 := by
      rw [← hsplit]
      exact PowerSeries.mul_inv_cancel _ (constantCoeff_Ppoly_ne m)

/-! ## `Formula.lean` 中的 `E` 就是 `∏ b_v^{-1}` 的系数 -/

/-- 辅助引理（T1.5(2)）：`b_v · Σ_n E(v::l, n) xⁿ = Σ_n E(l, n) xⁿ`（由 `E_cons`）。 -/
theorem bser_mul_mkE (v : ℕ) (l : List ℕ) :
    bser v * PowerSeries.mk (fun n => (E (v :: l) n : ℚ)) =
      PowerSeries.mk (fun n => (E l n : ℚ)) := by
  ext n
  rw [bser, coe_bpoly, coeff_b_mul]
  simp only [PowerSeries.coeff_mk]
  have h := E_cons v l n
  by_cases h1 : 1 ≤ n <;> by_cases h3 : 3 ≤ n <;> simp only [h1, h3, ↓reduceIte] at h ⊢ <;>
    rw [h] <;> push_cast <;> ring

/-- 辅助引理（T1.5(2)）：`Σ_n E([], n) xⁿ = 1`。 -/
theorem mkE_nil : PowerSeries.mk (fun n => (E [] n : ℚ)) = 1 := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, E_nil]
  split_ifs <;> simp

/-- 辅助引理（T1.5(2)）：`(Σ_n E(l, n) xⁿ) · ∏_{v∈l} b_v = 1`。 -/
theorem mkE_mul_prod (l : List ℕ) :
    PowerSeries.mk (fun n => (E l n : ℚ)) * (l.map bser).prod = 1 := by
  induction l with
  | nil => simp [mkE_nil]
  | cons v l ih =>
    calc PowerSeries.mk (fun n => (E (v :: l) n : ℚ)) * ((v :: l).map bser).prod
        = (bser v * PowerSeries.mk (fun n => (E (v :: l) n : ℚ))) * (l.map bser).prod := by
          rw [List.map_cons, List.prod_cons]; ring
      _ = 1 := by rw [bser_mul_mkE, ih]

/-- 辅助引理（T1.5(2)、T2.5(2)）：`vars j m = [m, m−1, …, j]` 上的乘积就是 `∏_{i=j}^{m}`。 -/
theorem prod_vars {M : Type*} [CommMonoid M] (f : ℕ → M) {j m : ℕ} (h : j ≤ m + 1) :
    ((vars j m).map f).prod = ∏ i ∈ Icc j m, f i := by
  induction m with
  | zero =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
    · simp [vars]
    · simp [vars]
  | succ m ih =>
    by_cases hj : j ≤ m + 1
    · rw [vars_succ hj, List.map_cons, List.prod_cons, ih hj, prod_Icc_succ_top hj, mul_comm]
    · obtain rfl : j = m + 1 + 1 := by omega
      rw [vars_self_succ (m + 1), Finset.Icc_eq_empty (by omega)]
      simp

/-- 辅助引理（T1.5(2)、T2.5(2)）：`∏_{v=j}^{m} b_v^{-1} = Σ_n E([m,…,j], n) xⁿ`（`j ≤ m+1`）。 -/
theorem prod_Icc_inv_eq_mkE (j m : ℕ) (h : j ≤ m + 1) :
    ∏ i ∈ Icc j m, (bser i)⁻¹ = PowerSeries.mk (fun n => (E (vars j m) n : ℚ)) := by
  refine ps_inv_unique (prod_inv_mul_prod (Icc j m)) ?_
  rw [← prod_vars bser h]
  exact mkE_mul_prod _

/-- 辅助引理（T1.5(2)、T2.5(2)）：`[xⁿ] ∏_{v=j}^{m} b_v^{-1} = E([m,…,j], n)`。 -/
theorem coeff_prod_Icc_inv (j m n : ℕ) (h : j ≤ m + 1) :
    PowerSeries.coeff n (∏ i ∈ Icc j m, (bser i)⁻¹) = (E (vars j m) n : ℚ) := by
  rw [prod_Icc_inv_eq_mkE j m h, PowerSeries.coeff_mk]

/-- 辅助引理（T1.5(2)、T2.5(1)）：把 `E([m,…,j], n)` 写成 `H(m,s,j)·C(n+m−j−2s, m−j+s)` 之和
（`j ≤ m`；求和范围 `3s ≤ n` 恰是使二项式非零的 `s`）。 -/
theorem E_vars_eq (j m n : ℕ) (h : j ≤ m) :
    E (vars j m) n = ∑ s ∈ range (n / 3 + 1),
      hc s (vars j m) * (n + m - j - 2 * s).choose (m - j + s) := by
  unfold E
  apply sum_congr rfl
  intro s hs
  rw [mem_range] at hs
  have h3 : 3 * s ≤ n := by omega
  simp only [g, h3, ↓reduceIte, length_vars (show j ≤ m + 1 by omega), Nat.multichoose_eq]
  congr 1
  rw [show m + 1 - j + s + (n - 3 * s) - 1 = n + m - j - 2 * s by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- 辅助引理（T2.5(2)）：`E([m,…,m−t], n) = Σ_s H(m,s,m−t)·C(n+t−2s, n−3s)`（`t ≤ m`）。 -/
theorem E_vars_sub_eq (t m n : ℕ) (h : t ≤ m) :
    E (vars (m - t) m) n = ∑ s ∈ range (n / 3 + 1),
      hc s (vars (m - t) m) * (n + t - 2 * s).choose (n - 3 * s) := by
  unfold E
  apply sum_congr rfl
  intro s hs
  rw [mem_range] at hs
  have h3 : 3 * s ≤ n := by omega
  simp only [g, h3, ↓reduceIte, length_vars (show m - t ≤ m + 1 by omega), Nat.multichoose_eq]
  congr 2
  omega

/-! ## T1.5(1)：`c_i(n)` 的显式式 -/

/-- 辅助引理（T1.5(1)）：`h_s(i) = i^s`。 -/
theorem hc_single (i s : ℕ) : hc s [i] = i ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [hc_succ_cons, ih, hc_succ_nil, zero_add, pow_succ, mul_comm]

/-- 辅助引理（T1.5(1)）：`1/b_i = Σ_n E([i], n) xⁿ`。 -/
theorem inv_bser_eq_mkE (i : ℕ) : (bser i)⁻¹ = PowerSeries.mk (fun n => (E [i] n : ℚ)) := by
  refine ps_inv_unique (inv_mul_bser i) ?_
  simpa using mkE_mul_prod [i]

/-- **T1.5(1)**：`c_i(n) = [xⁿ] 1/b_i = Σ_{0≤j≤n/3} C(n−2j, j)·i^j`（`0^0 = 1`，故 `c_0 ≡ 1`）。 -/
theorem ci_formula (i n : ℕ) :
    ci i n = ∑ j ∈ range (n / 3 + 1), ((n - 2 * j).choose j : ℚ) * (i : ℚ) ^ j := by
  rw [ci, inv_bser_eq_mkE, PowerSeries.coeff_mk, E, Nat.cast_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have h3 : 3 * j ≤ n := by omega
  have hm : Nat.multichoose ([i].length + j) (n - 3 * j) = (n - 2 * j).choose j := by
    rw [Nat.multichoose_eq, List.length_singleton,
      show 1 + j + (n - 3 * j) - 1 = n - 2 * j by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  simp only [g, h3, ↓reduceIte, hc_single, hm]
  push_cast
  ring

/-- 辅助引理（T2.5(3) 的推论）：`c_0(n) = 1`。 -/
theorem ci_zero (n : ℕ) : ci 0 n = 1 := by
  rw [ci_formula, sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    simp at h

/-! ## T1.5(2)：Stirling 型公式 -/

/-- **T1.5(2)**：`[xⁿ] 1/P_m = Σ_s S(m+s, m)·C(n+m−2s, m+s)`，求和按二项式约定截断：
`s` 取遍使 `C(n+m−2s, m+s)` 非零的值，即 `0 ≤ s ≤ n/3`。 -/
theorem coeff_inv_Ppoly (m n : ℕ) :
    PowerSeries.coeff n (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ =
      ∑ s ∈ range (n / 3 + 1),
        (Nat.stirlingSecond (m + s) m : ℚ) * ((n + m - 2 * s).choose (m + s) : ℚ) := by
  rw [Ppoly_inv_eq_prod, coeff_prod_Icc_inv 0 m n (Nat.zero_le _),
    E_vars_eq 0 m n (Nat.zero_le _), Nat.cast_sum]
  apply sum_congr rfl
  intro s _
  rw [hc_vars_zero]
  simp only [Nat.sub_zero, Nat.cast_mul]

/-! ## 有限差分恒等式（T1.5(3)(4) 与 T2.5(3) 的共同基础） -/

/-- 辅助引理（T1.5(3)(4)）：`f(i) = b_i^{-1}` 的 `t` 阶前向差分
`Δ^t f(a) = t!·x^{3t}·∏_{j=0}^{t} b_{a+j}^{-1}`（对 `t` 归纳，用 `b_a − b_{a+t+1} = (t+1)x³`）。 -/
theorem fwdDiff_iter_bser_inv (t a : ℕ) :
    (fwdDiff 1)^[t] (fun i => (bser i)⁻¹) a =
      (t.factorial : PowerSeries ℚ) * PowerSeries.X ^ (3 * t) *
        ∏ j ∈ range (t + 1), (bser (a + j))⁻¹ := by
  induction t generalizing a with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    show (fwdDiff 1)^[t] (fun i => (bser i)⁻¹) (a + 1) -
      (fwdDiff 1)^[t] (fun i => (bser i)⁻¹) a = _
    rw [ih (a + 1), ih a]
    have hA1 : ∏ j ∈ range (t + 1), (bser (a + 1 + j))⁻¹ =
        bser a * ∏ j ∈ range (t + 1 + 1), (bser (a + j))⁻¹ := by
      rw [prod_range_succ' _ (t + 1), add_zero,
        show (∏ j ∈ range (t + 1), (bser (a + 1 + j))⁻¹) =
          ∏ j ∈ range (t + 1), (bser (a + (j + 1)))⁻¹ from
          prod_congr rfl fun j _ => by rw [show a + 1 + j = a + (j + 1) by omega]]
      rw [mul_left_comm, bser_mul_inv, mul_one]
    have hA2 : ∏ j ∈ range (t + 1), (bser (a + j))⁻¹ =
        bser (a + (t + 1)) * ∏ j ∈ range (t + 1 + 1), (bser (a + j))⁻¹ := by
      rw [prod_range_succ _ (t + 1), mul_left_comm, bser_mul_inv, mul_one]
    have hb : bser a - bser (a + (t + 1)) = ((t : PowerSeries ℚ) + 1) * PowerSeries.X ^ 3 := by
      rw [bser_eq, bser_eq]; push_cast; ring
    rw [hA1, hA2, Nat.factorial_succ]
    push_cast
    linear_combination ((t.factorial : PowerSeries ℚ) * PowerSeries.X ^ (3 * t) *
      ∏ j ∈ range (t + 1 + 1), (bser (a + j))⁻¹) * hb

/-- 辅助引理（T1.5(3)(4)）：`Σ_{k=0}^{t} (−1)^{t−k} C(t,k)·b_{a+k}^{-1} = t!·x^{3t}·∏_{j=0}^{t} b_{a+j}^{-1}`
（节点 `a, …, a+t` 的部分分式）。 -/
theorem alt_sum_bser_inv (t a : ℕ) :
    ∑ k ∈ range (t + 1), (((-1 : ℤ) ^ (t - k) * (t.choose k : ℤ) : ℤ) : PowerSeries ℚ) *
        (bser (a + k))⁻¹ =
      (t.factorial : PowerSeries ℚ) * PowerSeries.X ^ (3 * t) *
        ∏ j ∈ range (t + 1), (bser (a + j))⁻¹ := by
  rw [← fwdDiff_iter_bser_inv, fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro k _
  rw [zsmul_eq_mul, smul_eq_mul, mul_one]

/-- 辅助引理（T1.5(3)(4)）：上式取 `x^{n+3t}` 的系数。 -/
theorem alt_sum_ci (t a n : ℕ) :
    ∑ k ∈ range (t + 1), (-1 : ℚ) ^ (t - k) * (t.choose k : ℚ) * ci (a + k) (n + 3 * t) =
      (t.factorial : ℚ) * PowerSeries.coeff n (∏ j ∈ range (t + 1), (bser (a + j))⁻¹) := by
  have h := congrArg (PowerSeries.coeff (n + 3 * t)) (alt_sum_bser_inv t a)
  rw [map_sum, mul_assoc, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X_pow_mul] at h
  rw [← h]
  apply sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_intCast_mul, ci]
  push_cast
  ring

/-- 辅助引理（T1.5(3)）：`N < 3t` 时 `Σ_{k=0}^{t} (−1)^{t−k} C(t,k)·c_{a+k}(N) = 0`
（c1.md §6.3 的附带结论取 `a = 0, t = m`）。 -/
theorem alt_sum_ci_eq_zero (t a N : ℕ) (hN : N < 3 * t) :
    ∑ k ∈ range (t + 1), (-1 : ℚ) ^ (t - k) * (t.choose k : ℚ) * ci (a + k) N = 0 := by
  have h := congrArg (PowerSeries.coeff N) (alt_sum_bser_inv t a)
  rw [map_sum, mul_assoc, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X_pow_mul'] at h
  simp only [show ¬ (3 * t ≤ N) by omega, ↓reduceIte, mul_zero] at h
  rw [← h]
  apply sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_intCast_mul, ci]
  push_cast
  ring

/-! ## T1.5(3)：部分分式公式 -/

/-- **T1.5(3)**：`m!·[xⁿ] 1/P_m = Σ_{i=0}^{m} (−1)^{m−i}·C(m,i)·c_i(n+3m)`。 -/
theorem factorial_mul_coeff_inv_Ppoly (m n : ℕ) :
    (m.factorial : ℚ) * PowerSeries.coeff n (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ =
      ∑ i ∈ range (m + 1), (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * ci i (n + 3 * m) := by
  have h := alt_sum_ci m 0 n
  simp only [zero_add] at h
  rw [h, Ppoly_inv_eq_prod, ← Nat.range_succ_eq_Icc_zero]

/-- 辅助引理（T1.5(3)，c1.md §6.3 的附带结论）：`0 ≤ N < 3m` 时
`Σ_{i=0}^{m} (−1)^{m−i}·C(m,i)·c_i(N) = 0`。 -/
theorem alt_sum_ci_vanish (m N : ℕ) (hN : N < 3 * m) :
    ∑ i ∈ range (m + 1), (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * ci i N = 0 := by
  have h := alt_sum_ci_eq_zero m 0 N hN
  simpa only [zero_add] using h

/-! ## T1.5(4)：Θ 公式 -/

/-- **T1.5(4)**（第二部分）：对 `0 ≤ t ≤ m`，`Θ_t(n+3t) = [xⁿ] ∏_{i=m−t}^{m} b_i^{-1}`。 -/
theorem Theta_eq_coeff_prod (m t n : ℕ) (ht : t ≤ m) :
    Theta m t (n + 3 * t) = PowerSeries.coeff n (∏ i ∈ Icc (m - t) m, (bser i)⁻¹) := by
  have hrefl : ∑ r ∈ range (t + 1), (-1 : ℚ) ^ r * (t.choose r : ℚ) * ci (m - r) (n + 3 * t) =
      ∑ k ∈ range (t + 1), (-1 : ℚ) ^ (t - k) * (t.choose k : ℚ) * ci (m - t + k) (n + 3 * t) := by
    rw [← sum_range_reflect
      (fun r => (-1 : ℚ) ^ r * (t.choose r : ℚ) * ci (m - r) (n + 3 * t)) (t + 1)]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [show t + 1 - 1 - k = t - k by omega, Nat.choose_symm (by omega : k ≤ t),
      show m - (t - k) = m - t + k by omega]
  have hprod : ∏ j ∈ range (t + 1), (bser (m - t + j))⁻¹ = ∏ i ∈ Icc (m - t) m, (bser i)⁻¹ := by
    rw [← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range,
      show m + 1 - (m - t) = t + 1 by omega]
  rw [Theta, hrefl, alt_sum_ci t (m - t) n, hprod, ← mul_assoc, one_div_mul_cancel, one_mul]
  exact_mod_cast Nat.factorial_ne_zero t

/-- **T1.5(4)**（第二部分，商的写法）：对 `0 ≤ t ≤ m`，
`Θ_t(n+3t) = [xⁿ] P_{m−t−1}/P_m`，其中 `P_{m−t−1} = ∏_{i<m−t} b_i`（约定 `P_{−1} = 1`）。 -/
theorem Theta_eq_coeff_div (m t n : ℕ) (ht : t ≤ m) :
    Theta m t (n + 3 * t) = PowerSeries.coeff n
      ((↑(∏ i ∈ range (m - t), bpoly ℚ i) : PowerSeries ℚ) *
        (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹) := by
  rw [Theta_eq_coeff_prod m t n ht, coe_prod_range_mul_Ppoly_inv (m - t) m (by omega)]

/-- **T1.5(4)**（第二部分，`t < m` 时直接用 `Ppoly`）：`Θ_t(n+3t) = [xⁿ] P_{m−t−1}/P_m`。 -/
theorem Theta_eq_coeff_Ppoly_div (m t n : ℕ) (ht : t < m) :
    Theta m t (n + 3 * t) = PowerSeries.coeff n
      ((↑(Ppoly ℚ (m - t - 1)) : PowerSeries ℚ) * (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹) := by
  have e : Ppoly ℚ (m - t - 1) = ∏ i ∈ range (m - t), bpoly ℚ i := by
    rw [Ppoly, show m - t - 1 + 1 = m - t by omega]
  rw [e, Theta_eq_coeff_div m t n ht.le]

/-- 辅助引理（T1.5(4)、T2.5(1)）：`x·G_m = 1/P_m − 1 − x·Σ_{j<m} P_j/P_m`
（由 `X_mul_W` 与 `P_mul_G`，即 T1.3(1) 的闭式）。 -/
theorem X_mul_Gser (m : ℕ) :
    PowerSeries.X * Gser m = (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ - 1 -
      PowerSeries.X * ∑ j ∈ range m,
        (↑(Ppoly ℚ j) : PowerSeries ℚ) * (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ := by
  have hc := constantCoeff_Ppoly_ne m
  have hW : PowerSeries.X * (↑(Wpoly ℚ m) : PowerSeries ℚ) =
      1 - (↑(Ppoly ℚ m) : PowerSeries ℚ) -
        PowerSeries.X * ∑ j ∈ range m, (↑(Ppoly ℚ j) : PowerSeries ℚ) := by
    have h := congrArg (fun p : Polynomial ℚ => (↑p : PowerSeries ℚ)) (X_mul_W ℚ m)
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
      psCoe_sum] at h
    exact h
  have hG : Gser m = (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ * (↑(Wpoly ℚ m) : PowerSeries ℚ) := by
    rw [← P_mul_G m, ← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul]
  have hinv : (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ * (↑(Ppoly ℚ m) : PowerSeries ℚ) = 1 :=
    PowerSeries.inv_mul_cancel _ hc
  rw [hG, ← sum_mul]
  linear_combination (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ * hW - hinv

/-- 辅助引理（T1.5(4)、T2.5(1)，「F3 外层」）：对一切 `k ≥ 0`，
`U_k(m) = [x^{k+1}] 1/P_m − Σ_{j=1}^{m} [x^k] ∏_{i=j}^{m} b_i^{-1}`（这里 `j` 记为 `j+1`）。 -/
theorem U_eq_outer (k m : ℕ) :
    (U k m : ℚ) = PowerSeries.coeff (k + 1) (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ -
      ∑ j ∈ range m, PowerSeries.coeff k (∏ i ∈ Icc (j + 1) m, (bser i)⁻¹) := by
  have h := congrArg (PowerSeries.coeff (k + 1)) (X_mul_Gser m)
  rw [PowerSeries.coeff_succ_X_mul, coeff_Gser, map_sub, map_sub, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_one, map_sum] at h
  simp only [show k + 1 ≠ 0 from Nat.succ_ne_zero k, ↓reduceIte, sub_zero] at h
  rw [h]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [← coe_prod_range_mul_Ppoly_inv (j + 1) m (by omega)]
  rfl

/-- **T1.5(4)**（Θ 公式）：对一切 `k ≥ 0`（报告：提示词写 `k ≥ 1`，`k = 0` 也成立），
`U_k(m) = Θ_m(k+1+3m) − Σ_{t=0}^{m−1} Θ_t(k+3t)`。 -/
theorem U_eq_Theta (k m : ℕ) :
    (U k m : ℚ) = Theta m m (k + 1 + 3 * m) - ∑ t ∈ range m, Theta m t (k + 3 * t) := by
  rw [U_eq_outer, Theta_eq_coeff_prod m m (k + 1) le_rfl, Nat.sub_self, ← Ppoly_inv_eq_prod]
  congr 1
  rw [← sum_range_reflect (fun t => Theta m t (k + 3 * t)) m]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [Theta_eq_coeff_prod m (m - 1 - j) k (by omega), show m - (m - 1 - j) = j + 1 by omega]

/-! ## T1.5 注：求和范围必须按二项式约定截断 -/

/-- 辅助引理（T1.5 注）：广义二项式系数 `C(−1, 2) = 1`（`Ring.choose` 是 Mathlib 的广义二项式，
即多项式 `C(y,b) = y(y−1)⋯(y−b+1)/b!` 在 `ℤ` 上的取值）。 -/
theorem ringChoose_neg_one_two : Ring.choose (-1 : ℤ) 2 = 1 := by
  have h := Ring.choose_succ_succ (-1 : ℤ) 1
  rw [show (-1 : ℤ) + 1 = 0 by norm_num, Ring.choose_zero_succ, Ring.choose_one_right] at h
  have h2 : Ring.choose (-1 : ℤ) (1 + 1) = Ring.choose (-1 : ℤ) 2 := rfl
  rw [h2] at h
  linarith

/-- **T1.5 注**（反例一）：若把 T1.5(2) 的 `Σ_s` 按广义二项式求和到 `n/3` 之外，公式错误。
`m = 1, n = 0`：`s = 1` 项 `S(2,1)·C(−1,2) = 1 ≠ 0`；对 `s = 0, 1` 求和得 `2`，而真值
`[x⁰] 1/P_1 = 1`（按约定截断时只有 `s = 0` 项）。 -/
theorem T15_note_P :
    (Nat.stirlingSecond 2 1 : ℤ) * Ring.choose ((0 : ℤ) + 1 - 2 * 1) (1 + 1) = 1 ∧
    (∑ s ∈ range 2,
      (Nat.stirlingSecond (1 + s) 1 : ℤ) * Ring.choose ((0 : ℤ) + 1 - 2 * (s : ℤ)) (1 + s)) = 2 ∧
    PowerSeries.coeff 0 (↑(Ppoly ℚ 1) : PowerSeries ℚ)⁻¹ = 1 := by
  have hS2 : Nat.stirlingSecond 2 1 = 1 := Nat.stirlingSecond_one_right 1
  have hS1 : Nat.stirlingSecond 1 1 = 1 := Nat.stirlingSecond_self 1
  refine ⟨?_, ?_, ?_⟩
  · rw [hS2, show (0 : ℤ) + 1 - 2 * 1 = -1 by norm_num, show (1 + 1 : ℕ) = 2 from rfl,
      ringChoose_neg_one_two]
    norm_num
  · rw [sum_range_succ, sum_range_one]
    rw [show (0 : ℤ) + 1 - 2 * ((0 : ℕ) : ℤ) = 1 by norm_num,
      show (0 : ℤ) + 1 - 2 * ((1 : ℕ) : ℤ) = -1 by norm_num, show (1 + 0 : ℕ) = 1 from rfl,
      show (1 + 1 : ℕ) = 2 from rfl, hS1, hS2, ringChoose_neg_one_two, Ring.choose_one_right]
    norm_num
  · rw [coeff_inv_Ppoly]
    simp [hS1]

/-- **T1.5 注**（反例二）：若把 T1.5(1) 的 `Σ_j` 按广义二项式求和到 `j ≤ n`，公式错误：
`n = 1, i = 5` 时 `Σ_{j=0}^{1} C(1−2j, j)·5^j = 1 − 5 = −4`，而真值 `c_5(1) = 1`。 -/
theorem T15_note_c :
    (∑ j ∈ range 2, Ring.choose ((1 : ℤ) - 2 * (j : ℤ)) j * (5 : ℤ) ^ j) = -4 ∧ ci 5 1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [sum_range_succ, sum_range_one]
    rw [show (1 : ℤ) - 2 * ((0 : ℕ) : ℤ) = 1 by norm_num,
      show (1 : ℤ) - 2 * ((1 : ℕ) : ℤ) = -1 by norm_num, Ring.choose_zero_right,
      Ring.choose_one_right]
    norm_num
  · rw [ci_formula]
    simp

/-! ## T2.5(1)：F3 型 -/

/-- 辅助引理（T2.5(1)）：F3 型在 `ℚ` 中的形式。 -/
theorem U_F3_rat (k m : ℕ) :
    (U k m : ℚ) = (∑ s ∈ range ((k + 1) / 3 + 1),
        (Nat.stirlingSecond (m + s) m : ℚ) * ((k + 1 + m - 2 * s).choose (m + s) : ℚ)) -
      ∑ j ∈ Icc 1 m, ∑ s ∈ range (k / 3 + 1),
        (hc s (vars j m) : ℚ) * ((k + m - j - 2 * s).choose (m - j + s) : ℚ) := by
  rw [U_eq_outer, coeff_inv_Ppoly]
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [coeff_prod_Icc_inv (j + 1) m k (by omega), E_vars_eq (j + 1) m k (by omega), Nat.cast_sum,
    show 1 + j = j + 1 by ring]
  push_cast
  rfl

/-- **T2.5(1)**（F3 型，单和减双和；整数减法）：对一切 `k, m ≥ 0`，
`U_k(m) = Σ_s S(m+s,m)·C(k+1+m−2s, m+s) − Σ_{j=1}^{m} Σ_s H(m,s,j)·C(k+m−j−2s, m−j+s)`，
其中 `H(m,s,j) = hc s (vars j m) = h_s(j,…,m)`；两个 `Σ_s` 都按二项式约定截断
（分别是 `3s ≤ k+1` 与 `3s ≤ k`）。 -/
theorem U_F3 (k m : ℕ) :
    (U k m : ℤ) = (∑ s ∈ range ((k + 1) / 3 + 1),
        (Nat.stirlingSecond (m + s) m : ℤ) * ((k + 1 + m - 2 * s).choose (m + s) : ℤ)) -
      ∑ j ∈ Icc 1 m, ∑ s ∈ range (k / 3 + 1),
        (hc s (vars j m) : ℤ) * ((k + m - j - 2 * s).choose (m - j + s) : ℤ) := by
  have h := U_F3_rat k m
  apply Int.cast_injective (α := ℚ)
  push_cast
  exact h

/-- **T2.5(1)**（F3 型，移项后的自然数等式）。 -/
theorem U_F3_nat (k m : ℕ) :
    U k m + ∑ j ∈ Icc 1 m, ∑ s ∈ range (k / 3 + 1),
        hc s (vars j m) * (k + m - j - 2 * s).choose (m - j + s) =
      ∑ s ∈ range ((k + 1) / 3 + 1),
        Nat.stirlingSecond (m + s) m * (k + 1 + m - 2 * s).choose (m + s) := by
  have h := U_F3 k m
  have h' : ((U k m + ∑ j ∈ Icc 1 m, ∑ s ∈ range (k / 3 + 1),
        hc s (vars j m) * (k + m - j - 2 * s).choose (m - j + s) : ℕ) : ℤ) =
      ((∑ s ∈ range ((k + 1) / 3 + 1),
        Nat.stirlingSecond (m + s) m * (k + 1 + m - 2 * s).choose (m + s) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

/-! ## T2.5(2)：Θ 公式与 F3 型逐项相同 -/

/-- **T2.5(2)**：对 `0 ≤ t ≤ m`，`Θ_t(n+3t) = [xⁿ] ∏_{v=m−t}^{m} b_v^{-1} = Σ_s H(m,s,m−t)·C(n+t−2s, n−3s)`
（`Σ_s` 按二项式约定截断为 `3s ≤ n`）。 -/
theorem Theta_eq_H (m t n : ℕ) (ht : t ≤ m) :
    Theta m t (n + 3 * t) = ∑ s ∈ range (n / 3 + 1),
      (hc s (vars (m - t) m) : ℚ) * ((n + t - 2 * s).choose (n - 3 * s) : ℚ) := by
  rw [Theta_eq_coeff_prod m t n ht, coeff_prod_Icc_inv (m - t) m n (by omega),
    E_vars_sub_eq t m n ht]
  push_cast
  rfl

/-- **T2.5(2)**（逐项相同，首项）：Θ 公式的首项 `Θ_m(k+1+3m)` 就是 F3 型的单和
`Σ_s S(m+s,m)·C(k+1+m−2s, m+s)`。 -/
theorem Theta_eq_F3_head (m k : ℕ) :
    Theta m m (k + 1 + 3 * m) = ∑ s ∈ range ((k + 1) / 3 + 1),
      (Nat.stirlingSecond (m + s) m : ℚ) * ((k + 1 + m - 2 * s).choose (m + s) : ℚ) := by
  rw [Theta_eq_coeff_prod m m (k + 1) le_rfl, Nat.sub_self, ← Ppoly_inv_eq_prod, coeff_inv_Ppoly]

/-- **T2.5(2)**（逐项相同，其余项）：对 `0 ≤ t < m`，Θ 公式的项 `Θ_t(k+3t)` 就是 F3 型双和中
`j = m−t` 的内层和 `Σ_s H(m,s,j)·C(k+m−j−2s, m−j+s)`。 -/
theorem Theta_eq_F3_term (m t k : ℕ) (ht : t < m) :
    Theta m t (k + 3 * t) = ∑ s ∈ range (k / 3 + 1),
      (hc s (vars (m - t) m) : ℚ) *
        ((k + m - (m - t) - 2 * s).choose (m - (m - t) + s) : ℚ) := by
  rw [Theta_eq_coeff_prod m t k ht.le, coeff_prod_Icc_inv (m - t) m k (by omega),
    E_vars_eq (m - t) m k (by omega)]
  push_cast
  rfl

/-- **T2.5(2)**（反例：Θ 公式与推荐的 H 型只是内层相同，外层不逐项相同）：`m = 1, k = 3` 时
Θ 型两项为 `Θ_1(7) = 8` 与 `−Θ_0(3) = −2`（`U_eq_Theta`），H 型两项（`U_explicit` 的两个被加项）为
`5` 与 `1`，两种写法的和都是 `U_3(1) = 6`。 -/
theorem Theta_vs_H_example :
    Theta 1 1 (3 + 1 + 3 * 1) = 8 ∧ Theta 1 0 (3 + 3 * 0) = 2 ∧
    (∑ s ∈ range (3 / 3 + 1),
      Nat.stirlingSecond (1 + s) 1 * (3 + 1 - 2 * s).choose (3 - 3 * s)) = 5 ∧
    (∑ j ∈ Icc 1 1, j * ∑ s ∈ range ((3 - 2) / 3 + 1),
      hc s (vars j 1) * (3 - 2 + 1 - j - 2 * s).choose (3 - 2 - 3 * s)) = 1 ∧
    (U 3 1 : ℚ) = Theta 1 1 (3 + 1 + 3 * 1) - Theta 1 0 (3 + 3 * 0) ∧
    U 3 1 = 5 + 1 := by
  have hT1 : Theta 1 1 (3 + 1 + 3 * 1) = 8 := by
    rw [Theta_eq_F3_head 1 3]
    have h : (∑ s ∈ range ((3 + 1) / 3 + 1),
        Nat.stirlingSecond (1 + s) 1 * (3 + 1 + 1 - 2 * s).choose (1 + s)) = 8 := by decide
    exact_mod_cast h
  -- `hc` 由良基递归定义，不交给 `decide`；先把 `vars 1 1` 与 `h_s(1)` 化简掉。
  have hv : vars 1 1 = [1] := by simp [vars]
  have hT0 : Theta 1 0 (3 + 3 * 0) = 2 := by
    rw [Theta_eq_F3_term 1 0 3 (by norm_num)]
    norm_num [sum_range_succ, hv, hc_single]
  have hH1 : (∑ s ∈ range (3 / 3 + 1),
      Nat.stirlingSecond (1 + s) 1 * (3 + 1 - 2 * s).choose (3 - 3 * s)) = 5 := by decide
  have hH2 : (∑ j ∈ Icc 1 1, j * ∑ s ∈ range ((3 - 2) / 3 + 1),
      hc s (vars j 1) * (3 - 2 + 1 - j - 2 * s).choose (3 - 2 - 3 * s)) = 1 := by
    norm_num [sum_range_succ, hv, hc_single]
  refine ⟨hT1, hT0, hH1, hH2, ?_, ?_⟩
  · have h := U_eq_Theta 3 1
    rw [sum_range_one] at h
    exact h
  · rw [U_explicit 3 1, hH1]
    simp only [show 2 ≤ 3 by norm_num, ↓reduceIte, hH2]

/-! ## T2.5(3)：`c_i` 偏分式型（F4） -/

/-- 辅助引理（T2.5(3)）：`i^{\underline{j+1}} = i^{\underline j}·(i − j)`（在 `ℚ` 中，含 `j > i` 时两边为 0）。 -/
theorem descFactorial_succ_cast (i j : ℕ) :
    (i.descFactorial (j + 1) : ℚ) = (i.descFactorial j : ℚ) * ((i : ℚ) - j) := by
  rw [Nat.descFactorial_succ]
  by_cases hji : j ≤ i
  · push_cast [Nat.cast_sub hji]
    ring
  · have h0 : i.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

/-- 辅助引理（T2.5(3)）：`P_{j−1} = ∏_{v<j} b_v ≡ i^{\underline j}·x^{3j} (mod b_i)`
（因为 `b_v ≡ (i−v)·x³ (mod b_i)`）。 -/
theorem bpoly_dvd_prod_sub (i j : ℕ) :
    bpoly ℚ i ∣ (∏ v ∈ range j, bpoly ℚ v) -
      Polynomial.C (i.descFactorial j : ℚ) * Polynomial.X ^ (3 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q * bpoly ℚ j + Polynomial.C (i.descFactorial j : ℚ) * Polynomial.X ^ (3 * j), ?_⟩
    have hbj : bpoly ℚ j = bpoly ℚ i + Polynomial.C ((i : ℚ) - j) * Polynomial.X ^ 3 := by
      simp only [bpoly, map_sub]
      ring
    have hP : ∏ v ∈ range j, bpoly ℚ v =
        bpoly ℚ i * q + Polynomial.C (i.descFactorial j : ℚ) * Polynomial.X ^ (3 * j) := by
      rw [← hq]
      ring
    rw [prod_range_succ, hP, descFactorial_succ_cast, map_mul, hbj]
    ring

/-- 辅助引理（T2.5(3)）：`W_m − W̃_i = x²·Σ_{j=1}^{m} j·(P_{j−1} − i^{\underline j}x^{3j})`（`i ≤ m`）。 -/
theorem Wpoly_sub_Wtil (i m : ℕ) (him : i ≤ m) :
    Wpoly ℚ m - Wtil i = Polynomial.X ^ 2 * ∑ j ∈ Icc 1 m, Polynomial.C (j : ℚ) *
      (Ppoly ℚ (j - 1) - Polynomial.C (i.descFactorial j : ℚ) * Polynomial.X ^ (3 * j)) := by
  have hsub : ∑ j ∈ Icc 1 i,
      Polynomial.C ((j : ℚ) * (i.descFactorial j : ℚ)) * Polynomial.X ^ (3 * j + 2) =
      ∑ j ∈ Icc 1 m,
      Polynomial.C ((j : ℚ) * (i.descFactorial j : ℚ)) * Polynomial.X ^ (3 * j + 2) := by
    apply sum_subset
    · intro j hj
      rw [mem_Icc] at hj ⊢
      omega
    · intro j hj hji
      rw [mem_Icc] at hj hji
      have h0 : i.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [h0]
  rw [Wpoly, Wtil, hsub, add_sub_add_left_eq_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  ring

/-- 辅助引理（T2.5(3)）：`W_m ≡ W̃_i (mod b_i)`（`i ≤ m`）。 -/
theorem bpoly_dvd_W_sub_Wtil {i m : ℕ} (him : i ≤ m) : bpoly ℚ i ∣ Wpoly ℚ m - Wtil i := by
  rw [Wpoly_sub_Wtil i m him]
  apply Dvd.dvd.mul_left
  apply dvd_sum
  intro j hj
  rw [mem_Icc] at hj
  apply Dvd.dvd.mul_left
  have e : Ppoly ℚ (j - 1) = ∏ v ∈ range j, bpoly ℚ v := by
    rw [Ppoly, Nat.sub_add_cancel hj.1]
  rw [e]
  exact bpoly_dvd_prod_sub i j

/-- 辅助引理（T2.5(3)）：`W̃_0 = 1`。 -/
theorem Wtil_zero : Wtil 0 = 1 := by
  simp [Wtil]

/-- 辅助引理（T2.5(3)）：`deg W̃_i ≤ 3i + 2`。 -/
theorem natDegree_Wtil_le (i : ℕ) : (Wtil i).natDegree ≤ 3 * i + 2 := by
  unfold Wtil
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  rw [mem_Icc] at hj
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- 辅助引理（T2.5(3)）：`deg(W_m − W̃_i) < 3m + deg b_i`（`i ≤ m`），
所以商 `(W_m − W̃_i)/b_i` 的次数 `< 3m`。 -/
theorem natDegree_W_sub_Wtil_lt {i m : ℕ} (him : i ≤ m) :
    (Wpoly ℚ m - Wtil i).natDegree < 3 * m + (bpoly ℚ i).natDegree := by
  have h1 := Polynomial.natDegree_sub_le (Wpoly ℚ m) (Wtil i)
  have h2 := natDegree_W_le m
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [natDegree_bpoly_zero]
    rw [Wtil_zero] at h1 ⊢
    rw [Polynomial.natDegree_one] at h1
    exact lt_of_le_of_lt h1 (max_lt (by omega) (by omega))
  · rw [natDegree_bpoly hi]
    have h3 := natDegree_Wtil_le i
    exact lt_of_le_of_lt h1 (max_lt (by omega) (by omega))

/-- 辅助引理（T2.5(3)）：`k ≥ 0, i ≤ m` 时 `[x^{k+3m}] W_m/b_i = [x^{k+3m}] W̃_i/b_i`
（`W_m = W̃_i + b_i·Z`，`deg Z < 3m`）。 -/
theorem coeff_W_mul_inv_bser {i m : ℕ} (him : i ≤ m) (k : ℕ) :
    PowerSeries.coeff (k + 3 * m) ((↑(Wpoly ℚ m) : PowerSeries ℚ) * (bser i)⁻¹) =
      PowerSeries.coeff (k + 3 * m) ((↑(Wtil i) : PowerSeries ℚ) * (bser i)⁻¹) := by
  obtain ⟨Z, hZ⟩ := bpoly_dvd_W_sub_Wtil him
  have hW : Wpoly ℚ m = Wtil i + bpoly ℚ i * Z := by
    rw [← hZ]
    ring
  have hZc : Z.coeff (k + 3 * m) = 0 := by
    by_cases hZ0 : Z = 0
    · rw [hZ0, Polynomial.coeff_zero]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hdeg := Polynomial.natDegree_mul (bpoly_ne_zero i) hZ0
      rw [← hZ] at hdeg
      have := natDegree_W_sub_Wtil_lt him
      omega
  have hbZ : (↑(bpoly ℚ i * Z) : PowerSeries ℚ) * (bser i)⁻¹ = (↑Z : PowerSeries ℚ) := by
    rw [Polynomial.coe_mul, mul_comm (↑(bpoly ℚ i) : PowerSeries ℚ), mul_assoc,
      show (↑(bpoly ℚ i) : PowerSeries ℚ) * (bser i)⁻¹ = 1 from bser_mul_inv i, mul_one]
  rw [hW, Polynomial.coe_add, add_mul, hbZ, map_add, Polynomial.coeff_coe, hZc, add_zero]

/-- 辅助引理（T2.5(3)）：`[x^N] W̃_i/b_i = c_i(N) + Σ_{j=1}^{i} j·i^{\underline j}·[3j+2 ≤ N]·c_i(N−3j−2)`。 -/
theorem coeff_Wtil_mul_inv_bser (i N : ℕ) :
    PowerSeries.coeff N ((↑(Wtil i) : PowerSeries ℚ) * (bser i)⁻¹) =
      ci i N + ∑ j ∈ Icc 1 i, (j : ℚ) * (i.descFactorial j : ℚ) *
        (if 3 * j + 2 ≤ N then ci i (N - (3 * j + 2)) else 0) := by
  have hcoe : (↑(Wtil i) : PowerSeries ℚ) = 1 + ∑ j ∈ Icc 1 i,
      PowerSeries.C ((j : ℚ) * (i.descFactorial j : ℚ)) * PowerSeries.X ^ (3 * j + 2) := by
    rw [Wtil, Polynomial.coe_add, Polynomial.coe_one, psCoe_sum]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  simp only [ci]
  rw [hcoe, add_mul, one_mul, map_add, sum_mul, map_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']

/-- 辅助引理（T2.5(3)）：把截断写法换成「`n < 0` 时 `c_i(n) = 0`」的整数下标写法。 -/
theorem ite_ci_eq_ciZ (i k m j : ℕ) :
    (if 3 * j + 2 ≤ k + 3 * m then ci i (k + 3 * m - (3 * j + 2)) else 0) =
      ciZ i ((k : ℤ) + 3 * m - 3 * j - 2) := by
  unfold ciZ
  by_cases h : 3 * j + 2 ≤ k + 3 * m
  · have h' : (0 : ℤ) ≤ (k : ℤ) + 3 * m - 3 * j - 2 := by omega
    simp only [h, h', ↓reduceIte]
    congr 1
    omega
  · have h' : ¬ ((0 : ℤ) ≤ (k : ℤ) + 3 * m - 3 * j - 2) := by omega
    simp only [h, h', ↓reduceIte]

/-- **T2.5(3)**（`c_i` 偏分式型，只除一次 `m!`）：对一切 `k, m ≥ 0`，
`m!·U_k(m) = Σ_{i=0}^{m} (−1)^{m−i}·C(m,i)·[c_i(k+3m) + Σ_{j=1}^{i} j·i^{\underline j}·c_i(k+3m−3j−2)]`，
其中 `n < 0` 时 `c_i(n) = 0`（`ciZ`）。 -/
theorem U_F4 (k m : ℕ) :
    (m.factorial : ℚ) * (U k m : ℚ) = ∑ i ∈ range (m + 1), (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) *
      (ci i (k + 3 * m) + ∑ j ∈ Icc 1 i,
        (j : ℚ) * (i.descFactorial j : ℚ) * ciZ i ((k : ℤ) + 3 * m - 3 * j - 2)) := by
  have hser := alt_sum_bser_inv m 0
  simp only [zero_add] at hser
  have hP : ∏ j ∈ range (m + 1), (bser j)⁻¹ = (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ := by
    rw [Ppoly_inv_eq_prod, Nat.range_succ_eq_Icc_zero]
  have hG : (↑(Wpoly ℚ m) : PowerSeries ℚ) * (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ = Gser m := by
    rw [← P_mul_G m, mul_comm, ← mul_assoc,
      PowerSeries.inv_mul_cancel _ (constantCoeff_Ppoly_ne m), one_mul]
  have key : ∑ i ∈ range (m + 1), (((-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) : ℤ) : PowerSeries ℚ) *
        ((↑(Wpoly ℚ m) : PowerSeries ℚ) * (bser i)⁻¹) =
      (m.factorial : PowerSeries ℚ) * (PowerSeries.X ^ (3 * m) * Gser m) := by
    calc _ = (↑(Wpoly ℚ m) : PowerSeries ℚ) * ∑ i ∈ range (m + 1),
          (((-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) : ℤ) : PowerSeries ℚ) * (bser i)⁻¹ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i _
          ring
      _ = _ := by
          rw [hser, hP, ← hG]
          ring
  have h2 := congrArg (PowerSeries.coeff (k + 3 * m)) key
  rw [map_sum, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X_pow_mul, coeff_Gser] at h2
  rw [← h2]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [PowerSeries.coeff_intCast_mul, coeff_W_mul_inv_bser (by omega : i ≤ m) k,
    coeff_Wtil_mul_inv_bser]
  push_cast
  congr 2
  apply sum_congr rfl
  intro j _
  rw [ite_ci_eq_ciZ]

/-- **T2.5(3)**（推论）：`R_k := U_k(1) = c_1(k+3) + c_1(k−2) − 1`，其中 `n < 0` 时 `c_1(n) = 0`。 -/
theorem R_formula (k : ℕ) : (U k 1 : ℚ) = ci 1 (k + 3) + ciZ 1 ((k : ℤ) - 2) - 1 := by
  have h := U_F4 k 1
  simp [sum_range_succ, ci_zero] at h
  linarith

/-- **T2.5(3)**（推论，`k ≥ 2`）：`R_k = c_1(k+3) + c_1(k−2) − 1`（自然数下标）。 -/
theorem R_formula_of_two_le (k : ℕ) (hk : 2 ≤ k) :
    (U k 1 : ℚ) = ci 1 (k + 3) + ci 1 (k - 2) - 1 := by
  rw [R_formula, ciZ]
  have h' : (0 : ℤ) ≤ (k : ℤ) - 2 := by omega
  simp only [h', ↓reduceIte]
  congr 3
  omega

/-- **T2.5(3)**（推论，`k < 2`）：此时 `c_1(k−2)` 的下标为负、按约定取 `0`，`R_k = c_1(k+3) − 1`。 -/
theorem R_formula_of_lt_two (k : ℕ) (hk : k < 2) : (U k 1 : ℚ) = ci 1 (k + 3) - 1 := by
  rw [R_formula, ciZ]
  have h' : ¬ ((0 : ℤ) ≤ (k : ℤ) - 2) := by omega
  simp only [h', ↓reduceIte, add_zero]

end A207123
