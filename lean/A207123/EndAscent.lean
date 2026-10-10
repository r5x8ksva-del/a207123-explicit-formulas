import A207123.Ascent
import A207123.Recurrence

/-!
# 论文注记 5.2：不以上升结尾的序列与 `₁F₁`

论文定理 4.4 之后说：第二式的第一项 `1/P_m` 计数不以上升结尾的序列。注记 5.2：取 `λ = (1 − x)/x³`，在
`ℚ(x)[[t]]` 中 `Σ_{m≥0} tᵐ/P_m = (1/(1 − x))·₁F₁(1; 1 − λ; −t/x³)`，而 `xᵏtᵐ` 的系数是 `H_k(m)` 中不以上升结尾的
序列个数。

* `endsAsc`：以上升结尾（最后两项 `x < y`）；`NA k m`：`H_k(m)` 中不以上升结尾的序列个数；
  `NAser m = Σ_k NA k m xᵏ`。
* `P_mul_NAser`：`P_m·Σ_k NA k m xᵏ = 1`，即 `1/P_m` 的 `xᵏ` 系数是 `NA k m`。证明照引理 1：按最大值首次出现的位置
  分类（`L_split` 等）；截断块 `[a, m]` 以上升结尾，所以没有 `m·x²` 项。
* `hyp1F1 a b z = Σ_n (a)_n/(b)_n·zⁿ/n!·tⁿ`（Kummer 合流超几何级数，`(a)_n` 是升阶乘 `ascPochhammer`）。
* `sum_inv_P_eq_hyp1F1`：域 `K` 中（`n! ≠ 0`），`x ≠ 0` 且各 `b_i(x) ≠ 0` 时
  `Σ_m tᵐ/P_m(x) = (1 − x)⁻¹·₁F₁(1; 1 − λ; −1/x³·t)`；`remark_1F1` 取 `K = ℚ(x)`、`x = X`。
  证明：`(1 − λ)_n = Π_{i=1}^{n} (i − λ) = (−1)ⁿ·(x³)^{−n}·Π_{i=1}^{n} b_i(x)`，`(1)_n = n!`。
-/

open Finset

namespace A207123

/-- 以上升结尾：最后两项 `x < y`（即 `h_{k−1} < h_k`）。 -/
def endsAsc : List ℕ → Bool
  | [x, y] => decide (x < y)
  | _ :: b :: c :: t => endsAsc (b :: c :: t)
  | _ => false

/-- 辅助引理（注记 5.2）：首项是后面各项的上界时，去掉它不改变是否以上升结尾。 -/
theorem endsAsc_cons_of_le {M : ℕ} {t : List ℕ} (ht : ∀ x ∈ t, x ≤ M) :
    endsAsc (M :: t) = endsAsc t := by
  match t, ht with
  | [], _ => rfl
  | [x], ht =>
    have hx : x ≤ M := ht x (by simp)
    simp [endsAsc, hx]
  | _ :: _ :: _, _ => rfl

/-- 辅助引理（注记 5.2）：`a :: M :: M :: t`（`t` 的项都 ≤ `M`）与 `t` 同时以上升结尾或都不。 -/
theorem endsAsc_third (a : ℕ) {M : ℕ} {t : List ℕ} (ht : ∀ x ∈ t, x ≤ M) :
    endsAsc (a :: M :: M :: t) = endsAsc t := by
  have hMt : ∀ x ∈ M :: t, x ≤ M := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact ht x hx
  show endsAsc (M :: M :: t) = endsAsc t
  rw [endsAsc_cons_of_le hMt, endsAsc_cons_of_le ht]

/-- 辅助引理（注记 5.2）：全零序列不以上升结尾。 -/
theorem endsAsc_replicate_zero (k : ℕ) : endsAsc (List.replicate k 0) = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,
      endsAsc_cons_of_le (M := 0) (t := List.replicate k 0) (fun x hx => (List.eq_of_mem_replicate hx).le), ih]

/-- `H_k(m)` 中不以上升结尾的序列个数。 -/
def NA (k m : ℕ) : ℕ := ((L k m).filter fun l => endsAsc l = false).card

/-- 辅助引理（注记 5.2）：第二部分 `(m+1) :: w`。 -/
theorem NA_cons_max (k m : ℕ) :
    (((L k (m + 1)).image (List.cons (m + 1))).filter fun l => endsAsc l = false).card
      = NA k (m + 1) := by
  rw [filter_image, card_image_of_injective _ List.cons_injective]
  unfold NA
  congr 1
  apply filter_congr
  intro w hw
  rw [endsAsc_cons_of_le (mem_L.mp hw).2.1]

/-- 辅助引理（注记 5.2）：第三部分 `a :: (m+1) :: (m+1) :: t`（`a ≤ m`）。 -/
theorem NA_third (k m : ℕ) :
    ((((range (m + 1)) ×ˢ (L k (m + 1))).image
        (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2)).filter
          fun l => endsAsc l = false).card = (m + 1) * NA k (m + 1) := by
  rw [filter_image, card_image_of_injective _ (L_split_inj m)]
  have h : ∀ p ∈ (range (m + 1)) ×ˢ (L k (m + 1)),
      endsAsc (p.1 :: (m + 1) :: (m + 1) :: p.2) = false ↔ endsAsc p.2 = false := by
    intro p hp
    rw [mem_product, mem_range, mem_L] at hp
    rw [endsAsc_third p.1 hp.2.2.1]
  rw [filter_congr h, filter_product_right (fun t => endsAsc t = false), card_product, card_range]
  rfl

/-- 辅助引理（注记 5.2，k ≥ 3）：`NA` 满足引理 1 的递推。 -/
theorem NA_split (k m : ℕ) :
    NA (k + 3) (m + 1) = NA (k + 3) m + NA (k + 2) (m + 1) + (m + 1) * NA k (m + 1) := by
  obtain ⟨hAB, hAC, hBC⟩ := L_split_disjoint k m
  show ((L (k + 3) (m + 1)).filter fun l => endsAsc l = false).card = _
  rw [L_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_union_left.mpr ⟨hAC, hBC⟩)),
    filter_union, card_union_of_disjoint (disjoint_filter_filter hAB), NA_cons_max, NA_third]
  rfl

/-- 辅助引理（注记 5.2）：`NA_0(m) = 1`。 -/
theorem NA_zero_left (m : ℕ) : NA 0 m = 1 := by
  have h : endsAsc [] = false := rfl
  simp [NA, L_zero_left, Finset.filter_singleton, h]

/-- 辅助引理（注记 5.2）：`NA_k(0) = 1`。 -/
theorem NA_zero_right (k : ℕ) : NA k 0 = 1 := by
  simp [NA, L_zero_right, Finset.filter_singleton, endsAsc_replicate_zero]

/-- 辅助引理（注记 5.2，k = 1）。 -/
theorem NA_one (m : ℕ) : NA 1 (m + 1) = NA 1 m + NA 0 (m + 1) := by
  show ((L 1 (m + 1)).filter fun l => endsAsc l = false).card = _
  rw [L_one_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_L_cons 1 0 m)), NA_cons_max]
  rfl

/-- 辅助引理（注记 5.2，k = 2）：截断块 `[a, m+1]` 以上升结尾，不计入。 -/
theorem NA_two (m : ℕ) : NA 2 (m + 1) = NA 2 m + NA 1 (m + 1) := by
  have hAC : Disjoint (L 2 m) ((range (m + 1)).image (fun a => [a, m + 1])) := by
    rw [disjoint_left]
    intro l hlA hlC
    rw [mem_L] at hlA
    rw [mem_image] at hlC
    obtain ⟨a, -, rfl⟩ := hlC
    have := hlA.2.1 (m + 1) (by simp)
    omega
  have hBC : Disjoint ((L 1 (m + 1)).image (List.cons (m + 1)))
      ((range (m + 1)).image (fun a => [a, m + 1])) := by
    rw [disjoint_left]
    intro l hlB hlC
    rw [mem_image] at hlB hlC
    obtain ⟨w, -, rfl⟩ := hlB
    obtain ⟨a, ha, hae⟩ := hlC
    rw [mem_range] at ha
    have := (List.cons.inj hae).1
    omega
  have hC : (((range (m + 1)).image (fun a => [a, m + 1])).filter
      fun l => endsAsc l = false) = ∅ := by
    rw [filter_eq_empty_iff]
    intro l hl
    rw [mem_image] at hl
    obtain ⟨a, ha, rfl⟩ := hl
    rw [mem_range] at ha
    simp [endsAsc, ha]
  show ((L 2 (m + 1)).filter fun l => endsAsc l = false).card = _
  rw [L_two_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_union_left.mpr ⟨hAC, hBC⟩)),
    filter_union, card_union_of_disjoint (disjoint_filter_filter (disjoint_L_cons 2 1 m)),
    NA_cons_max, hC, card_empty, add_zero]
  rfl

/-- `Σ_k NA_k(m) xᵏ`。 -/
noncomputable def NAser (m : ℕ) : PowerSeries ℚ := PowerSeries.mk fun k => (NA k m : ℚ)

/-- 辅助引理（注记 5.2）：`NAser m` 的系数。 -/
theorem coeff_NAser (k m : ℕ) : PowerSeries.coeff k (NAser m) = (NA k m : ℚ) := by
  rw [NAser, PowerSeries.coeff_mk]

/-- 辅助引理（注记 5.2）：`(1 − x)·Σ_k NA_k(0) xᵏ = 1`。 -/
theorem NAser_zero : (↑(bpoly ℚ 0) : PowerSeries ℚ) * NAser 0 = 1 := by
  ext k
  rw [coe_bpoly, coeff_b_mul, PowerSeries.coeff_one]
  simp only [coeff_NAser, NA_zero_right, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [ite_eq_left (by omega : 1 ≤ k), ite_eq_right (by omega : k ≠ 0), sub_self]

/-- 辅助引理（注记 5.2）：`(1 − x − (m+1)x³)·Σ_k NA_k(m+1) xᵏ = Σ_k NA_k(m) xᵏ`。 -/
theorem NAser_rec (m : ℕ) :
    (↑(bpoly ℚ (m + 1)) : PowerSeries ℚ) * NAser (m + 1) = NAser m := by
  ext k
  rw [coe_bpoly, coeff_b_mul]
  simp only [coeff_NAser]
  push_cast
  match k with
  | 0 => simp [NA_zero_left]
  | 1 =>
    have h : (NA 1 (m + 1) : ℚ) = NA 1 m + NA 0 (m + 1) := by exact_mod_cast NA_one m
    norm_num
    linear_combination h
  | 2 =>
    have h : (NA 2 (m + 1) : ℚ) = NA 2 m + NA 1 (m + 1) := by exact_mod_cast NA_two m
    norm_num
    linear_combination h
  | k + 3 =>
    have h : (NA (k + 3) (m + 1) : ℚ) =
        NA (k + 3) m + NA (k + 2) (m + 1) + (m + 1) * NA k (m + 1) := by
      exact_mod_cast NA_split k m
    rw [ite_eq_left (by omega : 1 ≤ k + 3), ite_eq_left (by omega : 3 ≤ k + 3),
      show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel]
    linear_combination h

/-- **注记 5.2（组合部分）**：`P_m·Σ_k NA_k(m) xᵏ = 1`，即 `1/P_m` 的 `xᵏ` 系数是 `H_k(m)` 中不以上升结尾的
序列个数。 -/
theorem P_mul_NAser (m : ℕ) : (↑(Ppoly ℚ m) : PowerSeries ℚ) * NAser m = 1 := by
  induction m with
  | zero => rw [Ppoly_zero]; exact NAser_zero
  | succ m ih => rw [Ppoly_succ, Polynomial.coe_mul, mul_assoc, NAser_rec, ih]

/-- Kummer 合流超几何级数（`t` 的形式幂级数）：`₁F₁(a; b; z·t) = Σ_n (a)_n/(b)_n·zⁿ/n!·tⁿ`，
`(a)_n` 是升阶乘。 -/
noncomputable def hyp1F1 {K : Type*} [Field K] (a b z : K) : PowerSeries K :=
  PowerSeries.mk fun n =>
    (ascPochhammer K n).eval a / (ascPochhammer K n).eval b * z ^ n / (n.factorial : K)

/-- 辅助引理（注记 5.2）：`(1 − λ)_n = (−1)ⁿ·(x³)^{−n}·Π_{i=1}^{n} b_i(x)`，`λ = (1 − x)/x³`。 -/
theorem ascPochhammer_one_sub_lambda {K : Type*} [Field K] {x : K} (hx : x ≠ 0) (n : ℕ) :
    (ascPochhammer K n).eval (1 - (1 - x) / x ^ 3) =
      (-1) ^ n * (x ^ 3)⁻¹ ^ n * ∏ i ∈ range n, (bpoly K (i + 1)).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : (bpoly K (n + 1)).eval x = 1 - x - ((n : K) + 1) * x ^ 3 := by
      simp [bpoly]
    have h3 : x ^ 3 * (x ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 3 hx)
    rw [ascPochhammer_succ_eval, ih, prod_range_succ, hbn]
    linear_combination (-((-1) ^ n * (x ^ 3)⁻¹ ^ n * (∏ i ∈ range n, (bpoly K (i + 1)).eval x) *
      ((n : K) + 1))) * h3

/-- 注记 5.2 的一般形式：域 `K` 中 `n! ≠ 0`、`x ≠ 0`、各 `b_i(x) ≠ 0` 时，
`Σ_m tᵐ/P_m(x) = (1 − x)⁻¹·₁F₁(1; 1 − λ; −1/x³·t)`，`λ = (1 − x)/x³`。 -/
theorem sum_inv_P_eq_hyp1F1 {K : Type*} [Field K] [CharZero K] {x : K} (hx : x ≠ 0)
    (hb : ∀ i : ℕ, (bpoly K i).eval x ≠ 0) :
    PowerSeries.mk (fun m => ((Ppoly K m).eval x)⁻¹) =
      PowerSeries.C (1 - x)⁻¹ * hyp1F1 1 (1 - (1 - x) / x ^ 3) (-1 / x ^ 3) := by
  ext n
  have hb0 : (bpoly K 0).eval x = 1 - x := by simp [bpoly]
  have h1x : (1 : K) - x ≠ 0 := by
    rw [← hb0]
    exact hb 0
  have hP : ∏ i ∈ range n, (bpoly K (i + 1)).eval x ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hb (i + 1)
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, hyp1F1, PowerSeries.coeff_mk,
    ascPochhammer_eval_one, ascPochhammer_one_sub_lambda hx, Ppoly, Polynomial.eval_prod,
    prod_range_succ', hb0]
  field_simp
  ring

/-- 辅助引理（注记 5.2）：`b_i(x) ∈ ℚ(x)` 就是多项式 `b_i` 的像。 -/
theorem eval_bpoly_ratFunc (i : ℕ) :
    (bpoly (RatFunc ℚ) i).eval RatFunc.X = algebraMap (Polynomial ℚ) (RatFunc ℚ) (bpoly ℚ i) := by
  simp [bpoly, RatFunc.algebraMap_X]

/-- **注记 5.2**：在 `ℚ(x)[[t]]` 中 `Σ_{m≥0} tᵐ/P_m = (1/(1 − x))·₁F₁(1; 1 − λ; −t/x³)`，`λ = (1 − x)/x³`
（`P_m(x)` 写成 `(Ppoly (RatFunc ℚ) m).eval RatFunc.X`）。 -/
theorem remark_1F1 :
    PowerSeries.mk (fun m => ((Ppoly (RatFunc ℚ) m).eval RatFunc.X)⁻¹) =
      PowerSeries.C (1 - RatFunc.X)⁻¹ *
        hyp1F1 1 (1 - (1 - RatFunc.X) / RatFunc.X ^ 3) (-1 / RatFunc.X ^ 3) := by
  refine sum_inv_P_eq_hyp1F1 RatFunc.X_ne_zero fun i h => bpoly_ne_zero i ?_
  rw [eval_bpoly_ratFunc] at h
  exact RatFunc.algebraMap_injective ℚ (h.trans (map_zero _).symm)

end A207123
