import A207123.Ascent

/-!
# 论文定理 4.4（按上升数细化的母函数）与引理 4.5 的按 `y` 细化

`U_k(m,s)`（`Us k m s`）是长 `k`、取值 ≤ `m`、恰有 `s` 个上升的合法序列个数。二元母函数
`G_m(x, y) = Σ_{k,s} U_k(m,s) x^k y^s` 在这里写成 `x` 的幂级数、系数是 `y` 的幂级数（`Gxy m`），
`b_v = 1 − x − v·y·x³`（`bxy v`）。

* **定理 4.4**：`Gxy_zero`（`b_0·G_0 = 1`，即约定 `G_{−1} = 1`）、`Gxy_rec`
  （`b_{m+1}·G_{m+1} = G_m + (m+1)·y·x²`，即 `G_m = (G_{m−1} + m·y·x²)/(1 − x − m·y·x³)`）、`Gxy_prod`
  （第二式乘掉分母：`G_m·∏_{v=0}^{m} b_v = 1 + y·x²·Σ_{j=1}^{m} j·∏_{v=0}^{j−1} b_v`）。
* **引理 4.5，按 `y` 细化**（`coef_formula_xy`）：`∏_{v=j}^{m} b_v⁻¹` 的 `xⁿyˢ` 系数是
  `H(m,s,j)·C(n + m − j − 2s, n − 3s)`（`3s > n` 时为 0），`H(m,s,j) = h_s(j, …, m)`（`hc s (vars j m)`）。
  写成：以这些数为系数的幂级数乘以 `∏_{v=j}^{m} b_v` 等于 1。

论文用块分解（定理 4.2）证明定理 4.4；这里走按上升数细化的引理 1（`Ascent.lean` 的 `lemma1_asc` 等），
逐系数比较，与 `Recurrence.lean` 中 `y = 1` 的 `G_rec` 同一路线。引理 4.5 用 `Formula.lean` 的 `g`
（定义成 `[3s ≤ n]·h_s(l)·multichoose(|l| + s, n − 3s)`）与它的「加入最大变量」递推 `g_cons`。
-/

open Finset

namespace A207123

/-- `G_m(x, y) = Σ_{k,s} U_k(m,s) x^k y^s`：`x^k` 的系数是 `y` 的幂级数 `Σ_s U_k(m,s) y^s`。 -/
noncomputable def Gxy (m : ℕ) : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.mk fun k => PowerSeries.mk fun s => (Us k m s : ℚ)

/-- `b_v = 1 − x − v·y·x³`（定理 4.4 的记号）。 -/
noncomputable def bxy (v : ℕ) : PowerSeries (PowerSeries ℚ) :=
  1 - PowerSeries.X - PowerSeries.C ((v : PowerSeries ℚ) * PowerSeries.X) * PowerSeries.X ^ 3

/-- `∏_{v ∈ l} b_v⁻¹` 的系数：`xⁿyˢ` 的系数是 `g l n s`（引理 4.5 用）。 -/
noncomputable def Gl (l : List ℕ) : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.mk fun n => PowerSeries.mk fun s => (g l n s : ℚ)

/-- 辅助引理（定理 4.4）：乘以 `1 − x − c·x³` 后的系数（任意交换环，同 `coeff_b_mul`）。 -/
theorem coeff_b_mul_gen {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.X - PowerSeries.C c * PowerSeries.X ^ 3) * F) =
      PowerSeries.coeff k F - (if 1 ≤ k then PowerSeries.coeff (k - 1) F else 0) -
        c * (if 3 ≤ k then PowerSeries.coeff (k - 3) F else 0) := by
  have hX : PowerSeries.X * F = PowerSeries.X ^ 1 * F := by rw [pow_one]
  rw [sub_mul, sub_mul, one_mul, mul_assoc, map_sub, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', hX, PowerSeries.coeff_X_pow_mul']

/-- 辅助引理（定理 4.4）：`[y^s] (c·y·F) = [s ≥ 1]·c·[y^{s−1}] F`。 -/
theorem coeff_natCast_mul_X_mul (c : ℕ) (F : PowerSeries ℚ) (s : ℕ) :
    PowerSeries.coeff s ((c : PowerSeries ℚ) * PowerSeries.X * F) =
      if s = 0 then 0 else (c : ℚ) * PowerSeries.coeff (s - 1) F := by
  rw [← map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) c, mul_assoc, PowerSeries.coeff_C_mul]
  rcases s with _ | s
  · rw [PowerSeries.coeff_zero_X_mul, mul_zero, ite_eq_left (rfl : (0 : ℕ) = 0)]
  · rw [PowerSeries.coeff_succ_X_mul, ite_eq_right (by omega : s + 1 ≠ 0), Nat.add_sub_cancel]

/-- 辅助引理（定理 4.4）：`[y^s] (c·y) = [s = 1]·c`。 -/
theorem coeff_natCast_mul_X (c s : ℕ) :
    PowerSeries.coeff s ((c : PowerSeries ℚ) * PowerSeries.X) = if s = 1 then (c : ℚ) else 0 := by
  rw [← map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) c, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X]
  by_cases hs : s = 1
  · rw [ite_eq_left hs, ite_eq_left hs, mul_one]
  · rw [ite_eq_right hs, ite_eq_right hs, mul_zero]

/-- 辅助引理（定理 4.4）：`G_m` 的 `x^k` 系数是 `Σ_s U_k(m,s) y^s`。 -/
theorem coeff_Gxy (k m : ℕ) :
    PowerSeries.coeff k (Gxy m) = PowerSeries.mk fun s => (Us k m s : ℚ) := by
  rw [Gxy, PowerSeries.coeff_mk]

/-- 辅助引理（定理 4.4）：`G_0` 的每个 `x^k` 系数都是 1（`U_k(0,s) = [s = 0]`）。 -/
theorem coeff_Gxy_zero (k : ℕ) : PowerSeries.coeff k (Gxy 0) = 1 := by
  rw [coeff_Gxy]
  ext s
  rw [PowerSeries.coeff_mk, Us_zero_right, PowerSeries.coeff_one]
  by_cases hs : s = 0 <;> simp [hs]

/-- **定理 4.4**，`m = 0`：`(1 − x)·G_0 = 1`（即约定 `G_{−1} = 1`）。 -/
theorem Gxy_zero : bxy 0 * Gxy 0 = 1 := by
  ext k : 1
  rw [bxy, coeff_b_mul_gen, PowerSeries.coeff_one]
  simp only [coeff_Gxy_zero]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ite_eq_right (by omega : ¬ 1 ≤ 0), ite_eq_right (by omega : ¬ 3 ≤ 0),
      ite_eq_left (rfl : (0 : ℕ) = 0), mul_zero, sub_zero, sub_zero]
  · rw [ite_eq_left (by omega : 1 ≤ k), ite_eq_right (by omega : k ≠ 0), Nat.cast_zero, zero_mul,
      zero_mul, sub_zero, sub_self]

/-- **定理 4.4**（第一式）：`(1 − x − (m+1)·y·x³)·G_{m+1} = G_m + (m+1)·y·x²`。
逐系数比较：`k = 0` 用 `U_0(m,s) = [s=0]`，`k = 1` 用 `lemma1_asc_one`，`k = 2` 用 `lemma1_asc_two`，
`k ≥ 3` 用 `lemma1_asc_s0`（`s = 0`）与 `lemma1_asc`（`s ≥ 1`）。 -/
theorem Gxy_rec (m : ℕ) :
    bxy (m + 1) * Gxy (m + 1) =
      Gxy m + PowerSeries.C (((m + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X) * PowerSeries.X ^ 2 := by
  ext k : 1
  rw [bxy, coeff_b_mul_gen, map_add, PowerSeries.coeff_C_mul_X_pow]
  match k with
  | 0 =>
    rw [ite_eq_right (by omega : ¬ 1 ≤ 0), ite_eq_right (by omega : ¬ 3 ≤ 0),
      ite_eq_right (by omega : (0 : ℕ) ≠ 2), mul_zero, sub_zero, sub_zero, add_zero, coeff_Gxy,
      coeff_Gxy]
    simp only [Us_zero_left]
  | 1 =>
    rw [ite_eq_left (by omega : 1 ≤ 1), ite_eq_right (by omega : ¬ 3 ≤ 1),
      ite_eq_right (by omega : (1 : ℕ) ≠ 2), mul_zero, sub_zero, add_zero, Nat.sub_self]
    ext s
    simp only [map_sub, coeff_Gxy, PowerSeries.coeff_mk]
    have h : (Us 1 (m + 1) s : ℚ) = Us 1 m s + Us 0 (m + 1) s := by
      exact_mod_cast lemma1_asc_one m s
    linear_combination h
  | 2 =>
    rw [ite_eq_left (by omega : 1 ≤ 2), ite_eq_right (by omega : ¬ 3 ≤ 2),
      ite_eq_left (rfl : (2 : ℕ) = 2), mul_zero, sub_zero, show (2 : ℕ) - 1 = 1 from rfl]
    ext s
    simp only [map_sub, map_add, coeff_Gxy, PowerSeries.coeff_mk, coeff_natCast_mul_X]
    have h : (Us 2 (m + 1) s : ℚ) =
        Us 2 m s + Us 1 (m + 1) s + ((m + 1 : ℕ) : ℚ) * (if s = 1 then 1 else 0) := by
      exact_mod_cast lemma1_asc_two m s
    by_cases hs : s = 1
    · rw [ite_eq_left hs] at h ⊢
      linear_combination h
    · rw [ite_eq_right hs] at h ⊢
      linear_combination h
  | k + 3 =>
    rw [ite_eq_left (by omega : 1 ≤ k + 3), ite_eq_left (by omega : 3 ≤ k + 3),
      ite_eq_right (by omega : k + 3 ≠ 2), show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel,
      add_zero]
    ext s
    simp only [map_sub, coeff_Gxy, PowerSeries.coeff_mk, coeff_natCast_mul_X_mul]
    rcases s with _ | s
    · have h : (Us (k + 3) (m + 1) 0 : ℚ) = Us (k + 3) m 0 + Us (k + 2) (m + 1) 0 := by
        exact_mod_cast lemma1_asc_s0 k m
      rw [ite_eq_left (rfl : (0 : ℕ) = 0), sub_zero]
      linear_combination h
    · have h : (Us (k + 3) (m + 1) (s + 1) : ℚ) =
          Us (k + 3) m (s + 1) + Us (k + 2) (m + 1) (s + 1) + ((m + 1 : ℕ) : ℚ) * Us k (m + 1) s := by
        exact_mod_cast lemma1_asc k m s
      rw [ite_eq_right (by omega : s + 1 ≠ 0), Nat.add_sub_cancel]
      linear_combination h

/-- **定理 4.4**（第二式，乘掉分母）：`G_m·∏_{v=0}^{m} b_v = 1 + y·x²·Σ_{j=1}^{m} j·∏_{v=0}^{j−1} b_v`，
即 `G_m = 1/∏_{v=0}^{m} b_v + y·x²·Σ_{j=1}^{m} j/∏_{v=j}^{m} b_v`。 -/
theorem Gxy_prod (m : ℕ) :
    Gxy m * ∏ v ∈ range (m + 1), bxy v =
      1 + PowerSeries.C (PowerSeries.X : PowerSeries ℚ) * PowerSeries.X ^ 2 *
        ∑ j ∈ Icc 1 m, (j : PowerSeries (PowerSeries ℚ)) * ∏ v ∈ range j, bxy v := by
  induction m with
  | zero =>
    rw [prod_range_succ, prod_range_zero, one_mul, mul_comm (Gxy 0), Gxy_zero,
      Icc_eq_empty (by omega : ¬ 1 ≤ 0), sum_empty, mul_zero, add_zero]
  | succ m ih =>
    rw [prod_range_succ, sum_Icc_succ_top (by omega : 1 ≤ m + 1),
      show Gxy (m + 1) * ((∏ v ∈ range (m + 1), bxy v) * bxy (m + 1))
        = (bxy (m + 1) * Gxy (m + 1)) * ∏ v ∈ range (m + 1), bxy v by ring,
      Gxy_rec, add_mul, ih, map_mul, map_natCast]
    ring

/-! ### 引理 4.5，按 `y` 细化 -/

/-- 辅助引理（引理 4.5）：乘以 `b_v` 后 `xⁿyˢ` 的系数。 -/
theorem coeff_coeff_bxy_mul (v : ℕ) (F : PowerSeries (PowerSeries ℚ)) (n s : ℕ) :
    PowerSeries.coeff s (PowerSeries.coeff n (bxy v * F)) =
      PowerSeries.coeff s (PowerSeries.coeff n F)
        - (if 1 ≤ n then PowerSeries.coeff s (PowerSeries.coeff (n - 1) F) else 0)
        - (if 3 ≤ n ∧ 1 ≤ s then (v : ℚ) * PowerSeries.coeff (s - 1) (PowerSeries.coeff (n - 3) F)
            else 0) := by
  rw [bxy, coeff_b_mul_gen, map_sub, map_sub, coeff_natCast_mul_X_mul]
  by_cases h1 : 1 ≤ n
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h3 : 3 ≤ n
    · rw [ite_eq_left h3]
      rcases s with _ | s
      · rw [ite_eq_left (rfl : (0 : ℕ) = 0),
          ite_eq_right (by omega : ¬ (3 ≤ n ∧ 1 ≤ 0))]
      · rw [ite_eq_right (by omega : s + 1 ≠ 0), ite_eq_left (⟨h3, by omega⟩ : 3 ≤ n ∧ 1 ≤ s + 1)]
    · rw [ite_eq_right h3, map_zero, mul_zero, ite_self,
        ite_eq_right (fun h => h3 h.1 : ¬ (3 ≤ n ∧ 1 ≤ s))]
  · rw [ite_eq_right h1, ite_eq_right h1, map_zero, ite_eq_right (by omega : ¬ 3 ≤ n), map_zero,
      mul_zero, ite_self, ite_eq_right (by omega : ¬ (3 ≤ n ∧ 1 ≤ s))]

/-- 辅助引理（引理 4.5）：空积的逆是 1。 -/
theorem Gl_nil : Gl [] = 1 := by
  ext n s
  rw [Gl, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases n with _ | n
  · rw [g_zero, ite_eq_left (rfl : (0 : ℕ) = 0), PowerSeries.coeff_one]
    by_cases hs : s = 0 <;> simp [hs]
  · rw [g_nil_succ, ite_eq_right (by omega : n + 1 ≠ 0), map_zero, Nat.cast_zero]

/-- 辅助引理（引理 4.5）：`b_v·∏_{u ∈ v::l} b_u⁻¹ = ∏_{u ∈ l} b_u⁻¹`（`g_cons` 的幂级数形式）。 -/
theorem Gl_cons (v : ℕ) (l : List ℕ) : bxy v * Gl (v :: l) = Gl l := by
  ext n s
  rw [coeff_coeff_bxy_mul]
  simp only [Gl, PowerSeries.coeff_mk]
  rw [g_cons v l n s]
  push_cast
  split_ifs <;> ring

/-- 辅助引理（引理 4.5）：`(∏_{v ∈ l} b_v⁻¹)·∏_{v ∈ l} b_v = 1`。 -/
theorem Gl_mul_prod (l : List ℕ) : Gl l * (l.map bxy).prod = 1 := by
  induction l with
  | nil => rw [Gl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons,
      show Gl (v :: l) * (bxy v * (l.map bxy).prod) = (bxy v * Gl (v :: l)) * (l.map bxy).prod by ring,
      Gl_cons, ih]

/-- 辅助引理（引理 4.5）：`vars j m = [m, …, j]` 上的积就是 `∏_{v=j}^{m}`。 -/
theorem prod_vars_bxy {j m : ℕ} (h : j ≤ m + 1) :
    ((vars j m).map bxy).prod = ∏ v ∈ Icc j m, bxy v := by
  induction m with
  | zero =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
    · rw [vars_zero_zero, Icc_self, prod_singleton, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
    · have h1 : vars 1 0 = [] := by simp [vars]
      have h2 : Icc 1 0 = (∅ : Finset ℕ) := Icc_eq_empty (by omega)
      rw [h1, h2, List.map_nil, List.prod_nil, prod_empty]
  | succ m ih =>
    by_cases hj : j ≤ m + 1
    · rw [vars_succ hj, List.map_cons, List.prod_cons, ih hj, prod_Icc_succ_top hj, mul_comm]
    · have h1 : vars j (m + 1) = [] := by simp [vars, hj]
      have h2 : Icc j (m + 1) = (∅ : Finset ℕ) := Icc_eq_empty (by omega)
      rw [h1, h2, List.map_nil, List.prod_nil, prod_empty]

/-- **引理 4.5，按 `y` 细化**：对 `0 ≤ j ≤ m`，`∏_{v=j}^{m} (1 − x − v·y·x³)⁻¹` 的 `xⁿyˢ` 系数是
`H(m,s,j)·C(n + m − j − 2s, n − 3s)`（`3s > n` 时为 0），`H(m,s,j) = h_s(j, …, m)` 是 `hc s (vars j m)`。
写成：以这些数为系数的幂级数乘以 `∏_{v=j}^{m} b_v` 等于 1。 -/
theorem coef_formula_xy {j m : ℕ} (hj : j ≤ m) :
    (PowerSeries.mk fun n => PowerSeries.mk fun s =>
        ((if 3 * s ≤ n then hc s (vars j m) * (n + m - j - 2 * s).choose (n - 3 * s) else 0 : ℕ) : ℚ))
      * ∏ v ∈ Icc j m, bxy v = 1 := by
  rw [← prod_vars_bxy (by omega : j ≤ m + 1), ← Gl_mul_prod (vars j m)]
  congr 1
  ext n s
  rw [Gl, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, g,
    length_vars (by omega : j ≤ m + 1)]
  by_cases h : 3 * s ≤ n
  · rw [ite_eq_left h, ite_eq_left h, Nat.multichoose_eq,
      show m + 1 - j + s + (n - 3 * s) - 1 = n + m - j - 2 * s by omega]
  · rw [ite_eq_right h, ite_eq_right h]

end A207123
