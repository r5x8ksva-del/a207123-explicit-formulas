import A207123.RootExpansion
import A207123.Growth

/-!
# 论文定理 3.2(3)：`c_m` 的两个表达式、`c_m > 0` 与 `U_k(m)` 的渐近式

论文定理 3.2(3)：`c_0 = 1`；`m ≥ 1` 时 `x_m = 1/ρ_m`，
`c_m = α_m(ρ_m) = (G_{m−1}(x_m) + m·x_m²)/(x_m(1 + 3m·x_m²))
     = ρ_m^{3m+3}/(m!(ρ_m² + 3m))·(1 + Σ_{j=1}^{m} j·m^{\underline j}·ρ_m^{−3j−2}) > 0`，
且对 `m ≥ 1`，`U_k(m) = c_m ρ_m^k − c_{m−1} ρ_{m−1}^{k+3} + O(τ_m^k)`（`k → ∞`），其中 `τ_1 = √(ρ_1(ρ_1 − 1))`，
`m ≥ 2` 时 `τ_m = max(ρ_{m−2}, √(ρ_m(ρ_m − 1))) < ρ_{m−1}`。

* `cm m`：用第二个表达式定义（`m^{\underline j}` 是 `Nat.descFactorial`）；`cm_zero`：`c_0 = 1`；`cm_pos`：`c_m > 0`。
* `alpha_rho`：`α_m(ρ_m) = c_m`（`α_m` 见 `RootExpansion.lean`）。
* `cm_eq_G`、`hasSum_G`：第一个表达式；`G_{m−1}(x_m)` 是级数 `Σ_k U_k(m−1)·x_m^k` 的和（`HasSum`），
  等于 `W_{m−1}(x_m)/P_{m−1}(x_m)`。
* `tau m`、`tau_lt`：`τ_m < ρ_{m−1}`；`U_asymp_bound`：存在常数 `C`，对一切 `k ≥ 0`，
  `|U_k(m) − c_m ρ_m^k + c_{m−1} ρ_{m−1}^{k+3}| ≤ C·τ_m^k`；`U_asymp`：`O(τ_m^k)` 的形式。
* `thm_asym_three`：以上合在一起。

证明同论文：`1 − x_m = m x_m³`，所以 `b_v(x_m) = (m − v)x_m³`，`P_{j−1}(x_m) = m^{\underline j} x_m^{3j}`，
`W_m(x_m) = 1 + Σ_j j·m^{\underline j} x_m^{3j+2}`；`b_m = (1 − ρ_m x)(1 + (ρ_m − 1)x + ρ_m(ρ_m − 1)x²)`，第二个因子在 `x_m`
处等于 `x_m(1 + 3m x_m²)`，于是 `α_m(ρ_m) = W_m(x_m)/(P_{m−1}(x_m)·x_m(1 + 3m x_m²))`。渐近式：由定理 3.2(2) 分出
`ρ_m`、`ρ_{m−1}` 两项，`α_m(ρ_{m−1}) = −c_{m−1}ρ_{m−1}³`，其余根的模都 ≤ `τ_m`（定理 3.2(1)）。
-/

open Polynomial Finset Filter Asymptotics

namespace A207123

/-- 定理 3.2(3) 的常数：`c_m = ρ_m^{3m+3}/(m!(ρ_m² + 3m))·(1 + Σ_{j=1}^{m} j·m^{\underline j}·ρ_m^{−3j−2})`。 -/
noncomputable def cm (m : ℕ) : ℝ :=
  rho m ^ (3 * m + 3) / ((m.factorial : ℝ) * (rho m ^ 2 + 3 * m)) *
    (1 + ∑ j ∈ Icc 1 m, (j : ℝ) * (m.descFactorial j : ℝ) * (rho m ^ (3 * j + 2))⁻¹)

/-- 定理 3.2(3) 的 `τ_m`：`τ_1 = √(ρ_1(ρ_1 − 1))`，`m ≥ 2` 时 `τ_m = max(ρ_{m−2}, √(ρ_m(ρ_m − 1)))`。 -/
noncomputable def tau (m : ℕ) : ℝ :=
  if m = 1 then Real.sqrt (rho 1 * (rho 1 - 1)) else max (rho (m - 2)) (Real.sqrt (rho m * (rho m - 1)))

/-- 辅助引理（定理 3.2(3)）：`ρ_m > 0`。 -/
theorem rho_pos (m : ℕ) : 0 < rho m := lt_of_lt_of_le one_pos (one_le_rho m)

/-- **定理 3.2(3)**：`c_m > 0`。 -/
theorem cm_pos (m : ℕ) : 0 < cm m := by
  have hρ := rho_pos m
  unfold cm
  positivity

/-- **定理 3.2(3)**：`c_0 = 1`。 -/
theorem cm_zero : cm 0 = 1 := by
  rw [cm, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), sum_empty, rho_zero]
  norm_num

/-- 辅助引理（定理 3.2(3)）：`τ_m ≥ 0`。 -/
theorem tau_nonneg (m : ℕ) : 0 ≤ tau m := by
  unfold tau
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_max_of_le_right (Real.sqrt_nonneg _)

/-- 辅助引理（定理 3.2(3)）：`r³ − r² = c`、`r ≠ 0` 时 `1 − 1/r = c/r³`。 -/
theorem one_sub_inv_eq {K : Type*} [Field K] {r : K} (hr : r ≠ 0) {c : K} (h : r ^ 3 - r ^ 2 = c) :
    1 - r⁻¹ = c * r⁻¹ ^ 3 := by
  have hx1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  linear_combination (-((r * r⁻¹) ^ 2 + r * r⁻¹ + 1) + r⁻¹ * (r * r⁻¹ + 1)) * hx1 + r⁻¹ ^ 3 * h

/-- 辅助引理（定理 3.2(3)）：`1 − x = M x³` 时 `b_v(x) = (M − v)x³`。 -/
theorem eval_bpoly_of_rel {K : Type*} [CommRing K] {M : ℕ} {x : K} (hx : 1 - x = M * x ^ 3) (v : ℕ) :
    (bpoly K v).eval x = ((M : K) - v) * x ^ 3 := by
  rw [eval_bpoly]
  linear_combination hx

/-- 辅助引理（定理 3.2(3)）：`1 − x = M x³`、`j ≤ M` 时 `P_j(x) = M^{\underline{j+1}} x^{3(j+1)}`。 -/
theorem eval_Ppoly_of_rel {K : Type*} [CommRing K] {M : ℕ} {x : K} (hx : 1 - x = M * x ^ 3) :
    ∀ j : ℕ, j ≤ M → (Ppoly K j).eval x = (M.descFactorial (j + 1) : K) * x ^ (3 * (j + 1)) := by
  intro j hj
  induction j with
  | zero =>
    rw [Ppoly_zero, eval_bpoly_of_rel hx, Nat.zero_add, Nat.descFactorial_one, Nat.cast_zero, sub_zero]
  | succ j ih =>
    rw [Ppoly_succ, eval_mul, ih (by omega), eval_bpoly_of_rel hx, Nat.descFactorial_succ M (j + 1), Nat.cast_mul,
      Nat.cast_sub (by omega : j + 1 ≤ M)]
    ring

/-- 辅助引理（定理 3.2(3)）：`1 − x = M x³`、`m ≤ M` 时 `W_m(x) = 1 + Σ_{j=1}^{m} j·M^{\underline j}·x^{3j+2}`。 -/
theorem eval_Wpoly_of_rel {K : Type*} [CommRing K] {M : ℕ} {x : K} (hx : 1 - x = M * x ^ 3) (m : ℕ)
    (hm : m ≤ M) :
    (Wpoly K m).eval x = 1 + ∑ j ∈ Icc 1 m, (j : K) * (M.descFactorial j : K) * x ^ (3 * j + 2) := by
  rw [Wpoly, eval_add, eval_one, eval_mul, eval_pow, eval_X, eval_finsetSum, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  rw [eval_mul, eval_C, eval_Ppoly_of_rel hx (j - 1) (by omega), Nat.sub_add_cancel hj.1]
  ring

/-- 辅助引理（定理 3.2(3)）：`m ≥ 1` 时 `c_m = W_m(x_m)/(P_{m−1}(x_m)·x_m(1 + 3m x_m²))`（实数）。 -/
theorem cm_eq_W {m : ℕ} (hm : 1 ≤ m) :
    cm m = (Wpoly ℝ m).eval (rho m)⁻¹ /
      ((Ppoly ℝ (m - 1)).eval (rho m)⁻¹ * ((rho m)⁻¹ * (1 + 3 * m * (rho m)⁻¹ ^ 2))) := by
  have hρ0 : rho m ≠ 0 := (rho_pos m).ne'
  have hx : 1 - (rho m)⁻¹ = (m : ℝ) * (rho m)⁻¹ ^ 3 := one_sub_inv_eq hρ0 (rho_spec m)
  have hT : (rho m)⁻¹ ^ (3 * m) * rho m ^ (3 * m) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hρ0, one_pow]
  have hx1 : (rho m)⁻¹ * rho m = 1 := inv_mul_cancel₀ hρ0
  have hFG : (m.factorial : ℝ) * (rho m ^ 2 + 3 * m) ≠ 0 := by
    have := rho_pos m
    positivity
  have hfac : rho m ^ (3 * m + 3) *
      ((m.factorial : ℝ) * (rho m)⁻¹ ^ (3 * m) * ((rho m)⁻¹ * (1 + 3 * m * (rho m)⁻¹ ^ 2))) =
        (m.factorial : ℝ) * (rho m ^ 2 + 3 * m) := by
    linear_combination
      ((m.factorial : ℝ) * ((rho m)⁻¹ * rho m ^ 3 + 3 * m * (rho m)⁻¹ ^ 3 * rho m ^ 3)) * hT +
        ((m.factorial : ℝ) * (rho m ^ 2 + 3 * m * (((rho m)⁻¹ * rho m) ^ 2 + (rho m)⁻¹ * rho m + 1))) * hx1
  have hD : (m.factorial : ℝ) * (rho m)⁻¹ ^ (3 * m) * ((rho m)⁻¹ * (1 + 3 * m * (rho m)⁻¹ ^ 2)) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hFG hfac.symm
  have hS : ∑ j ∈ Icc 1 m, (j : ℝ) * (m.descFactorial j : ℝ) * (rho m)⁻¹ ^ (3 * j + 2) =
      ∑ j ∈ Icc 1 m, (j : ℝ) * (m.descFactorial j : ℝ) * (rho m ^ (3 * j + 2))⁻¹ :=
    sum_congr rfl fun j _ => by rw [inv_pow]
  rw [eval_Wpoly_of_rel hx m le_rfl, eval_Ppoly_of_rel hx (m - 1) (by omega), Nat.sub_add_cancel hm,
    Nat.descFactorial_self, hS, eq_div_iff hD, cm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hFG,
    mul_comm (rho m ^ (3 * m + 3)), mul_assoc, hfac]

/-- 辅助引理（定理 3.2(3)）：`1 ≤ m` 时 `W_m(x) = W_{m−1}(x) + m x²·P_{m−1}(x)`。 -/
theorem eval_Wpoly_pred {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    (Wpoly ℝ m).eval x = (Wpoly ℝ (m - 1)).eval x + m * x ^ 2 * (Ppoly ℝ (m - 1)).eval x := by
  have h := Wpoly_succ (R := ℝ) (m - 1)
  rw [Nat.sub_add_cancel hm] at h
  rw [h]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [Nat.cast_sub hm, Nat.cast_one]
  ring

/-- **定理 3.2(3)**（第一个表达式）：`m ≥ 1` 时 `c_m = (W_{m−1}(x_m)/P_{m−1}(x_m) + m x_m²)/(x_m(1 + 3m x_m²))`；
`W_{m−1}(x_m)/P_{m−1}(x_m)` 就是 `G_{m−1}(x_m)`（`hasSum_G`）。 -/
theorem cm_eq_G {m : ℕ} (hm : 1 ≤ m) :
    cm m = ((Wpoly ℝ (m - 1)).eval (rho m)⁻¹ / (Ppoly ℝ (m - 1)).eval (rho m)⁻¹ + m * (rho m)⁻¹ ^ 2) /
      ((rho m)⁻¹ * (1 + 3 * m * (rho m)⁻¹ ^ 2)) := by
  have hρ0 : rho m ≠ 0 := (rho_pos m).ne'
  have hx : 1 - (rho m)⁻¹ = (m : ℝ) * (rho m)⁻¹ ^ 3 := one_sub_inv_eq hρ0 (rho_spec m)
  have hP : (Ppoly ℝ (m - 1)).eval (rho m)⁻¹ ≠ 0 := by
    rw [eval_Ppoly_of_rel hx (m - 1) (by omega), Nat.sub_add_cancel hm, Nat.descFactorial_self]
    have := rho_pos m
    positivity
  rw [cm_eq_W hm, eval_Wpoly_pred hm, div_add' _ _ _ hP, div_div]

/-- 辅助引理（定理 3.2(3)）：`Q_m` 的根 `σ` 是某个 `y³ − y² − i`（`i ≤ m`）的根。 -/
theorem sig_level {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) : ∃ i ≤ m, σ ^ 3 - σ ^ 2 = i := by
  obtain ⟨hσ0, hP⟩ := mem_sig.mp hσ
  rw [Ppoly, eval_prod] at hP
  obtain ⟨i, hi, hb⟩ := prod_eq_zero_iff.mp hP
  refine ⟨i, by rw [mem_range] at hi; omega, ?_⟩
  have h := eval_bpoly_inv i hσ0
  rw [hb, zero_mul] at h
  linear_combination -h

/-- 辅助引理（定理 3.2(3)）：`σ ≠ 0`、`σ³ − σ² = 0` 时 `σ = 1`。 -/
theorem eq_one_of_cubic_zero {σ : ℂ} (hσ0 : σ ≠ 0) (h : σ ^ 3 - σ ^ 2 = ((0 : ℕ) : ℂ)) : σ = 1 := by
  have h2 : σ ^ 2 * (σ - 1) = 0 := by
    rw [Nat.cast_zero] at h
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd ((pow_eq_zero_iff (by norm_num)).mp h3) hσ0
  · linear_combination h3

/-- 辅助引理（定理 3.2(3)）：`Q_m` 的根的模都不超过 `ρ_m`。 -/
theorem norm_le_rho_of_mem_sig {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) : ‖σ‖ ≤ rho m := by
  obtain ⟨i, him, hi⟩ := sig_level hσ
  have hσ0 := (mem_sig.mp hσ).1
  have hmono : rho i ≤ rho m := rho_strictMono.monotone him
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · rw [eq_one_of_cubic_zero hσ0 hi, norm_one]
    exact one_le_rho m
  · by_cases hρi : σ = (rho i : ℂ)
    · rw [hρi, Complex.norm_real, Real.norm_of_nonneg (rho_pos i).le]
      exact hmono
    · exact (norm_lt_rho_of_root (by omega) (by linear_combination hi) hρi).le.trans hmono

/-- 辅助引理（定理 3.2(3)）：`Q_n` 的根 `σ` 都满足 `1 − σz ≠ 0` 时，`Σ_σ α_n(σ)/(1 − σz) = W_n(z)/P_n(z)`。 -/
theorem sum_alpha_div (n : ℕ) {z : ℂ} (hz : ∀ σ ∈ sig n, 1 - σ * z ≠ 0) :
    ∑ σ ∈ sig n, alpha n σ * (1 - σ * z)⁻¹ = (Wpoly ℂ n).eval z / (Ppoly ℂ n).eval z := by
  have hP : (Ppoly ℂ n).eval z ≠ 0 := by
    rw [Ppoly_eq_prod_sig, eval_prod]
    refine prod_ne_zero_iff.mpr fun σ hσ => ?_
    simpa using hz σ hσ
  rw [eq_div_iff hP, sum_mul]
  conv_rhs => rw [W_eq_sum_alpha n, eval_finsetSum]
  refine sum_congr rfl fun σ hσ => ?_
  rw [eval_mul, eval_C, Ppoly_eq_mul_cof hσ, eval_mul]
  have h1 : (1 - C σ * X : ℂ[X]).eval z = 1 - σ * z := by simp
  rw [h1, mul_assoc, inv_mul_cancel_left₀ (hz σ hσ)]

/-- **定理 3.2(3)**（`G_{m−1}(x_m)` 的意义）：`0 ≤ x`、`x·ρ_n < 1` 时级数 `Σ_k U_k(n)·x^k` 收敛到 `W_n(x)/P_n(x)`。 -/
theorem hasSum_G {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx : x * rho n < 1) :
    HasSum (fun k => (U k n : ℝ) * x ^ k) ((Wpoly ℝ n).eval x / (Ppoly ℝ n).eval x) := by
  have hxσ : ∀ σ ∈ sig n, ‖σ * (x : ℂ)‖ < 1 := fun σ hσ => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0]
    calc ‖σ‖ * x ≤ rho n * x := mul_le_mul_of_nonneg_right (norm_le_rho_of_mem_sig hσ) hx0
      _ < 1 := by rw [mul_comm]; exact hx
  have h1 : HasSum (fun k => ∑ σ ∈ sig n, alpha n σ * (σ * (x : ℂ)) ^ k)
      (∑ σ ∈ sig n, alpha n σ * (1 - σ * (x : ℂ))⁻¹) :=
    hasSum_sum fun σ hσ => (hasSum_geometric_of_norm_lt_one (hxσ σ hσ)).mul_left (alpha n σ)
  have h2 : (fun k => ∑ σ ∈ sig n, alpha n σ * (σ * (x : ℂ)) ^ k) =
      fun k => (((U k n : ℝ) * x ^ k : ℝ) : ℂ) := by
    funext k
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, U_eq_sum_alpha n k, sum_mul]
    refine sum_congr rfl fun σ _ => ?_
    ring
  have hne : ∀ σ ∈ sig n, 1 - σ * (x : ℂ) ≠ 0 := fun σ hσ h => by
    have h3 := hxσ σ hσ
    rw [show σ * (x : ℂ) = 1 by linear_combination -h, norm_one] at h3
    exact lt_irrefl _ h3
  have h3 : ∑ σ ∈ sig n, alpha n σ * (1 - σ * (x : ℂ))⁻¹ =
      (((Wpoly ℝ n).eval x / (Ppoly ℝ n).eval x : ℝ) : ℂ) := by
    rw [sum_alpha_div n hne, Complex.ofReal_div, ← eval_ofReal_map, ← eval_ofReal_map, Wpoly_map, Ppoly_map]
  rw [h2, h3] at h1
  exact Complex.hasSum_ofReal.mp h1

/-- 辅助引理（定理 3.2(3)）：`α_0(1) = 1`（`G_0 = 1/(1 − x)`）。 -/
theorem alpha_zero_one : alpha 0 1 = 1 := by
  have h1 : (1 : ℂ) ∈ sig 0 := mem_sig_of_cubic (j := 0) (m := 0) le_rfl one_ne_zero (by norm_num)
  have hc : #(sig 0) = 1 := by simpa using card_sig 0
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hs : sig 0 = {1} := by
    rw [ha] at h1 ⊢
    rw [Finset.mem_singleton.mp h1]
  rw [alpha, cof, hs, Finset.erase_singleton, prod_empty, Wpoly_zero]
  simp

/-- **定理 3.2(3)**：`α_m(ρ_m) = c_m`（`c_0 = 1 = α_0(1)`）。 -/
theorem alpha_rho (m : ℕ) : alpha m (rho m) = (cm m : ℂ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [rho_zero, cm_zero, Complex.ofReal_one]
    exact alpha_zero_one
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ, ρ = ((rho m : ℝ) : ℂ) := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ0 : ρ ≠ 0 := by
    rw [hρdef]
    exact Complex.ofReal_ne_zero.mpr (rho_pos m).ne'
  have hρm : ρ ^ 3 - ρ ^ 2 = (m : ℂ) := by
    rw [hρdef]
    exact_mod_cast rho_spec m
  have hmem : ρ ∈ sig m := mem_sig_of_cubic le_rfl hρ0 hρm
  have hb : bpoly ℂ m = (1 - C ρ * X) * (1 + C (ρ - 1) * X + C (ρ * (ρ - 1)) * X ^ 2) := by
    rw [bpoly, ← hρm]
    simp only [map_sub, map_mul, map_pow, map_one]
    ring
  have hPs : Ppoly ℂ m = Ppoly ℂ (m - 1) * bpoly ℂ m := by
    have h := Ppoly_succ (R := ℂ) (m - 1)
    rwa [Nat.sub_add_cancel hm] at h
  have hcof : cof m ρ = Ppoly ℂ (m - 1) * (1 + C (ρ - 1) * X + C (ρ * (ρ - 1)) * X ^ 2) := by
    have hne : (1 - C ρ * X : ℂ[X]) ≠ 0 := by
      intro h
      have h2 := congrArg (eval 0) h
      simp at h2
    refine mul_left_cancel₀ hne ?_
    rw [← Ppoly_eq_mul_cof hmem, hPs, hb]
    ring
  have hx1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0
  have hrel : 1 - ρ⁻¹ = (m : ℂ) * ρ⁻¹ ^ 3 := one_sub_inv_eq hρ0 hρm
  have hq : (1 + C (ρ - 1) * X + C (ρ * (ρ - 1)) * X ^ 2 : ℂ[X]).eval ρ⁻¹ =
      ρ⁻¹ * (1 + 3 * m * ρ⁻¹ ^ 2) := by
    simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, eval_pow]
    linear_combination (ρ * ρ⁻¹ + 2 - ρ⁻¹) * hx1 + 3 * hrel
  have hreal : ((cm m : ℝ) : ℂ) = (((Wpoly ℝ m).eval (rho m)⁻¹ /
      ((Ppoly ℝ (m - 1)).eval (rho m)⁻¹ * ((rho m)⁻¹ * (1 + 3 * m * (rho m)⁻¹ ^ 2))) : ℝ) : ℂ) := by
    rw [cm_eq_W hm]
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, ← eval_ofReal_map, ← eval_ofReal_map,
    Wpoly_map, Ppoly_map] at hreal
  push_cast at hreal
  rw [← hρdef] at hreal
  rw [hreal, alpha, hcof, eval_mul, hq]

/-- 辅助引理（定理 3.2(3)）：`m ≥ 1` 时 `α_m(ρ_{m−1}) = −c_{m−1}ρ_{m−1}³`（由定理 3.2(2) 第二句）。 -/
theorem alpha_rho_pred {m : ℕ} (hm : 1 ≤ m) :
    alpha m (rho (m - 1)) = -(cm (m - 1) : ℂ) * ((rho (m - 1) : ℝ) : ℂ) ^ 3 := by
  have hne0 : ((rho (m - 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos (m - 1)).ne'
  have hspec : ((rho (m - 1) : ℝ) : ℂ) ^ 3 - ((rho (m - 1) : ℝ) : ℂ) ^ 2 = ((m - 1 : ℕ) : ℂ) := by
    exact_mod_cast rho_spec (m - 1)
  have h := alpha_eq (j := m - 1) (m := m) (by omega) hne0 hspec
  rw [Nat.sub_sub_self hm, pow_one, Nat.factorial_one, Nat.cast_one, div_one, alpha_rho] at h
  rw [h]
  ring

/-- 辅助引理（定理 3.2(3)）：`m ≥ 1` 时 `ρ_m(ρ_m − 1) < ρ_{m−1}²`（定理 3.2(1) 的证明里的不等式）。 -/
theorem rho_mul_lt_rho_pred_sq {m : ℕ} (hm : 1 ≤ m) : rho m * (rho m - 1) < rho (m - 1) ^ 2 := by
  have hρ : 1 < rho m := one_lt_rho hm
  have hlt : rho (m - 1) < rho m := rho_strictMono (by omega)
  have hge : 1 ≤ rho (m - 1) := one_le_rho (m - 1)
  have hspec : rho (m - 1) ^ 3 - rho (m - 1) ^ 2 = (m : ℝ) - 1 := by
    have h := rho_spec (m - 1)
    rw [Nat.cast_sub hm, Nat.cast_one] at h
    exact h
  have hkey : (m : ℝ) < rho (m - 1) ^ 2 * rho m := by
    have h1 : 0 < rho (m - 1) ^ 2 * (rho m - rho (m - 1)) :=
      mul_pos (pow_pos (by linarith) 2) (sub_pos.mpr hlt)
    have h2 : 1 ≤ rho (m - 1) ^ 2 := by nlinarith
    nlinarith
  have hm' : rho m * (rho m - 1) * rho m = m := by linear_combination rho_spec m
  by_contra hcon
  have h3 := mul_le_mul_of_nonneg_right (not_lt.mp hcon) (le_of_lt (show (0 : ℝ) < rho m by linarith))
  linarith

/-- **定理 3.2(3)**：`m ≥ 1` 时 `τ_m < ρ_{m−1}`。 -/
theorem tau_lt {m : ℕ} (hm : 1 ≤ m) : tau m < rho (m - 1) := by
  have hsq : Real.sqrt (rho m * (rho m - 1)) < rho (m - 1) := by
    have h0 : 0 ≤ rho m * (rho m - 1) := mul_nonneg (rho_pos m).le (by linarith [one_le_rho m])
    calc Real.sqrt (rho m * (rho m - 1)) < Real.sqrt (rho (m - 1) ^ 2) :=
          Real.sqrt_lt_sqrt h0 (rho_mul_lt_rho_pred_sq hm)
      _ = rho (m - 1) := Real.sqrt_sq (rho_pos _).le
  unfold tau
  split_ifs with h
  · subst h
    exact hsq
  · exact max_lt (rho_strictMono (by omega)) hsq

/-- 辅助引理（定理 3.2(3)）：`Q_m` 中除 `ρ_m`、`ρ_{m−1}` 外的根的模都不超过 `τ_m`。 -/
theorem norm_le_tau {m : ℕ} (hm : 1 ≤ m) {σ : ℂ} (hσ : σ ∈ sig m) (h1 : σ ≠ (rho m : ℂ))
    (h2 : σ ≠ (rho (m - 1) : ℂ)) : ‖σ‖ ≤ tau m := by
  obtain ⟨i, him, hi⟩ := sig_level hσ
  have hσ0 := (mem_sig.mp hσ).1
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have hσ1 : σ = 1 := eq_one_of_cubic_zero hσ0 hi
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm1 : m = 1 := by omega
      apply h2
      rw [hσ1, hm1]
      simp [rho_zero]
    rw [hσ1, norm_one, tau, ite_eq_right (show ¬m = 1 by omega)]
    exact (one_le_rho _).trans (le_max_left _ _)
  · by_cases hρi : σ = (rho i : ℂ)
    · have him' : i ≠ m := fun h => h1 (by rw [hρi, h])
      have him'' : i ≠ m - 1 := fun h => h2 (by rw [hρi, h])
      rw [hρi, Complex.norm_real, Real.norm_of_nonneg (rho_pos i).le, tau, ite_eq_right (show ¬m = 1 by omega)]
      exact (rho_strictMono.monotone (by omega : i ≤ m - 2)).trans (le_max_left _ _)
    · have hns := (normSq_eq_of_root (by omega) (by linear_combination hi) hρi).1
      have hle : rho i * (rho i - 1) ≤ rho m * (rho m - 1) := rho_mul_rho_sub_one_strictMono.monotone him
      have hnorm : ‖σ‖ ≤ Real.sqrt (rho m * (rho m - 1)) := by
        rw [← Real.sqrt_sq (norm_nonneg σ), ← Complex.normSq_eq_norm_sq, hns]
        exact Real.sqrt_le_sqrt hle
      unfold tau
      split_ifs with h
      · subst h
        exact hnorm
      · exact hnorm.trans (le_max_right _ _)

/-- **定理 3.2(3)**（误差界）：`m ≥ 1` 时有常数 `C`，对一切 `k ≥ 0`，
`|U_k(m) − (c_m ρ_m^k − c_{m−1} ρ_{m−1}^{k+3})| ≤ C·τ_m^k`。 -/
theorem U_asymp_bound {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ k : ℕ,
      |(U k m : ℝ) - (cm m * rho m ^ k - cm (m - 1) * rho (m - 1) ^ (k + 3))| ≤ C * tau m ^ k := by
  have hρ0 : ((rho m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos m).ne'
  have hρ0' : ((rho (m - 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos (m - 1)).ne'
  have hmem1 : ((rho m : ℝ) : ℂ) ∈ sig m :=
    mem_sig_of_cubic (j := m) (m := m) le_rfl hρ0 (by exact_mod_cast rho_spec m)
  have hne : ((rho (m - 1) : ℝ) : ℂ) ≠ ((rho m : ℝ) : ℂ) := fun h =>
    (rho_strictMono (by omega : m - 1 < m)).ne (Complex.ofReal_injective h)
  have hmem2 : ((rho (m - 1) : ℝ) : ℂ) ∈ (sig m).erase ((rho m : ℝ) : ℂ) :=
    mem_erase.mpr ⟨hne, mem_sig_of_cubic (j := m - 1) (m := m) (by omega) hρ0'
      (by exact_mod_cast rho_spec (m - 1))⟩
  refine ⟨∑ σ ∈ ((sig m).erase ((rho m : ℝ) : ℂ)).erase ((rho (m - 1) : ℝ) : ℂ), ‖alpha m σ‖, fun k => ?_⟩
  have hU := U_eq_sum_alpha m k
  rw [← add_sum_erase (sig m) (fun σ => alpha m σ * σ ^ k) hmem1,
    ← add_sum_erase ((sig m).erase ((rho m : ℝ) : ℂ)) (fun σ => alpha m σ * σ ^ k) hmem2,
    alpha_rho m, alpha_rho_pred hm] at hU
  have hdiff : ((((U k m : ℝ) - (cm m * rho m ^ k - cm (m - 1) * rho (m - 1) ^ (k + 3)) : ℝ)) : ℂ) =
      ∑ σ ∈ ((sig m).erase ((rho m : ℝ) : ℂ)).erase ((rho (m - 1) : ℝ) : ℂ), alpha m σ * σ ^ k := by
    push_cast
    rw [hU]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun σ hσ => ?_)
  rw [mem_erase, mem_erase] at hσ
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg σ) (norm_le_tau hm hσ.2.2 hσ.2.1 hσ.1) k) (norm_nonneg _)

/-- **定理 3.2(3)**（渐近式）：`m ≥ 1` 时 `U_k(m) = c_m ρ_m^k − c_{m−1} ρ_{m−1}^{k+3} + O(τ_m^k)`（`k → ∞`）。 -/
theorem U_asymp {m : ℕ} (hm : 1 ≤ m) :
    (fun k : ℕ => (U k m : ℝ) - (cm m * rho m ^ k - cm (m - 1) * rho (m - 1) ^ (k + 3))) =O[atTop]
      fun k : ℕ => tau m ^ k := by
  obtain ⟨C, hC⟩ := U_asymp_bound hm
  refine IsBigO.of_bound C (Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (tau_nonneg m) k)]
  exact hC k

/-- **定理 3.2(3)**：`m ≥ 1` 时，`c_m = α_m(ρ_m) > 0`；`G_{m−1}(x_m) = Σ_k U_k(m−1)·x_m^k` 收敛，且
`c_m = (G_{m−1}(x_m) + m x_m²)/(x_m(1 + 3m x_m²))`（`x_m = 1/ρ_m`；第二个表达式是 `cm` 的定义）；`τ_m < ρ_{m−1}`；
`U_k(m) = c_m ρ_m^k − c_{m−1} ρ_{m−1}^{k+3} + O(τ_m^k)`。另有 `c_0 = 1`（`cm_zero`）。 -/
theorem thm_asym_three {m : ℕ} (hm : 1 ≤ m) :
    (cm m : ℂ) = alpha m (rho m) ∧ 0 < cm m ∧
      (∃ g : ℝ, HasSum (fun k => (U k (m - 1) : ℝ) * (rho m)⁻¹ ^ k) g ∧
        cm m = (g + m * (rho m)⁻¹ ^ 2) / ((rho m)⁻¹ * (1 + 3 * m * (rho m)⁻¹ ^ 2))) ∧
      tau m < rho (m - 1) ∧
      (fun k : ℕ => (U k m : ℝ) - (cm m * rho m ^ k - cm (m - 1) * rho (m - 1) ^ (k + 3))) =O[atTop]
        fun k : ℕ => tau m ^ k := by
  refine ⟨(alpha_rho m).symm, cm_pos m, ⟨_, hasSum_G (inv_nonneg.mpr (rho_pos m).le) ?_, cm_eq_G hm⟩,
    tau_lt hm, U_asymp hm⟩
  have hlt : rho (m - 1) < rho m := rho_strictMono (by omega)
  have h := mul_lt_mul_of_pos_left hlt (inv_pos.mpr (rho_pos m))
  rwa [inv_mul_cancel₀ (rho_pos m).ne'] at h

end A207123
