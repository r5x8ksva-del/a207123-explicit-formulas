import A207123.ShapeFibre

/-!
# `X³ + X − 1` 的根（论文定理 6.3 情形分析用的数论事实）

* `irreducible_fQ`：`X³ + X − 1` 在 `ℚ` 上不可约（没有有理根：首一整系数多项式的有理根是整除常数项的整数，
  `exists_integer_of_is_root_of_monic`）；`eq_zero_of_aeval_root_b1`、`quad_rel_root_b1`：次数 `≤ 2` 的有理系数
  多项式在 `X³ + X − 1` 的任一复根处为 0 只能是零多项式（`minpoly ℚ z = X³ + X − 1`；论文说「`ℚ(ξ)` 是三次域」）。
* `exists_real_root_b1`：实根 `r ∈ (2/3, 1)`；`complex_root_b1`：复根 `z = −r/2 + i√(3r²/4 + 1)`，`|z|² = r² + 1`。
* `real_root_pow_not_rat`：`N ≥ 1` 时 `r^N ∉ ℚ`。论文用范数（`r^N = q` 则 `q³ = N(r)^N = 1`）；这里把 `X^N` 对
  `X³ + X − 1` 取余，余式在 `r` 处等于 `q`，只能是常数 `q`，于是复根也满足 `z^N = q`，但 `|z| > 1 > r`。
* `root_poly_eq_of_eq`：同理，有理系数多项式 `g` 在 `r` 处为 0 时在每个根处都为 0（情形 `α = 0` 用）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 在 `ℚ` 上不可约 -/

/-- `f = X³ + X − 1 ∈ ℚ[X]`。 -/
def fQ : ℚ[X] := X ^ 3 + (X - 1)

theorem degree_X_sub_one_lt_three {R : Type*} [CommRing R] [Nontrivial R] : (X - 1 : R[X]).degree < 3 := by
  have h1 : (X - 1 : R[X]).degree ≤ 1 :=
    (degree_sub_le _ _).trans (max_le degree_X_le (degree_one_le.trans zero_le_one))
  exact h1.trans_lt (by norm_num)

theorem fQ_monic : fQ.Monic := monic_X_pow_add degree_X_sub_one_lt_three

theorem natDegree_fQ : fQ.natDegree = 3 := by
  rw [fQ, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_X_sub_one_lt_three),
    natDegree_X_pow]

theorem aeval_fQ (z : ℂ) : aeval z fQ = z ^ 3 + z - 1 := by
  simp only [fQ, map_add, map_sub, map_pow, aeval_X, map_one]
  ring

/-- `X³ + X − 1` 没有有理根。 -/
theorem no_rat_root_b1 (q : ℚ) : q ^ 3 + q - 1 ≠ 0 := by
  intro hq
  have hp : (X ^ 3 + (X - 1) : ℤ[X]).Monic := monic_X_pow_add degree_X_sub_one_lt_three
  have hr : aeval q (X ^ 3 + (X - 1) : ℤ[X]) = 0 := by
    simp only [map_add, map_sub, map_pow, aeval_X, map_one]
    linear_combination hq
  obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic hp hr
  rw [hn] at hq
  have hz : (n : ℚ) ^ 3 + n - 1 = 0 := by simpa using hq
  have hz' : n ^ 3 + n - 1 = 0 := by exact_mod_cast hz
  rcases le_or_gt n 0 with h | h
  · nlinarith [sq_nonneg n]
  · nlinarith [sq_nonneg n, mul_pos h h]

theorem irreducible_fQ : Irreducible fQ := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_fQ]; simp) fun x hx => ?_
  apply no_rat_root_b1 x
  simp only [IsRoot, fQ, eval_add, eval_sub, eval_pow, eval_X, eval_one] at hx
  linear_combination hx

theorem minpoly_root_b1 {z : ℂ} (hz : z ^ 3 + z - 1 = 0) : minpoly ℚ z = fQ :=
  (minpoly.eq_of_irreducible_of_monic irreducible_fQ (by rw [aeval_fQ]; exact hz) fQ_monic).symm

/-- 次数 `≤ 2` 的有理系数多项式在 `X³ + X − 1` 的根处为 0 只能是零多项式。 -/
theorem eq_zero_of_aeval_root_b1 {z : ℂ} (hz : z ^ 3 + z - 1 = 0) {p : ℚ[X]} (hp : p.natDegree ≤ 2)
    (h : aeval z p = 0) : p = 0 := by
  by_contra hp0
  have hdvd := minpoly.dvd ℚ z h
  rw [minpoly_root_b1 hz] at hdvd
  have := natDegree_le_of_dvd hdvd hp0
  rw [natDegree_fQ] at this
  omega

theorem quad_rel_root_b1 {z : ℂ} (hz : z ^ 3 + z - 1 = 0) {a b c : ℚ}
    (h : (a : ℂ) + b * z + c * z ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hp : C a + C b * X + C c * X ^ 2 = (0 : ℚ[X]) := by
    refine eq_zero_of_aeval_root_b1 hz ?_ ?_
    · compute_degree!
    · simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
      exact h
  have h0 := congrArg (coeff · 0) hp
  have h1 := congrArg (coeff · 1) hp
  have h2 := congrArg (coeff · 2) hp
  simp at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- 有理系数多项式 `X^N` 对 `X³ + X − 1` 的余式：在每个根 `w` 处 `R(w) = w^N`。 -/
theorem aeval_mod_fQ {w : ℂ} (hw : w ^ 3 + w - 1 = 0) (g : ℚ[X]) : aeval w (g %ₘ fQ) = aeval w g := by
  have hsplit := modByMonic_add_div g fQ
  have := congrArg (aeval w) hsplit
  rw [map_add, map_mul, aeval_fQ, hw, zero_mul, add_zero] at this
  exact this

theorem natDegree_mod_fQ_le (g : ℚ[X]) : (g %ₘ fQ).natDegree ≤ 2 := by
  have hne : fQ ≠ 1 := by
    intro h
    have := natDegree_fQ
    rw [h, natDegree_one] at this
    omega
  have := natDegree_modByMonic_lt g fQ_monic hne
  rw [natDegree_fQ] at this
  omega

/-- 有理系数多项式在 `X³ + X − 1` 的一个根处为 0，则在每个根处都为 0。 -/
theorem aeval_root_b1_eq_zero {z w : ℂ} (hz : z ^ 3 + z - 1 = 0) (hw : w ^ 3 + w - 1 = 0) {g : ℚ[X]}
    (hg : aeval z g = 0) : aeval w g = 0 := by
  have h0 : g %ₘ fQ = 0 := by
    refine eq_zero_of_aeval_root_b1 hz (natDegree_mod_fQ_le g) ?_
    rw [aeval_mod_fQ hz, hg]
  rw [← aeval_mod_fQ hw, h0, map_zero]

/-! ## 2. 实根与复根 -/

theorem exists_real_root_b1 : ∃ r : ℝ, r ^ 3 + r - 1 = 0 ∧ 2 / 3 < r ∧ r < 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 + x - 1) (Set.Icc (2 / 3) 1) := by fun_prop
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (by norm_num : (2 / 3 : ℝ) ≤ 1) hcont
    (show (0 : ℝ) ∈ Set.Icc ((2 / 3 : ℝ) ^ 3 + 2 / 3 - 1) ((1 : ℝ) ^ 3 + 1 - 1) by norm_num)
  refine ⟨r, hr0, lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_⟩
  · rintro rfl
    norm_num at hr0
  · rintro rfl
    norm_num at hr0

/-- `r` 是实根时 `z = −r/2 + i√(3r²/4 + 1)` 是另一个根，`|z|² = r² + 1`。 -/
theorem complex_root_b1 {r : ℝ} (hr : r ^ 3 + r - 1 = 0) :
    ∃ z : ℂ, z ^ 3 + z - 1 = 0 ∧ Complex.normSq z = r ^ 2 + 1 := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = Real.sqrt (3 * r ^ 2 / 4 + 1) := ⟨_, rfl⟩
  have hγ2 : γ ^ 2 = 3 * r ^ 2 / 4 + 1 := by rw [hγ]; exact Real.sq_sqrt (by positivity)
  have hγc : (γ : ℂ) ^ 2 = 3 * (r : ℂ) ^ 2 / 4 + 1 := by exact_mod_cast hγ2
  have hrc : (r : ℂ) ^ 3 + r - 1 = 0 := by exact_mod_cast hr
  refine ⟨((-r / 2 : ℝ) : ℂ) + γ * Complex.I, ?_, ?_⟩
  · have hq : (((-r / 2 : ℝ) : ℂ) + γ * Complex.I) ^ 2 + r * (((-r / 2 : ℝ) : ℂ) + γ * Complex.I) +
        ((r : ℂ) ^ 2 + 1) = 0 := by
      push_cast
      linear_combination (γ : ℂ) ^ 2 * Complex.I_sq - hγc
    have e : ∀ w : ℂ, w ^ 3 + w - 1 = (w - r) * (w ^ 2 + r * w + ((r : ℂ) ^ 2 + 1)) := by
      intro w
      linear_combination hrc
    rw [e, hq, mul_zero]
  · rw [Complex.normSq_add_mul_I]
    linear_combination hγ2

/-- `N ≥ 1` 时实根的 `N` 次幂不是有理数。 -/
theorem real_root_pow_not_rat {r : ℝ} (hr : r ^ 3 + r - 1 = 0) (hr0 : 0 < r) (hr1 : r < 1)
    {N : ℕ} (hN : 1 ≤ N) (q : ℚ) : (r : ℂ) ^ N ≠ q := by
  intro h
  obtain ⟨z, hz, hnz⟩ := complex_root_b1 hr
  have hrc : (r : ℂ) ^ 3 + r - 1 = 0 := by exact_mod_cast hr
  -- `X^N − q` 在 `r` 处为 0，所以在 `z` 处也为 0
  have hg : aeval (r : ℂ) (X ^ N - C q : ℚ[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast, h, sub_self]
  have hgz := aeval_root_b1_eq_zero hrc hz hg
  rw [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast, sub_eq_zero] at hgz
  -- 取模：`|z|^N = r^N`，但 `|z| > 1 > r`
  have hn1 : ‖z‖ ^ N = r ^ N := by
    rw [← norm_pow, hgz, ← h, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hz1 : 1 < ‖z‖ := by
    have h2 : ‖z‖ ^ 2 = r ^ 2 + 1 := by rw [← Complex.normSq_eq_norm_sq, hnz]
    nlinarith [norm_nonneg z, sq_nonneg r]
  have hlt1 : 1 < ‖z‖ ^ N := one_lt_pow₀ hz1 (by omega)
  have hlt2 : r ^ N < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  linarith

end

end A207123
