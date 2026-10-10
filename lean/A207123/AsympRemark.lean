import A207123.RootAsymp

/-!
# 论文注记 3.3：渐近式的推论与特例（精确的部分）

论文注记 3.3 中的精确陈述：
* `U_k(m)/(c_m ρ_m^k) − 1 = −κ_m θ_m^k (1 + o(1))`，`θ_m = ρ_{m−1}/ρ_m`，`κ_m = c_{m−1}ρ_{m−1}³/c_m > 0`，且速率 `θ_m`
  不能改进：`tendsto_ratio`（`(U_k(m)/(c_m ρ_m^k) − 1)/θ_m^k → −κ_m`）、`kappaConst_pos`、`rate_not_improvable`
  （对 `0 ≤ θ' < θ_m`，`U_k(m)/(c_m ρ_m^k) − 1` 不是 `O(θ'^k)`）。
* `c_1 = (10 + 15ρ_1 + 17ρ_1²)/31`：`cm_one`。
* `ρ_m` 是整数当且仅当 `m = y²(y − 1)`（`m = 4, 18, 48, …`），此时 `c_m` 是有理数：`rho_int_iff`、`cm_rat_of_rho_int`。
* `ρ_4 = 2`、`c_4 = 215/2`、`U_k(4) = (215/2)·2^k − c_3 ρ_3^{k+3} + O(ρ_2^k)`：`rho_four`、`cm_four`、`U_four_asymp`。
* `1 − θ_m ~ 1/(3m)`（`m → ∞`）：`tendsto_one_sub_theta`（`m(1 − θ_m) → 1/3`）。
注记里的数值（`ρ_1 ≈ 1.46557`、`c_1 ≈ 2.20961` 等、`κ_m` 在 `1 ≤ m ≤ 24` 内递增、相对误差）是数值观察，不在这里。
`θ_m`、`κ_m` 在 Lean 里叫 `thetaRatio`、`kappaConst`（`theta` 已用作 `NonDFinite.lean` 的算子名）。

证明：比值式由定理 3.2(3) 的误差界 `U_asymp_bound` 与 `τ_m < ρ_{m−1}` 得到；`1 − θ_m ~ 1/(3m)` 用
`(ρ_m − ρ_{m−1})(ρ_m² + ρ_m ρ_{m−1} + ρ_{m−1}² − ρ_m − ρ_{m−1}) = 1`（中值定理的离散形式）与 `ρ_m → ∞`、`ρ_{m−1}/ρ_m → 1`。
-/

open Polynomial Finset Filter Asymptotics Topology

namespace A207123

/-- 注记 3.3 的 `θ_m = ρ_{m−1}/ρ_m`。 -/
noncomputable def thetaRatio (m : ℕ) : ℝ := rho (m - 1) / rho m

/-- 注记 3.3 的 `κ_m = c_{m−1}ρ_{m−1}³/c_m`。 -/
noncomputable def kappaConst (m : ℕ) : ℝ := cm (m - 1) * rho (m - 1) ^ 3 / cm m

/-- **注记 3.3**：`κ_m > 0`。 -/
theorem kappaConst_pos (m : ℕ) : 0 < kappaConst m := by
  have h1 := cm_pos (m - 1)
  have h2 := cm_pos m
  have h3 := rho_pos (m - 1)
  unfold kappaConst
  positivity

/-- **注记 3.3**：`m ≥ 1` 时 `(U_k(m)/(c_m ρ_m^k) − 1)/θ_m^k → −κ_m`（`k → ∞`），即
`U_k(m)/(c_m ρ_m^k) − 1 = −κ_m θ_m^k (1 + o(1))`。 -/
theorem tendsto_ratio {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => ((U k m : ℝ) / (cm m * rho m ^ k) - 1) / thetaRatio m ^ k) atTop
      (𝓝 (-kappaConst m)) := by
  obtain ⟨C, hC⟩ := U_asymp_bound hm
  have hc := cm_pos m
  have hc0 : cm m ≠ 0 := hc.ne'
  have hρ := rho_pos m
  have hρ0 : rho m ≠ 0 := hρ.ne'
  have hρ' := rho_pos (m - 1)
  have hρ0' : rho (m - 1) ≠ 0 := hρ'.ne'
  have hτ0 := tau_nonneg m
  have hτ := tau_lt hm
  have hid : ∀ k : ℕ, ((U k m : ℝ) / (cm m * rho m ^ k) - 1) / thetaRatio m ^ k - -kappaConst m =
      ((U k m : ℝ) - (cm m * rho m ^ k - cm (m - 1) * rho (m - 1) ^ (k + 3))) / (cm m * rho (m - 1) ^ k) := by
    intro k
    unfold thetaRatio kappaConst
    rw [div_pow]
    field_simp
    ring
  have hg : Tendsto (fun k : ℕ => C / cm m * (tau m / rho (m - 1)) ^ k) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hτ0 hρ'.le) ((div_lt_one hρ').mpr hτ)).const_mul
      (C / cm m)
    rwa [mul_zero] at h
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun k => ?_) hg
  show ‖((U k m : ℝ) / (cm m * rho m ^ k) - 1) / thetaRatio m ^ k - -kappaConst m‖ ≤
    C / cm m * (tau m / rho (m - 1)) ^ k
  rw [hid k, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < cm m * rho (m - 1) ^ k),
    div_le_iff₀ (by positivity : 0 < cm m * rho (m - 1) ^ k)]
  calc |(U k m : ℝ) - (cm m * rho m ^ k - cm (m - 1) * rho (m - 1) ^ (k + 3))| ≤ C * tau m ^ k := hC k
    _ = C / cm m * (tau m / rho (m - 1)) ^ k * (cm m * rho (m - 1) ^ k) := by
      rw [div_pow]
      field_simp

/-- **注记 3.3**（速率不能改进）：`m ≥ 1`、`0 ≤ θ' < θ_m` 时 `U_k(m)/(c_m ρ_m^k) − 1` 不是 `O(θ'^k)`。 -/
theorem rate_not_improvable {m : ℕ} (hm : 1 ≤ m) {θ' : ℝ} (hθ' : 0 ≤ θ') (hlt : θ' < thetaRatio m) :
    ¬ (fun k : ℕ => (U k m : ℝ) / (cm m * rho m ^ k) - 1) =O[atTop] fun k : ℕ => θ' ^ k := by
  intro h
  have hθ : 0 < thetaRatio m := div_pos (rho_pos _) (rho_pos _)
  have h2 : (fun k : ℕ => ((U k m : ℝ) / (cm m * rho m ^ k) - 1) / thetaRatio m ^ k) =O[atTop]
      fun k : ℕ => (θ' / thetaRatio m) ^ k := by
    refine (h.mul (isBigO_refl (fun k : ℕ => (thetaRatio m ^ k)⁻¹) atTop)).congr (fun k => ?_) (fun k => ?_)
    · show ((U k m : ℝ) / (cm m * rho m ^ k) - 1) * (thetaRatio m ^ k)⁻¹ =
        ((U k m : ℝ) / (cm m * rho m ^ k) - 1) / thetaRatio m ^ k
      exact (div_eq_mul_inv _ _).symm
    · show θ' ^ k * (thetaRatio m ^ k)⁻¹ = (θ' / thetaRatio m) ^ k
      rw [div_pow, div_eq_mul_inv]
  have h3 : Tendsto (fun k : ℕ => ((U k m : ℝ) / (cm m * rho m ^ k) - 1) / thetaRatio m ^ k) atTop (𝓝 0) :=
    h2.trans_tendsto
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hθ' hθ.le) ((div_lt_one hθ).mpr hlt))
  have h4 := tendsto_nhds_unique h3 (tendsto_ratio hm)
  have h5 := kappaConst_pos m
  linarith

/-- **注记 3.3**：`c_1 = (10 + 15ρ_1 + 17ρ_1²)/31`。 -/
theorem cm_one : cm 1 = (10 + 15 * rho 1 + 17 * rho 1 ^ 2) / 31 := by
  have hρ : rho 1 ≠ 0 := (rho_pos 1).ne'
  have h := rho_spec 1
  rw [Nat.cast_one] at h
  have hden : rho 1 ^ 2 + 3 ≠ 0 := by positivity
  have hc : cm 1 = rho 1 ^ 6 / (rho 1 ^ 2 + 3) * (1 + (rho 1 ^ 5)⁻¹) := by
    rw [cm, Finset.Icc_self, sum_singleton, Nat.descFactorial_self, Nat.factorial_one]
    norm_num
  have h5 : rho 1 ^ 5 * (rho 1 ^ 5)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 5 hρ)
  have key : rho 1 ^ 6 * (1 + (rho 1 ^ 5)⁻¹) = rho 1 ^ 6 + rho 1 := by
    linear_combination rho 1 * h5
  rw [hc, div_mul_eq_mul_div, key, div_eq_div_iff hden (by norm_num : (31 : ℝ) ≠ 0)]
  linear_combination (31 * rho 1 ^ 3 + 31 * rho 1 ^ 2 + 14 * rho 1 + 30) * h

/-- 辅助引理（注记 3.3）：`m ≥ 1`、`y³ − y² = m` 时 `ρ_m = y`（`ρ_m` 是唯一实根）。 -/
theorem rho_eq_of_root {m : ℕ} (hm : 1 ≤ m) {y : ℝ} (hy : y ^ 3 - y ^ 2 = m) : rho m = y :=
  (existsUnique_rho hm).unique (by linarith [rho_spec m]) (by linarith)

/-- **注记 3.3**：`ρ_4 = 2`。 -/
theorem rho_four : rho 4 = 2 := rho_eq_of_root (by norm_num) (by norm_num)

/-- **注记 3.3**：`c_4 = 215/2`。 -/
theorem cm_four : cm 4 = 215 / 2 := by
  have hI : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hf : Nat.factorial 4 = 24 := rfl
  have d1 : Nat.descFactorial 4 1 = 4 := rfl
  have d2 : Nat.descFactorial 4 2 = 12 := rfl
  have d3 : Nat.descFactorial 4 3 = 24 := rfl
  have d4 : Nat.descFactorial 4 4 = 24 := rfl
  rw [cm, rho_four, hI]
  norm_num [Finset.sum_insert, hf, d1, d2, d3, d4]

/-- 辅助引理（注记 3.3）：`τ_4 = ρ_2`（`√(ρ_4(ρ_4 − 1)) = √2 ≤ ρ_2`）。 -/
theorem tau_four : tau 4 = rho 2 := by
  have h2 : Real.sqrt (rho 4 * (rho 4 - 1)) ≤ rho 2 := by
    rw [rho_four]
    have hspec := rho_spec 2
    norm_num at hspec
    have h1 := one_lt_rho (show 1 ≤ 2 by norm_num)
    have hsq : (2 : ℝ) ≤ rho 2 ^ 2 := by nlinarith [sq_nonneg (rho 2 - 1)]
    calc Real.sqrt (2 * (2 - 1)) = Real.sqrt 2 := by norm_num
      _ ≤ Real.sqrt (rho 2 ^ 2) := Real.sqrt_le_sqrt hsq
      _ = rho 2 := Real.sqrt_sq (rho_pos 2).le
  rw [tau, ite_eq_right (show ¬(4 : ℕ) = 1 by norm_num), show (4 - 2 : ℕ) = 2 from rfl]
  exact max_eq_left h2

/-- **注记 3.3**：`U_k(4) = (215/2)·2^k − c_3 ρ_3^{k+3} + O(ρ_2^k)`。 -/
theorem U_four_asymp :
    (fun k : ℕ => (U k 4 : ℝ) - (215 / 2 * 2 ^ k - cm 3 * rho 3 ^ (k + 3))) =O[atTop]
      fun k : ℕ => rho 2 ^ k := by
  have h := U_asymp (m := 4) (by norm_num)
  rw [cm_four, rho_four, tau_four, show (4 - 1 : ℕ) = 3 from rfl] at h
  exact h

/-- **注记 3.3**：`ρ_m` 是整数当且仅当 `m = y²(y − 1)`（`y` 是自然数）。 -/
theorem rho_int_iff (m : ℕ) : (∃ n : ℤ, rho m = n) ↔ ∃ y : ℕ, m = y ^ 2 * (y - 1) := by
  constructor
  · rintro ⟨n, hn⟩
    have h1 : (1 : ℝ) ≤ n := by
      rw [← hn]
      exact one_le_rho m
    have hn1 : 1 ≤ n := by exact_mod_cast h1
    have hspec := rho_spec m
    rw [hn] at hspec
    refine ⟨n.toNat, ?_⟩
    have hy : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
    have hm : (m : ℤ) = n ^ 3 - n ^ 2 := by exact_mod_cast hspec.symm
    have h1' : 1 ≤ n.toNat := by omega
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1', Nat.cast_one, hy, hm]
    ring
  · rintro ⟨y, rfl⟩
    rcases Nat.lt_or_ge y 2 with hy | hy
    · have h0 : y ^ 2 * (y - 1) = 0 := by interval_cases y <;> rfl
      rw [h0, rho_zero]
      exact ⟨1, by norm_num⟩
    · refine ⟨y, ?_⟩
      have hm1 : 1 ≤ y ^ 2 * (y - 1) :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega))
      rw [rho_eq_of_root hm1 (y := (y : ℝ))]
      · simp
      · push_cast [Nat.cast_sub (by omega : 1 ≤ y)]
        ring

/-- **注记 3.3**：`ρ_m` 是整数时 `c_m` 是有理数。 -/
theorem cm_rat_of_rho_int {m : ℕ} {n : ℤ} (hn : rho m = n) : ∃ q : ℚ, cm m = q := by
  refine ⟨(n : ℚ) ^ (3 * m + 3) / ((m.factorial : ℚ) * ((n : ℚ) ^ 2 + 3 * m)) *
    (1 + ∑ j ∈ Icc 1 m, (j : ℚ) * (m.descFactorial j : ℚ) * ((n : ℚ) ^ (3 * j + 2))⁻¹), ?_⟩
  rw [cm, hn]
  push_cast
  ring

/-- 辅助引理（注记 3.3）：`ρ_m → ∞`。 -/
theorem tendsto_rho : Tendsto rho atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun R => ⟨⌈R ^ 3⌉₊ + 1, fun m hm => ?_⟩
  by_contra hlt0
  have hlt : rho m < R := not_le.mp hlt0
  have hρ := rho_pos m
  have h1 : (m : ℝ) < rho m ^ 3 := by
    have := rho_spec m
    nlinarith
  have h2 : rho m ^ 3 < R ^ 3 := pow_lt_pow_left₀ hlt hρ.le (by norm_num)
  have h3 : R ^ 3 ≤ ⌈R ^ 3⌉₊ := Nat.le_ceil _
  have h4 : ((⌈R ^ 3⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  push_cast at h4
  linarith

/-- 辅助引理（注记 3.3）：`(ρ_m − ρ_{m−1})(ρ_m² + ρ_m ρ_{m−1} + ρ_{m−1}² − ρ_m − ρ_{m−1}) = 1`（`m ≥ 1`）。 -/
theorem rho_diff_mul {m : ℕ} (hm : 1 ≤ m) :
    (rho m - rho (m - 1)) * (rho m ^ 2 + rho m * rho (m - 1) + rho (m - 1) ^ 2 - rho m - rho (m - 1)) = 1 := by
  have h := rho_spec (m - 1)
  rw [Nat.cast_sub hm, Nat.cast_one] at h
  linear_combination rho_spec m - h

/-- 辅助引理（注记 3.3）：`a, b ≥ 1` 时 `a² + ab + b² − a − b ≥ 1`。 -/
theorem one_le_D {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a ^ 2 + a * b + b ^ 2 - a - b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (le_trans zero_le_one ha),
    mul_nonneg (sub_nonneg.mpr hb) (le_trans zero_le_one hb), mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)]

/-- 辅助引理（注记 3.3）：`m ≥ 1` 时 `ρ_m − 1 ≤ ρ_{m−1}`。 -/
theorem rho_sub_one_le {m : ℕ} (hm : 1 ≤ m) : rho m - 1 ≤ rho (m - 1) := by
  have hd := rho_diff_mul hm
  have hD := one_le_D (one_le_rho m) (one_le_rho (m - 1))
  by_contra h0
  have h : rho (m - 1) < rho m - 1 := not_le.mp h0
  have h' : 1 < rho m - rho (m - 1) := by linarith
  nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr h')) (sub_nonneg.mpr hD)]

/-- 辅助引理（注记 3.3）：`a·x = 1` 时 `1 + bx + (bx)² − x − bx·x = (a² + ab + b² − a − b)·x²`。 -/
theorem D'_eq {a b x : ℝ} (hx : a * x = 1) :
    1 + b * x + (b * x) ^ 2 - x - b * x * x = (a ^ 2 + a * b + b ^ 2 - a - b) * x ^ 2 := by
  linear_combination (-(1 + a * x + b * x - x)) * hx

/-- 辅助引理（注记 3.3）：`(a − b)(a² + ab + b² − a − b) = 1`、`a³ − a² = M`、`a·x = 1` 时
`1 − x = M(1 − bx)(1 + bx + (bx)² − x − bx·x)`（即 `M(1 − b/a) = (1 − 1/a)/((a² + ab + b² − a − b)/a²)`）。 -/
theorem theta_identity {a b x M : ℝ} (hd : (a - b) * (a ^ 2 + a * b + b ^ 2 - a - b) = 1)
    (hm : a ^ 3 - a ^ 2 = M) (hx : a * x = 1) :
    1 - x = M * (1 - b * x) * (1 + b * x + (b * x) ^ 2 - x - b * x * x) := by
  linear_combination (-(M * x ^ 3)) * hd + x ^ 3 * hm -
    ((a * x) ^ 2 + a * x + 1 - x * (a * x + 1) -
      M * (x * (a - b) * (1 + a * x + b * x - x) + x ^ 2 * (a ^ 2 + a * b + b ^ 2 - a - b) +
        (1 - a * x) * (1 + a * x + b * x - x))) * hx

/-- **注记 3.3**：`1 − θ_m ~ 1/(3m)`（`m → ∞`），即 `m(1 − θ_m) → 1/3`。 -/
theorem tendsto_one_sub_theta : Tendsto (fun m : ℕ => (m : ℝ) * (1 - thetaRatio m)) atTop (𝓝 (1 / 3)) := by
  have hu : Tendsto (fun m : ℕ => (rho m)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_rho
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hv : Tendsto (fun m : ℕ => rho (m - 1) * (rho m)⁻¹) atTop (𝓝 1) := by
    have hlow : Tendsto (fun m : ℕ => 1 - (rho m)⁻¹) atTop (𝓝 1) := by
      simpa using h1.sub hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow h1 ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with m hm
      show 1 - (rho m)⁻¹ ≤ rho (m - 1) * (rho m)⁻¹
      have hx : 0 < (rho m)⁻¹ := inv_pos.mpr (rho_pos m)
      have e1 : rho m * (rho m)⁻¹ = 1 := mul_inv_cancel₀ (rho_pos m).ne'
      have key : rho (m - 1) * (rho m)⁻¹ - (1 - (rho m)⁻¹) = (rho m)⁻¹ * (rho (m - 1) - (rho m - 1)) := by
        linear_combination e1
      have : 0 ≤ (rho m)⁻¹ * (rho (m - 1) - (rho m - 1)) :=
        mul_nonneg hx.le (by linarith [rho_sub_one_le hm])
      linarith
    · refine Eventually.of_forall fun m => ?_
      show rho (m - 1) * (rho m)⁻¹ ≤ 1
      rw [← div_eq_mul_inv]
      exact (div_le_one (rho_pos m)).mpr (rho_strictMono.monotone (Nat.sub_le m 1))
  have hden := ((((h1.add hv).add (hv.pow 2)).sub hu).sub (hv.mul hu)).inv₀ (by norm_num)
  have hlim := (h1.sub hu).mul hden
  have h13 : ((1 : ℝ) - 0) * (1 + 1 + 1 ^ 2 - 0 - 1 * 0)⁻¹ = 1 / 3 := by norm_num
  rw [h13] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  show (1 - (rho m)⁻¹) * (1 + rho (m - 1) * (rho m)⁻¹ + (rho (m - 1) * (rho m)⁻¹) ^ 2 - (rho m)⁻¹ -
      rho (m - 1) * (rho m)⁻¹ * (rho m)⁻¹)⁻¹ = (m : ℝ) * (1 - thetaRatio m)
  have hx1 : rho m * (rho m)⁻¹ = 1 := mul_inv_cancel₀ (rho_pos m).ne'
  have hD := one_le_D (one_le_rho m) (one_le_rho (m - 1))
  have hD' : 1 + rho (m - 1) * (rho m)⁻¹ + (rho (m - 1) * (rho m)⁻¹) ^ 2 - (rho m)⁻¹ -
      rho (m - 1) * (rho m)⁻¹ * (rho m)⁻¹ ≠ 0 := by
    rw [D'_eq hx1]
    have hx : 0 < (rho m)⁻¹ := inv_pos.mpr (rho_pos m)
    have hDpos : 0 < rho m ^ 2 + rho m * rho (m - 1) + rho (m - 1) ^ 2 - rho m - rho (m - 1) := by linarith
    exact mul_ne_zero hDpos.ne' (pow_ne_zero 2 hx.ne')
  rw [thetaRatio, div_eq_mul_inv, mul_inv_eq_iff_eq_mul₀ hD']
  exact theta_identity (rho_diff_mul hm) (rho_spec m) hx1

end A207123
