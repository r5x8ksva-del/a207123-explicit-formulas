import A207123.Coeffs

/-!
# 每个 `i` 三个相邻原子的单和：存在且唯一（猜想总表 A25 (b)；notes/12 定理 2(b)）

原子 `c_i(n) = [xⁿ] 1/b_i`（`b_i = 1 − x − i x³`，`n < 0` 时取 0：`ciZ`）。notes/12 定理 2(b)：对每个 `m ≥ 0`
与每个整数 `σ`，存在唯一的一组数 `γ₀` 与 `γ_r(m,i)`（`1 ≤ i ≤ m`，`r = 0, 1, 2`），使
`U_k(m) = γ₀ + Σ_{i=1}^{m} Σ_{r=0}^{2} γ_r(m,i)·c_i(k+3m+σ−r)` 对充分大的 `k` 成立；而且
`a_r^{(σ)}(i) := (−1)^{m−i}·i!(m−i)!·γ_r(m,i)` 与 `m` 无关，是 `x^σ·W̃_i` 在 `K_i = ℚ[x]/(b_i)` 中约化代表的系数
（`σ = 0` 时就是引理 2.1 的 `A_i^{(r)}`）。

* 存在（`three_atoms_exists`）：由 T2.5(3) 的部分分式式（`U_F4`，`m!·U_k(m) = Σ_i (−1)^{m−i} C(m,i)·Φ_{W̃_i}(k+3m)`，
  `Φ_θ(n) := [xⁿ] θ/b_i`）出发；`Φ_θ` 只依赖 `θ mod b_i`（差一个多项式，`phi_eq_of_dvd`），乘 `x^s` 是平移
  （`phi_X_pow_mul`），`x⁻¹ ≡ 1 + i x²`（`bpoly_dvd_inv_shift`），次数 ≤ 2 的代表给出三个相邻原子
  （`phi_of_natDegree_le_two`）。
* 唯一（`three_atoms_unique`）：把数列看成 `ℚ` 上的向量，`E` 为平移算子（`shiftE`）。`n ↦ c_i(n + b)` 最终被
  `q_i(E) = E³ − E² − i` 零化（`evZero_qpoly`）；`q_i` 两两互素，也与 `E − 1` 互素，用 Bezout 把各个 `i` 的分量分开
  （`evZero_of_coprime`），再由 `c_i` 的递推往回推出三个系数都是零（`atomComb_evZero_imp`）。
-/

namespace A207123

open Polynomial Finset Filter

noncomputable section

/-! ## `c_i` 的递推与前几项 -/

/-- `c_i(n+3) = c_i(n+2) + i·c_i(n)`（`b_i·(1/b_i) = 1` 的 `x^{n+3}` 系数）。 -/
theorem ci_add_three (i n : ℕ) : ci i (n + 3) = ci i (n + 2) + (i : ℚ) * ci i n := by
  have h : PowerSeries.coeff (n + 3)
      ((1 - PowerSeries.X - (i : PowerSeries ℚ) * PowerSeries.X ^ 3) * (bser i)⁻¹) = 0 := by
    rw [← bser_eq, bser_mul_inv, PowerSeries.coeff_one, ite_eq_right (by omega)]
  have e1 : PowerSeries.coeff (n + 3) (PowerSeries.X * (bser i)⁻¹) = ci i (n + 2) :=
    PowerSeries.coeff_succ_X_mul (n + 2) _
  have e2 : PowerSeries.coeff (n + 3) ((i : PowerSeries ℚ) * PowerSeries.X ^ 3 * (bser i)⁻¹) =
      (i : ℚ) * ci i n := by
    rw [mul_assoc, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X_pow_mul]
    rfl
  rw [sub_mul, sub_mul, one_mul, map_sub, map_sub, e1, e2] at h
  have h' : ci i (n + 3) - ci i (n + 2) - (i : ℚ) * ci i n = 0 := h
  linarith

theorem ci_small (i : ℕ) : ci i 0 = 1 ∧ ci i 1 = 1 ∧ ci i 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ci_formula]

theorem ci_three (i : ℕ) : ci i 3 = 1 + i := by
  have h : ci i 3 = ci i 2 + (i : ℚ) * ci i 0 := ci_add_three i 0
  rw [h, (ci_small i).2.2, (ci_small i).1]
  ring

theorem ci_four (i : ℕ) : ci i 4 = 1 + 2 * i := by
  have h : ci i 4 = ci i 3 + (i : ℚ) * ci i 1 := ci_add_three i 1
  rw [h, ci_three, (ci_small i).2.1]
  ring

theorem ciZ_natCast (i n : ℕ) : ciZ i (n : ℤ) = ci i n := by
  simp [ciZ]

/-! ## `Φ_θ(n) = [xⁿ] θ/b_i` -/

/-- `Φ_θ(n) := [xⁿ] θ/b_i`（notes/12 引理 2.0 的 `Φ_θ`，这里只用自然数下标）。 -/
def phi (i : ℕ) (θ : ℚ[X]) (n : ℕ) : ℚ := PowerSeries.coeff n ((↑θ : PowerSeries ℚ) * (bser i)⁻¹)

/-- `Φ_θ` 只依赖 `θ mod b_i`：`b_i ∣ θ − θ'` 时两者只差一个多项式，`n` 充分大时相等。 -/
theorem phi_eq_of_dvd (i : ℕ) {θ θ' : ℚ[X]} (h : bpoly ℚ i ∣ θ - θ') :
    ∃ N, ∀ n ≥ N, phi i θ n = phi i θ' n := by
  obtain ⟨Z, hZ⟩ := h
  refine ⟨Z.natDegree + 1, fun n hn => ?_⟩
  have key : (↑θ : PowerSeries ℚ) * (bser i)⁻¹ - (↑θ' : PowerSeries ℚ) * (bser i)⁻¹ = ↑Z := by
    rw [← sub_mul, ← Polynomial.coe_sub, hZ, Polynomial.coe_mul,
      mul_comm (↑(bpoly ℚ i) : PowerSeries ℚ), mul_assoc,
      show (↑(bpoly ℚ i) : PowerSeries ℚ) * (bser i)⁻¹ = 1 from bser_mul_inv i, mul_one]
  have hc := congrArg (PowerSeries.coeff n) key
  rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hc
  unfold phi
  linarith

/-- 乘 `x^s` 是平移：`Φ_{x^s θ}(n + s) = Φ_θ(n)`。 -/
theorem phi_X_pow_mul (i s : ℕ) (θ : ℚ[X]) (n : ℕ) : phi i (X ^ s * θ) (n + s) = phi i θ n := by
  unfold phi
  rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
    PowerSeries.coeff_X_pow_mul]

/-- 次数 ≤ 2 的 `ρ`：`Φ_ρ(n + 2) = Σ_{r<3} ρ_r·c_i(n + 2 − r)`。 -/
theorem phi_of_natDegree_le_two (i : ℕ) {ρ : ℚ[X]} (hρ : ρ.natDegree ≤ 2) (n : ℕ) :
    phi i ρ (n + 2) = ∑ r ∈ range 3, ρ.coeff r * ci i (n + 2 - r) := by
  unfold phi
  conv_lhs => rw [ρ.as_sum_range' 3 (by omega)]
  rw [psCoe_sum, sum_mul, map_sum]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  rw [← C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_X, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    ite_eq_left (by omega)]
  rfl

theorem phi_zero_Wtil (n : ℕ) : phi 0 (Wtil 0) n = 1 := by
  rw [phi, Wtil_zero, Polynomial.coe_one, one_mul]
  exact ci_zero n

/-- T2.5(3)（`U_F4`）写成 `Φ` 的形式：`m!·U_k(m) = Σ_{i=0}^{m} (−1)^{m−i}·C(m,i)·Φ_{W̃_i}(k+3m)`。 -/
theorem U_F4_phi (k m : ℕ) : (m.factorial : ℚ) * (U k m : ℚ) =
    ∑ i ∈ range (m + 1), (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * phi i (Wtil i) (k + 3 * m) := by
  rw [U_F4]
  refine sum_congr rfl fun i _ => ?_
  rw [phi, coeff_Wtil_mul_inv_bser]
  simp only [ite_ci_eq_ciZ]

/-! ## `K_i` 中的约化代表 -/

/-- `K_i` 中 `x^σ` 的多项式代表：`σ ≥ 0` 时 `x^σ`，`σ < 0` 时 `(1 + i x²)^{−σ}`（`x·(1 + i x²) = 1 − b_i`）。 -/
def xpowRep (i : ℕ) (σ : ℤ) : ℚ[X] :=
  if 0 ≤ σ then X ^ σ.toNat else (1 + C (i : ℚ) * X ^ 2) ^ (-σ).toNat

/-- `x^σ·W̃_i` 在 `K_i = ℚ[x]/(b_i)` 中的约化代表（次数 ≤ 2）；其系数就是 `a_r^{(σ)}(i)`。 -/
def atomRep (i : ℕ) (σ : ℤ) : ℚ[X] := (xpowRep i σ * Wtil i) % bpoly ℚ i

/-- 定理 2(b) 的系数 `γ_r(m,i) = (−1)^{m−i}/(i!(m−i)!)·a_r^{(σ)}(i)`。 -/
def atomCoeff (m i : ℕ) (σ : ℤ) (r : ℕ) : ℚ :=
  (-1 : ℚ) ^ (m - i) / ((i.factorial : ℚ) * ((m - i).factorial : ℚ)) * (atomRep i σ).coeff r

theorem bpoly_dvd_sub_mod (i : ℕ) (θ : ℚ[X]) : bpoly ℚ i ∣ θ - θ % bpoly ℚ i :=
  ⟨θ / bpoly ℚ i, sub_eq_iff_eq_add.2 (EuclideanDomain.div_add_mod θ (bpoly ℚ i)).symm⟩

/-- `x^s·(1 + i x²)^s ≡ 1 (mod b_i)`。 -/
theorem bpoly_dvd_inv_shift (i s : ℕ) (θ : ℚ[X]) :
    bpoly ℚ i ∣ X ^ s * ((1 + C (i : ℚ) * X ^ 2) ^ s * θ) - θ := by
  have hb : (1 : ℚ[X]) - bpoly ℚ i = X * (1 + C (i : ℚ) * X ^ 2) := by
    rw [bpoly]
    ring
  have h1 : X ^ s * ((1 + C (i : ℚ) * X ^ 2) ^ s * θ) - θ = ((1 - bpoly ℚ i) ^ s - 1 ^ s) * θ := by
    rw [hb, mul_pow, one_pow]
    ring
  rw [h1]
  apply Dvd.dvd.mul_right
  have h2 := sub_dvd_pow_sub_pow (1 - bpoly ℚ i) 1 s
  rwa [show (1 : ℚ[X]) - bpoly ℚ i - 1 = -bpoly ℚ i by ring, neg_dvd] at h2

theorem atomRep_natDegree_le {i : ℕ} (hi : 1 ≤ i) (σ : ℤ) : (atomRep i σ).natDegree ≤ 2 := by
  unfold atomRep
  by_cases h0 : (xpowRep i σ * Wtil i) % bpoly ℚ i = 0
  · rw [h0, natDegree_zero]
    omega
  · have h := natDegree_lt_natDegree h0 (degree_mod_lt (xpowRep i σ * Wtil i) (bpoly_ne_zero i))
    rw [natDegree_bpoly hi] at h
    omega

/-- `a_r^{(σ)}(i) = (−1)^{m−i}·i!(m−i)!·γ_r(m,i)` 与 `m` 无关（就是约化代表的系数）。 -/
theorem atomCoeff_normalized (m i : ℕ) (σ : ℤ) (r : ℕ) :
    (-1 : ℚ) ^ (m - i) * (i.factorial : ℚ) * ((m - i).factorial : ℚ) * atomCoeff m i σ r =
      (atomRep i σ).coeff r := by
  have h1 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((m - i).factorial : ℚ) ≠ 0 := by exact_mod_cast (m - i).factorial_ne_zero
  have h3 : (i.factorial : ℚ) * ((m - i).factorial : ℚ) ≠ 0 := mul_ne_zero h1 h2
  have hsq : (-1 : ℚ) ^ (m - i) * (-1) ^ (m - i) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [atomCoeff, div_eq_mul_inv]
  calc _ = ((-1 : ℚ) ^ (m - i) * (-1) ^ (m - i)) * (atomRep i σ).coeff r *
        (((i.factorial : ℚ) * ((m - i).factorial : ℚ)) *
          ((i.factorial : ℚ) * ((m - i).factorial : ℚ))⁻¹) := by ring
    _ = _ := by rw [hsq, mul_inv_cancel₀ h3, one_mul, mul_one]

theorem atomCoeff_mul_factorial {m i : ℕ} (hi : i ≤ m) (σ : ℤ) (r : ℕ) :
    (m.factorial : ℚ) * atomCoeff m i σ r =
      (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * (atomRep i σ).coeff r := by
  have h1 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((m - i).factorial : ℚ) ≠ 0 := by exact_mod_cast (m - i).factorial_ne_zero
  have h3 : (i.factorial : ℚ) * ((m - i).factorial : ℚ) ≠ 0 := mul_ne_zero h1 h2
  have hc : (m.factorial : ℚ) = (m.choose i : ℚ) * (i.factorial : ℚ) * ((m - i).factorial : ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi).symm
  rw [atomCoeff, hc, div_eq_mul_inv]
  calc _ = (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * (atomRep i σ).coeff r *
        (((i.factorial : ℚ) * ((m - i).factorial : ℚ)) *
          ((i.factorial : ℚ) * ((m - i).factorial : ℚ))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ h3, mul_one]

/-- 对 `1 ≤ i`：`k` 充分大时 `Φ_{W̃_i}(k+3m) = Σ_{r<3} a_r^{(σ)}(i)·c_i(k+3m+σ−r)`。 -/
theorem phi_Wtil_atoms {i : ℕ} (hi : 1 ≤ i) (σ : ℤ) (m : ℕ) :
    ∃ K, ∀ k ≥ K, phi i (Wtil i) (k + 3 * m) =
      ∑ r ∈ range 3, (atomRep i σ).coeff r * ciZ i ((k : ℤ) + 3 * m + σ - r) := by
  have hdeg := atomRep_natDegree_le hi σ
  rcases le_or_gt 0 σ with hσ | hσ
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, σ = s := ⟨σ.toNat, (Int.toNat_of_nonneg hσ).symm⟩
    have hrep : atomRep i s = (X ^ s * Wtil i) % bpoly ℚ i := by
      rw [atomRep, xpowRep, ite_eq_left (by omega), Int.toNat_natCast]
    obtain ⟨N, hN⟩ := phi_eq_of_dvd i (bpoly_dvd_sub_mod i (X ^ s * Wtil i))
    refine ⟨N + 2, fun k hk => ?_⟩
    rw [← phi_X_pow_mul i s (Wtil i) (k + 3 * m), hN (k + 3 * m + s) (by omega), ← hrep,
      show k + 3 * m + s = (k + 3 * m + s - 2) + 2 by omega, phi_of_natDegree_le_two i hdeg]
    refine sum_congr rfl fun r hr => ?_
    rw [mem_range] at hr
    rw [← ciZ_natCast]
    congr 2
    omega
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, σ = -(s : ℤ) := ⟨(-σ).toNat, by omega⟩
    subst hs
    have hrep : atomRep i (-(s : ℤ)) = ((1 + C (i : ℚ) * X ^ 2) ^ s * Wtil i) % bpoly ℚ i := by
      rw [atomRep, xpowRep, ite_eq_right (by omega), neg_neg, Int.toNat_natCast]
    obtain ⟨N1, hN1⟩ := phi_eq_of_dvd i (bpoly_dvd_inv_shift i s (Wtil i))
    obtain ⟨N2, hN2⟩ := phi_eq_of_dvd i (bpoly_dvd_sub_mod i ((1 + C (i : ℚ) * X ^ 2) ^ s * Wtil i))
    refine ⟨N1 + N2 + s + 2, fun k hk => ?_⟩
    rw [← hN1 (k + 3 * m) (by omega), show k + 3 * m = (k + 3 * m - s) + s by omega, phi_X_pow_mul,
      hN2 (k + 3 * m - s) (by omega), ← hrep, show k + 3 * m - s = (k + 3 * m - s - 2) + 2 by omega,
      phi_of_natDegree_le_two i hdeg]
    refine sum_congr rfl fun r hr => ?_
    rw [mem_range] at hr
    rw [← ciZ_natCast]
    congr 2
    omega

theorem sum_range_succ_eq_add_Icc (f : ℕ → ℚ) : ∀ m : ℕ,
    ∑ i ∈ range (m + 1), f i = f 0 + ∑ i ∈ Icc 1 m, f i
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, sum_range_succ_eq_add_Icc f m, Finset.sum_Icc_succ_top (by omega)]
    ring

/-- **定理 2(b)，存在**：`k` 充分大时
`U_k(m) = (−1)^m/m! + Σ_{i=1}^{m} Σ_{r=0}^{2} γ_r(m,i)·c_i(k+3m+σ−r)`。 -/
theorem three_atoms_exists (m : ℕ) (σ : ℤ) : ∀ᶠ k in atTop,
    (U k m : ℚ) = (-1) ^ m / (m.factorial : ℚ) +
      ∑ i ∈ Icc 1 m, ∑ r ∈ range 3, atomCoeff m i σ r * ciZ i ((k : ℤ) + 3 * m + σ - r) := by
  have hall : ∀ᶠ k in atTop, ∀ i ∈ Icc 1 m, phi i (Wtil i) (k + 3 * m) =
      ∑ r ∈ range 3, (atomRep i σ).coeff r * ciZ i ((k : ℤ) + 3 * m + σ - r) := by
    rw [eventually_all_finset]
    intro i hi
    obtain ⟨K, hK⟩ := phi_Wtil_atoms (mem_Icc.1 hi).1 σ m
    exact eventually_atTop.2 ⟨K, hK⟩
  filter_upwards [hall] with k hk
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hS : (m.factorial : ℚ) * (∑ i ∈ Icc 1 m, ∑ r ∈ range 3,
        atomCoeff m i σ r * ciZ i ((k : ℤ) + 3 * m + σ - r)) =
      ∑ i ∈ Icc 1 m, (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * phi i (Wtil i) (k + 3 * m) := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [hk i hi, mul_sum, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_assoc, atomCoeff_mul_factorial (mem_Icc.1 hi).2]
    ring
  have hF : (m.factorial : ℚ) * (U k m : ℚ) = (-1) ^ m + (m.factorial : ℚ) * (∑ i ∈ Icc 1 m,
      ∑ r ∈ range 3, atomCoeff m i σ r * ciZ i ((k : ℤ) + 3 * m + σ - r)) := by
    rw [hS, U_F4_phi, sum_range_succ_eq_add_Icc, phi_zero_Wtil, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one, mul_one]
  rw [div_add' _ _ _ hm, eq_div_iff hm]
  linear_combination hF

/-! ## 唯一性：平移算子 -/

/-- 数列的平移算子 `(E f)(k) = f(k + 1)`。 -/
def shiftE : Module.End ℚ (ℕ → ℚ) := LinearMap.funLeft ℚ ℚ (fun k : ℕ => k + 1)

theorem shiftE_pow_apply (n : ℕ) (f : ℕ → ℚ) (k : ℕ) : (shiftE ^ n) f k = f (k + n) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rfl

theorem aeval_shiftE_apply (p : ℚ[X]) (f : ℕ → ℚ) (k : ℕ) :
    aeval shiftE p f k = ∑ j ∈ range (p.natDegree + 1), p.coeff j * f (k + j) := by
  rw [aeval_eq_sum_range]
  simp [shiftE_pow_apply]

/-- 数列「最终为零」。 -/
abbrev EvZero (f : ℕ → ℚ) : Prop := ∀ᶠ k in atTop, f k = 0

theorem evZero_zero : EvZero (0 : ℕ → ℚ) := eventually_atTop.2 ⟨0, fun _ _ => rfl⟩

theorem evZero_add {f g : ℕ → ℚ} (hf : EvZero f) (hg : EvZero g) : EvZero (f + g) :=
  (hf.and hg).mono fun k hk => by rw [Pi.add_apply, hk.1, hk.2, add_zero]

theorem evZero_sub {f g : ℕ → ℚ} (hf : EvZero f) (hg : EvZero g) : EvZero (f - g) :=
  (hf.and hg).mono fun k hk => by rw [Pi.sub_apply, hk.1, hk.2, sub_zero]

theorem evZero_smul {f : ℕ → ℚ} (hf : EvZero f) (c : ℚ) : EvZero (c • f) :=
  hf.mono fun k hk => by rw [Pi.smul_apply, hk, smul_zero]

theorem evZero_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℚ) (hf : ∀ i ∈ s, EvZero (f i)) :
    EvZero (∑ i ∈ s, f i) :=
  ((eventually_all_finset s).2 hf).mono fun k hk => by
    rw [Finset.sum_apply]
    exact sum_eq_zero hk

theorem evZero_aeval {f : ℕ → ℚ} (hf : EvZero f) (p : ℚ[X]) : EvZero (aeval shiftE p f) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hf
  refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
  rw [aeval_shiftE_apply]
  exact sum_eq_zero fun j _ => by rw [hK (k + j) (by omega), mul_zero]

theorem evZero_aeval_of_dvd {p Q : ℚ[X]} (hpQ : p ∣ Q) {g : ℕ → ℚ}
    (hg : EvZero (aeval shiftE p g)) : EvZero (aeval shiftE Q g) := by
  obtain ⟨R, rfl⟩ := hpQ
  rw [mul_comm, map_mul, Module.End.mul_apply]
  exact evZero_aeval hg R

/-- 互素：`p(E) g`、`q(E) g` 都最终为零，则 `g` 最终为零。 -/
theorem evZero_of_coprime {p q : ℚ[X]} (hpq : IsCoprime p q) {g : ℕ → ℚ}
    (hp : EvZero (aeval shiftE p g)) (hq : EvZero (aeval shiftE q g)) : EvZero g := by
  obtain ⟨u, v, huv⟩ := hpq
  have h1 : aeval shiftE (u * p + v * q) g = g := by
    rw [huv, map_one]
    rfl
  have h2 : aeval shiftE (u * p + v * q) g =
      aeval shiftE u (aeval shiftE p g) + aeval shiftE v (aeval shiftE q g) := by
    rw [map_add, map_mul, map_mul]
    rfl
  rw [← h1, h2]
  exact evZero_add (evZero_aeval hp u) (evZero_aeval hq v)

theorem aeval_X_sub_one_const (c : ℚ) : aeval shiftE (X - 1 : ℚ[X]) (fun _ : ℕ => c) = 0 := by
  rw [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply]
  funext k
  show c - c = 0
  ring

/-- `q_i(y) = y³ − y² − i`：`c_i` 的递推的特征多项式。 -/
def qpoly (i : ℕ) : ℚ[X] := X ^ 3 - X ^ 2 - C (i : ℚ)

theorem qpoly_sub (i j : ℕ) : qpoly i - qpoly j = C ((j : ℚ) - i) := by
  unfold qpoly
  rw [C_sub]
  ring

theorem isCoprime_qpoly {i j : ℕ} (h : i ≠ j) : IsCoprime (qpoly i) (qpoly j) := by
  have hne : ((j : ℚ) - i) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.symm)
  refine ⟨C ((j : ℚ) - i)⁻¹, -C ((j : ℚ) - i)⁻¹, ?_⟩
  rw [neg_mul, ← sub_eq_add_neg, ← mul_sub, qpoly_sub, ← C_mul, inv_mul_cancel₀ hne, C_1]

theorem isCoprime_qpoly_X_sub_one {i : ℕ} (hi : 1 ≤ i) : IsCoprime (qpoly i) (X - 1) := by
  have hne : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  refine ⟨-C (i : ℚ)⁻¹, C (i : ℚ)⁻¹ * X ^ 2, ?_⟩
  calc -C (i : ℚ)⁻¹ * qpoly i + C (i : ℚ)⁻¹ * X ^ 2 * (X - 1) = C (i : ℚ)⁻¹ * C (i : ℚ) := by
        unfold qpoly
        ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hne, C_1]

/-- `n ↦ c_i(n + b)` 最终被 `q_i(E)` 零化。 -/
theorem evZero_qpoly (i : ℕ) (b : ℤ) :
    EvZero (aeval shiftE (qpoly i) (fun k : ℕ => ciZ i ((k : ℤ) + b))) := by
  refine eventually_atTop.2 ⟨b.natAbs, fun k hk => ?_⟩
  have hb : -b ≤ (b.natAbs : ℤ) := by
    have := @Int.le_natAbs (-b)
    rwa [Int.natAbs_neg] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℤ) + b = n := ⟨((k : ℤ) + b).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  simp only [qpoly, map_sub, map_pow, aeval_X, aeval_C, LinearMap.sub_apply, Pi.sub_apply,
    shiftE_pow_apply, Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul]
  rw [show ((k + 3 : ℕ) : ℤ) + b = ((n + 3 : ℕ) : ℤ) by push_cast; omega,
    show ((k + 2 : ℕ) : ℤ) + b = ((n + 2 : ℕ) : ℤ) by push_cast; omega, hn,
    ciZ_natCast, ciZ_natCast, ciZ_natCast, ci_add_three]
  ring

/-- 第 `i` 个分量 `g_i(k) = Σ_{r<3} δ_r·c_i(k + a − r)`。 -/
def atomComb (i : ℕ) (a : ℤ) (δ : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ r ∈ range 3, δ r * ciZ i ((k : ℤ) + a - r)

theorem atomComb_eq (i : ℕ) (a : ℤ) (δ : ℕ → ℚ) :
    atomComb i a δ = ∑ r ∈ range 3, δ r • (fun k : ℕ => ciZ i ((k : ℤ) + (a - r))) := by
  funext k
  rw [atomComb, Finset.sum_apply]
  refine sum_congr rfl fun r _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, add_sub_assoc]

theorem evZero_qpoly_atomComb (i : ℕ) (a : ℤ) (δ : ℕ → ℚ) :
    EvZero (aeval shiftE (qpoly i) (atomComb i a δ)) := by
  rw [atomComb_eq, map_sum]
  exact evZero_sum _ _ fun r _ => by
    rw [map_smul]
    exact evZero_smul (evZero_qpoly i _) _

/-- `T(n) = δ₀·c_i(n+2) + δ₁·c_i(n+1) + δ₂·c_i(n)`。 -/
def atomSeq (i : ℕ) (δ : ℕ → ℚ) (n : ℕ) : ℚ := δ 0 * ci i (n + 2) + δ 1 * ci i (n + 1) + δ 2 * ci i n

theorem atomSeq_rec (i : ℕ) (δ : ℕ → ℚ) (n : ℕ) :
    atomSeq i δ (n + 3) = atomSeq i δ (n + 2) + (i : ℚ) * atomSeq i δ n := by
  have e0 : ci i (n + 3 + 2) = ci i (n + 2 + 2) + (i : ℚ) * ci i (n + 2) := ci_add_three i (n + 2)
  have e1 : ci i (n + 3 + 1) = ci i (n + 2 + 1) + (i : ℚ) * ci i (n + 1) := ci_add_three i (n + 1)
  have e2 : ci i (n + 3) = ci i (n + 2) + (i : ℚ) * ci i n := ci_add_three i n
  simp only [atomSeq]
  rw [e0, e1, e2]
  ring

/-- 对 `1 ≤ i`：`Σ_{r<3} δ_r·c_i(k + a − r)` 最终为零，则三个系数都是零。 -/
theorem atomComb_evZero_imp {i : ℕ} (hi : 1 ≤ i) (a : ℤ) (δ : ℕ → ℚ)
    (h : EvZero (atomComb i a δ)) : ∀ r < 3, δ r = 0 := by
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.1 h
  have ha1 : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
  have ha2 : -a ≤ (a.natAbs : ℤ) := by
    have := @Int.le_natAbs (-a)
    rwa [Int.natAbs_neg] at this
  have hT : ∀ n ≥ K + a.natAbs, atomSeq i δ n = 0 := by
    intro n hn
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = n + 2 - a :=
      ⟨((n : ℤ) + 2 - a).toNat, Int.toNat_of_nonneg (by omega)⟩
    have h0 := hK k (by omega)
    rw [atomComb, sum_range_succ, sum_range_succ, sum_range_one] at h0
    rw [show (k : ℤ) + a - ((0 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by push_cast; omega,
      show (k : ℤ) + a - ((1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by push_cast; omega,
      show (k : ℤ) + a - ((2 : ℕ) : ℤ) = ((n : ℕ) : ℤ) by push_cast; omega,
      ciZ_natCast, ciZ_natCast, ciZ_natCast] at h0
    rw [atomSeq]
    linarith
  have hall : ∀ j n, K + a.natAbs ≤ n + j → atomSeq i δ n = 0 := by
    intro j
    induction j with
    | zero => exact fun n hn => hT n (by omega)
    | succ j ih =>
      intro n hn
      have hrec := atomSeq_rec i δ n
      rw [ih (n + 3) (by omega), ih (n + 2) (by omega), zero_add] at hrec
      exact (mul_eq_zero.1 hrec.symm).resolve_left hi0
  have h0 := hall (K + a.natAbs) 0 (by omega)
  have h1 := hall (K + a.natAbs) 1 (by omega)
  have h2 := hall (K + a.natAbs) 2 (by omega)
  simp only [atomSeq, zero_add, Nat.reduceAdd, (ci_small i).1, (ci_small i).2.1, (ci_small i).2.2,
    ci_three, ci_four] at h0 h1 h2
  have hd0 : δ 0 = 0 := by
    have : δ 0 * (i : ℚ) = 0 := by linear_combination h1 - h0
    exact (mul_eq_zero.1 this).resolve_right hi0
  have hd1 : δ 1 = 0 := by
    have : δ 1 * (i : ℚ) = 0 := by linear_combination h2 - h1 - (i : ℚ) * hd0
    exact (mul_eq_zero.1 this).resolve_right hi0
  have hd2 : δ 2 = 0 := by linear_combination h0 - hd0 - hd1
  intro r hr
  interval_cases r
  · exact hd0
  · exact hd1
  · exact hd2

/-- **定理 2(b) 的唯一性**：`δ₀ + Σ_{i=1}^{m} Σ_{r<3} δ_{i,r}·c_i(k + a − r)` 最终为零，则全部系数为零。 -/
theorem atoms_lin_indep (m : ℕ) (a : ℤ) (δ0 : ℚ) (δ : ℕ → ℕ → ℚ)
    (h : ∀ᶠ k in atTop, δ0 + ∑ i ∈ Icc 1 m, atomComb i a (δ i) k = 0) :
    δ0 = 0 ∧ ∀ i ∈ Icc 1 m, ∀ r < 3, δ i r = 0 := by
  have hf : EvZero ((fun _ : ℕ => δ0) + ∑ i ∈ Icc 1 m, atomComb i a (δ i)) :=
    h.mono fun k hk => by
      rw [Pi.add_apply, Finset.sum_apply]
      exact hk
  have hcomp : ∀ i ∈ Icc 1 m, EvZero (atomComb i a (δ i)) := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
    obtain ⟨Q, hQ⟩ : ∃ Q : ℚ[X], Q = (X - 1) * ∏ l ∈ (Icc 1 m).erase i, qpoly l := ⟨_, rfl⟩
    have hcop : IsCoprime (qpoly i) Q := by
      rw [hQ]
      exact (isCoprime_qpoly_X_sub_one hi1).mul_right
        (IsCoprime.prod_right fun j hj => isCoprime_qpoly (ne_of_mem_erase hj).symm)
    have hdvd1 : (X - 1 : ℚ[X]) ∣ Q := ⟨_, hQ⟩
    have hdvd : ∀ j ∈ (Icc 1 m).erase i, qpoly j ∣ Q := fun j hj => by
      rw [hQ]
      exact Dvd.dvd.mul_left (dvd_prod_of_mem _ hj) _
    refine evZero_of_coprime hcop (evZero_qpoly_atomComb i a (δ i)) ?_
    have hT : aeval shiftE Q ((fun _ : ℕ => δ0) + ∑ j ∈ Icc 1 m, atomComb j a (δ j)) =
        aeval shiftE Q (fun _ : ℕ => δ0) + (aeval shiftE Q (atomComb i a (δ i)) +
          ∑ j ∈ (Icc 1 m).erase i, aeval shiftE Q (atomComb j a (δ j))) := by
      rw [map_add, map_sum, ← add_sum_erase _ _ hi]
    have hconst : EvZero (aeval shiftE Q (fun _ : ℕ => δ0)) :=
      evZero_aeval_of_dvd hdvd1 (by rw [aeval_X_sub_one_const]; exact evZero_zero)
    have hothers : EvZero (∑ j ∈ (Icc 1 m).erase i, aeval shiftE Q (atomComb j a (δ j))) :=
      evZero_sum _ _ fun j hj => evZero_aeval_of_dvd (hdvd j hj) (evZero_qpoly_atomComb j a (δ j))
    have e : aeval shiftE Q (atomComb i a (δ i)) =
        aeval shiftE Q ((fun _ : ℕ => δ0) + ∑ j ∈ Icc 1 m, atomComb j a (δ j)) -
          aeval shiftE Q (fun _ : ℕ => δ0) -
            ∑ j ∈ (Icc 1 m).erase i, aeval shiftE Q (atomComb j a (δ j)) := by
      rw [hT]
      abel
    rw [e]
    exact evZero_sub (evZero_sub (evZero_aeval hf Q) hconst) hothers
  have hconst : EvZero (fun _ : ℕ => δ0) := by
    have e : (fun _ : ℕ => δ0) =
        ((fun _ : ℕ => δ0) + ∑ i ∈ Icc 1 m, atomComb i a (δ i)) - ∑ i ∈ Icc 1 m, atomComb i a (δ i) := by
      abel
    rw [e]
    exact evZero_sub hf (evZero_sum _ _ hcomp)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hconst
  exact ⟨hK K le_rfl, fun i hi r hr => atomComb_evZero_imp (mem_Icc.1 hi).1 a (δ i) (hcomp i hi) r hr⟩

/-- **定理 2(b)，唯一**：任何一组 `γ₀`、`γ_r(m,i)` 使 `U_k(m) = γ₀ + Σ_i Σ_r γ_r(m,i)·c_i(k+3m+σ−r)` 对充分大的
`k` 成立，就是 `three_atoms_exists` 中的那一组。 -/
theorem three_atoms_unique (m : ℕ) (σ : ℤ) (γ0 : ℚ) (γ : ℕ → ℕ → ℚ)
    (h : ∀ᶠ k in atTop, (U k m : ℚ) =
      γ0 + ∑ i ∈ Icc 1 m, ∑ r ∈ range 3, γ i r * ciZ i ((k : ℤ) + 3 * m + σ - r)) :
    γ0 = (-1) ^ m / (m.factorial : ℚ) ∧ ∀ i ∈ Icc 1 m, ∀ r < 3, γ i r = atomCoeff m i σ r := by
  have hd := atoms_lin_indep m (3 * m + σ) (γ0 - (-1) ^ m / (m.factorial : ℚ))
    (fun i r => γ i r - atomCoeff m i σ r) (by
      filter_upwards [h, three_atoms_exists m σ] with k hk1 hk2
      have e : ∀ i, atomComb i (3 * m + σ) (fun r => γ i r - atomCoeff m i σ r) k =
          ∑ r ∈ range 3, γ i r * ciZ i ((k : ℤ) + 3 * m + σ - r) -
            ∑ r ∈ range 3, atomCoeff m i σ r * ciZ i ((k : ℤ) + 3 * m + σ - r) := by
        intro i
        rw [atomComb, ← sum_sub_distrib]
        refine sum_congr rfl fun r _ => ?_
        rw [show (k : ℤ) + (3 * m + σ) - r = (k : ℤ) + 3 * m + σ - r by ring]
        ring
      simp only [e, sum_sub_distrib]
      linarith)
  refine ⟨by linarith [hd.1], fun i hi r hr => ?_⟩
  have h3 : γ i r - atomCoeff m i σ r = 0 := hd.2 i hi r hr
  linarith

/-- **猜想总表 A25 (b)（notes/12 定理 2(b)）**：对每个 `m ≥ 0` 与每个整数 `σ`，`k` 充分大时
`U_k(m) = (−1)^m/m! + Σ_{i=1}^{m} Σ_{r=0}^{2} γ_r(m,i)·c_i(k+3m+σ−r)`，其中
`γ_r(m,i) = (−1)^{m−i}/(i!(m−i)!)·a_r^{(σ)}(i)`，`a_r^{(σ)}(i)` 是 `x^σ·W̃_i` 在 `K_i = ℚ[x]/(b_i)` 中约化代表的
系数（与 `m` 无关，`atomCoeff_normalized`）；而且这样的表示唯一。 -/
theorem three_atoms (m : ℕ) (σ : ℤ) :
    (∀ᶠ k in atTop, (U k m : ℚ) = (-1) ^ m / (m.factorial : ℚ) +
      ∑ i ∈ Icc 1 m, ∑ r ∈ range 3, atomCoeff m i σ r * ciZ i ((k : ℤ) + 3 * m + σ - r)) ∧
    ∀ (γ0 : ℚ) (γ : ℕ → ℕ → ℚ), (∀ᶠ k in atTop, (U k m : ℚ) =
      γ0 + ∑ i ∈ Icc 1 m, ∑ r ∈ range 3, γ i r * ciZ i ((k : ℤ) + 3 * m + σ - r)) →
      γ0 = (-1) ^ m / (m.factorial : ℚ) ∧ ∀ i ∈ Icc 1 m, ∀ r < 3, γ i r = atomCoeff m i σ r :=
  ⟨three_atoms_exists m σ, fun γ0 γ h => three_atoms_unique m σ γ0 γ h⟩

end

end A207123
