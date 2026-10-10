import A207123.NumStruct

/-!
# T4.3(6) 的 `j = 2, 3`：`Num_q` 次高两项系数的闭式（猜想总表 A5 (6) 的一部分）

报告 T4.3(6)：`a_{q,j} := [x^{3q−2−j}] Num_q`，例如 `j = 0` 时 `(q−1)!`，`j = 1` 时 `0`，
`j = 2` 时 `(q−1)!·(q−1+H_{q−1})`，`j = 3` 时 `(q−1)·(q−1)!·(H_{q−1}−1)`（`H_n` 为调和数，Mathlib 的 `harmonic`）。
`j = 0, 1` 已形式化（`leadingCoeff_Numq`、`Numq_coeff_gap`）。这里由三项递推 `Numq_three_term` 推出 `a_{q,j}` 的递推
（`Numq_coeff_step`），对 `q` 归纳证明 `j = 2, 3` 的式子（`q ≥ 2`）。一般 `j` 的结构（`a_{q,j}` 是第一类 Stirling 数
`c(q,i)`（`i ≤ ⌊j/2⌋+1`）的 `ℚ[q]` 线性组合）没有形式化。
-/

namespace A207123

open Polynomial

/-- `a_{q,j}` 的递推（由 `Num_q = (x + 2(q−1)x³)·Num_{q−1} + (q−1)x³·b_{q−2}·Num_{q−2}`，`q ≥ 3`，取 `x^{n+6}` 的系数）。 -/
theorem Numq_coeff_step {q : ℕ} (hq : 3 ≤ q) (n : ℕ) :
    (Numq q).coeff (n + 6) = (Numq (q - 1)).coeff (n + 5) +
      2 * ((q : ℚ) - 1) * (Numq (q - 1)).coeff (n + 3) +
      ((q : ℚ) - 1) * ((Numq (q - 2)).coeff (n + 3) - (Numq (q - 2)).coeff (n + 2) -
        ((q - 2 : ℕ) : ℚ) * (Numq (q - 2)).coeff n) := by
  have h := Numq_three_term hq
  have hpoly : Numq q = Numq (q - 1) * X + C (2 * ((q : ℚ) - 1)) * (Numq (q - 1) * X ^ 3)
      + C ((q : ℚ) - 1) * (Numq (q - 2) * X ^ 3) - C ((q : ℚ) - 1) * (Numq (q - 2) * X ^ 4)
      - C ((q : ℚ) - 1) * C ((q - 2 : ℕ) : ℚ) * (Numq (q - 2) * X ^ 6) := by
    rw [h, bpoly]
    ring
  have t1 : (Numq (q - 1) * X).coeff (n + 6) = (Numq (q - 1)).coeff (n + 5) := coeff_mul_X _ _
  have t2 : (Numq (q - 1) * X ^ 3).coeff (n + 6) = (Numq (q - 1)).coeff (n + 3) :=
    coeff_mul_X_pow _ 3 (n + 3)
  have t3 : (Numq (q - 2) * X ^ 3).coeff (n + 6) = (Numq (q - 2)).coeff (n + 3) :=
    coeff_mul_X_pow _ 3 (n + 3)
  have t4 : (Numq (q - 2) * X ^ 4).coeff (n + 6) = (Numq (q - 2)).coeff (n + 2) :=
    coeff_mul_X_pow _ 4 (n + 2)
  have t5 : (Numq (q - 2) * X ^ 6).coeff (n + 6) = (Numq (q - 2)).coeff n := coeff_mul_X_pow _ 6 n
  rw [hpoly]
  simp only [coeff_add, coeff_sub, mul_assoc, coeff_C_mul, t1, t2, t3, t4, t5]
  ring

theorem Numq_three_eq : Numq 3 = 2 * X ^ 3 + 2 * X ^ 4 + 7 * X ^ 5 + 2 * X ^ 7 := by
  have h := Numq_three_term (q := 3) le_rfl
  rw [show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) - 2 = 1 from rfl, Numq_two, Numq_one] at h
  have e1 : C (2 * (((3 : ℕ) : ℚ) - 1)) = (4 : ℚ[X]) := by
    norm_num
    exact map_ofNat C 4
  have e2 : C (((3 : ℕ) : ℚ) - 1) = (2 : ℚ[X]) := by
    norm_num
    exact map_ofNat C 2
  have e3 : C ((1 : ℕ) : ℚ) = (1 : ℚ[X]) := by norm_num
  rw [h, bpoly, e1, e2, e3]
  ring

/-- `a_{q,0} = (q−1)!`（首项系数，`q ≥ 1`）。 -/
theorem Numq_coeff_top {q : ℕ} (hq : 1 ≤ q) : (Numq q).coeff (3 * q - 2) = ((q - 1).factorial : ℚ) := by
  rw [← natDegree_Numq hq]
  exact leadingCoeff_Numq hq

theorem Numq_coeff_above {q n : ℕ} (hq : 1 ≤ q) (hn : 3 * q - 2 < n) : (Numq q).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [natDegree_Numq hq]; exact hn)

theorem harmonic_one_eq : harmonic 1 = 1 := by
  norm_num [harmonic]

theorem harmonic_two_eq : harmonic 2 = 3 / 2 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- **T4.3(6)，`j = 2`**：`[x^{3q−4}] Num_q = (q−1)!·(q − 1 + H_{q−1})`（`q ≥ 2`）。 -/
theorem Numq_top_two : ∀ q : ℕ, 2 ≤ q →
    (Numq q).coeff (3 * q - 4) = ((q - 1).factorial : ℚ) * (((q - 1 : ℕ) : ℚ) + harmonic (q - 1)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq
  rcases Nat.lt_or_ge q 4 with h4 | h4
  · interval_cases q
    · show (Numq 2).coeff 2 = ((1 : ℕ).factorial : ℚ) * (((1 : ℕ) : ℚ) + harmonic 1)
      rw [(Numq_lowest le_rfl).2, harmonic_one_eq]
      norm_num
    · show (Numq 3).coeff 5 = ((2 : ℕ).factorial : ℚ) * (((2 : ℕ) : ℚ) + harmonic 2)
      rw [Numq_three_eq, harmonic_two_eq]
      norm_num [coeff_X_pow, Nat.factorial]
  · obtain ⟨p, rfl⟩ : ∃ p, q = p + 4 := ⟨q - 4, by omega⟩
    have hstep := Numq_coeff_step (q := p + 4) (by omega) (3 * p + 2)
    rw [show p + 4 - 1 = p + 3 by omega, show p + 4 - 2 = p + 2 by omega,
      show 3 * p + 2 + 6 = 3 * p + 8 by omega, show 3 * p + 2 + 5 = 3 * p + 7 by omega,
      show 3 * p + 2 + 3 = 3 * p + 5 by omega, show 3 * p + 2 + 2 = 3 * p + 4 by omega] at hstep
    have v1 : (Numq (p + 3)).coeff (3 * p + 7) = ((p + 2).factorial : ℚ) := by
      have := Numq_coeff_top (q := p + 3) (by omega)
      rwa [show 3 * (p + 3) - 2 = 3 * p + 7 by omega, show p + 3 - 1 = p + 2 by omega] at this
    have v2 := ih (p + 3) (by omega) (by omega)
    rw [show 3 * (p + 3) - 4 = 3 * p + 5 by omega, show p + 3 - 1 = p + 2 by omega] at v2
    have v3 : (Numq (p + 2)).coeff (3 * p + 5) = 0 := Numq_coeff_above (by omega) (by omega)
    have v4 : (Numq (p + 2)).coeff (3 * p + 4) = ((p + 1).factorial : ℚ) := by
      have := Numq_coeff_top (q := p + 2) (by omega)
      rwa [show 3 * (p + 2) - 2 = 3 * p + 4 by omega, show p + 2 - 1 = p + 1 by omega] at this
    have v5 := ih (p + 2) (by omega) (by omega)
    rw [show 3 * (p + 2) - 4 = 3 * p + 2 by omega, show p + 2 - 1 = p + 1 by omega] at v5
    rw [show 3 * (p + 4) - 4 = 3 * p + 8 by omega, show p + 4 - 1 = p + 3 by omega, hstep,
      v1, v2, v3, v4, v5]
    have f2 : ((p + 2).factorial : ℚ) = ((p : ℚ) + 2) * ((p + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ (p + 1)]
      push_cast
      ring
    have f3 : ((p + 3).factorial : ℚ) = ((p : ℚ) + 3) * ((p : ℚ) + 2) * ((p + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ (p + 2), Nat.factorial_succ (p + 1)]
      push_cast
      ring
    have h2 : harmonic (p + 2) = harmonic (p + 1) + ((p : ℚ) + 2)⁻¹ := by
      rw [harmonic_succ]
      push_cast
      ring
    have h3 : harmonic (p + 3) = harmonic (p + 1) + ((p : ℚ) + 2)⁻¹ + ((p : ℚ) + 3)⁻¹ := by
      rw [harmonic_succ, h2]
      push_cast
      ring
    have e2 : ((p : ℚ) + 2) * ((p : ℚ) + 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have e3 : ((p : ℚ) + 3) * ((p : ℚ) + 3)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    rw [f2, f3, h2, h3]
    push_cast
    linear_combination ((p : ℚ) + 3) * ((p + 1).factorial : ℚ) * e2 -
      ((p : ℚ) + 2) * ((p + 1).factorial : ℚ) * e3

/-- **T4.3(6)，`j = 3`**：`[x^{3q−5}] Num_q = (q−1)·(q−1)!·(H_{q−1} − 1)`（`q ≥ 2`）。 -/
theorem Numq_top_three : ∀ q : ℕ, 2 ≤ q →
    (Numq q).coeff (3 * q - 5) =
      ((q - 1 : ℕ) : ℚ) * ((q - 1).factorial : ℚ) * (harmonic (q - 1) - 1) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq
  rcases Nat.lt_or_ge q 4 with h4 | h4
  · interval_cases q
    · show (Numq 2).coeff 1 = ((1 : ℕ) : ℚ) * ((1 : ℕ).factorial : ℚ) * (harmonic 1 - 1)
      rw [(Numq_lowest le_rfl).1 1 (by norm_num), harmonic_one_eq]
      norm_num
    · show (Numq 3).coeff 4 = ((2 : ℕ) : ℚ) * ((2 : ℕ).factorial : ℚ) * (harmonic 2 - 1)
      rw [Numq_three_eq, harmonic_two_eq]
      norm_num [coeff_X_pow, Nat.factorial]
  · obtain ⟨p, rfl⟩ : ∃ p, q = p + 4 := ⟨q - 4, by omega⟩
    have hstep := Numq_coeff_step (q := p + 4) (by omega) (3 * p + 1)
    rw [show p + 4 - 1 = p + 3 by omega, show p + 4 - 2 = p + 2 by omega,
      show 3 * p + 1 + 6 = 3 * p + 7 by omega, show 3 * p + 1 + 5 = 3 * p + 6 by omega,
      show 3 * p + 1 + 3 = 3 * p + 4 by omega, show 3 * p + 1 + 2 = 3 * p + 3 by omega] at hstep
    have v1 : (Numq (p + 3)).coeff (3 * p + 6) = 0 := by
      have := Numq_coeff_gap (q := p + 3) (by omega)
      rwa [show 3 * (p + 3) - 3 = 3 * p + 6 by omega] at this
    have v2 := ih (p + 3) (by omega) (by omega)
    rw [show 3 * (p + 3) - 5 = 3 * p + 4 by omega, show p + 3 - 1 = p + 2 by omega] at v2
    have v3 : (Numq (p + 2)).coeff (3 * p + 4) = ((p + 1).factorial : ℚ) := by
      have := Numq_coeff_top (q := p + 2) (by omega)
      rwa [show 3 * (p + 2) - 2 = 3 * p + 4 by omega, show p + 2 - 1 = p + 1 by omega] at this
    have v4 : (Numq (p + 2)).coeff (3 * p + 3) = 0 := by
      have := Numq_coeff_gap (q := p + 2) (by omega)
      rwa [show 3 * (p + 2) - 3 = 3 * p + 3 by omega] at this
    have v5 := ih (p + 2) (by omega) (by omega)
    rw [show 3 * (p + 2) - 5 = 3 * p + 1 by omega, show p + 2 - 1 = p + 1 by omega] at v5
    rw [show 3 * (p + 4) - 5 = 3 * p + 7 by omega, show p + 4 - 1 = p + 3 by omega, hstep,
      v1, v2, v3, v4, v5]
    have f2 : ((p + 2).factorial : ℚ) = ((p : ℚ) + 2) * ((p + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ (p + 1)]
      push_cast
      ring
    have f3 : ((p + 3).factorial : ℚ) = ((p : ℚ) + 3) * ((p : ℚ) + 2) * ((p + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ (p + 2), Nat.factorial_succ (p + 1)]
      push_cast
      ring
    have h2 : harmonic (p + 2) = harmonic (p + 1) + ((p : ℚ) + 2)⁻¹ := by
      rw [harmonic_succ]
      push_cast
      ring
    have h3 : harmonic (p + 3) = harmonic (p + 1) + ((p : ℚ) + 2)⁻¹ + ((p : ℚ) + 3)⁻¹ := by
      rw [harmonic_succ, h2]
      push_cast
      ring
    have e2 : ((p : ℚ) + 2) * ((p : ℚ) + 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have e3 : ((p : ℚ) + 3) * ((p : ℚ) + 3)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    rw [f2, f3, h2, h3]
    push_cast
    linear_combination ((p : ℚ) + 3) * ((p + 1).factorial : ℚ) * ((p : ℚ) + 1) * e2 -
      ((p : ℚ) + 3) * ((p + 1).factorial : ℚ) * ((p : ℚ) + 2) * e3

end A207123
