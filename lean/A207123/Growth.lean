import A207123.Recurrence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# 报告 T1.3(4) 的前半：`y³ − y² − m` 的根与 `P_m` 的模最小根

**T1.3(4)**（根的部分）：
* `existsUnique_rho`：`m ≥ 1` 时 `y³ − y² − m` 只有一个实根 `ρ_m`，且 `ρ_m > 1`；另约定 `ρ_0 := 1`
  （`y³ = y²` 的最大实根），见 `rho`、`rho_spec`、`one_lt_rho`。
* `rho_strictMono`：`ρ_m` 关于 `m` 严格增。
* `normSq_eq_of_root`、`norm_lt_rho_of_root`：其余（非实）根 `w` 满足 `|w|² = m/ρ_m = ρ_m(ρ_m − 1) < ρ_m²`。
* `root_P_min`：于是 `x_m = 1/ρ_m` 是 `P_m = ∏_{i≤m} b_i` 唯一的模最小根（其余根的模都严格大于 `x_m`）。

T1.3(4) 的渐近部分（`U_k(m) = c_m ρ_m^k + O(r^k)`、`c_m > 0`）不在本文件。
-/

open Polynomial Finset

namespace A207123

/-- 三次式 `f_m(y) = y³ − y² − m`（实变量）。 -/
noncomputable def fcub (m : ℕ) (y : ℝ) : ℝ := y ^ 3 - y ^ 2 - m

/-- 辅助引理（T1.3(4)）：`m ≥ 1`、`y ≤ 1` 时 `f_m(y) < 0`。 -/
theorem fcub_neg_of_le_one {m : ℕ} (hm : 1 ≤ m) {y : ℝ} (hy : y ≤ 1) : fcub m y < 0 := by
  unfold fcub
  have h1 : y ^ 2 * (y - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith)
  have h2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- 辅助引理（T1.3(4)）：`f_m` 在 `[1, ∞)` 上严格增。 -/
theorem fcub_strictMonoOn (m : ℕ) : StrictMonoOn (fcub m) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold fcub
  have hba : 0 < b - a := sub_pos.mpr hab
  have hq : 0 < b ^ 2 + a * b + a ^ 2 - a - b := by nlinarith
  have : b ^ 3 - b ^ 2 - (a ^ 3 - a ^ 2) = (b - a) * (b ^ 2 + a * b + a ^ 2 - a - b) := by ring
  nlinarith [mul_pos hba hq]

/-- 辅助引理（T1.3(4)）：`m ≥ 1` 时有大于 1 的实根。 -/
theorem exists_root_gt_one {m : ℕ} (hm : 1 ≤ m) : ∃ ρ : ℝ, 1 < ρ ∧ fcub m ρ = 0 := by
  have hcont : ContinuousOn (fcub m) (Set.Icc 1 ((m : ℝ) + 1)) := by
    unfold fcub; fun_prop
  have h1 : fcub m 1 < 0 := fcub_neg_of_le_one hm le_rfl
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : 0 < fcub m ((m : ℝ) + 1) := by
    unfold fcub; nlinarith
  obtain ⟨ρ, hρ, hρ0⟩ := intermediate_value_Icc (by linarith) hcont ⟨h1.le, h2.le⟩
  refine ⟨ρ, ?_, hρ0⟩
  rcases eq_or_lt_of_le hρ.1 with h | h
  · rw [← h] at hρ0; linarith
  · exact h

/-- **T1.3(4)**：`m ≥ 1` 时 `y³ − y² − m` 只有一个实根，且它大于 1。 -/
theorem existsUnique_rho {m : ℕ} (hm : 1 ≤ m) : ∃! ρ : ℝ, ρ ^ 3 - ρ ^ 2 - m = 0 := by
  obtain ⟨ρ, hρ1, hρ⟩ := exists_root_gt_one hm
  refine ⟨ρ, hρ, fun σ hσ => ?_⟩
  have hσ1 : 1 < σ := by
    by_contra h
    push Not at h
    have := fcub_neg_of_le_one hm h
    unfold fcub at this; linarith
  exact (fcub_strictMonoOn m).injOn (Set.mem_Ici.mpr hσ1.le) (Set.mem_Ici.mpr hρ1.le)
    (by unfold fcub at hρ ⊢; rw [hσ, ← hρ])

/-- `ρ_m`：`m ≥ 1` 时为 `y³ − y² − m` 的唯一实根；`ρ_0 := 1`。 -/
noncomputable def rho (m : ℕ) : ℝ :=
  if h : 1 ≤ m then Classical.choose (exists_root_gt_one h) else 1

/-- 辅助引理（T1.3(4)）。 -/
theorem rho_zero : rho 0 = 1 := by simp [rho]

/-- 辅助引理（T1.3(4)）。 -/
theorem rho_of_one_le {m : ℕ} (hm : 1 ≤ m) : rho m = Classical.choose (exists_root_gt_one hm) := by
  simp only [rho, hm, ↓reduceDIte]

/-- **T1.3(4)**：`ρ_m > 1`（`m ≥ 1`）。 -/
theorem one_lt_rho {m : ℕ} (hm : 1 ≤ m) : 1 < rho m := by
  rw [rho_of_one_le hm]
  exact (Classical.choose_spec (exists_root_gt_one hm)).1

/-- 辅助引理（T1.3(4)）：`ρ_m ≥ 1`。 -/
theorem one_le_rho (m : ℕ) : 1 ≤ rho m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [rho_zero]
  · exact (one_lt_rho hm).le

/-- **T1.3(4)**：`ρ_m³ − ρ_m² = m`（`m = 0` 时 `ρ_0 = 1` 也满足）。 -/
theorem rho_spec (m : ℕ) : rho m ^ 3 - rho m ^ 2 = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [rho_zero]; norm_num
  · have hm1 : 1 ≤ m := hm
    have h := (Classical.choose_spec (exists_root_gt_one hm1)).2
    rw [rho_of_one_le hm1]
    unfold fcub at h
    exact sub_eq_zero.mp h

/-- **T1.3(4)**：`ρ_m` 关于 `m` 严格增。 -/
theorem rho_strictMono : StrictMono rho := by
  intro m m' hmm'
  have hm' : 1 ≤ m' := by omega
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [rho_zero]; exact one_lt_rho hm'
  · have h1 : fcub m' (rho m) < fcub m' (rho m') := by
      unfold fcub
      rw [rho_spec m, rho_spec m']
      have : (m : ℝ) < m' := by exact_mod_cast hmm'
      linarith
    exact (fcub_strictMonoOn m').lt_iff_lt (Set.mem_Ici.mpr (one_le_rho m))
      (Set.mem_Ici.mpr (one_le_rho m')) |>.mp h1

/-- 辅助引理（T1.3(4)）：`y³ − y² − m = (y − ρ)(y² + (ρ − 1)y + ρ(ρ − 1))`（复数域中）。 -/
theorem cubic_factor (m : ℕ) (w : ℂ) :
    w ^ 3 - w ^ 2 - m = (w - rho m) * (w ^ 2 + ((rho m : ℂ) - 1) * w + (rho m : ℂ) * ((rho m : ℂ) - 1)) := by
  have h : ((rho m : ℂ)) ^ 3 - (rho m : ℂ) ^ 2 = (m : ℂ) := by exact_mod_cast rho_spec m
  linear_combination h

/-- **T1.3(4)**：`y³ − y² − m` 的不等于 `ρ_m` 的复根 `w` 满足 `|w|² = ρ_m(ρ_m − 1) = m/ρ_m`。 -/
theorem normSq_eq_of_root {m : ℕ} (hm : 1 ≤ m) {w : ℂ} (hw : w ^ 3 - w ^ 2 - m = 0)
    (hne : w ≠ rho m) : Complex.normSq w = rho m * (rho m - 1) ∧ rho m * (rho m - 1) = m / rho m := by
  have hρ1 := one_lt_rho hm
  have hq : w ^ 2 + ((rho m : ℂ) - 1) * w + (rho m : ℂ) * ((rho m : ℂ) - 1) = 0 := by
    rw [cubic_factor] at hw
    exact (mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hne)
  -- `w` 不是实数：否则它是 `f_m` 的另一个实根
  have hnr : w ≠ (starRingEnd ℂ) w := by
    intro hconj
    have him : w.im = 0 := by
      have := congrArg Complex.im hconj
      simp only [Complex.conj_im] at this
      linarith
    have hre : w = (w.re : ℂ) := Complex.ext rfl (by simp [him])
    have hreal : w.re ^ 3 - w.re ^ 2 - m = 0 := by
      have := hw
      rw [hre] at this
      exact_mod_cast this
    obtain ⟨ρ, _, huniq⟩ := existsUnique_rho hm
    have e1 : w.re = ρ := huniq _ hreal
    have e2 : rho m = ρ := huniq _ (by have := rho_spec m; linarith)
    exact hne (by rw [hre, e1, ← e2])
  have hq' : (starRingEnd ℂ) w ^ 2 + ((rho m : ℂ) - 1) * (starRingEnd ℂ) w
      + (rho m : ℂ) * ((rho m : ℂ) - 1) = 0 := by
    have := congrArg (starRingEnd ℂ) hq
    simpa [map_add, map_mul, map_pow, map_sub, Complex.conj_ofReal] using this
  have hsum : w + (starRingEnd ℂ) w = 1 - (rho m : ℂ) := by
    have h3 : (w - (starRingEnd ℂ) w) * (w + (starRingEnd ℂ) w + ((rho m : ℂ) - 1)) = 0 := by
      linear_combination hq - hq'
    have := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hnr)
    linear_combination this
  have hprod : w * (starRingEnd ℂ) w = (rho m : ℂ) * ((rho m : ℂ) - 1) := by
    linear_combination -hq + w * hsum
  have hns : (Complex.normSq w : ℂ) = (rho m : ℂ) * ((rho m : ℂ) - 1) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]; exact hprod
  refine ⟨by exact_mod_cast hns, ?_⟩
  have hρ0 : rho m ≠ 0 := by linarith
  rw [eq_div_iff hρ0]
  have := rho_spec m
  nlinarith

/-- **T1.3(4)**：`y³ − y² − m` 的不等于 `ρ_m` 的复根的模严格小于 `ρ_m`。 -/
theorem norm_lt_rho_of_root {m : ℕ} (hm : 1 ≤ m) {w : ℂ} (hw : w ^ 3 - w ^ 2 - m = 0)
    (hne : w ≠ rho m) : ‖w‖ < rho m := by
  have hρ1 := one_lt_rho hm
  have hns := (normSq_eq_of_root hm hw hne).1
  have h1 : ‖w‖ ^ 2 < rho m ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hns]; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith) h1

/-- 辅助引理（T1.3(4)）：`b_i` 的复根 `z` 不为 0，且 `1/z` 是 `y³ − y² − i` 的根。 -/
theorem inv_root_of_bpoly_root {i : ℕ} {z : ℂ} (hz : (bpoly ℂ i).IsRoot z) :
    z ≠ 0 ∧ z⁻¹ ^ 3 - z⁻¹ ^ 2 - i = 0 := by
  have h : 1 - z - (i : ℂ) * z ^ 3 = 0 := by
    have := hz.eq_zero
    rwa [eval_bpoly] at this
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at h; norm_num at h
  refine ⟨hz0, ?_⟩
  have : z⁻¹ ^ 3 - z⁻¹ ^ 2 - i = z⁻¹ ^ 3 * (1 - z - (i : ℂ) * z ^ 3) := by
    field_simp
  rw [this, h, mul_zero]

/-- **T1.3(4)**：`m ≥ 1` 时 `x_m = 1/ρ_m` 是 `P_m = ∏_{i≤m} b_i` 唯一的模最小根：`P_m` 的任一复根 `z`
要么等于 `1/ρ_m`，要么 `|z| > 1/ρ_m`。 -/
theorem root_P_min {m : ℕ} (hm : 1 ≤ m) {z : ℂ} (hz : (Ppoly ℂ m).IsRoot z) :
    z = ((rho m)⁻¹ : ℝ) ∨ (rho m)⁻¹ < ‖z‖ := by
  have hρ1 := one_lt_rho hm
  have hρ0 : 0 < rho m := by linarith
  -- `z` 是某个 `b_i`（`i ≤ m`）的根
  have hz' : ∏ i ∈ range (m + 1), (bpoly ℂ i).eval z = 0 := by
    have := hz.eq_zero
    rwa [Ppoly, eval_prod] at this
  obtain ⟨i, hi, hiz⟩ := Finset.prod_eq_zero_iff.mp hz'
  rw [mem_range] at hi
  obtain ⟨hz0, hroot⟩ := inv_root_of_bpoly_root (show (bpoly ℂ i).IsRoot z from hiz)
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · -- `b_0 = 1 − x` 的根是 1
    right
    have h1 : z = 1 := by
      have : 1 - z - ((0 : ℕ) : ℂ) * z ^ 3 = 0 := by
        have := hiz; rw [eval_bpoly] at this; exact this
      simp at this
      linear_combination -this
    rw [h1, norm_one]
    exact inv_lt_one_of_one_lt₀ hρ1
  · by_cases hreal : z⁻¹ = (rho i : ℂ)
    · -- 实根 `1/z = ρ_i`
      have hzr : z = ((rho i)⁻¹ : ℝ) := by
        rw [Complex.ofReal_inv, ← hreal, inv_inv]
      rcases Nat.lt_or_ge i m with him | him
      · right
        rw [hzr, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (by linarith [one_lt_rho hi1]))]
        exact inv_strictAnti₀ (by linarith [one_lt_rho hi1]) (rho_strictMono him)
      · left
        have : i = m := by omega
        subst this
        exact hzr
    · -- 非实根：`|1/z| < ρ_i ≤ ρ_m`
      right
      have h1 : ‖z⁻¹‖ < rho i := norm_lt_rho_of_root hi1 hroot hreal
      have h2 : rho i ≤ rho m := rho_strictMono.monotone (by omega)
      rw [norm_inv] at h1
      have h3 : ‖z‖⁻¹ < rho m := lt_of_lt_of_le h1 h2
      calc (rho m)⁻¹ < (‖z‖⁻¹)⁻¹ := inv_strictAnti₀ (inv_pos.mpr hnz) h3
        _ = ‖z‖ := inv_inv _

end A207123
