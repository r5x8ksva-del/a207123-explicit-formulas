import A207123.HNum
import A207123.DFiniteN

/-!
# 报告 T3.6：h 多项式的二元母函数 `𝓗(z,t) = Σ_k h_k(t) z^k`

**T3.6**：
* `HH_eq_F`：`𝓗(z,t) = (1−t)·F(z(1−t), t)`。
* `HH_eq_N`：`𝓗 = 1 + (𝒩(z(1−t), t/(1−t)) − 1)/t`，写成乘以 `t` 的形式 `t·𝓗 = t + 𝒩(z(1−t), t/(1−t)) − 1`。
* `HH_pde`：`(1 − z − z³t(1−t))·𝓗 − z⁴t(1−t)·∂_z𝓗 − z³t(1−t)²·∂_t𝓗 = 1 + z²t`；
  取 `z^k` 系数即 (C6) 的递推（`hpoly_rec`）加初值 `h_0 = 1`、`h_1 = 1`、`h_2 = 1 + t`。

**定义的取法**：`𝓗` 写成 `PS2 ℚ = ℚ[[t]][[z]]`（外层变量 `z`、内层变量 `t`），沿用 `HNum.lean` 的
`tvar = X`（这里是 `z`）、`xvar = C X`（这里是 `t`）；`∂_z = dTK ℚ`（外层导数），`∂_t = dXK ℚ`（逐个系数求导）。
* `F(z(1−t), t)`：`F` 以 `x` 为外层变量写成 `Fx = Σ_k f_k(t)·x^k`（`f_k = Σ_m U_k(m) t^m`，与 `FK` 的系数相同，
  只是外层变量换成 `x`），把 `x` 换成 `z·(1−t)` 就是 Mathlib 的 `PowerSeries.rescale (1 − t)`。
* `𝒩(z(1−t), t/(1−t))`：`𝒩 = Σ_k x^k·Σ_q N(k,q) y^q`，把 `x` 换成 `z(1−t)`、`y` 换成 `t/(1−t)`
  （`DFiniteN.lean` 的 `tFrac`）；`N(k,q) = 0`（`q > k`），所以 `z^k` 的系数是有限和
  `(1−t)^k·Σ_{q≤k} N(k,q)·(t/(1−t))^q`（`NsubH`）。
-/

open Polynomial Finset

namespace A207123

/-- `𝓗(z,t) = Σ_k h_k(t)·z^k ∈ ℚ[[t]][[z]]`（外层变量 `z`、内层变量 `t`）。 -/
noncomputable def HH : PS2 ℚ := PowerSeries.mk fun k => ((hpoly k : ℚ[X]) : PowerSeries ℚ)

/-- `F` 以 `x` 为外层变量：`Σ_k f_k(t)·x^k`，`f_k = Σ_m U_k(m) t^m`。 -/
noncomputable def Fx : PS2 ℚ := PowerSeries.mk fun k => fser k

/-- `𝒩(z(1−t), t/(1−t))`：`z^k` 的系数是 `(1−t)^k·Σ_{q≤k} N(k,q)·(t/(1−t))^q`。 -/
noncomputable def NsubH : PS2 ℚ :=
  PowerSeries.mk fun k => (1 - PowerSeries.X) ^ k *
    ∑ q ∈ range (k + 1), PowerSeries.C (N k q : ℚ) * tFrac ℚ ^ q

/-- **T3.6**：`𝓗(z,t) = (1−t)·F(z(1−t), t)`（`F(z(1−t), t) = rescale (1−t) Fx`）。 -/
theorem HH_eq_F :
    HH = PowerSeries.C (1 - PowerSeries.X) * PowerSeries.rescale (1 - PowerSeries.X) Fx := by
  refine PowerSeries.ext fun k => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  simp only [HH, Fx, PowerSeries.coeff_mk]
  rw [← hpoly_spec k]
  ring

/-- 辅助引理（T3.6）：`h_k` 作为 `t` 的幂级数（`k ≥ 1`）。 -/
theorem coe_hpoly_succ (k : ℕ) :
    ((hpoly (k + 1) : ℚ[X]) : PowerSeries ℚ) = ∑ q ∈ Icc 1 (k + 1),
      PowerSeries.C (N (k + 1) q : ℚ) * PowerSeries.X ^ (q - 1) * (1 - PowerSeries.X) ^ (k + 1 - q) := by
  rw [hpoly_succ, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  apply sum_congr rfl
  intro q _
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_one]

/-- **T3.6**：`𝓗 = 1 + (𝒩(z(1−t), t/(1−t)) − 1)/t`，写成 `t·𝓗 = t + 𝒩(z(1−t), t/(1−t)) − 1`。 -/
theorem HH_eq_N : xvar * HH = xvar + NsubH - 1 := by
  refine PowerSeries.ext fun k => ?_
  simp only [xvar, HH, NsubH, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_one]
  rcases k with _ | k
  · simp [hpoly_zero, N_init.1]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, sub_zero]
    have key : ∀ q ∈ range (k + 1 + 1), (1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1) *
        (PowerSeries.C (N (k + 1) q : ℚ) * tFrac ℚ ^ q)
        = PowerSeries.C (N (k + 1) q : ℚ) * PowerSeries.X ^ q * (1 - PowerSeries.X) ^ (k + 1 - q) := by
      intro q hq
      rw [mem_range] at hq
      have e : (1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1)
          = (1 - PowerSeries.X) ^ q * (1 - PowerSeries.X) ^ (k + 1 - q) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      have ht : (1 - PowerSeries.X : PowerSeries ℚ) ^ q * tFrac ℚ ^ q = PowerSeries.X ^ q := by
        rw [← mul_pow, mul_comm, tFrac_mul_one_sub_X]
      rw [e]
      linear_combination (PowerSeries.C (N (k + 1) q : ℚ) * (1 - PowerSeries.X) ^ (k + 1 - q)) * ht
    rw [mul_sum, sum_congr rfl key, coe_hpoly_succ, mul_sum]
    symm
    rw [← Finset.sum_subset (s₁ := Icc 1 (k + 1)) (s₂ := range (k + 1 + 1))]
    · apply sum_congr rfl
      intro q hq
      rw [mem_Icc] at hq
      have e : PowerSeries.X ^ q = PowerSeries.X * (PowerSeries.X : PowerSeries ℚ) ^ (q - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hq.1]
      rw [e]
      ring
    · intro q hq
      rw [mem_Icc] at hq
      rw [mem_range]
      omega
    · intro q hq2 hq
      rw [mem_Icc] at hq
      rw [mem_range] at hq2
      have hq0 : q = 0 := by omega
      subst hq0
      rw [N_succ_zero]
      simp

/-- 辅助引理（T3.6）：`[z^k](C a·z^b·Y) = a·[z^{k−b}]Y`（越界为 0）。 -/
theorem coeff_C_mul_X_pow_mul (a : PowerSeries ℚ) (b : ℕ) (Y : PS2 ℚ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.C a * (PowerSeries.X ^ b * Y))
      = if b ≤ k then a * PowerSeries.coeff (k - b) Y else 0 := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

/-- **T3.6**：`(1 − z − z³t(1−t))·𝓗 − z⁴t(1−t)·∂_z𝓗 − z³t(1−t)²·∂_t𝓗 = 1 + z²t`。取 `z^k` 系数即
(C6) 的递推 `hpoly_rec`（`k ≥ 3`）与初值 `h_0 = 1`、`h_1 = 1`、`h_2 = 1 + t`。 -/
theorem HH_pde :
    (1 - tvar - tvar ^ 3 * xvar * (1 - xvar)) * HH
      - tvar ^ 4 * xvar * (1 - xvar) * dTK ℚ HH
      - tvar ^ 3 * xvar * (1 - xvar) ^ 2 * dXK ℚ HH
    = 1 + tvar ^ 2 * xvar := by
  set T : PowerSeries ℚ := PowerSeries.X with hT
  have eL : (1 - tvar - tvar ^ 3 * xvar * (1 - xvar)) * HH
      - tvar ^ 4 * xvar * (1 - xvar) * dTK ℚ HH
      - tvar ^ 3 * xvar * (1 - xvar) ^ 2 * dXK ℚ HH
      = PowerSeries.C 1 * (PowerSeries.X ^ 0 * HH) - PowerSeries.C 1 * (PowerSeries.X ^ 1 * HH)
        - PowerSeries.C (T * (1 - T)) * (PowerSeries.X ^ 3 * HH)
        - PowerSeries.C (T * (1 - T)) * (PowerSeries.X ^ 4 * dTK ℚ HH)
        - PowerSeries.C (T * (1 - T) ^ 2) * (PowerSeries.X ^ 3 * dXK ℚ HH) := by
    simp only [xvar, tvar, hT, map_mul, map_sub, map_one, map_pow]
    ring
  have eR : (1 + tvar ^ 2 * xvar : PS2 ℚ)
      = PowerSeries.C 1 * (PowerSeries.X ^ 0 * 1) + PowerSeries.C T * (PowerSeries.X ^ 2 * 1) := by
    simp only [xvar, tvar, hT, map_one]
    ring
  rw [eL, eR]
  refine PowerSeries.ext fun k => ?_
  simp only [map_sub, map_add, coeff_C_mul_X_pow_mul, PowerSeries.coeff_one]
  -- 各项系数
  have cH : ∀ n, PowerSeries.coeff n HH = ((hpoly n : ℚ[X]) : PowerSeries ℚ) := fun n => by
    simp [HH]
  have cD : ∀ n, PowerSeries.coeff n (dTK ℚ HH)
      = ((hpoly (n + 1) : ℚ[X]) : PowerSeries ℚ) * ((n : PowerSeries ℚ) + 1) := fun n => by
    rw [dTK, PowerSeries.coeff_derivative, cH]
  have cX : ∀ n, PowerSeries.coeff n (dXK ℚ HH)
      = ((derivative (hpoly n) : ℚ[X]) : PowerSeries ℚ) := fun n => by
    rw [dXK, PowerSeries.coeff_mk, cH, PowerSeries.derivative_coe]
  simp only [cH, cD, cX]
  rcases k with _ | _ | _ | j
  · simp [hpoly_zero]
  · simp [hpoly_zero, hpoly_one]
  · simp [hpoly_one, hpoly_two, hT]
  · have hr := hpoly_rec (j + 3) (by omega)
    rw [show j + 3 - 1 = j + 2 by omega, show j + 3 - 3 = j by omega] at hr
    have hr' : ((hpoly (j + 3) : ℚ[X]) : PowerSeries ℚ) = ((hpoly (j + 2) : ℚ[X]) : PowerSeries ℚ)
        + T * (1 - T) * ((1 - T) * ((derivative (hpoly j) : ℚ[X]) : PowerSeries ℚ)
          + ((j : PowerSeries ℚ) + 1) * ((hpoly j : ℚ[X]) : PowerSeries ℚ)) := by
      rw [hr]
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
        Polynomial.coe_X, Polynomial.coe_C, hT]
      congr 3
      rw [show ((↑(j + 3) : ℚ) - 2) = (j : ℚ) + 1 by push_cast; ring, map_add, map_natCast, map_one]
    simp only [show 0 ≤ j + 1 + 1 + 1 from Nat.zero_le _, show 1 ≤ j + 1 + 1 + 1 by omega,
      show 3 ≤ j + 1 + 1 + 1 by omega, ↓reduceIte]
    have e0 : j + 1 + 1 + 1 - 0 = j + 3 := by omega
    have e1 : j + 1 + 1 + 1 - 1 = j + 2 := by omega
    have e3 : j + 1 + 1 + 1 - 3 = j := by omega
    rw [e0, e1, e3]
    rcases j with _ | j
    · simp only [show ¬ (4 ≤ 0 + 1 + 1 + 1) by omega, ↓reduceIte]
      rw [hr']
      simp [hpoly_zero]
    · simp only [show 4 ≤ j + 1 + 1 + 1 + 1 by omega, ↓reduceIte,
        show j + 1 + 1 + 1 + 1 - 4 = j by omega]
      rw [show j + 1 + 3 = j + 1 + 1 + 1 + 1 by omega] at hr'
      rw [hr']
      push_cast
      ring

end A207123
