import A207123.HNum
import A207123.DFiniteN

/-!
# 报告 T3.5(2)：`𝒩` 满足的一阶 PDE

**T3.5(2)**（`NK_pde`）：在 `ℚ[[x,y]]` 中
`(1 − x(1+y) + x³(1−y²))·𝒩 − x³·y·(1+y)²·∂_y 𝒩 = 1 − x + x³ + x²y²`，
`𝒩 = Σ N(k,q) x^k y^q`（`DFiniteN.lean` 的 `NKser`）。取 `x^k y^q` 系数（`NK_pde_coeff`）恰为 (C3) 的三角递推
加 4 个边界修正项（右边的 `1`、`−x`、`x³`、`x²y²`）。

`ℚ[[x,y]]` 写成 `PS2 ℚ = ℚ[[x]][[y]]`（外层变量 `y`，沿用 `HNum.lean` 的 `xvar = C X`、`tvar = X`，这里
`tvar` 就是 `y`）；`∂_y` 是 `dTK ℚ`。

**证明**：把左边展成单项式 `x^a y^b·𝒩`、`x^a y^b·∂_y𝒩` 之和（`coeff2_xt`、`coeff_dTK` 计算系数），
逐个系数比较。`k ≥ 3`、`q ≥ 1` 时就是 `Binomial.lean` 的三角递推 `N_tri`；其余是边界情形，用 `N` 的小值
（`N(0,q) = [q=0]`、`N(1,q) = [q=1]`、`N(2,·)`、`N(k,0) = 0`（`k ≥ 1`））直接验证。

报告说「三角递推可由引理 1 推出」：`N_tri` 在 `Binomial.lean` 中正是由引理 1 代入二项式基得到的，
本文件把它与 PDE 的系数形式对上。T3.5(3)（Laplace 形式、₁F₁ 和式、Humbert 闭式）没有形式化。
-/

open Polynomial Finset

namespace A207123

/-- 辅助引理（T3.5(2)）：`[x^k y^q](x^a·y^b·Y) = [x^{k−a} y^{q−b}]Y`（越界为 0）。 -/
theorem coeff2_xt (a b : ℕ) (Y : PS2 ℚ) (k q : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff q (xvar ^ a * tvar ^ b * Y)) =
      if a ≤ k ∧ b ≤ q then PowerSeries.coeff (k - a) (PowerSeries.coeff (q - b) Y) else 0 := by
  have e : xvar ^ a * tvar ^ b * Y
      = PowerSeries.C ((PowerSeries.X : PowerSeries ℚ) ^ a) * (PowerSeries.X ^ b * Y) := by
    simp only [xvar, tvar, map_pow]; ring
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hb : b ≤ q <;> by_cases ha : a ≤ k <;> simp [ha, hb]

/-- 辅助引理（T3.5(2)）：`[x^k y^n]∂_y Y = (n+1)·[x^k y^{n+1}]Y`。 -/
theorem coeff_dTK (Y : PS2 ℚ) (n k : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff n (dTK ℚ Y))
      = ((n : ℚ) + 1) * PowerSeries.coeff k (PowerSeries.coeff (n + 1) Y) := by
  rw [dTK, PowerSeries.coeff_derivative]
  have e : ((n : PowerSeries ℚ) + 1) = PowerSeries.C ((n : ℚ) + 1) := by simp
  rw [e, PowerSeries.coeff_mul_C, mul_comm]

/-- 辅助引理（T3.5(2)）：`N` 在 `k ≤ 2` 与 `q = 0` 处的值。 -/
theorem N_small_values :
    (∀ q, (N 0 q : ℚ) = if q = 0 then 1 else 0) ∧
    (∀ q, (N 1 q : ℚ) = if q = 1 then 1 else 0) ∧
    (∀ q, (N 2 q : ℚ) = if q = 1 then 1 else if q = 2 then 2 else 0) ∧
    (∀ k, (N (k + 1) 0 : ℚ) = 0) := by
  obtain ⟨h00, h11, h21, h22⟩ := N_init
  refine ⟨fun q => ?_, fun q => ?_, fun q => ?_, fun k => by rw [N_succ_zero]; simp⟩
  · rcases q with _ | q
    · simp [h00]
    · rw [N_eq_zero_of_lt (by omega)]; simp
  · rcases q with _ | _ | q
    · rw [N_succ_zero]; simp
    · simp [h11]
    · rw [N_eq_zero_of_lt (by omega)]; simp
  · rcases q with _ | _ | _ | q
    · rw [N_succ_zero]; simp
    · simp [h21]
    · simp [h22]
    · rw [N_eq_zero_of_lt (by omega)]; simp

/-- **T3.5(2)**：`(1 − x(1+y) + x³(1−y²))·𝒩 − x³·y·(1+y)²·∂_y 𝒩 = 1 − x + x³ + x²y²`（`ℚ[[x,y]]` 中）。
取 `x^k y^q` 系数：`k ≥ 3`、`q ≥ 1` 时恰为三角递推 `N_tri`，其余是右边的 4 个边界修正项。 -/
theorem NK_pde :
    (1 - xvar * (1 + tvar) + xvar ^ 3 * (1 - tvar ^ 2)) * NKser ℚ
        - xvar ^ 3 * tvar * (1 + tvar) ^ 2 * dTK ℚ (NKser ℚ)
      = 1 - xvar + xvar ^ 3 + xvar ^ 2 * tvar ^ 2 := by
  have eL : (1 - xvar * (1 + tvar) + xvar ^ 3 * (1 - tvar ^ 2)) * NKser ℚ
        - xvar ^ 3 * tvar * (1 + tvar) ^ 2 * dTK ℚ (NKser ℚ)
      = xvar ^ 0 * tvar ^ 0 * NKser ℚ - xvar ^ 1 * tvar ^ 0 * NKser ℚ - xvar ^ 1 * tvar ^ 1 * NKser ℚ
        + xvar ^ 3 * tvar ^ 0 * NKser ℚ - xvar ^ 3 * tvar ^ 2 * NKser ℚ
        - xvar ^ 3 * tvar ^ 1 * dTK ℚ (NKser ℚ)
        - (xvar ^ 3 * tvar ^ 2 * dTK ℚ (NKser ℚ) + xvar ^ 3 * tvar ^ 2 * dTK ℚ (NKser ℚ))
        - xvar ^ 3 * tvar ^ 3 * dTK ℚ (NKser ℚ) := by ring
  have eR : (1 - xvar + xvar ^ 3 + xvar ^ 2 * tvar ^ 2 : PS2 ℚ)
      = xvar ^ 0 * tvar ^ 0 * 1 - xvar ^ 1 * tvar ^ 0 * 1 + xvar ^ 3 * tvar ^ 0 * 1
        + xvar ^ 2 * tvar ^ 2 * 1 := by ring
  rw [eL, eR]
  refine PowerSeries.ext fun q => PowerSeries.ext fun k => ?_
  simp only [map_sub, map_add, coeff2_xt, coeff_dTK, coeff_NKser, PowerSeries.coeff_one]
  obtain ⟨N0, N1, N2, Nk0⟩ := N_small_values
  have T : ∀ j r : ℕ, (N (j + 3) (r + 1) : ℚ)
      = N (j + 2) r + N (j + 2) (r + 1) + (r : ℚ) * (N j (r - 1) + 2 * N j r + N j (r + 1)) :=
    fun j r => by exact_mod_cast N_tri j r
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> rcases q with _ | _ | _ | r <;> simp [N0, N1, N2, add_assoc]
    all_goals norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rcases q with _ | _ | _ | r
    · have h1 := Nk0 (j + 2)
      have h2 := Nk0 (j + 1)
      simp only [add_assoc, Nat.reduceAdd] at h1 h2
      simp [h1, h2]
      rcases j with _ | j
      · simp [N0]
      · simp [Nk0]
    · have h := T j 0
      simp [add_assoc] at h ⊢
      linarith
    · have h := T j 1
      simp [add_assoc] at h ⊢
      linarith
    · have h := T j (r + 2)
      simp [add_assoc] at h ⊢
      linarith

end A207123
