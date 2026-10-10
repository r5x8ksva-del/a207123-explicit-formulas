import A207123.ThreeAtoms
import A207123.Binomial

/-!
# `N(k,q)` 的三原子单和：存在且唯一（猜想总表 A26 (ii) 的一部分；notes/13 定理 5(b)）

原子 `c_i(n) = [xⁿ] 1/b_i`（`n < 0` 时取 0：`ciZ`），平移取 `3(q−1) + σ`（`σ` 与 `q` 无关）。notes/13 定理 5(b)：
对每个整数 `σ`，存在唯一的一组数 `γ^{(0)}` 与 `γ_r(q,i)`（`1 ≤ i ≤ q−1`，`r = 0, 1, 2`），使
`N(k,q) = γ^{(0)} + Σ_{i=1}^{q−1} Σ_{r=0}^{2} γ_r(q,i)·c_i(k+3(q−1)+σ−r)` 对充分大的 `k` 成立；最高一项满足
`(q−1)!·γ_r(q,q−1) = a_r^{(σ)}(q−1)`（notes/12 定理 2(b) 中 `U` 的规范化系数，`atomRep`）。

* 存在（`N_three_atoms_exists`）：`k ≥ 1` 时 `N(k,q) = Σ_{M=0}^{q−1} (−1)^{q−1−M} C(q,M+1)·U_k(M)`（T1.4(1)，
  `N_eq_sum_U`），对每个 `M` 用 `three_atoms_exists`，平移取 `σ + 3(q−1−M)`，使原子都成为
  `c_i(k+3(q−1)+σ−r)`，再交换求和次序；系数 `NatomConst`、`NatomCoeff`。
* 唯一（`N_three_atoms_unique`）：直接由原子的线性无关 `atoms_lin_indep`。
* 最高一项（`NatomCoeff_top`）：`i = q−1` 只有 `M = q−1` 一项。
* 常数项（`NatomConst_eq`）：`γ^{(0)} = (−1)^{q−1} Σ_{M=0}^{q−1} C(q,M+1)/M!`；`q = 2, 3` 时为 `−3`、`13/2`
  （notes/13 注 5.2 两个例子里的常数）。

「每个 i 一个原子不存在」（定理 5(a)）与「沿最高对角线的系数不是 P-递推的」（归结为 A25(c)）不在这里。
-/

namespace A207123

open Finset Filter

noncomputable section

/-- T1.4(1) 换下标写在 `ℚ` 中（`k ≥ 1`）：`N(k,q) = Σ_{M=0}^{q−1} (−1)^{q−1−M}·C(q,M+1)·U_k(M)`。 -/
theorem N_eq_sum_U {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    (N k q : ℚ) = ∑ M ∈ range q, (-1 : ℚ) ^ (q - 1 - M) * (q.choose (M + 1) : ℚ) * (U k M : ℚ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := congrArg (Int.cast : ℤ → ℚ) (N_eq_inv_Vn (1 + k) q)
  push_cast at h
  rw [h, sum_range_succ', show 1 + k = k + 1 by omega, Vn_succ_zero]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  refine sum_congr rfl fun M _ => ?_
  rw [U_eq_Vn, show q - (M + 1) = q - 1 - M by omega]

/-- 定理 5(b) 的常数项 `γ^{(0)} = Σ_{M=0}^{q−1} (−1)^{q−1−M}·C(q,M+1)·(−1)^M/M!`。 -/
def NatomConst (q : ℕ) : ℚ :=
  ∑ M ∈ range q, (-1 : ℚ) ^ (q - 1 - M) * (q.choose (M + 1) : ℚ) * ((-1) ^ M / (M.factorial : ℚ))

/-- 定理 5(b) 的系数 `γ_r(q,i) = Σ_{M=i}^{q−1} (−1)^{q−1−M}·C(q,M+1)·γ_r(M,i)`，其中 `γ_r(M,i)` 是
`U_k(M)` 在平移 `3M + (σ + 3(q−1−M)) = 3(q−1) + σ` 下的系数（`atomCoeff`）。 -/
def NatomCoeff (q i : ℕ) (σ : ℤ) (r : ℕ) : ℚ :=
  ∑ M ∈ Ico i q, (-1 : ℚ) ^ (q - 1 - M) * (q.choose (M + 1) : ℚ) *
    atomCoeff M i (σ + 3 * ((q : ℤ) - 1 - M)) r

/-- **定理 5(b)，存在**：`k` 充分大时
`N(k,q) = γ^{(0)} + Σ_{i=1}^{q−1} Σ_{r=0}^{2} γ_r(q,i)·c_i(k+3(q−1)+σ−r)`。 -/
theorem N_three_atoms_exists (q : ℕ) (σ : ℤ) : ∀ᶠ k in atTop,
    (N k q : ℚ) = NatomConst q +
      ∑ i ∈ Icc 1 (q - 1), ∑ r ∈ range 3, NatomCoeff q i σ r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r) := by
  have hall : ∀ᶠ k in atTop, ∀ M ∈ range q, (U k M : ℚ) = (-1) ^ M / (M.factorial : ℚ) +
      ∑ i ∈ Icc 1 M, ∑ r ∈ range 3, atomCoeff M i (σ + 3 * ((q : ℤ) - 1 - M)) r *
        ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r) := by
    rw [eventually_all_finset]
    intro M _
    filter_upwards [three_atoms_exists M (σ + 3 * ((q : ℤ) - 1 - M))] with k hk
    rw [hk]
    congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun r _ => ?_
    rw [show (k : ℤ) + 3 * M + (σ + 3 * ((q : ℤ) - 1 - M)) - r = (k : ℤ) + 3 * (q - 1) + σ - r by ring]
  filter_upwards [hall, eventually_ge_atTop 1] with k hk hk1
  have e1 : (N k q : ℚ) = ∑ M ∈ range q, (-1 : ℚ) ^ (q - 1 - M) * (q.choose (M + 1) : ℚ) *
      ((-1) ^ M / (M.factorial : ℚ) + ∑ i ∈ Icc 1 M, ∑ r ∈ range 3,
        atomCoeff M i (σ + 3 * ((q : ℤ) - 1 - M)) r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r)) := by
    rw [N_eq_sum_U hk1]
    exact sum_congr rfl fun M hM => by rw [hk M hM]
  have hc : NatomConst q = ∑ M ∈ range q, (-1 : ℚ) ^ (q - 1 - M) * (q.choose (M + 1) : ℚ) *
      ((-1) ^ M / (M.factorial : ℚ)) := rfl
  rw [e1, hc]
  simp only [mul_add, sum_add_distrib]
  congr 1
  simp only [mul_sum]
  rw [sum_comm' (t' := Icc 1 (q - 1)) (s' := fun i => Ico i q) (fun M i => by
    simp only [mem_range, mem_Icc, mem_Ico]
    omega)]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [NatomCoeff, sum_mul]
  refine sum_congr rfl fun M _ => ?_
  ring

/-- **定理 5(b)，唯一**：任何一组 `γ₀`、`γ_r(q,i)` 使
`N(k,q) = γ₀ + Σ_i Σ_r γ_r(q,i)·c_i(k+3(q−1)+σ−r)` 对充分大的 `k` 成立，就是 `N_three_atoms_exists` 中的那一组。 -/
theorem N_three_atoms_unique (q : ℕ) (σ : ℤ) (γ0 : ℚ) (γ : ℕ → ℕ → ℚ)
    (h : ∀ᶠ k in atTop, (N k q : ℚ) =
      γ0 + ∑ i ∈ Icc 1 (q - 1), ∑ r ∈ range 3, γ i r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r)) :
    γ0 = NatomConst q ∧ ∀ i ∈ Icc 1 (q - 1), ∀ r < 3, γ i r = NatomCoeff q i σ r := by
  have hd := atoms_lin_indep (q - 1) (3 * ((q : ℤ) - 1) + σ) (γ0 - NatomConst q)
    (fun i r => γ i r - NatomCoeff q i σ r) (by
      filter_upwards [h, N_three_atoms_exists q σ] with k hk1 hk2
      have e : ∀ i, atomComb i (3 * ((q : ℤ) - 1) + σ) (fun r => γ i r - NatomCoeff q i σ r) k =
          ∑ r ∈ range 3, γ i r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r) -
            ∑ r ∈ range 3, NatomCoeff q i σ r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r) := by
        intro i
        rw [atomComb, ← sum_sub_distrib]
        refine sum_congr rfl fun r _ => ?_
        rw [show (k : ℤ) + (3 * ((q : ℤ) - 1) + σ) - r = (k : ℤ) + 3 * (q - 1) + σ - r by ring]
        ring
      simp only [e, sum_sub_distrib]
      linarith)
  refine ⟨by linarith [hd.1], fun i hi r hr => ?_⟩
  have h3 : γ i r - NatomCoeff q i σ r = 0 := hd.2 i hi r hr
  linarith

/-- **猜想总表 A26 (ii) 的存在唯一部分（notes/13 定理 5(b)）**：对每个 `q` 与每个整数 `σ`，`k` 充分大时
`N(k,q) = γ^{(0)} + Σ_{i=1}^{q−1} Σ_{r=0}^{2} γ_r(q,i)·c_i(k+3(q−1)+σ−r)`（`γ^{(0)} = NatomConst q`，
`γ_r(q,i) = NatomCoeff q i σ r`），而且这样的表示唯一。 -/
theorem N_three_atoms (q : ℕ) (σ : ℤ) :
    (∀ᶠ k in atTop, (N k q : ℚ) = NatomConst q +
      ∑ i ∈ Icc 1 (q - 1), ∑ r ∈ range 3, NatomCoeff q i σ r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r)) ∧
    ∀ (γ0 : ℚ) (γ : ℕ → ℕ → ℚ), (∀ᶠ k in atTop, (N k q : ℚ) =
      γ0 + ∑ i ∈ Icc 1 (q - 1), ∑ r ∈ range 3, γ i r * ciZ i ((k : ℤ) + 3 * (q - 1) + σ - r)) →
      γ0 = NatomConst q ∧ ∀ i ∈ Icc 1 (q - 1), ∀ r < 3, γ i r = NatomCoeff q i σ r :=
  ⟨N_three_atoms_exists q σ, fun γ0 γ h => N_three_atoms_unique q σ γ0 γ h⟩

/-- **定理 5(b) 的最高一项**：`(q−1)!·γ_r(q,q−1) = a_r^{(σ)}(q−1)`，即 `x^σ·W̃_{q−1}` 在 `K_{q−1}` 中约化代表的
系数（与 notes/12 定理 2(b) 中 `U` 的规范化系数相同）。 -/
theorem NatomCoeff_top (q : ℕ) (hq : 1 ≤ q) (σ : ℤ) (r : ℕ) :
    ((q - 1).factorial : ℚ) * NatomCoeff q (q - 1) σ r = (atomRep (q - 1) σ).coeff r := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hσ : σ + 3 * (((p + 1 : ℕ) : ℤ) - 1 - (p : ℤ)) = σ := by
    push_cast
    ring
  have h := atomCoeff_normalized p p σ r
  rw [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul] at h
  rw [NatomCoeff, Nat.add_sub_cancel, Nat.Ico_succ_singleton, sum_singleton, hσ, Nat.choose_self,
    Nat.sub_self, pow_zero, Nat.cast_one, one_mul, one_mul, h]

/-- 常数项的闭式：`γ^{(0)} = (−1)^{q−1}·Σ_{M=0}^{q−1} C(q,M+1)/M!`。 -/
theorem NatomConst_eq (q : ℕ) :
    NatomConst q = (-1) ^ (q - 1) * ∑ M ∈ range q, (q.choose (M + 1) : ℚ) / (M.factorial : ℚ) := by
  rw [NatomConst, mul_sum]
  refine sum_congr rfl fun M hM => ?_
  have hM' : M ≤ q - 1 := by
    rw [mem_range] at hM
    omega
  have e : (-1 : ℚ) ^ (q - 1) = (-1) ^ (q - 1 - M) * (-1) ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hM']
  rw [e]
  ring

/-- `q = 2`：`γ^{(0)} = −3`（notes/13 注 5.2：`N(k,2) = c_1(k+3) + c_1(k−2) − 3`）。 -/
theorem NatomConst_two : NatomConst 2 = -3 := by
  have h1 : Nat.choose 2 1 = 2 := by decide
  have h2 : Nat.choose 2 2 = 1 := by decide
  norm_num [NatomConst, sum_range_succ, h1, h2]

/-- `q = 3`：`γ^{(0)} = 13/2`（notes/13 注 5.2 中 `N(k,3)` 的常数）。 -/
theorem NatomConst_three : NatomConst 3 = 13 / 2 := by
  have h1 : Nat.choose 3 1 = 3 := by decide
  have h2 : Nat.choose 3 2 = 3 := by decide
  have h3 : Nat.choose 3 3 = 1 := by decide
  have h4 : Nat.factorial 2 = 2 := by decide
  norm_num [NatomConst, sum_range_succ, h1, h2, h3, h4]

end

end A207123
