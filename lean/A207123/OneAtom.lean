import A207123.ThreeAtoms

/-!
# 每个 `i` 一个原子的单和不存在（猜想总表 A25 (a) 的 `U` 部分；notes/12 定理 2(a)）

原子 `c_i(n) = [xⁿ] 1/b_i`（`n < 0` 时取 0：`ciZ`）。notes/12 定理 2(a)：设 `m ≥ 1`，不存在复数 `γ(i)`、整数 `δ(i)`
（`0 ≤ i ≤ m`）使 `U_k(m) = Σ_{i=0}^{m} γ(i)·c_i(k+δ(i))` 对充分大的 `k` 成立（`U_no_one_atom`）。

证明（与 notes/12 相同的范数障碍，「比较留数」换成第四十六项的唯一性）：
* 先化为有理系数（`U_no_one_atom_rat`）：取 ℚ-线性泛函 `ψ : ℂ → ℚ`，`ψ(1) = 1`，作用在等式两边（`U` 与 `c_i` 都是有理数）。
* 单个原子换成三个相邻原子：`c_i(k+δ) = Σ_{r<3} ρ_r·c_i(k+3m−r)`，`ρ` 是 `x^{3m−δ}` 在 `K_i = ℚ[x]/(b_i)` 中的约化代表
  （`ciZ_eq_atoms`，由一般的 `phi_atoms`）。由三原子表示的唯一性（`three_atoms_unique`，`σ = 0`），`i = 1` 处
  `γ(1)·x^{3m−δ(1)} ≡ (−1)^{m−1}/(m−1)!·W̃_1 (mod b_1)`。
* 范数：`N(f) := det f(M_1)`，`M_1` 是 `K_1` 中乘以 `x` 的矩阵（`M1`，`1 − M_1 − M_1³ = 0`）；`N` 只依赖 `f mod b_1`、
  可乘，`N(x) = det M_1 = 1`、`N(x^{−1}) = det(1 + M_1²) = 1`、`N(W̃_1) = det(1 + M_1⁵) = 3`。于是
  `γ(1)³ = 3·((−1)^{m−1}/(m−1)!)³`，`3` 是有理数的立方，与 `3` 的 3 进赋值为 1 矛盾（`rat_cube_ne_three`）。
「以上升结尾的 `E`、`m ≥ 2`」的情形（用 `b_2` 与 `N(W̃_2 − 1) = 17/8`）不在这里。
-/

namespace A207123

open Polynomial Finset Filter

/-! ## 一般的 `θ`：三个相邻原子 -/

theorem phi_one (i n : ℕ) : phi i 1 n = ci i n := by
  rw [phi, Polynomial.coe_one, one_mul]
  rfl

theorem mod_bpoly_natDegree_le {i : ℕ} (hi : 1 ≤ i) (θ : ℚ[X]) : (θ % bpoly ℚ i).natDegree ≤ 2 := by
  by_cases h0 : θ % bpoly ℚ i = 0
  · rw [h0, natDegree_zero]
    omega
  · have h := natDegree_lt_natDegree h0 (degree_mod_lt θ (bpoly_ne_zero i))
    rw [natDegree_bpoly hi] at h
    omega

/-- 对 `1 ≤ i`、任意 `θ` 与整数 `σ`：`n` 充分大时 `Φ_θ(n) = Σ_{r<3} ρ_r·c_i(n+σ−r)`，`ρ` 是 `x^σ·θ` 在 `K_i` 中的
约化代表（`phi_Wtil_atoms` 对一般 `θ` 的写法）。 -/
theorem phi_atoms {i : ℕ} (hi : 1 ≤ i) (θ : ℚ[X]) (σ : ℤ) :
    ∃ N, ∀ n ≥ N, phi i θ n =
      ∑ r ∈ range 3, ((xpowRep i σ * θ) % bpoly ℚ i).coeff r * ciZ i ((n : ℤ) + σ - r) := by
  have hdeg := mod_bpoly_natDegree_le hi (xpowRep i σ * θ)
  rcases le_or_gt 0 σ with hσ | hσ
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, σ = s := ⟨σ.toNat, (Int.toNat_of_nonneg hσ).symm⟩
    have hrep : xpowRep i s * θ = X ^ s * θ := by
      rw [xpowRep, ite_eq_left (by omega), Int.toNat_natCast]
    rw [hrep] at hdeg ⊢
    obtain ⟨N, hN⟩ := phi_eq_of_dvd i (bpoly_dvd_sub_mod i (X ^ s * θ))
    refine ⟨N + 2, fun n hn => ?_⟩
    rw [← phi_X_pow_mul i s θ n, hN (n + s) (by omega),
      show n + s = (n + s - 2) + 2 by omega, phi_of_natDegree_le_two i hdeg]
    refine sum_congr rfl fun r hr => ?_
    rw [mem_range] at hr
    rw [← ciZ_natCast]
    congr 2
    omega
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, σ = -(s : ℤ) := ⟨(-σ).toNat, by omega⟩
    subst hs
    have hrep : xpowRep i (-(s : ℤ)) * θ = (1 + C (i : ℚ) * X ^ 2) ^ s * θ := by
      rw [xpowRep, ite_eq_right (by omega), neg_neg, Int.toNat_natCast]
    rw [hrep] at hdeg ⊢
    obtain ⟨N1, hN1⟩ := phi_eq_of_dvd i (bpoly_dvd_inv_shift i s θ)
    obtain ⟨N2, hN2⟩ := phi_eq_of_dvd i (bpoly_dvd_sub_mod i ((1 + C (i : ℚ) * X ^ 2) ^ s * θ))
    refine ⟨N1 + N2 + s + 2, fun n hn => ?_⟩
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 + s := ⟨n - s - 2, by omega⟩
    rw [← hN1 (t + 2 + s) (by omega), phi_X_pow_mul, hN2 (t + 2) (by omega),
      phi_of_natDegree_le_two i hdeg]
    refine sum_congr rfl fun r hr => ?_
    rw [mem_range] at hr
    rw [← ciZ_natCast]
    congr 2
    omega

/-- 单个原子换成三个相邻原子：`k` 充分大时 `c_i(k+δ) = Σ_{r<3} ρ_r·c_i(k+a−r)`，`ρ` 是 `x^{a−δ}` 在 `K_i` 中的约化代表。 -/
theorem ciZ_eq_atoms {i : ℕ} (hi : 1 ≤ i) (a δ : ℤ) :
    ∀ᶠ k : ℕ in atTop, ciZ i ((k : ℤ) + δ) =
      ∑ r ∈ range 3, ((xpowRep i (a - δ) * 1) % bpoly ℚ i).coeff r * ciZ i ((k : ℤ) + a - r) := by
  obtain ⟨N, hN⟩ := phi_atoms hi 1 (a - δ)
  obtain ⟨B, hB⟩ : ∃ B : ℕ, -δ ≤ (B : ℤ) := ⟨(-δ).toNat, Int.self_le_toNat _⟩
  filter_upwards [eventually_ge_atTop (N + B)] with k hk
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = (k : ℤ) + δ :=
    ⟨((k : ℤ) + δ).toNat, Int.toNat_of_nonneg (by omega)⟩
  rw [← hn, ciZ_natCast, ← phi_one, hN n (by omega)]
  refine sum_congr rfl fun r _ => ?_
  congr 2
  omega

/-! ## `K_1` 中的范数：乘以 `x` 的矩阵的行列式 -/

/-- `K_1 = ℚ[x]/(b_1)` 中乘以 `x` 的矩阵（基 `1, x, x²`，`x³ = 1 − x`）。 -/
def M1 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 1; 1, 0, -1; 0, 1, 0]

theorem M1_sq : M1 ^ 2 = !![0, 1, 0; 0, -1, 1; 1, 0, -1] := by
  rw [sq, M1, Matrix.mul_fin_three]
  norm_num

theorem M1_pow_three : M1 ^ 3 = !![1, 0, -1; -1, 1, 1; 0, -1, 1] := by
  rw [pow_succ, M1_sq, M1, Matrix.mul_fin_three]
  norm_num

theorem M1_pow_four : M1 ^ 4 = !![0, -1, 1; 1, 1, -2; -1, 1, 1] := by
  rw [pow_succ, M1_pow_three, M1, Matrix.mul_fin_three]
  norm_num

theorem M1_pow_five : M1 ^ 5 = !![-1, 1, 1; 1, -2, 0; 1, 1, -2] := by
  rw [pow_succ, M1_pow_four, M1, Matrix.mul_fin_three]
  norm_num

theorem det_M1 : M1.det = 1 := by
  rw [M1, Matrix.det_fin_three]
  norm_num

theorem det_one_add_M1_sq : (1 + M1 ^ 2).det = 1 := by
  rw [M1_sq, Matrix.det_fin_three]
  norm_num [Matrix.one_apply]

theorem det_one_add_M1_pow_five : (1 + M1 ^ 5).det = 3 := by
  rw [M1_pow_five, Matrix.det_fin_three]
  norm_num [Matrix.one_apply]

/-- `1 − M_1 − M_1³ = 0`，即 `b_1(M_1) = 0`。 -/
theorem aeval_M1_bpoly : aeval M1 (bpoly ℚ 1) = 0 := by
  rw [bpoly]
  simp only [map_sub, map_one, aeval_X, map_pow, Nat.cast_one, one_mul]
  rw [M1_pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [M1, Matrix.one_apply]

/-- `f(M_1)` 只依赖 `f mod b_1`。 -/
theorem aeval_M1_mod (f : ℚ[X]) : aeval M1 (f % bpoly ℚ 1) = aeval M1 f := by
  conv_rhs => rw [← EuclideanDomain.div_add_mod f (bpoly ℚ 1)]
  rw [map_add, map_mul, aeval_M1_bpoly, zero_mul, zero_add]

theorem det_aeval_M1_C_mul (c : ℚ) (f : ℚ[X]) : (aeval M1 (C c * f)).det = c ^ 3 * (aeval M1 f).det := by
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul,
    Fintype.card_fin]

/-- `N(x^σ) = 1`（`N(x) = 1`，`N(x^{−1}) = N(1 + x²) = 1`）。 -/
theorem det_aeval_M1_xpowRep (s : ℤ) : (aeval M1 (xpowRep 1 s)).det = 1 := by
  unfold xpowRep
  split_ifs
  · rw [map_pow, aeval_X, Matrix.det_pow, det_M1, one_pow]
  · have e : aeval M1 (1 + C ((1 : ℕ) : ℚ) * X ^ 2) = 1 + M1 ^ 2 := by simp
    rw [map_pow, e, Matrix.det_pow, det_one_add_M1_sq, one_pow]

theorem Wtil_one_eq : Wtil 1 = 1 + X ^ 5 := by
  rw [Wtil, Icc_self, sum_singleton]
  simp

/-- `N(W̃_1) = 3`，所以 `x^0·W̃_1` 的约化代表 `atomRep 1 0` 的范数也是 3。 -/
theorem det_aeval_M1_atomRep : (aeval M1 (atomRep 1 0)).det = 3 := by
  rw [atomRep, aeval_M1_mod, map_mul, Matrix.det_mul, det_aeval_M1_xpowRep, Wtil_one_eq]
  simp only [map_add, map_one, map_pow, aeval_X]
  rw [det_one_add_M1_pow_five, one_mul]

/-- 3 不是有理数的立方（3 进赋值）。 -/
theorem rat_cube_ne_three (q : ℚ) : q ^ 3 ≠ 3 := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := congrArg (padicValRat 3) h
  rw [padicValRat.pow] at h3
  have h1 : padicValRat 3 (3 : ℚ) = 1 := by
    have := padicValRat.self (p := 3) (by norm_num)
    exact_mod_cast this
  rw [h1] at h3
  push_cast at h3
  omega


/-! ## 主定理 -/

/-- 有理系数的情形：`m ≥ 1` 时不存在有理数 `γ₀`、`γ(i)` 与整数 `δ(i)` 使
`U_k(m) = γ₀ + Σ_{i=1}^{m} γ(i)·c_i(k+δ(i))` 对充分大的 `k` 成立。 -/
theorem U_no_one_atom_rat {m : ℕ} (hm : 1 ≤ m) (γ0 : ℚ) (γ : ℕ → ℚ) (δ : ℕ → ℤ) :
    ¬ ∀ᶠ k in atTop, (U k m : ℚ) = γ0 + ∑ i ∈ Icc 1 m, γ i * ciZ i ((k : ℤ) + δ i) := by
  intro h
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Icc 1 m, ciZ i ((k : ℤ) + δ i) =
      ∑ r ∈ range 3, ((xpowRep i (3 * (m : ℤ) + 0 - δ i) * 1) % bpoly ℚ i).coeff r *
        ciZ i ((k : ℤ) + 3 * m + 0 - r) := by
    rw [eventually_all_finset]
    intro i hi
    filter_upwards [ciZ_eq_atoms (mem_Icc.1 hi).1 (3 * (m : ℤ) + 0) (δ i)] with k hk
    rw [hk]
    refine sum_congr rfl fun r _ => ?_
    rw [show (k : ℤ) + (3 * (m : ℤ) + 0) - r = (k : ℤ) + 3 * m + 0 - r by ring]
  have hrep : ∀ᶠ k in atTop, (U k m : ℚ) = γ0 + ∑ i ∈ Icc 1 m, ∑ r ∈ range 3,
      γ i * ((xpowRep i (3 * (m : ℤ) + 0 - δ i) * 1) % bpoly ℚ i).coeff r *
        ciZ i ((k : ℤ) + 3 * m + 0 - r) := by
    filter_upwards [h, hall] with k hk hk'
    rw [hk]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [hk' i hi, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    ring
  have h3 := three_atoms_unique m 0 γ0
    (fun i r => γ i * ((xpowRep i (3 * (m : ℤ) + 0 - δ i) * 1) % bpoly ℚ i).coeff r) hrep
  have h1 : (1 : ℕ) ∈ Icc 1 m := mem_Icc.2 ⟨le_rfl, hm⟩
  have hκ0 : (-1 : ℚ) ^ (m - 1) / ((Nat.factorial 1 : ℚ) * ((m - 1).factorial : ℚ)) ≠ 0 := by
    positivity
  have hpoly : C (γ 1) * ((xpowRep 1 (3 * (m : ℤ) + 0 - δ 1) * 1) % bpoly ℚ 1) =
      C ((-1 : ℚ) ^ (m - 1) / ((Nat.factorial 1 : ℚ) * ((m - 1).factorial : ℚ))) * atomRep 1 0 := by
    ext r
    rw [coeff_C_mul, coeff_C_mul]
    rcases Nat.lt_or_ge r 3 with hr | hr
    · exact (h3.2 1 h1 r hr).trans (by rw [atomCoeff])
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (mod_bpoly_natDegree_le le_rfl _) (by omega)),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (atomRep_natDegree_le le_rfl 0) (by omega)),
        mul_zero, mul_zero]
  have hdet := congrArg (fun f => (aeval M1 f).det) hpoly
  simp only [det_aeval_M1_C_mul, det_aeval_M1_atomRep] at hdet
  rw [aeval_M1_mod, mul_one, det_aeval_M1_xpowRep, mul_one] at hdet
  apply rat_cube_ne_three (γ 1 / ((-1 : ℚ) ^ (m - 1) / ((Nat.factorial 1 : ℚ) * ((m - 1).factorial : ℚ))))
  rw [div_pow, hdet, mul_div_cancel_left₀ _ (pow_ne_zero 3 hκ0)]

/-- **猜想总表 A25 (a) 的 `U` 部分（notes/12 定理 2(a)）**：设 `m ≥ 1`。不存在复数 `γ(i)`、整数 `δ(i)`（`0 ≤ i ≤ m`）
使 `U_k(m) = Σ_{i=0}^{m} γ(i)·c_i(k+δ(i))` 对一切充分大的 `k` 成立。 -/
theorem U_no_one_atom {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ (γ : ℕ → ℂ) (δ : ℕ → ℤ), ∀ᶠ k in atTop,
      (U k m : ℂ) = ∑ i ∈ range (m + 1), γ i * (ciZ i ((k : ℤ) + δ i) : ℂ) := by
  rintro ⟨γ, δ, h⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ (one_ne_zero : (1 : ℂ) ≠ 0)
  let ψ : Module.Dual ℚ ℂ := (φ 1)⁻¹ • φ
  have hψ1 : ψ 1 = 1 := by
    simp only [ψ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hφ
  have hψq : ∀ (q : ℚ) (z : ℂ), ψ ((q : ℂ) * z) = q * ψ z := by
    intro q z
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : ℕ, -(δ 0) ≤ (B : ℤ) := ⟨(-(δ 0)).toNat, Int.self_le_toNat _⟩
  apply U_no_one_atom_rat hm (ψ (γ 0)) (fun i => ψ (γ i)) δ
  filter_upwards [h, eventually_ge_atTop B] with k hk hk0
  have e := congrArg ψ hk
  have hU : ψ (U k m : ℂ) = (U k m : ℚ) := by
    rw [show (U k m : ℂ) = ((U k m : ℚ) : ℂ) * 1 by rw [mul_one, Rat.cast_natCast], hψq, hψ1, mul_one]
  rw [hU, map_sum] at e
  rw [e, sum_range_succ_eq_add_Icc]
  have h0 : ciZ 0 ((k : ℤ) + δ 0) = 1 := by
    rw [ciZ, ite_eq_left (by omega), ci_zero]
  congr 1
  · rw [mul_comm (γ 0), hψq, h0, one_mul]
  · refine sum_congr rfl fun i _ => ?_
    rw [mul_comm (γ i), hψq, mul_comm]

end A207123
