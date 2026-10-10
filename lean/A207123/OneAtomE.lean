import A207123.OneAtom
import A207123.EndAscent

/-!
# 以上升结尾的序列：每个 `i` 一个原子的单和也不存在（猜想总表 A25 (a) 的 `E` 部分；notes/12 定理 2(a)）

`E_k(m)`（`EA`）：`H_k(m)` 中以上升结尾的序列个数；`E = U − NA`（`NA` 是不以上升结尾的个数，
`P_m·Σ_k NA(k,m)xᵏ = 1`：`P_mul_NAser`）。notes/12 定理 2(a) 的第二句：设 `m ≥ 2`，不存在复数 `γ(i)`、整数 `δ(i)`
（`0 ≤ i ≤ m`）使 `E_k(m) = Σ_{i=0}^{m} γ(i)·c_i(k+δ(i))` 对充分大的 `k` 成立（`EA_no_one_atom`）。

* 三原子表示（`EA_atoms_exists`）：`m!·E_k(m) = Σ_i (−1)^{m−i} C(m,i)·Φ_{W̃_i − 1}(k+3m)`（`EA_F4_phi`：`U_F4_phi` 减去
  `1/P_m` 的部分分式 `NA_F4`），再由 `phi_atoms` 化成三个相邻原子；`i = 0` 一项为零（`W̃_0 = 1`）。
* 唯一性（`atoms_lin_indep`）给出 `i = 2` 处 `γ(2)·x^{3m−δ(2)} ≡ (−1)^{m−2}C(m,2)/m!·(W̃_2 − 1) (mod b_2)`。
* 范数 `N(f) = det f(M_2)`，`M_2` 是 `K_2 = ℚ[x]/(b_2)` 中乘以 `x` 的矩阵（`M2`）：`N(x) = 1/2`、`N(x^{−1}) = N(1 + 2x²) = 2`、
  `N(W̃_2 − 1) = det(2M_2⁵ + 4M_2⁸) = 17/8`。于是 `γ(2)³·2^{±a} = κ³·17/8`，比较 17 进赋值得 `3v = 1`，矛盾。
复数系数用 ℚ-线性泛函化成有理系数（`one_atom_rat_of_complex`，与 `U_no_one_atom` 相同）。
-/

namespace A207123

open Polynomial Finset Filter

/-! ## `E_k(m)` 与它的三原子表示 -/

/-- `H_k(m)` 中以上升结尾的序列个数（notes/12 的 `E_k(m)`）。 -/
def EA (k m : ℕ) : ℕ := ((L k m).filter fun l => endsAsc l = true).card

theorem EA_add_NA (k m : ℕ) : EA k m + NA k m = U k m := by
  have h := Finset.card_filter_add_card_filter_not (s := L k m) (fun l => endsAsc l = true)
  simpa [EA, NA, U] using h

theorem coe_Ppoly_inv_eq_NAser (m : ℕ) : (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ = NAser m := by
  rw [← mul_one ((↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹), ← P_mul_NAser m, ← mul_assoc,
    PowerSeries.inv_mul_cancel _ (constantCoeff_Ppoly_ne m), one_mul]

/-- `1/P_m` 的部分分式：`m!·NA_k(m) = Σ_{i=0}^{m} (−1)^{m−i} C(m,i)·c_i(k+3m)`。 -/
theorem NA_F4 (k m : ℕ) : (m.factorial : ℚ) * (NA k m : ℚ) =
    ∑ i ∈ range (m + 1), (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * ci i (k + 3 * m) := by
  have hser := alt_sum_bser_inv m 0
  simp only [zero_add] at hser
  have hP : ∏ j ∈ range (m + 1), (bser j)⁻¹ = NAser m := by
    rw [← coe_Ppoly_inv_eq_NAser, Ppoly_inv_eq_prod, Nat.range_succ_eq_Icc_zero]
  rw [hP, mul_assoc] at hser
  have h2 := congrArg (PowerSeries.coeff (k + 3 * m)) hser
  rw [map_sum, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X_pow_mul, coeff_NAser] at h2
  rw [← h2]
  refine sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_intCast_mul]
  push_cast
  rfl

theorem phi_sub_one (i : ℕ) (θ : ℚ[X]) (n : ℕ) : phi i (θ - 1) n = phi i θ n - ci i n := by
  rw [phi, phi, Polynomial.coe_sub, Polynomial.coe_one, sub_mul, one_mul, map_sub]
  rfl

/-- `m!·E_k(m) = Σ_{i=0}^{m} (−1)^{m−i} C(m,i)·Φ_{W̃_i − 1}(k+3m)`（一切 `k`）。 -/
theorem EA_F4_phi (k m : ℕ) : (m.factorial : ℚ) * (EA k m : ℚ) =
    ∑ i ∈ range (m + 1), (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * phi i (Wtil i - 1) (k + 3 * m) := by
  have hE : (EA k m : ℚ) = (U k m : ℚ) - (NA k m : ℚ) := by
    rw [← EA_add_NA k m]
    push_cast
    ring
  rw [hE, mul_sub, U_F4_phi, NA_F4, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [phi_sub_one]
  ring

/-- `E_k(m)` 的三原子表示（平移 `3m`）：`k` 充分大时
`E_k(m) = Σ_{i=1}^{m} Σ_{r<3} (−1)^{m−i}C(m,i)/m!·[x^r]((W̃_i − 1) mod b_i)·c_i(k+3m−r)`。 -/
theorem EA_atoms_exists (m : ℕ) : ∀ᶠ k in atTop, (EA k m : ℚ) =
    ∑ i ∈ Icc 1 m, ∑ r ∈ range 3, (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) / (m.factorial : ℚ) *
      ((xpowRep i 0 * (Wtil i - 1)) % bpoly ℚ i).coeff r * ciZ i ((k : ℤ) + 3 * m + 0 - r) := by
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Icc 1 m, phi i (Wtil i - 1) (k + 3 * m) =
      ∑ r ∈ range 3, ((xpowRep i 0 * (Wtil i - 1)) % bpoly ℚ i).coeff r *
        ciZ i ((k : ℤ) + 3 * m + 0 - r) := by
    rw [eventually_all_finset]
    intro i hi
    obtain ⟨N, hN⟩ := phi_atoms (mem_Icc.1 hi).1 (Wtil i - 1) 0
    refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
    rw [hN (k + 3 * m) (by omega)]
    refine sum_congr rfl fun r _ => ?_
    congr 2
  filter_upwards [hall] with k hk
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h := EA_F4_phi k m
  rw [sum_range_succ_eq_add_Icc] at h
  have h0 : phi 0 (Wtil 0 - 1) (k + 3 * m) = 0 := by
    rw [Wtil_zero, sub_self, phi, Polynomial.coe_zero, zero_mul, map_zero]
  rw [h0, mul_zero, zero_add] at h
  rw [← inv_mul_cancel_left₀ hm (EA k m : ℚ), h, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [hk i hi, mul_sum, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  ring

/-! ## `K_2` 中的范数：乘以 `x` 的矩阵的行列式 -/

/-- `K_2 = ℚ[x]/(b_2)` 中乘以 `x` 的矩阵（基 `1, x, x²`，`x³ = (1 − x)/2`）。 -/
def M2 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 1 / 2; 1, 0, -1 / 2; 0, 1, 0]

theorem M2_sq : M2 ^ 2 = !![0, 1 / 2, 0; 0, -1 / 2, 1 / 2; 1, 0, -1 / 2] := by
  rw [sq, M2, Matrix.mul_fin_three]
  norm_num

theorem M2_pow_three : M2 ^ 3 = !![1 / 2, 0, -1 / 4; -1 / 2, 1 / 2, 1 / 4; 0, -1 / 2, 1 / 2] := by
  rw [pow_succ, M2_sq, M2, Matrix.mul_fin_three]
  norm_num

theorem M2_pow_four : M2 ^ 4 = !![0, -1 / 4, 1 / 4; 1 / 2, 1 / 4, -1 / 2; -1 / 2, 1 / 2, 1 / 4] := by
  rw [pow_succ, M2_pow_three, M2, Matrix.mul_fin_three]
  norm_num

theorem M2_pow_five : M2 ^ 5 = !![-1 / 4, 1 / 4, 1 / 8; 1 / 4, -1 / 2, 1 / 8; 1 / 2, 1 / 4, -1 / 2] := by
  rw [pow_succ, M2_pow_four, M2, Matrix.mul_fin_three]
  norm_num

theorem M2_pow_six : M2 ^ 6 = !![1 / 4, 1 / 8, -1 / 4; -1 / 2, 1 / 8, 3 / 8; 1 / 4, -1 / 2, 1 / 8] := by
  rw [pow_succ, M2_pow_five, M2, Matrix.mul_fin_three]
  norm_num

theorem M2_pow_seven :
    M2 ^ 7 = !![1 / 8, -1 / 4, 1 / 16; 1 / 8, 3 / 8, -5 / 16; -1 / 2, 1 / 8, 3 / 8] := by
  rw [pow_succ, M2_pow_six, M2, Matrix.mul_fin_three]
  norm_num

theorem M2_pow_eight :
    M2 ^ 8 = !![-1 / 4, 1 / 16, 3 / 16; 3 / 8, -5 / 16, -1 / 8; 1 / 8, 3 / 8, -5 / 16] := by
  rw [pow_succ, M2_pow_seven, M2, Matrix.mul_fin_three]
  norm_num

theorem aeval_C_mul_eq_smul (M : Matrix (Fin 3) (Fin 3) ℚ) (c : ℚ) (f : ℚ[X]) :
    aeval M (C c * f) = c • aeval M f := by
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem det_aeval_C_mul (M : Matrix (Fin 3) (Fin 3) ℚ) (c : ℚ) (f : ℚ[X]) :
    (aeval M (C c * f)).det = c ^ 3 * (aeval M f).det := by
  rw [aeval_C_mul_eq_smul, Matrix.det_smul, Fintype.card_fin]

/-- `1 − M_2 − 2M_2³ = 0`，即 `b_2(M_2) = 0`。 -/
theorem aeval_M2_bpoly : aeval M2 (bpoly ℚ 2) = 0 := by
  rw [bpoly, map_sub, map_sub, map_one, aeval_X, aeval_C_mul_eq_smul, map_pow, aeval_X, M2_pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [M2, Matrix.one_apply]

/-- `f(M_2)` 只依赖 `f mod b_2`。 -/
theorem aeval_M2_mod (f : ℚ[X]) : aeval M2 (f % bpoly ℚ 2) = aeval M2 f := by
  conv_rhs => rw [← EuclideanDomain.div_add_mod f (bpoly ℚ 2)]
  rw [map_add, map_mul, aeval_M2_bpoly, zero_mul, zero_add]

theorem det_M2 : M2.det = 1 / 2 := by
  rw [M2, Matrix.det_fin_three]
  norm_num

theorem det_one_add_two_smul_M2_sq : (1 + (2 : ℚ) • M2 ^ 2).det = 2 := by
  rw [M2_sq, Matrix.det_fin_three]
  norm_num [Matrix.one_apply]

theorem aeval_M2_Wtil_two_sub_one : aeval M2 (Wtil 2 - 1) = (2 : ℚ) • M2 ^ 5 + (4 : ℚ) • M2 ^ 8 := by
  rw [Wtil, show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, sum_pair (by norm_num), add_sub_cancel_left]
  simp only [map_add, aeval_C_mul_eq_smul, map_pow, aeval_X]
  norm_num [Nat.descFactorial_self, Nat.descFactorial_one]

/-- `N(W̃_2 − 1) = 17/8`。 -/
theorem det_aeval_M2_Wtil_two_sub_one : (aeval M2 (Wtil 2 - 1)).det = 17 / 8 := by
  rw [aeval_M2_Wtil_two_sub_one, M2_pow_five, M2_pow_eight, Matrix.det_fin_three]
  norm_num

theorem xpowRep_zero (i : ℕ) : xpowRep i 0 = 1 := by
  simp [xpowRep]

theorem det_aeval_M2_A : (aeval M2 ((xpowRep 2 0 * (Wtil 2 - 1)) % bpoly ℚ 2)).det = 17 / 8 := by
  rw [aeval_M2_mod, xpowRep_zero, one_mul, det_aeval_M2_Wtil_two_sub_one]

/-- `N(x^σ)` 是 `2` 的整数次幂（`N(x) = 1/2`，`N(x^{−1}) = 2`）。 -/
theorem det_aeval_M2_xpowRep (s : ℤ) : ∃ a : ℕ, (aeval M2 (xpowRep 2 s)).det = 2 ^ a ∨
    (aeval M2 (xpowRep 2 s)).det = ((2 : ℚ) ^ a)⁻¹ := by
  unfold xpowRep
  split_ifs
  · refine ⟨s.toNat, Or.inr ?_⟩
    rw [map_pow, aeval_X, Matrix.det_pow, det_M2, one_div, inv_pow]
  · refine ⟨(-s).toNat, Or.inl ?_⟩
    rw [map_pow, map_add, map_one, aeval_C_mul_eq_smul, map_pow, aeval_X, Nat.cast_ofNat,
      Matrix.det_pow, det_one_add_two_smul_M2_sq]

theorem padicValRat_seventeen_two_pow (a : ℕ) : padicValRat 17 ((2 : ℚ) ^ a) = 0 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have h2 : padicValRat 17 (2 : ℚ) = 0 := by
    have h := padicValRat.of_nat (p := 17) (n := 2)
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num)] at h
    exact_mod_cast h
  rw [padicValRat.pow, h2, mul_zero]

/-- `17` 进赋值：`w` 的 17 进赋值为 0 时 `a³·w ≠ 17·b³`（`b ≠ 0`）。 -/
theorem cube_mul_ne_seventeen_mul_cube {a b w : ℚ} (hb : b ≠ 0) (hw : w ≠ 0)
    (hv : padicValRat 17 w = 0) : a ^ 3 * w ≠ 17 * b ^ 3 := by
  intro h
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  by_cases ha : a = 0
  · have h17 : (17 : ℚ) * b ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hb)
    rw [← h, ha] at h17
    simp at h17
  · have h3 := congrArg (padicValRat 17) h
    rw [padicValRat.mul (pow_ne_zero 3 ha) hw, padicValRat.mul (by norm_num) (pow_ne_zero 3 hb),
      padicValRat.pow, padicValRat.pow, hv] at h3
    have h17 : padicValRat 17 (17 : ℚ) = 1 := by
      have := padicValRat.self (p := 17) (by norm_num)
      exact_mod_cast this
    rw [h17] at h3
    push_cast at h3
    omega

/-! ## 主定理 -/

/-- 有理系数的情形：`m ≥ 2` 时不存在有理数 `γ₀`、`γ(i)` 与整数 `δ(i)` 使
`E_k(m) = γ₀ + Σ_{i=1}^{m} γ(i)·c_i(k+δ(i))` 对充分大的 `k` 成立。 -/
theorem EA_no_one_atom_rat {m : ℕ} (hm : 2 ≤ m) (γ0 : ℚ) (γ : ℕ → ℚ) (δ : ℕ → ℤ) :
    ¬ ∀ᶠ k in atTop, (EA k m : ℚ) = γ0 + ∑ i ∈ Icc 1 m, γ i * ciZ i ((k : ℤ) + δ i) := by
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
  have hzero : ∀ᶠ k in atTop, γ0 + ∑ i ∈ Icc 1 m, atomComb i (3 * (m : ℤ) + 0)
      (fun r => γ i * ((xpowRep i (3 * (m : ℤ) + 0 - δ i) * 1) % bpoly ℚ i).coeff r -
        (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) / (m.factorial : ℚ) *
          ((xpowRep i 0 * (Wtil i - 1)) % bpoly ℚ i).coeff r) k = 0 := by
    filter_upwards [h, hall, EA_atoms_exists m] with k hk hk' hE
    have e : ∀ i ∈ Icc 1 m, atomComb i (3 * (m : ℤ) + 0)
        (fun r => γ i * ((xpowRep i (3 * (m : ℤ) + 0 - δ i) * 1) % bpoly ℚ i).coeff r -
          (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) / (m.factorial : ℚ) *
            ((xpowRep i 0 * (Wtil i - 1)) % bpoly ℚ i).coeff r) k =
        γ i * ciZ i ((k : ℤ) + δ i) - ∑ r ∈ range 3, (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) /
          (m.factorial : ℚ) * ((xpowRep i 0 * (Wtil i - 1)) % bpoly ℚ i).coeff r *
            ciZ i ((k : ℤ) + 3 * m + 0 - r) := by
      intro i hi
      rw [atomComb, hk' i hi, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun r _ => ?_
      rw [show (k : ℤ) + (3 * (m : ℤ) + 0) - r = (k : ℤ) + 3 * m + 0 - r by ring]
      ring
    rw [sum_congr rfl e, sum_sub_distrib]
    linarith
  have hd := atoms_lin_indep m (3 * (m : ℤ) + 0) γ0
    (fun i r => γ i * ((xpowRep i (3 * (m : ℤ) + 0 - δ i) * 1) % bpoly ℚ i).coeff r -
      (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) / (m.factorial : ℚ) *
        ((xpowRep i 0 * (Wtil i - 1)) % bpoly ℚ i).coeff r) hzero
  have h2 : (2 : ℕ) ∈ Icc 1 m := mem_Icc.2 ⟨by norm_num, hm⟩
  have hc : (m.choose 2 : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hκ0 : (-1 : ℚ) ^ (m - 2) * (m.choose 2 : ℚ) / (m.factorial : ℚ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc) hf
  have hpoly : C (γ 2) * ((xpowRep 2 (3 * (m : ℤ) + 0 - δ 2) * 1) % bpoly ℚ 2) =
      C ((-1 : ℚ) ^ (m - 2) * (m.choose 2 : ℚ) / (m.factorial : ℚ)) *
        ((xpowRep 2 0 * (Wtil 2 - 1)) % bpoly ℚ 2) := by
    ext r
    rw [coeff_C_mul, coeff_C_mul]
    rcases Nat.lt_or_ge r 3 with hr | hr
    · exact sub_eq_zero.1 (hd.2 2 h2 r hr)
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (mod_bpoly_natDegree_le (by norm_num) _) (by omega)),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (mod_bpoly_natDegree_le (by norm_num) _) (by omega)),
        mul_zero, mul_zero]
  have hdet := congrArg (fun f => (aeval M2 f).det) hpoly
  simp only [det_aeval_C_mul, det_aeval_M2_A] at hdet
  rw [aeval_M2_mod, mul_one] at hdet
  obtain ⟨a, ha⟩ := det_aeval_M2_xpowRep (3 * (m : ℤ) + 0 - δ 2)
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hD : (aeval M2 (xpowRep 2 (3 * (m : ℤ) + 0 - δ 2))).det ≠ 0 ∧
      padicValRat 17 (aeval M2 (xpowRep 2 (3 * (m : ℤ) + 0 - δ 2))).det = 0 := by
    rcases ha with ha | ha <;> rw [ha]
    · exact ⟨pow_ne_zero _ (by norm_num), padicValRat_seventeen_two_pow a⟩
    · exact ⟨inv_ne_zero (pow_ne_zero _ (by norm_num)),
        by rw [padicValRat.inv, padicValRat_seventeen_two_pow a, neg_zero]⟩
  apply cube_mul_ne_seventeen_mul_cube (a := γ 2)
    (w := 8 * (aeval M2 (xpowRep 2 (3 * (m : ℤ) + 0 - δ 2))).det) hκ0
    (mul_ne_zero (by norm_num) hD.1)
    (by rw [padicValRat.mul (by norm_num) hD.1, hD.2, add_zero, show (8 : ℚ) = 2 ^ 3 by norm_num,
      padicValRat_seventeen_two_pow])
  linear_combination 8 * hdet

/-- 复数系数的单原子表示给出有理系数的（取 ℚ-线性泛函 `ψ : ℂ → ℚ`，`ψ(1) = 1`）。 -/
theorem one_atom_rat_of_complex (f : ℕ → ℕ) (m : ℕ) (γ : ℕ → ℂ) (δ : ℕ → ℤ)
    (h : ∀ᶠ k in atTop, (f k : ℂ) = ∑ i ∈ range (m + 1), γ i * (ciZ i ((k : ℤ) + δ i) : ℂ)) :
    ∃ (γ0 : ℚ) (γ' : ℕ → ℚ), ∀ᶠ k in atTop,
      (f k : ℚ) = γ0 + ∑ i ∈ Icc 1 m, γ' i * ciZ i ((k : ℤ) + δ i) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ (one_ne_zero : (1 : ℂ) ≠ 0)
  let ψ : Module.Dual ℚ ℂ := (φ 1)⁻¹ • φ
  have hψ1 : ψ 1 = 1 := by
    simp only [ψ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hφ
  have hψq : ∀ (q : ℚ) (z : ℂ), ψ ((q : ℂ) * z) = q * ψ z := by
    intro q z
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : ℕ, -(δ 0) ≤ (B : ℤ) := ⟨(-(δ 0)).toNat, Int.self_le_toNat _⟩
  refine ⟨ψ (γ 0), fun i => ψ (γ i), ?_⟩
  filter_upwards [h, eventually_ge_atTop B] with k hk hk0
  have e := congrArg ψ hk
  have hf : ψ (f k : ℂ) = (f k : ℚ) := by
    rw [show (f k : ℂ) = ((f k : ℚ) : ℂ) * 1 by rw [mul_one, Rat.cast_natCast], hψq, hψ1, mul_one]
  rw [hf, map_sum] at e
  rw [e, sum_range_succ_eq_add_Icc]
  have h0 : ciZ 0 ((k : ℤ) + δ 0) = 1 := by
    rw [ciZ, ite_eq_left (by omega), ci_zero]
  congr 1
  · rw [mul_comm (γ 0), hψq, h0, one_mul]
  · refine sum_congr rfl fun i _ => ?_
    rw [mul_comm (γ i), hψq, mul_comm]

/-- **猜想总表 A25 (a) 的 `E` 部分（notes/12 定理 2(a)）**：设 `m ≥ 2`。不存在复数 `γ(i)`、整数 `δ(i)`（`0 ≤ i ≤ m`）
使以上升结尾的序列数 `E_k(m) = Σ_{i=0}^{m} γ(i)·c_i(k+δ(i))` 对一切充分大的 `k` 成立。 -/
theorem EA_no_one_atom {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ (γ : ℕ → ℂ) (δ : ℕ → ℤ), ∀ᶠ k in atTop,
      (EA k m : ℂ) = ∑ i ∈ range (m + 1), γ i * (ciZ i ((k : ℤ) + δ i) : ℂ) := by
  rintro ⟨γ, δ, h⟩
  obtain ⟨γ0, γ', h'⟩ := one_atom_rat_of_complex (fun k => EA k m) m γ δ h
  exact EA_no_one_atom_rat hm γ0 γ' δ h'

end A207123
