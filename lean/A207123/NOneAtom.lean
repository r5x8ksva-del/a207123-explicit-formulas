import A207123.OneAtomE
import A207123.NThreeAtoms

/-!
# `N(k,q)` 没有「每个 i 一个原子」的单和（猜想总表 A26 (ii) 的一部分；notes/13 定理 5(a)）

notes/13 定理 5(a)：设 `q ≥ 2`，不存在复数 `γ(i)`、整数 `δ(i)`（`0 ≤ i ≤ q−1`）使 `N(k,q) = Σ_i γ(i)·c_i(k+δ(i))` 对充分大的
`k` 成立（`N_no_one_atom`）。

* 化成有理系数（`one_atom_rat_of_complex`），每个原子换成三个相邻原子（`ciZ_eq_atoms`），由第四十八项的唯一性
  `N_three_atoms_unique`（`σ = 0`）得 `i = 1` 处 `γ(1)·x^{3(q−1)−δ(1)} ≡ Σ_{M=1}^{q−1} c_M·x^{3(q−1−M)}·W̃_1 (mod b_1)`，
  `c_M = (−1)^{q−1−M}C(q,M+1)·(−1)^{M−1}/(M−1)!`（`nOneCoeff`）。
* 取范数 `N(f) = det f(M_1)`（`N(x) = 1`，`N(W̃_1) = 3`）：`γ(1)³ = 3·det S`，`S = Σ_M c_M·Y^{q−1−M}`，`Y = M_1³`。乘以
  `((q−2)!·(−1)^q)³` 后 `det` 变成整数矩阵 `T_q = Σ_M C(q,M+1)·(q−2)^{\underline{q−1−M}}·Y^{q−1−M}`（`TZ`）的行列式。
* 模 3：`Y^{q−1−M}` 的系数在 `q−1−M ≥ 2` 时被 3 整除（`three_dvd_nCoefZ`），所以 `T_q ≡ 1 + q(q−2)·Y (mod 3)`，
  `q(q−2) ≡ 0` 或 `2`，两种情形行列式模 3 都是 1（`det_TZ_zmod_ne_zero`）。于是 `(γ(1)·(q−2)!·(−1)^q)³ = 3·det T_q`，
  `3 ∤ det T_q`，与 3 进赋值矛盾（`cube_ne_three_mul_int`）。
这就是 notes/13 的「`T_{q−2}(z)` 模 3 是 `Z[ξ]` 的单位，`3·N(T_{q−2}(z))` 不是立方」（这里 `T_q = Y^{q−2}·T_{q−2}(Y^{−1})`）。
-/

namespace A207123

open Polynomial Finset Filter

/-! ## 整数矩阵 `T_q` 与它的行列式模 3 -/

/-- `Y = M_1³`（整数矩阵）。 -/
def YZ : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, -1; -1, 1, 1; 0, -1, 1]

/-- `Y` 模 3。 -/
def Ybar : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 0, 2; 2, 1, 1; 0, 2, 1]

/-- `C(q, M+1)·(q−2)!/(M−1)! = C(q, M+1)·(q−2)^{\underline{q−1−M}}`。 -/
def nCoefZ (q M : ℕ) : ℕ := q.choose (M + 1) * (q - 2).descFactorial (q - 1 - M)

/-- `T_q = Σ_{M=1}^{q−1} C(q,M+1)·(q−2)^{\underline{q−1−M}}·Y^{q−1−M}`（整数矩阵）。 -/
def TZ (q : ℕ) : Matrix (Fin 3) (Fin 3) ℤ := ∑ M ∈ Ico 1 q, (nCoefZ q M : ℤ) • YZ ^ (q - 1 - M)

theorem mapMatrix_TZ {S : Type*} [CommRing S] (f : ℤ →+* S) (q : ℕ) :
    f.mapMatrix (TZ q) = ∑ M ∈ Ico 1 q, (nCoefZ q M : S) • (f.mapMatrix YZ) ^ (q - 1 - M) := by
  rw [TZ, map_sum]
  refine sum_congr rfl fun M _ => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (fun a b => map_mul f a b),
    ← RingHom.mapMatrix_apply, map_pow, map_natCast]

theorem YZ_map_rat : (Int.castRingHom ℚ).mapMatrix YZ = M1 ^ 3 := by
  rw [M1_pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [YZ]

theorem YZ_map_zmod : (Int.castRingHom (ZMod 3)).mapMatrix YZ = Ybar := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- `q−1−M ≥ 2` 时 `3 ∣ C(q,M+1)·(q−2)^{\underline{q−1−M}}`。 -/
theorem three_dvd_nCoefZ {q M : ℕ} (hM : M + 3 ≤ q) : 3 ∣ nCoefZ q M := by
  rcases Nat.lt_or_ge (q - 1 - M) 3 with hj | hj
  · have hj2 : q - 1 - M = 2 := by omega
    rw [nCoefZ, hj2, Nat.descFactorial_eq_factorial_mul_choose, show M + 1 = q - 2 by omega,
      Nat.choose_symm (by omega : 2 ≤ q)]
    have h := Nat.choose_mul (n := q) (k := 4) (s := 2) (by norm_num)
    have h6 : Nat.choose 4 2 = 6 := by decide
    rw [h6, show (4 : ℕ) - 2 = 2 from rfl] at h
    refine ⟨4 * q.choose 4, ?_⟩
    calc q.choose 2 * (Nat.factorial 2 * (q - 2).choose 2)
        = 2 * (q.choose 2 * (q - 2).choose 2) := by rw [Nat.factorial_two]; ring
      _ = 2 * (q.choose 4 * 6) := by rw [h]
      _ = 3 * (4 * q.choose 4) := by ring
  · have h3 : 3 ∣ (q - 1 - M).factorial := Nat.dvd_factorial (by norm_num) hj
    exact Dvd.dvd.mul_left (h3.trans (Nat.factorial_dvd_descFactorial _ _)) _

theorem det_Ybar_aux (c : ZMod 3) (hc : c = 0 ∨ c = 2) : (c • Ybar + 1).det ≠ 0 := by
  rcases hc with rfl | rfl <;> rw [Matrix.det_fin_three] <;> decide

/-- `det T_q` 不被 3 整除。 -/
theorem det_TZ_zmod_ne_zero (q : ℕ) (hq : 2 ≤ q) : ((TZ q).det : ZMod 3) ≠ 0 := by
  have h := RingHom.map_det (Int.castRingHom (ZMod 3)) (TZ q)
  rw [eq_intCast] at h
  rw [h, mapMatrix_TZ, YZ_map_zmod]
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : nCoefZ (0 + 2) 1 = 1 := by decide
    rw [show Ico 1 (0 + 2) = ({1} : Finset ℕ) by decide, sum_singleton, h1]
    simp
  · have hrest : ∑ M ∈ Ico 1 n, (nCoefZ (n + 1 + 1) M : ZMod 3) • Ybar ^ (n + 1 + 1 - 1 - M) = 0 := by
      refine sum_eq_zero fun M hM => ?_
      rw [mem_Ico] at hM
      rw [(ZMod.natCast_eq_zero_iff _ 3).2 (three_dvd_nCoefZ (by omega)), zero_smul]
    have hn1 : nCoefZ (n + 1 + 1) n = (n + 2) * n := by
      rw [nCoefZ, show n + 1 + 1 - 1 - n = 1 by omega, show n + 1 + 1 - 2 = n by omega,
        Nat.descFactorial_one, show n + 1 + 1 = (n + 1) + 1 from rfl, Nat.choose_succ_self_right]
    have hn0 : nCoefZ (n + 1 + 1) (n + 1) = 1 := by
      rw [nCoefZ, Nat.choose_self, show n + 1 + 1 - 1 - (n + 1) = 0 by omega, Nat.descFactorial_zero]
    rw [show n + 2 = n + 1 + 1 from rfl, sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), hrest,
      zero_add, hn1, hn0, show n + 1 + 1 - 1 - n = 1 by omega, show n + 1 + 1 - 1 - (n + 1) = 0 by omega,
      pow_one, pow_zero, Nat.cast_one, one_smul]
    have hc : ∀ x : ZMod 3, (x + 2) * x = 0 ∨ (x + 2) * x = 2 := by decide
    have := hc (n : ZMod 3)
    push_cast
    exact det_Ybar_aux _ this

/-- 3 进赋值：`3 ∤ D` 时 `a³ ≠ 3·D`。 -/
theorem cube_ne_three_mul_int {a : ℚ} {D : ℤ} (hD : ¬ (3 : ℤ) ∣ D) : a ^ 3 ≠ 3 * (D : ℚ) := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD0 : (D : ℚ) ≠ 0 := by
    intro h0
    apply hD
    rw [show D = 0 by exact_mod_cast h0]
    exact dvd_zero 3
  have h3 := congrArg (padicValRat 3) h
  rw [padicValRat.pow, padicValRat.mul (by norm_num) hD0] at h3
  have h1 : padicValRat 3 (3 : ℚ) = 1 := by
    have := padicValRat.self (p := 3) (by norm_num)
    exact_mod_cast this
  have h0 : padicValRat 3 (D : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hD), Nat.cast_zero]
  rw [h1, h0] at h3
  push_cast at h3
  omega

/-! ## 主定理 -/

/-- 纤维 1 上的系数 `c_M = (−1)^{q−1−M}·C(q,M+1)·(−1)^{M−1}/(1!·(M−1)!)`（`NatomCoeff q 1` 的各项）。 -/
def nOneCoeff (q M : ℕ) : ℚ := (-1 : ℚ) ^ (q - 1 - M) * (q.choose (M + 1) : ℚ) *
  ((-1 : ℚ) ^ (M - 1) / ((Nat.factorial 1 : ℚ) * ((M - 1).factorial : ℚ)))

theorem nOneCoeff_mul {q M : ℕ} (hM1 : 1 ≤ M) (hMq : M < q) :
    ((q - 2).factorial : ℚ) * (-1) ^ q * nOneCoeff q M = (nCoefZ q M : ℚ) := by
  have hfact : ((M - 1).factorial : ℚ) * ((q - 2).descFactorial (q - 1 - M) : ℚ) =
      ((q - 2).factorial : ℚ) := by
    have := Nat.factorial_mul_descFactorial (show q - 1 - M ≤ q - 2 by omega)
    rw [show q - 2 - (q - 1 - M) = M - 1 by omega] at this
    exact_mod_cast this
  have hsign : (-1 : ℚ) ^ q * (-1) ^ (q - 1 - M) * (-1) ^ (M - 1) = 1 := by
    rw [← pow_add, ← pow_add, show q + (q - 1 - M) + (M - 1) = 2 * (q - 1) by omega, pow_mul]
    norm_num
  have hf : ((M - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (M - 1).factorial_ne_zero
  have hinv : ((M - 1).factorial : ℚ) * ((M - 1).factorial : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hf
  rw [nOneCoeff, nCoefZ, ← hfact, Nat.factorial_one, Nat.cast_one, one_mul, div_eq_mul_inv]
  push_cast
  linear_combination
    ((q - 2).descFactorial (q - 1 - M) : ℚ) * (q.choose (M + 1) : ℚ) *
        ((-1 : ℚ) ^ q * (-1) ^ (q - 1 - M) * (-1) ^ (M - 1)) * hinv +
      ((q - 2).descFactorial (q - 1 - M) : ℚ) * (q.choose (M + 1) : ℚ) * hsign

/-- 有理系数的情形。 -/
theorem N_no_one_atom_rat {q : ℕ} (hq : 2 ≤ q) (γ0 : ℚ) (γ : ℕ → ℚ) (δ : ℕ → ℤ) :
    ¬ ∀ᶠ k in atTop, (N k q : ℚ) = γ0 + ∑ i ∈ Icc 1 (q - 1), γ i * ciZ i ((k : ℤ) + δ i) := by
  intro h
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Icc 1 (q - 1), ciZ i ((k : ℤ) + δ i) =
      ∑ r ∈ range 3, ((xpowRep i (3 * ((q : ℤ) - 1) + 0 - δ i) * 1) % bpoly ℚ i).coeff r *
        ciZ i ((k : ℤ) + 3 * (q - 1) + 0 - r) := by
    rw [eventually_all_finset]
    intro i hi
    filter_upwards [ciZ_eq_atoms (mem_Icc.1 hi).1 (3 * ((q : ℤ) - 1) + 0) (δ i)] with k hk
    rw [hk]
    refine sum_congr rfl fun r _ => ?_
    rw [show (k : ℤ) + (3 * ((q : ℤ) - 1) + 0) - r = (k : ℤ) + 3 * (q - 1) + 0 - r by ring]
  have hrep : ∀ᶠ k in atTop, (N k q : ℚ) = γ0 + ∑ i ∈ Icc 1 (q - 1), ∑ r ∈ range 3,
      γ i * ((xpowRep i (3 * ((q : ℤ) - 1) + 0 - δ i) * 1) % bpoly ℚ i).coeff r *
        ciZ i ((k : ℤ) + 3 * (q - 1) + 0 - r) := by
    filter_upwards [h, hall] with k hk hk'
    rw [hk]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [hk' i hi, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    ring
  have h3 := N_three_atoms_unique q 0 γ0
    (fun i r => γ i * ((xpowRep i (3 * ((q : ℤ) - 1) + 0 - δ i) * 1) % bpoly ℚ i).coeff r) hrep
  have h1 : (1 : ℕ) ∈ Icc 1 (q - 1) := mem_Icc.2 ⟨le_rfl, by omega⟩
  have hpoly : C (γ 1) * ((xpowRep 1 (3 * ((q : ℤ) - 1) + 0 - δ 1) * 1) % bpoly ℚ 1) =
      ∑ M ∈ Ico 1 q, C (nOneCoeff q M) * atomRep 1 (0 + 3 * ((q : ℤ) - 1 - M)) := by
    ext r
    rw [coeff_C_mul, finsetSum_coeff]
    rcases Nat.lt_or_ge r 3 with hr | hr
    · rw [h3.2 1 h1 r hr, NatomCoeff]
      refine sum_congr rfl fun M _ => ?_
      rw [coeff_C_mul, atomCoeff, nOneCoeff]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (mod_bpoly_natDegree_le le_rfl _) (by omega)),
        mul_zero]
      symm
      refine sum_eq_zero fun M _ => ?_
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (atomRep_natDegree_le le_rfl _) (by omega)), mul_zero]
  have haeval : aeval M1 (∑ M ∈ Ico 1 q, C (nOneCoeff q M) * atomRep 1 (0 + 3 * ((q : ℤ) - 1 - M))) =
      (∑ M ∈ Ico 1 q, nOneCoeff q M • (M1 ^ 3) ^ (q - 1 - M)) * (1 + M1 ^ 5) := by
    rw [map_sum, sum_mul]
    refine sum_congr rfl fun M hM => ?_
    rw [mem_Ico] at hM
    have e : (0 : ℤ) + 3 * ((q : ℤ) - 1 - M) = ((3 * (q - 1 - M) : ℕ) : ℤ) := by omega
    rw [aeval_C_mul_eq_smul, atomRep, aeval_M1_mod, map_mul, e, xpowRep, ite_eq_left (by omega),
      Int.toNat_natCast, map_pow, aeval_X, Wtil_one_eq, pow_mul, smul_mul_assoc]
    simp
  have hdet := congrArg (fun f => (aeval M1 f).det) hpoly
  simp only [det_aeval_C_mul] at hdet
  rw [aeval_M1_mod, mul_one, det_aeval_M1_xpowRep, mul_one, haeval, Matrix.det_mul,
    det_one_add_M1_pow_five] at hdet
  have hSQ : (((q - 2).factorial : ℚ) * (-1) ^ q) • ∑ M ∈ Ico 1 q, nOneCoeff q M • (M1 ^ 3) ^ (q - 1 - M) =
      (Int.castRingHom ℚ).mapMatrix (TZ q) := by
    rw [mapMatrix_TZ, YZ_map_rat, smul_sum]
    refine sum_congr rfl fun M hM => ?_
    rw [mem_Ico] at hM
    rw [smul_smul, nOneCoeff_mul hM.1 hM.2]
  have hT := congrArg Matrix.det hSQ
  rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det, eq_intCast] at hT
  apply cube_ne_three_mul_int (a := γ 1 * (((q - 2).factorial : ℚ) * (-1) ^ q))
    (fun hd => det_TZ_zmod_ne_zero q hq ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast hd)))
  rw [mul_pow, hdet, ← hT]
  ring

/-- **notes/13 定理 5(a)（猜想总表 A26 (ii) 的「每个 i 一个原子不存在」）**：设 `q ≥ 2`。不存在复数 `γ(i)`、整数 `δ(i)`
（`0 ≤ i ≤ q−1`）使 `N(k,q) = Σ_{i=0}^{q−1} γ(i)·c_i(k+δ(i))` 对一切充分大的 `k` 成立。 -/
theorem N_no_one_atom {q : ℕ} (hq : 2 ≤ q) :
    ¬ ∃ (γ : ℕ → ℂ) (δ : ℕ → ℤ), ∀ᶠ k in atTop,
      (N k q : ℂ) = ∑ i ∈ range q, γ i * (ciZ i ((k : ℤ) + δ i) : ℂ) := by
  rintro ⟨γ, δ, h⟩
  have e : q - 1 + 1 = q := by omega
  obtain ⟨γ0, γ', h'⟩ := one_atom_rat_of_complex (fun k => N k q) (q - 1) γ δ (by rw [e]; exact h)
  exact N_no_one_atom_rat hq γ0 γ' δ h'

end A207123
