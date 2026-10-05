import A207123.Basic

/-!
# 有理母函数、既约分母与最小递推阶（报告 T1.3(1)(2)）

记 `b_i(x) = 1 − x − i·x³`，`P_m = ∏_{i=0}^{m} b_i`，`W_m = 1 + x²·Σ_{j=1}^{m} j·P_{j−1}`，
`G_m(x) = Σ_k U_k(m)·x^k`（`ℚ` 上的形式幂级数）。

本文件证明：
* T1.3(1)：`G_zero`（`(1 − x)·G_0 = 1`）、`G_rec`（`(1 − x − (m+1)x³)·G_{m+1} = G_m + (m+1)x²`，
  由引理 1 逐系数比较）、`P_mul_G`（`P_m·G_m = W_m`，即 `G_m = W_m / P_m`）、
  `X_mul_W`（`x·W_m = 1 − P_m − x·Σ_{j<m} P_j`，对任意交换环成立）；
* T1.3(2)：`isCoprime_W_P`（`W_m` 与 `P_m` 在 `ℚ[x]` 中互素）、`natDegree_P`（`deg P_m = 3m+1`）、
  `coeff_zero_P`（`P_m(0) = 1`）、`P_recurrence`（`P_m` 的系数给出 `U_k(m)` 关于 `k` 的
  `3m+1` 阶递推）、`order_lower_bound`（任何系数不全为零、只要求对充分大的 `k` 成立的 `d` 阶递推
  都满足 `d ≥ 3m+1`）、`min_order`（最小递推阶恰为 `3m+1`）、`P_dvd_of_mul_G_poly`
  （若 `C·G_m` 是多项式，则 `P_m ∣ C`，即 `G_m` 的既约分母恰为 `P_m`）。

互素性的证明路线（全在 `ℚ[x]` 中，整系数论证用 Gauss 引理）：
* 对 `i ≤ m`，`W_m ≡ W_i (mod b_i)`（`bpoly_dvd_W_sub`），化为 `W_i` 与 `b_i` 互素
  （`isCoprime_W_b_self`）；
* 设不可约 `p` 同时整除 `W_i` 与 `b_i`（`i ≥ 1`），按 `deg p ∈ {1, 2, 3}` 分情形：
  - `deg p = 1`：`p` 的有理根 `r` 是 `b_i` 的根，正性引理（`one_le_eval_W_of_root`）给出
    `W_i(r) ≥ 1`，矛盾；
  - `deg p = 3`：`b_i ∣ W_i`，Gauss 引理给出 `b_i(1) = −i ∣ W_i(1) = 1`，故 `i = 1`，
    再由 `W_1 − b_1 = x + x²` 的次数矛盾；
  - `deg p = 2`：余因子有有理根 `r`，`1/r` 是首一整系数多项式 `t³ − t² − i` 的根，
    于是 `1/r = z ∈ ℤ`、`i = z²(z−1)`、`z ≥ 2`，`b_i = (1 − zx)(1 + (z−1)x + z(z−1)x²)`，
    `p` 与第二个因子 `q` 相伴，Gauss 引理给出 `q(1) = z² ∣ 1`，矛盾。
-/

namespace A207123

open Polynomial Finset

/-! ### 定义 -/

/-- `b_i = 1 − x − i·x³`。 -/
noncomputable def bpoly (R : Type*) [CommRing R] (i : ℕ) : R[X] := 1 - X - C (i : R) * X ^ 3

/-- `P_m = ∏_{i=0}^{m} b_i`。 -/
noncomputable def Ppoly (R : Type*) [CommRing R] (m : ℕ) : R[X] := ∏ i ∈ range (m + 1), bpoly R i

/-- `W_m = 1 + x²·Σ_{j=1}^{m} j·P_{j−1}`。 -/
noncomputable def Wpoly (R : Type*) [CommRing R] (m : ℕ) : R[X] :=
  1 + X ^ 2 * ∑ j ∈ Icc 1 m, C (j : R) * Ppoly R (j - 1)

/-- `G_m = Σ_k U_k(m)·x^k`。 -/
noncomputable def Gser (m : ℕ) : PowerSeries ℚ := PowerSeries.mk fun k => (U k m : ℚ)

/-! ### 基本性质（任意交换环） -/

section General

variable (R : Type*) [CommRing R]

/-- 辅助引理（T1.3）：`P_0 = b_0`。 -/
theorem Ppoly_zero : Ppoly R 0 = bpoly R 0 := by
  simp [Ppoly]

/-- 辅助引理（T1.3）：`P_{m+1} = P_m·b_{m+1}`。 -/
theorem Ppoly_succ (m : ℕ) : Ppoly R (m + 1) = Ppoly R m * bpoly R (m + 1) := by
  unfold Ppoly
  exact Finset.prod_range_succ _ _

/-- 辅助引理（T1.3）：`W_0 = 1`。 -/
theorem Wpoly_zero : Wpoly R 0 = 1 := by
  simp [Wpoly]

/-- 辅助引理（T1.3）：`W_{m+1} = W_m + x²·(m+1)·P_m`。 -/
theorem Wpoly_succ (m : ℕ) :
    Wpoly R (m + 1) = Wpoly R m + X ^ 2 * (C ((m : R) + 1) * Ppoly R m) := by
  unfold Wpoly
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), Nat.add_sub_cancel]
  push_cast
  ring

/-- 辅助引理（T1.3(2)）：`b_i(r) = 1 − r − i·r³`。 -/
theorem eval_bpoly (i : ℕ) (r : R) : (bpoly R i).eval r = 1 - r - i * r ^ 3 := by
  simp [bpoly]

/-- 辅助引理（T1.3(2)）：`b_i(0) = 1`。 -/
theorem coeff_zero_bpoly (i : ℕ) : (bpoly R i).coeff 0 = 1 := by
  simp [bpoly]

/-- 辅助引理（T1.3(2)）：`b_i` 与系数环同态相容（用于 `ℤ[x] → ℚ[x]`）。 -/
theorem bpoly_map {S : Type*} [CommRing S] (f : R →+* S) (i : ℕ) :
    (bpoly R i).map f = bpoly S i := by
  simp [bpoly]

/-- 辅助引理（T1.3(2)）：`P_m` 与系数环同态相容。 -/
theorem Ppoly_map {S : Type*} [CommRing S] (f : R →+* S) (m : ℕ) :
    (Ppoly R m).map f = Ppoly S m := by
  simp [Ppoly, Polynomial.map_prod, bpoly_map]

/-- 辅助引理（T1.3(2)）：`W_m` 与系数环同态相容。 -/
theorem Wpoly_map {S : Type*} [CommRing S] (f : R →+* S) (m : ℕ) :
    (Wpoly R m).map f = Wpoly S m := by
  simp [Wpoly, Polynomial.map_sum, Ppoly_map]

/-- 辅助引理（T1.3(2)）：`P_m(1) = 0`（因子 `b_0 = 1 − x`）。 -/
theorem eval_one_Ppoly (m : ℕ) : (Ppoly R m).eval 1 = 0 := by
  unfold Ppoly
  rw [eval_prod]
  exact Finset.prod_eq_zero (i := 0) (by simp) (by simp [eval_bpoly])

/-- 辅助引理（T1.3(2)）：`W_m(1) = 1`（`j ≥ 1` 时 `P_{j−1}(1) = 0`）。 -/
theorem eval_one_Wpoly (m : ℕ) : (Wpoly R m).eval 1 = 1 := by
  simp [Wpoly, eval_finsetSum, eval_one_Ppoly]

/-- **T1.3(1)**：`x·W_m = 1 − P_m − x·Σ_{j<m} P_j`。 -/
theorem X_mul_W (m : ℕ) : X * Wpoly R m = 1 - Ppoly R m - X * ∑ j ∈ range m, Ppoly R j := by
  induction m with
  | zero => simp [Wpoly_zero, Ppoly_zero, bpoly]
  | succ m ih =>
    rw [Wpoly_succ, mul_add, ih, Ppoly_succ, Finset.sum_range_succ]
    simp only [bpoly, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

end General

/-! ### T1.3(1)：母函数满足的递推与 `G_m = W_m / P_m` -/

/-- 辅助引理（T1.3(1)）：`b_i` 看作形式幂级数。 -/
theorem coe_bpoly (i : ℕ) :
    (↑(bpoly ℚ i) : PowerSeries ℚ) =
      1 - PowerSeries.X - PowerSeries.C (i : ℚ) * PowerSeries.X ^ 3 := by
  simp only [bpoly, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow]

/-- 辅助引理（T1.3(1)）：`G_m` 的 `x^k` 系数是 `U_k(m)`。 -/
theorem coeff_Gser (k m : ℕ) : PowerSeries.coeff k (Gser m) = (U k m : ℚ) := by
  rw [Gser, PowerSeries.coeff_mk]

/-- 辅助引理（T1.3(1)）：乘以 `1 − x − c·x³` 后的系数。 -/
theorem coeff_b_mul (c : ℚ) (F : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.X - PowerSeries.C c * PowerSeries.X ^ 3) * F) =
      PowerSeries.coeff k F - (if 1 ≤ k then PowerSeries.coeff (k - 1) F else 0) -
        c * (if 3 ≤ k then PowerSeries.coeff (k - 3) F else 0) := by
  have hX : PowerSeries.X * F = PowerSeries.X ^ 1 * F := by rw [pow_one]
  rw [sub_mul, sub_mul, one_mul, mul_assoc, map_sub, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', hX, PowerSeries.coeff_X_pow_mul']

/-- **T1.3(1)**，`m = 0` 的情形：`(1 − x)·G_0 = 1`（即约定 `G_{−1} = 1`）。 -/
theorem G_zero : (↑(bpoly ℚ 0) : PowerSeries ℚ) * Gser 0 = 1 := by
  ext k
  rw [coe_bpoly, coeff_b_mul, PowerSeries.coeff_one]
  simp only [coeff_Gser, U_zero_right, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [ite_eq_left (by omega : 1 ≤ k), ite_eq_right (by omega : k ≠ 0), sub_self]

/-- **T1.3(1)**：`(1 − x − (m+1)x³)·G_{m+1} = G_m + (m+1)x²`。
由引理 1 逐系数比较：`k = 0` 用 `U_0 = 1`，`k = 1` 用 `lemma1_one`，`k = 2` 用 `lemma1_two`，
`k ≥ 3` 用 `lemma1`。 -/
theorem G_rec (m : ℕ) :
    (↑(bpoly ℚ (m + 1)) : PowerSeries ℚ) * Gser (m + 1) =
      Gser m + PowerSeries.C ((m : ℚ) + 1) * PowerSeries.X ^ 2 := by
  ext k
  rw [coe_bpoly, coeff_b_mul, map_add, PowerSeries.coeff_C_mul_X_pow]
  simp only [coeff_Gser]
  push_cast
  match k with
  | 0 => simp [U_zero_left]
  | 1 =>
    have h : (U 1 (m + 1) : ℚ) = U 1 m + U 0 (m + 1) := by exact_mod_cast lemma1_one m
    norm_num
    linear_combination h
  | 2 =>
    have h : (U 2 (m + 1) : ℚ) = U 2 m + U 1 (m + 1) + (m + 1) * 1 := by
      exact_mod_cast lemma1_two m
    norm_num
    linear_combination h
  | k + 3 =>
    have h : (U (k + 3) (m + 1) : ℚ) =
        U (k + 3) m + U (k + 2) (m + 1) + (m + 1) * U k (m + 1) := by
      exact_mod_cast lemma1 k m
    rw [ite_eq_left (by omega : 1 ≤ k + 3), ite_eq_left (by omega : 3 ≤ k + 3),
      ite_eq_right (by omega : k + 3 ≠ 2), show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel]
    linear_combination h

/-- **T1.3(1)**：`P_m·G_m = W_m`，即 `G_m = W_m / P_m`。 -/
theorem P_mul_G (m : ℕ) : (↑(Ppoly ℚ m) : PowerSeries ℚ) * Gser m = ↑(Wpoly ℚ m) := by
  induction m with
  | zero => rw [Ppoly_zero, Wpoly_zero, Polynomial.coe_one]; exact G_zero
  | succ m ih =>
    have h1 : (↑(Ppoly ℚ (m + 1)) : PowerSeries ℚ) * Gser (m + 1) =
        ↑(Ppoly ℚ m) * ((↑(bpoly ℚ (m + 1)) : PowerSeries ℚ) * Gser (m + 1)) := by
      rw [Ppoly_succ, Polynomial.coe_mul, mul_assoc]
    rw [h1, G_rec, mul_add, ih, Wpoly_succ]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_C]
    ring

/-! ### T1.3(2)：次数、常数项与 `3m+1` 阶递推 -/

/-- 辅助引理（T1.3(2)）：`b_i ≠ 0`。 -/
theorem bpoly_ne_zero (i : ℕ) : bpoly ℚ i ≠ 0 := by
  intro h
  have := coeff_zero_bpoly ℚ i
  rw [h, Polynomial.coeff_zero] at this
  exact zero_ne_one this

/-- 辅助引理（T1.3(2)）：`P_m ≠ 0`。 -/
theorem Ppoly_ne_zero (m : ℕ) : Ppoly ℚ m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => bpoly_ne_zero i

/-- 辅助引理（T1.3(2)）：`deg b_0 = 1`。 -/
theorem natDegree_bpoly_zero : (bpoly ℚ 0).natDegree = 1 := by
  simp only [bpoly, Nat.cast_zero, map_zero, zero_mul, sub_zero]
  compute_degree!

/-- 辅助引理（T1.3(2)）：`deg b_i = 3`（`i ≥ 1`）。 -/
theorem natDegree_bpoly {i : ℕ} (hi : 1 ≤ i) : (bpoly ℚ i).natDegree = 3 := by
  have hi0 : i ≠ 0 := by omega
  unfold bpoly
  compute_degree!

/-- **T1.3(2)**：`deg P_m = 3m + 1`。 -/
theorem natDegree_P (m : ℕ) : (Ppoly ℚ m).natDegree = 3 * m + 1 := by
  induction m with
  | zero => rw [Ppoly_zero, natDegree_bpoly_zero]
  | succ m ih =>
    rw [Ppoly_succ, natDegree_mul (Ppoly_ne_zero m) (bpoly_ne_zero _), ih,
      natDegree_bpoly (by omega)]
    ring

/-- **T1.3(2)**：`P_m(0) = 1`。 -/
theorem coeff_zero_P (m : ℕ) : (Ppoly ℚ m).coeff 0 = 1 := by
  induction m with
  | zero => rw [Ppoly_zero, coeff_zero_bpoly]
  | succ m ih => rw [Ppoly_succ, mul_coeff_zero, ih, coeff_zero_bpoly, one_mul]

/-- 辅助引理（T1.3(2)）：`deg W_m ≤ 3m`。 -/
theorem natDegree_W_le (m : ℕ) : (Wpoly ℚ m).natDegree ≤ 3 * m := by
  induction m with
  | zero => simp [Wpoly_zero]
  | succ m ih =>
    rw [Wpoly_succ]
    refine (natDegree_add_le _ _).trans (max_le (ih.trans (by omega)) ?_)
    refine natDegree_mul_le.trans ?_
    have h1 := natDegree_X_pow_le (R := ℚ) 2
    have h2 := natDegree_C_mul_le ((m : ℚ) + 1) (Ppoly ℚ m)
    rw [natDegree_P] at h2
    omega

/-- **T1.3(2)**（递推存在）：`P_m` 的系数 `c_0, …, c_{3m+1}` 给出 `U_k(m)` 关于 `k` 的
`3m+1` 阶线性递推 `Σ_{i=0}^{3m+1} c_i·U_{k−i}(m) = 0`（对一切 `k ≥ 3m+1`）。 -/
theorem P_recurrence (m k : ℕ) (hk : 3 * m + 1 ≤ k) :
    ∑ i ∈ range (3 * m + 2), (Ppoly ℚ m).coeff i * (U (k - i) m : ℚ) = 0 := by
  have h := congrArg (PowerSeries.coeff k) (P_mul_G m)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_W_le m) (by omega))] at h
  simp only [Polynomial.coeff_coe, coeff_Gser] at h
  refine (Finset.sum_subset ?_ ?_).trans h
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_P]; omega), zero_mul]

/-! ### T1.3(2)：`W_m` 与 `P_m` 互素 -/

/-- 辅助引理（T1.3(2)，正性引理）：若 `b_i(r) = 0`（`i ≥ 1`），则 `r > 0`，
对 `v ≤ i` 有 `b_v(r) = (i−v)r³ ≥ 0`，从而 `W_i(r) ≥ 1`。 -/
theorem one_le_eval_W_of_root {i : ℕ} (hi : 1 ≤ i) {r : ℚ} (hr : (bpoly ℚ i).eval r = 0) :
    1 ≤ (Wpoly ℚ i).eval r := by
  rw [eval_bpoly] at hr
  have hi1 : (1 : ℚ) ≤ i := by exact_mod_cast hi
  have hr0 : 0 < r := by
    by_contra hneg
    have hle : r ≤ 0 := not_lt.mp hneg
    have h3 : r ^ 3 ≤ 0 := by nlinarith [sq_nonneg r]
    have h4 : (i : ℚ) * r ^ 3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h3
    linarith
  have hb : ∀ v ≤ i, 0 ≤ (bpoly ℚ v).eval r := by
    intro v hv
    rw [eval_bpoly]
    have hv' : (v : ℚ) ≤ i := by exact_mod_cast hv
    have h3 : 0 < r ^ 3 := pow_pos hr0 3
    nlinarith [mul_nonneg (sub_nonneg.mpr hv') h3.le]
  have hP : ∀ n ≤ i, 0 ≤ (Ppoly ℚ n).eval r := by
    intro n hn
    unfold Ppoly
    rw [eval_prod]
    exact Finset.prod_nonneg fun v hv => hb v (by simp only [Finset.mem_range] at hv; omega)
  have hS : 0 ≤ ∑ j ∈ Icc 1 i, (C (j : ℚ) * Ppoly ℚ (j - 1)).eval r := by
    apply Finset.sum_nonneg
    intro j hj
    rw [eval_mul, eval_C]
    exact mul_nonneg (Nat.cast_nonneg j) (hP (j - 1) (by simp only [Finset.mem_Icc] at hj; omega))
  unfold Wpoly
  rw [eval_add, eval_one, eval_mul, eval_pow, eval_X, eval_finsetSum]
  nlinarith [mul_nonneg (sq_nonneg r) hS]

/-- 辅助引理（T1.3(2)，Gauss 引理的应用）：若整系数多项式 `p` 常数项为 1（故本原），
且它在 `ℚ[x]` 中整除 `W_i`，则 `p(1) ∣ W_i(1) = 1`。 -/
theorem eval_one_dvd_of_dvd_W {p : ℤ[X]} (hp : p.coeff 0 = 1) (i : ℕ)
    (h : p.map (Int.castRingHom ℚ) ∣ Wpoly ℚ i) : p.eval 1 ∣ 1 := by
  have hprim : p.IsPrimitive := by
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have := hr 0
    rw [hp] at this
    exact isUnit_of_dvd_one this
  rw [← Wpoly_map ℤ (Int.castRingHom ℚ) i] at h
  have h2 := (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast p (Wpoly ℤ i) hprim).mpr h
  have h3 := eval_dvd (x := 1) h2
  rwa [eval_one_Wpoly] at h3

/-- 核心引理（T1.3(2)）：`W_i` 与 `b_i` 在 `ℚ[x]` 中互素。 -/
theorem isCoprime_W_b_self (i : ℕ) : IsCoprime (Wpoly ℚ i) (bpoly ℚ i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [Wpoly_zero]; exact isCoprime_one_left
  apply isCoprime_of_irreducible_dvd
  · rintro ⟨-, h⟩
    exact bpoly_ne_zero i h
  intro p hp hpW hpb
  obtain ⟨e, he⟩ := hpb
  obtain ⟨f, hf⟩ := hpW
  have hp0 : p ≠ 0 := hp.ne_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [mul_zero] at he
    exact bpoly_ne_zero i he
  have hdeg : p.natDegree + e.natDegree = 3 := by
    rw [← natDegree_mul hp0 he0, ← he, natDegree_bpoly hi]
  have hp1 : 0 < p.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hp)
  rcases (by omega : p.natDegree = 1 ∨ p.natDegree = 2 ∨ p.natDegree = 3) with h1 | h2 | h3
  · -- `deg p = 1`：`p` 的有理根同时是 `b_i` 与 `W_i` 的根，与正性引理矛盾。
    obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq hp0).mpr h1)
    have hbr : (bpoly ℚ i).eval r = 0 := by rw [he, eval_mul, hr.eq_zero, zero_mul]
    have hWr : (Wpoly ℚ i).eval r = 0 := by rw [hf, eval_mul, hr.eq_zero, zero_mul]
    have := one_le_eval_W_of_root hi hbr
    linarith
  · -- `deg p = 2`：余因子 `e` 是一次的，其有理根 `r` 满足 `1/r ∈ ℤ`。
    have he1 : e.natDegree = 1 := by omega
    obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq he0).mpr he1)
    have hbr : (bpoly ℚ i).eval r = 0 := by rw [he, eval_mul, hr.eq_zero, mul_zero]
    rw [eval_bpoly] at hbr
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hbr
    have htroot : r⁻¹ ^ 3 - r⁻¹ ^ 2 - (i : ℚ) = 0 := by
      have ht : r⁻¹ * r = 1 := inv_mul_cancel₀ hr0
      linear_combination r⁻¹ ^ 3 * hbr + (r⁻¹ ^ 2 + (i : ℚ) * (r⁻¹ ^ 2 * r ^ 2 + r⁻¹ * r + 1)) * ht
    have hmon : (X ^ 3 - X ^ 2 - C (i : ℤ) : ℤ[X]).Monic := by monicity!
    have hroot : aeval r⁻¹ (X ^ 3 - X ^ 2 - C (i : ℤ) : ℤ[X]) = 0 := by
      simpa using htroot
    obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmon hroot
    have hz' : r⁻¹ = (z : ℚ) := by simpa using hz
    rw [hz'] at htroot
    have hiz : (i : ℤ) = z ^ 3 - z ^ 2 := by
      have : (i : ℚ) = (z : ℚ) ^ 3 - (z : ℚ) ^ 2 := by linarith
      exact_mod_cast this
    have hz2 : 2 ≤ z := by
      by_contra hlt
      have hz1 : z ≤ 1 := by omega
      have h5 : (1 : ℤ) ≤ i := by exact_mod_cast hi
      nlinarith [mul_nonneg (sq_nonneg z) (by linarith : (0 : ℤ) ≤ 1 - z)]
    obtain ⟨q, hq⟩ : ∃ q : ℚ[X], q = 1 + C ((z : ℚ) - 1) * X + C ((z : ℚ) * (z - 1)) * X ^ 2 :=
      ⟨_, rfl⟩
    have hfac : bpoly ℚ i = (1 - C (z : ℚ) * X) * q := by
      have hiq : (i : ℚ) = (z : ℚ) ^ 3 - (z : ℚ) ^ 2 := by exact_mod_cast hiz
      rw [hq, bpoly, hiq]
      simp only [map_sub, map_mul, map_pow, map_one]
      ring
    have hdvd : p ∣ (1 - C (z : ℚ) * X) * q := by
      rw [← hfac]
      exact ⟨e, he⟩
    rcases hp.prime.dvd_or_dvd hdvd with hl | hpq
    · -- `p ∣ 1 − zx`：次数矛盾。
      have hz0 : z ≠ 0 := by omega
      have hlin : (1 - C (z : ℚ) * X).natDegree = 1 := by compute_degree!
      have hne : (1 - C (z : ℚ) * X) ≠ 0 := by
        intro h
        rw [h, natDegree_zero] at hlin
        exact zero_ne_one hlin
      have := natDegree_le_of_dvd hl hne
      omega
    · -- `p ∣ q`：两者次数都是 2，故相伴，于是 `q ∣ W_i`。
      obtain ⟨g, hg⟩ := hpq
      have hqdeg : q.natDegree = 2 := by
        rw [hq]
        compute_degree!
        exact ⟨by omega, by omega⟩
      have hq0 : q ≠ 0 := by
        intro h
        rw [h, natDegree_zero] at hqdeg
        omega
      have hg0 : g ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hg
        exact hq0 hg
      have hgdeg : g.natDegree = 0 := by
        have := natDegree_mul hp0 hg0
        rw [← hg, hqdeg, h2] at this
        omega
      obtain ⟨c, hgc⟩ : ∃ c, g = C c := ⟨_, eq_C_of_natDegree_eq_zero hgdeg⟩
      subst hgc
      have hc : c ≠ 0 := by
        rintro rfl
        exact hg0 (map_zero C)
      have hqW : q ∣ Wpoly ℚ i := by
        refine ⟨C c⁻¹ * f, ?_⟩
        rw [hf, hg, mul_assoc, ← mul_assoc (C c), ← map_mul, mul_inv_cancel₀ hc, map_one,
          one_mul]
      -- Gauss 引理：整系数的 `q` 在 `x = 1` 处的值 `z²` 整除 `W_i(1) = 1`。
      have hmap : (1 + C (z - 1) * X + C (z * (z - 1)) * X ^ 2 : ℤ[X]).map (Int.castRingHom ℚ) =
          q := by
        rw [hq]
        simp
      have hdvdZ := eval_one_dvd_of_dvd_W
        (p := (1 + C (z - 1) * X + C (z * (z - 1)) * X ^ 2 : ℤ[X])) (by simp) i
        (by rw [hmap]; exact hqW)
      have hval : (1 + C (z - 1) * X + C (z * (z - 1)) * X ^ 2 : ℤ[X]).eval 1 = z ^ 2 := by
        simp
        ring
      rw [hval] at hdvdZ
      have := Int.le_of_dvd one_pos hdvdZ
      nlinarith
  · -- `deg p = 3`：`e` 是非零常数，于是 `b_i ∣ W_i`。
    have he' : e.natDegree = 0 := by omega
    obtain ⟨c, hec⟩ : ∃ c, e = C c := ⟨_, eq_C_of_natDegree_eq_zero he'⟩
    subst hec
    have hc : c ≠ 0 := by
      rintro rfl
      exact he0 (map_zero C)
    have hbW : bpoly ℚ i ∣ Wpoly ℚ i := by
      refine ⟨C c⁻¹ * f, ?_⟩
      rw [hf, he, mul_assoc, ← mul_assoc (C c), ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    -- Gauss 引理：`b_i(1) = −i` 整除 `W_i(1) = 1`，故 `i = 1`。
    have hi1 : i = 1 := by
      have hdvdZ := eval_one_dvd_of_dvd_W (coeff_zero_bpoly ℤ i) i (by rw [bpoly_map]; exact hbW)
      rw [eval_bpoly] at hdvdZ
      have hiZ : (i : ℤ) ∣ 1 := by
        have h' : (1 : ℤ) - 1 - (i : ℤ) * 1 ^ 3 = -(i : ℤ) := by ring
        rwa [h', neg_dvd] at hdvdZ
      have hiN : i ∣ 1 := by exact_mod_cast hiZ
      exact Nat.dvd_one.mp hiN
    subst hi1
    -- `W_1 − b_1 = x + x²`，被 `b_1` 整除，但次数 2 < 3。
    have hsub : Wpoly ℚ 1 - bpoly ℚ 1 = X + X ^ 2 := by
      simp [Wpoly, Ppoly, bpoly]
      ring
    have hdvd2 : bpoly ℚ 1 ∣ X + X ^ 2 := hsub ▸ dvd_sub hbW dvd_rfl
    have hdeg2 : (X + X ^ 2 : ℚ[X]).natDegree = 2 := by compute_degree!
    have hne : (X + X ^ 2 : ℚ[X]) ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hdeg2
      omega
    have hle := natDegree_le_of_dvd hdvd2 hne
    rw [natDegree_bpoly le_rfl, hdeg2] at hle
    omega

/-- 辅助引理（T1.3(2)）：对 `i ≤ m`，`b_i ∣ W_m − W_i`（`j − 1 ≥ i` 时 `b_i ∣ P_{j−1}`）。 -/
theorem bpoly_dvd_W_sub {i m : ℕ} (him : i ≤ m) : bpoly ℚ i ∣ Wpoly ℚ m - Wpoly ℚ i := by
  induction m, him using Nat.le_induction with
  | base => simp
  | succ m him ih =>
    rw [Wpoly_succ]
    have e : Wpoly ℚ m + X ^ 2 * (C ((m : ℚ) + 1) * Ppoly ℚ m) - Wpoly ℚ i =
        (Wpoly ℚ m - Wpoly ℚ i) + X ^ 2 * (C ((m : ℚ) + 1) * Ppoly ℚ m) := by ring
    rw [e]
    refine dvd_add ih (Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _)
    unfold Ppoly
    exact Finset.dvd_prod_of_mem _ (by simp only [Finset.mem_range]; omega)

/-- 辅助引理（T1.3(2)）：对 `i ≤ m`，`W_m` 与 `b_i` 互素（由 `W_m ≡ W_i (mod b_i)`）。 -/
theorem isCoprime_W_b {i m : ℕ} (him : i ≤ m) : IsCoprime (Wpoly ℚ m) (bpoly ℚ i) := by
  obtain ⟨q, hq⟩ := bpoly_dvd_W_sub him
  have e : Wpoly ℚ m = Wpoly ℚ i + bpoly ℚ i * q := by rw [← hq]; ring
  rw [e]
  exact (isCoprime_W_b_self i).add_mul_left_left q

/-- **T1.3(2)**：对一切 `m ≥ 0`，`gcd(W_m, P_m) = 1`（在 `ℚ[x]` 中互素）。 -/
theorem isCoprime_W_P (m : ℕ) : IsCoprime (Wpoly ℚ m) (Ppoly ℚ m) := by
  unfold Ppoly
  apply IsCoprime.prod_right
  intro i hi
  exact isCoprime_W_b (by simp only [Finset.mem_range] at hi; omega)

/-! ### T1.3(2)：既约分母与最小递推阶 -/

/-- **T1.3(2)**（既约分母恰为 `P_m`）：若 `C·G_m` 是多项式 `Q`，则 `P_m ∣ C`。
证明：`C·W_m = C·P_m·G_m = P_m·Q`，由强制转换单射得多项式等式，再用互素。 -/
theorem P_dvd_of_mul_G_poly (m : ℕ) (Cp Q : ℚ[X])
    (h : (↑Cp : PowerSeries ℚ) * Gser m = ↑Q) : Ppoly ℚ m ∣ Cp := by
  have key : Cp * Wpoly ℚ m = Ppoly ℚ m * Q := by
    apply Polynomial.coe_injective ℚ
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← P_mul_G, ← h]
    ring
  exact (isCoprime_W_P m).symm.dvd_of_dvd_mul_right ⟨Q, key⟩

/-- **T1.3(2)**（阶的下界）：若 `γ_0, …, γ_d` 不全为零，且对一切 `k ≥ max(k0, d)` 都有
`Σ_{i=0}^{d} γ_i·U_{k−i}(m) = 0`，则 `d ≥ 3m+1`。 -/
theorem order_lower_bound (m d k0 : ℕ) (γ : ℕ → ℚ) (hγ : ∃ i ≤ d, γ i ≠ 0)
    (h : ∀ k, k0 ≤ k → d ≤ k → ∑ i ∈ range (d + 1), γ i * (U (k - i) m : ℚ) = 0) :
    3 * m + 1 ≤ d := by
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℚ[X], Γ = ∑ i ∈ range (d + 1), C (γ i) * X ^ i := ⟨_, rfl⟩
  have hΓcoeff : ∀ n, Γ.coeff n = if n ≤ d then γ n else 0 := by
    intro n
    rw [hΓ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_add_one_iff]
  have hΓne : Γ ≠ 0 := by
    obtain ⟨i, hi, hγi⟩ := hγ
    intro h0
    have := hΓcoeff i
    rw [h0, Polynomial.coeff_zero, ite_eq_left hi] at this
    exact hγi this.symm
  have hΓdeg : Γ.natDegree ≤ d := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hΓcoeff, ite_eq_right (by omega)]
  have hF : ∀ k, max k0 d ≤ k → PowerSeries.coeff k ((↑Γ : PowerSeries ℚ) * Gser m) = 0 := by
    intro k hk
    have hk0 : k0 ≤ k := le_trans (le_max_left _ _) hk
    have hdk : d ≤ k := le_trans (le_max_right _ _) hk
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Polynomial.coeff_coe, coeff_Gser]
    calc ∑ x ∈ range k.succ, Γ.coeff x * (U (k - x) m : ℚ)
        = ∑ x ∈ range (d + 1), Γ.coeff x * (U (k - x) m : ℚ) := by
          symm
          apply Finset.sum_subset
          · intro i hi
            simp only [Finset.mem_range] at hi ⊢
            omega
          · intro i _ hi
            simp only [Finset.mem_range, not_lt] at hi
            rw [hΓcoeff, ite_eq_right (by omega), zero_mul]
      _ = ∑ x ∈ range (d + 1), γ x * (U (k - x) m : ℚ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_range] at hi
          rw [hΓcoeff, ite_eq_left (by omega)]
      _ = 0 := h k hk0 hdk
  have hQ : (↑Γ : PowerSeries ℚ) * Gser m =
      ↑(PowerSeries.trunc (max k0 d) ((↑Γ : PowerSeries ℚ) * Gser m)) := by
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases hn : n < max k0 d
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn]
      exact hF n (by omega)
  have hdvd := P_dvd_of_mul_G_poly m Γ _ hQ
  have := natDegree_le_of_dvd hdvd hΓne
  rw [natDegree_P] at this
  omega

/-- **T1.3(2)**：`U_k(m)` 关于 `k` 的最小线性递推阶恰为 `3m+1`
（首项系数归一 `γ_0 = 1`，递推对一切 `k ≥ d` 成立）。 -/
theorem min_order (m : ℕ) :
    IsLeast {d | ∃ γ : ℕ → ℚ, γ 0 = 1 ∧
      ∀ k, d ≤ k → ∑ i ∈ range (d + 1), γ i * (U (k - i) m : ℚ) = 0} (3 * m + 1) := by
  refine ⟨⟨fun i => (Ppoly ℚ m).coeff i, coeff_zero_P m, fun k hk => P_recurrence m k hk⟩, ?_⟩
  rintro d ⟨γ, hγ0, hγ⟩
  exact order_lower_bound m d 0 γ ⟨0, Nat.zero_le d, by rw [hγ0]; exact one_ne_zero⟩
    (fun k _ hk => hγ k hk)

end A207123
