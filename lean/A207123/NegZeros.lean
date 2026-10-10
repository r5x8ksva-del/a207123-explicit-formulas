import A207123.HStruct
import A207123.LogConcave

/-!
# 报告 T5.3(2)：`u_k` 的负整数零点——同余、显式根界与顶端两层（猜想总表 A28 (i)–(iii)）

报告 T5.3(2) 在「`U_k` 没有其他负整数零点」（一般 `k` 仍是猜想）之前证明了三件对一切 `k` 成立的事；`k ≤ 300` 的
逐个计算（A28 (iv)）不在这里。这里形式化这三件（`U_k(−j)` 指插值多项式 `u_k = upoly k` 在 `−j` 处的值）：

* (a) `uInt_add_prime_pow`：`p` 素数、`p^e > k` 时 `u_k(m + p^e) ≡ u_k(m) (mod p)`（`m` 为任意整数；`uInt k m` 是
  `u_k(m)` 的整数值，`upoly_eval_int`）；证明用广义二项式 `Ring.choose` 的 Vandermonde 展开与 `p ∣ C(p^e, i)`
  （`0 < i < p^e`）。推论 `uInt_neg_modEq_one`、`upoly_eval_neg_ne_zero_of_prime_pow`：`p^e ∣ j` 时
  `u_k(−j) ≡ 1 (mod p)`，所以不为零；`dvd_lcm_of_upoly_eval_neg_eq_zero`：`u_k(−j) = 0`（`j ≥ 1`）推出
  `j ∣ lcm(1, …, k)`。
* (b) `upoly_eval_neg_sign`：`k ≥ 4`、`y > J_k := k(k² − k − 4)/2 − k + 2`（`y` 为有理数）时 `(−1)^k·u_k(−y) > 0`。
  证明：`(−1)^k u_k(−y) = Σ_q (−1)^{k+q} T_q`，`T_q = N(k,q)·(y−1)(y)⋯(y+q−2)/q!`；由 `N(k,·)` 严格对数凹（论文推论
  8.2，`cor_logconcave`）、`N(k,k) = 2`、`N(k,k−1) = k² − k − 4`，`y > J_k` 时 `0 = T_0 < T_1 < ⋯ < T_k`，交错和从顶端
  两两配对为正（`alt_sum_pos`）。
* (c) `upoly_eval_neg_ne_zero_two`：`u_k(−(s_k + 2)) ≠ 0`（`s_k = ⌊(k+2)/3⌋`）；`u_k(−(s_k+1)) ≠ 0` 已是
  `upoly_eval_neg_ne_zero`。证明用 `G_{−j}` 的顶端第 4–6 层系数的闭式（c5a 定理 4.3）：`(j−1)!`、`c(j,2) + c(j,3)`、
  `(j−1)! − c(j,2) − c(j,3)`（`coeff_gnegPoly_top_three`、`_four`、`_five`；`c` 为无符号第一类 Stirling 数），最后
  一个在 `j ≥ 3` 时为负（`factorial_lt_stirlingFirst_two`）。
-/

namespace A207123

open Polynomial Finset

open scoped Nat

/-! ## 1. (a) 整数点上的值与模素数幂的周期性 -/

/-- `u_k` 在整数 `m` 处的值：`Σ_q N(k,q)·C(m+1, q)`，`C` 是 Mathlib 的广义二项式 `Ring.choose`（对负整数也有定义）。 -/
def uInt (k : ℕ) (m : ℤ) : ℤ := ∑ q ∈ range (k + 1), (N k q : ℤ) * Ring.choose (m + 1) q

/-- 辅助引理：`C(y+1, q)` 在整数 `y = m` 处取值 `Ring.choose (m+1) q`。 -/
theorem binomPoly_eval_int (q : ℕ) (m : ℤ) :
    (binomPoly q).eval (m : ℚ) = ((Ring.choose (m + 1) q : ℤ) : ℚ) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (m + 1) q
  rw [← Polynomial.eval_eq_smeval] at h
  have h2 := descPochhammer_eval_cast (R := ℚ) q (m + 1)
  rw [Int.cast_add, Int.cast_one, h, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast] at h2
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, ← h2,
    inv_mul_cancel_left₀ (by exact_mod_cast q.factorial_ne_zero)]

/-- `u_k(m) = uInt k m`（`m ∈ ℤ`），特别地 `u_k` 在整数点取整数值。 -/
theorem upoly_eval_int (k : ℕ) (m : ℤ) : (upoly k).eval (m : ℚ) = (uInt k m : ℚ) := by
  rw [upoly, eval_finsetSum, uInt, Int.cast_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, binomPoly_eval_int, Int.cast_mul, Int.cast_natCast]

/-- 辅助引理：`q < p^e` 时 `p ∣ C(r + p^e, q) − C(r, q)`（Vandermonde 展开，`p ∣ C(p^e, i)`，`0 < i < p^e`）。 -/
theorem choose_add_prime_pow_sub {p e q : ℕ} (hp : p.Prime) (hq : q < p ^ e) (r : ℤ) :
    (p : ℤ) ∣ Ring.choose (r + ((p ^ e : ℕ) : ℤ)) q - Ring.choose r q := by
  rw [Ring.add_choose_eq q (Commute.all _ _),
    ← Finset.sum_erase_add _ _ (show (q, 0) ∈ antidiagonal q by simp)]
  simp only [Ring.choose_natCast, Nat.choose_zero_right, Nat.cast_one, mul_one, add_sub_cancel_right]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.mem_erase] at hij
  have hs : ij.1 + ij.2 = q := Finset.HasAntidiagonal.mem_antidiagonal.1 hij.2
  have h0 : ij.2 ≠ 0 := fun h => hij.1 (Prod.ext (by omega) h)
  exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (hp.dvd_choose_pow h0 (by omega))) _

/-- **T5.3(2)(a)**：`p` 素数、`p^e > k` 时 `u_k(m + p^e) ≡ u_k(m) (mod p)`（`m` 为任意整数）。 -/
theorem uInt_add_prime_pow {k p e : ℕ} (hp : p.Prime) (hk : k < p ^ e) (m : ℤ) :
    uInt k (m + (p : ℤ) ^ e) ≡ uInt k m [ZMOD p] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd, uInt, uInt, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun q hq => ?_
  rw [← mul_sub, show m + (p : ℤ) ^ e + 1 = (m + 1) + ((p ^ e : ℕ) : ℤ) by push_cast; ring]
  exact Dvd.dvd.mul_left (choose_add_prime_pow_sub hp (by have := Finset.mem_range.1 hq; omega) _) _

theorem uInt_add_mul_prime_pow {k p e : ℕ} (hp : p.Prime) (hk : k < p ^ e) (m : ℤ) (t : ℕ) :
    uInt k (m + t * (p : ℤ) ^ e) ≡ uInt k m [ZMOD p] := by
  induction t with
  | zero =>
    rw [Nat.cast_zero, zero_mul, add_zero]
  | succ t ih =>
    rw [show m + ((t + 1 : ℕ) : ℤ) * (p : ℤ) ^ e = (m + t * (p : ℤ) ^ e) + (p : ℤ) ^ e by push_cast; ring]
    exact (uInt_add_prime_pow hp hk _).trans ih

theorem uInt_zero (k : ℕ) : uInt k 0 = 1 := by
  have h := upoly_eval_nat k 0
  rw [U_zero_right, show ((0 : ℕ) : ℚ) = ((0 : ℤ) : ℚ) by simp, upoly_eval_int] at h
  exact_mod_cast h

/-- **T5.3(2)(a)**：`p^e > k`、`p^e ∣ j` 时 `u_k(−j) ≡ 1 (mod p)`。 -/
theorem uInt_neg_modEq_one {k p e j : ℕ} (hp : p.Prime) (hk : k < p ^ e) (hj : p ^ e ∣ j) :
    uInt k (-(j : ℤ)) ≡ 1 [ZMOD p] := by
  obtain ⟨t, rfl⟩ := hj
  have h := uInt_add_mul_prime_pow (k := k) hp hk (-((p ^ e * t : ℕ) : ℤ)) t
  rw [show -((p ^ e * t : ℕ) : ℤ) + (t : ℤ) * (p : ℤ) ^ e = 0 by push_cast; ring, uInt_zero] at h
  exact h.symm

/-- **T5.3(2)(a)**：`p^e > k`、`p^e ∣ j` 时 `u_k(−j) ≠ 0`。 -/
theorem upoly_eval_neg_ne_zero_of_prime_pow {k p e j : ℕ} (hp : p.Prime) (hk : k < p ^ e) (hj : p ^ e ∣ j) :
    (upoly k).eval (-(j : ℚ)) ≠ 0 := by
  rw [show -(j : ℚ) = ((-(j : ℤ) : ℤ) : ℚ) by push_cast; ring, upoly_eval_int]
  intro h0
  have h1 := uInt_neg_modEq_one hp hk hj
  rw [show uInt k (-(j : ℤ)) = 0 by exact_mod_cast h0, Int.modEq_iff_dvd, sub_zero] at h1
  have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h1
  have h3 : p = 1 := by exact_mod_cast h2
  exact hp.one_lt.ne' h3

/-- **T5.3(2)(a)**：`u_k(−j) = 0`（`j ≥ 1`）只可能在 `j ∣ lcm(1, …, k)` 时发生。 -/
theorem dvd_lcm_of_upoly_eval_neg_eq_zero {k j : ℕ} (hj : 1 ≤ j) (h : (upoly k).eval (-(j : ℚ)) = 0) :
    j ∣ (Finset.Icc 1 k).lcm id := by
  have hL : (Finset.Icc 1 k).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, h0⟩
    rw [Finset.mem_Icc] at hx
    simp only [id] at h0
    omega
  rw [← Nat.factorization_le_iff_dvd (by omega) hL, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hpow : p ^ j.factorization p ≤ k := by
      by_contra hlt
      exact upoly_eval_neg_ne_zero_of_prime_pow hp (by omega) (Nat.ordProj_dvd j p) h
    have hmem : p ^ j.factorization p ∈ Finset.Icc 1 k :=
      Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hp.pos, hpow⟩
    exact (hp.pow_dvd_iff_le_factorization hL).1 (Finset.dvd_lcm hmem)
  · rw [Nat.factorization_eq_zero_of_not_prime j hp]
    exact Nat.zero_le _

/-! ## 2. (b) `y > J_k` 时 `(−1)^k u_k(−y) > 0` -/

/-- 辅助引理：`C(−y+1, q) = (−1)^q·(y−1)y⋯(y+q−2)/q!`（上升阶乘 `ascPochhammer`）。 -/
theorem binomPoly_eval_neg (q : ℕ) (y : ℚ) :
    (binomPoly q).eval (-y) = (-1) ^ q * (ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ) := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℚ) (-(y - 1)) q
  rw [neg_neg] at h
  have hsq : ((-1 : ℚ) ^ q) * (-1) ^ q = 1 := by
    rw [← mul_pow]
    norm_num
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one,
    show -y + 1 = -(y - 1) by ring, h]
  linear_combination (-((descPochhammer ℚ q).eval (-(y - 1)) / (q ! : ℚ))) * hsq

/-- `T_q = N(k,q)·(y−1)y⋯(y+q−2)/q!`。 -/
noncomputable def negTerm (k : ℕ) (y : ℚ) (q : ℕ) : ℚ :=
  (N k q : ℚ) * ((ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ))

theorem upoly_eval_neg_eq_alt (k : ℕ) (y : ℚ) :
    (-1 : ℚ) ^ k * (upoly k).eval (-y) = ∑ q ∈ range (k + 1), (-1) ^ (k + q) * negTerm k y q := by
  rw [upoly, eval_finsetSum, mul_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, binomPoly_eval_neg, negTerm, pow_add]
  ring

/-- 辅助引理：交错和的一步 `A_{n+1} = T_{n+1} − A_n`。 -/
theorem alt_sum_succ (T : ℕ → ℚ) (n : ℕ) :
    ∑ q ∈ range (n + 1 + 1), (-1 : ℚ) ^ (n + 1 + q) * T q
      = T (n + 1) - ∑ q ∈ range (n + 1), (-1 : ℚ) ^ (n + q) * T q := by
  rw [sum_range_succ, show n + 1 + (n + 1) = 2 * (n + 1) by ring, pow_mul, neg_one_sq, one_pow, one_mul]
  have e : ∑ q ∈ range (n + 1), (-1 : ℚ) ^ (n + 1 + q) * T q
      = -∑ q ∈ range (n + 1), (-1 : ℚ) ^ (n + q) * T q := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [show n + 1 + q = (n + q) + 1 by ring, pow_succ]
    ring
  rw [e]
  ring

/-- 辅助引理：`T` 非负、单调不减时 `0 ≤ A_n ≤ T_n`，`A_n = Σ_{q≤n} (−1)^{n+q} T_q`。 -/
theorem alt_sum_bounds (T : ℕ → ℚ) (h0 : 0 ≤ T 0) : ∀ n, (∀ q, q < n → T q ≤ T (q + 1)) →
    0 ≤ ∑ q ∈ range (n + 1), (-1 : ℚ) ^ (n + q) * T q ∧ ∑ q ∈ range (n + 1), (-1 : ℚ) ^ (n + q) * T q ≤ T n
  | 0, _ => by simp [h0]
  | n + 1, hmono => by
    obtain ⟨ih1, ih2⟩ := alt_sum_bounds T h0 n fun q hq => hmono q (by omega)
    have hn := hmono n (by omega)
    rw [alt_sum_succ]
    constructor <;> linarith

/-- 辅助引理：`0 ≤ T_0 < T_1 < ⋯ < T_n`（`n ≥ 1`）时 `Σ_{q≤n} (−1)^{n+q} T_q ≥ T_n − T_{n−1} > 0`。 -/
theorem alt_sum_pos (T : ℕ → ℚ) (h0 : 0 ≤ T 0) {n : ℕ} (hn : 1 ≤ n) (hmono : ∀ q, q < n → T q < T (q + 1)) :
    0 < ∑ q ∈ range (n + 1), (-1 : ℚ) ^ (n + q) * T q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, h2⟩ := alt_sum_bounds T h0 m fun q hq => (hmono q (by omega)).le
  have h3 := hmono m (by omega)
  rw [alt_sum_succ]
  linarith

/-- 辅助引理：`1 ≤ q ≤ k − 1` 时 `N(k,q)·N(k,k) ≤ N(k,q+1)·N(k,k−1)`（严格对数凹，比值 `N(k,q+1)/N(k,q)` 递减）。 -/
theorem N_ratio_ge {k : ℕ} (hk : 1 ≤ k) :
    ∀ d q, 1 ≤ q → q + 1 + d = k → N k q * N k k ≤ N k (q + 1) * N k (k - 1)
  | 0, q, _, h => by
    obtain rfl : k = q + 1 := by omega
    rw [show q + 1 - 1 = q by omega]
    exact le_of_eq (Nat.mul_comm _ _)
  | d + 1, q, hq, h => by
    have ih := N_ratio_ge hk d (q + 1) (by omega) (by omega)
    obtain ⟨hpos, hlc, -⟩ := cor_logconcave hk
    have hlc' := hlc (q + 1) (by omega) (by omega)
    rw [show q + 1 - 1 = q by omega] at hlc'
    have hpk := hpos (k - 1) (by omega) (by omega)
    have key : N k q * N k k * N k (q + 1) < N k (q + 1) * N k (k - 1) * N k (q + 1) := by
      calc N k q * N k k * N k (q + 1) = N k q * (N k (q + 1) * N k k) := by ring
        _ ≤ N k q * (N k (q + 1 + 1) * N k (k - 1)) := Nat.mul_le_mul_left _ ih
        _ = N k q * N k (q + 1 + 1) * N k (k - 1) := by ring
        _ < N k (q + 1) ^ 2 * N k (k - 1) := Nat.mul_lt_mul_of_pos_right hlc' hpk
        _ = N k (q + 1) * N k (k - 1) * N k (q + 1) := by ring
    exact (Nat.lt_of_mul_lt_mul_right key).le

/-- 辅助引理（T5.3(2)(b)）：`k ≥ 4`、`y > J_k` 时 `T_q < T_{q+1}`（`q < k`）。 -/
theorem negTerm_lt_succ {k : ℕ} (hk : 4 ≤ k) {y : ℚ}
    (hy : (k : ℚ) * ((k : ℚ) ^ 2 - k - 4) / 2 - k + 2 < y) {q : ℕ} (hq : q < k) :
    negTerm k y q < negTerm k y (q + 1) := by
  obtain ⟨hpos, -, -⟩ := cor_logconcave (k := k) (by omega)
  have hk' : (4 : ℚ) ≤ k := by exact_mod_cast hk
  have hy1 : 1 < y := by nlinarith
  have hasc : 0 < (ascPochhammer ℚ q).eval (y - 1) := ascPochhammer_pos q _ (by linarith)
  have hP : 0 < (ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ) := div_pos hasc (by positivity)
  have hNq1 : (0 : ℚ) < N k (q + 1) := by exact_mod_cast hpos (q + 1) (by omega) (by omega)
  have hsucc : negTerm k y (q + 1) = (N k (q + 1) : ℚ) *
      ((ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ) * ((y - 1 + q) / ((q : ℚ) + 1))) := by
    rw [negTerm, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    field_simp
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · -- `T_0 = 0 < T_1`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hsucc, negTerm, N_succ_zero j, Nat.cast_zero, zero_mul]
    have : 0 < (y - 1 + ((0 : ℕ) : ℚ)) / (((0 : ℕ) : ℚ) + 1) := by
      rw [Nat.cast_zero]
      linarith
    positivity
  · have hNq : (0 : ℚ) < N k q := by exact_mod_cast hpos q (by omega) (by omega)
    -- `N(k,q)·2 ≤ N(k,q+1)·(k² − k − 4)`
    have hratio : (N k q : ℚ) * 2 ≤ (N k (q + 1) : ℚ) * ((k : ℚ) ^ 2 - k - 4) := by
      have h := N_ratio_ge (k := k) (by omega) (k - q - 1) q hq0 (by omega)
      rw [N_diag k (by omega)] at h
      have h2 : ((N k (k - 1) : ℕ) : ℤ) = (k : ℤ) ^ 2 - k - 4 := N_subdiag k hk
      have h3 : ((N k q * 2 : ℕ) : ℚ) ≤ ((N k (q + 1) * N k (k - 1) : ℕ) : ℚ) := by exact_mod_cast h
      have h4 : ((N k (k - 1) : ℕ) : ℚ) = (k : ℚ) ^ 2 - k - 4 := by exact_mod_cast h2
      push_cast at h3
      rw [h4] at h3
      exact h3
    have hqk : (q : ℚ) + 1 ≤ k := by exact_mod_cast hq
    have hc : (8 : ℚ) ≤ (k : ℚ) ^ 2 - k - 4 := by nlinarith
    -- `(k² − k − 4)(q + 1) < 2(y − 1 + q)`
    have hkey : ((k : ℚ) ^ 2 - k - 4) * ((q : ℚ) + 1) < 2 * (y - 1 + q) := by
      nlinarith [mul_nonneg (show (0 : ℚ) ≤ (k : ℚ) ^ 2 - k - 4 - 2 by linarith)
        (show (0 : ℚ) ≤ (k : ℚ) - 1 - q by linarith)]
    have hy2 : 0 < y - 1 + q := by positivity
    have e1 : (N k q : ℚ) * 2 * (y - 1 + q) ≤ (N k (q + 1) : ℚ) * ((k : ℚ) ^ 2 - k - 4) * (y - 1 + q) :=
      mul_le_mul_of_nonneg_right hratio hy2.le
    have e2 : (N k q : ℚ) * (((k : ℚ) ^ 2 - k - 4) * ((q : ℚ) + 1)) < (N k q : ℚ) * (2 * (y - 1 + q)) :=
      mul_lt_mul_of_pos_left hkey hNq
    have hmain : (N k q : ℚ) * ((q : ℚ) + 1) < (N k (q + 1) : ℚ) * (y - 1 + q) := by
      nlinarith
    rw [hsucc, negTerm]
    have hq1 : (0 : ℚ) < (q : ℚ) + 1 := by positivity
    have e3 : (N k (q + 1) : ℚ) * ((ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ) * ((y - 1 + q) / ((q : ℚ) + 1)))
        - (N k q : ℚ) * ((ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ))
        = (ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ) / ((q : ℚ) + 1)
          * ((N k (q + 1) : ℚ) * (y - 1 + q) - (N k q : ℚ) * ((q : ℚ) + 1)) := by
      field_simp
    have : 0 < (ascPochhammer ℚ q).eval (y - 1) / (q ! : ℚ) / ((q : ℚ) + 1)
        * ((N k (q + 1) : ℚ) * (y - 1 + q) - (N k q : ℚ) * ((q : ℚ) + 1)) :=
      mul_pos (div_pos hP hq1) (by linarith)
    linarith

/-- **T5.3(2)(b)**：`k ≥ 4`、`y > J_k := k(k² − k − 4)/2 − k + 2` 时 `(−1)^k·u_k(−y) > 0`；特别地 `u_k` 在
`(−∞, −J_k)` 上没有根。 -/
theorem upoly_eval_neg_sign {k : ℕ} (hk : 4 ≤ k) {y : ℚ}
    (hy : (k : ℚ) * ((k : ℚ) ^ 2 - k - 4) / 2 - k + 2 < y) :
    0 < (-1 : ℚ) ^ k * (upoly k).eval (-y) := by
  rw [upoly_eval_neg_eq_alt]
  refine alt_sum_pos (negTerm k y) ?_ (by omega) fun q hq => negTerm_lt_succ hk hy hq
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [negTerm, N_succ_zero j, Nat.cast_zero, zero_mul]

/-! ## 3. (c) 顶端两层：`u_k(−(s_k + 2)) ≠ 0` -/

/-- 辅助引理：`G_{−3} = 1 − 2x + 4x² + 2x³ − 3x⁴ + 2x⁵ + 2x⁶`。 -/
theorem gnegPoly_two :
    gnegPoly 2 = 1 - 2 * X + 4 * X ^ 2 + 2 * X ^ 3 - 3 * X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 := by
  show gnegPoly (1 + 1) = _
  rw [gnegPoly, gnegPoly_one]
  simp only [Nat.cast_one, map_add, map_one]
  ring

/-- **T5.3(2)**（c5a 定理 4.3 的第 4 高项）：`[x^{3n}]G_{−(n+2)} = (n+1)!`，即 `g_{j,3j−6} = (j−1)!`（`j ≥ 2`）。 -/
theorem coeff_gnegPoly_top_three (n : ℕ) : (gnegPoly (n + 1)).coeff (3 * n) = ((n + 1)! : ℚ) := by
  induction n with
  | zero =>
    rw [gnegPoly_one]
    simp [coeff_X, coeff_one, coeff_X_pow]
  | succ n ih =>
    have h1 : (gnegPoly (n + 1)).coeff (3 * n + 3) = ((n + 1)! : ℚ) := by
      have := coeff_gnegPoly_top (n + 1)
      rwa [show 3 * (n + 1) = 3 * n + 3 by ring] at this
    rw [show 3 * (n + 1) = 3 * n + 3 by ring, coeff_gnegPoly_succ_add_three, ih, h1,
      coeff_gnegPoly_top_one, Nat.factorial_succ (n + 1)]
    push_cast
    ring

/-- **T5.3(2)**（c5a 定理 4.3 的第 5 高项）：`[x^{3n+2}]G_{−(n+3)} = c(n+3,2) + c(n+3,3)`，即
`g_{j,3j−7} = c(j,2) + c(j,3)`（`j ≥ 3`）。 -/
theorem coeff_gnegPoly_top_four (n : ℕ) :
    (gnegPoly (n + 2)).coeff (3 * n + 2) =
      ((Nat.stirlingFirst (n + 3) 2 : ℕ) : ℚ) + ((Nat.stirlingFirst (n + 3) 3 : ℕ) : ℚ) := by
  induction n with
  | zero =>
    rw [gnegPoly_two]
    have e2 : Nat.stirlingFirst 3 2 = 3 := by decide
    have e3 : Nat.stirlingFirst 3 3 = 1 := by decide
    simp [coeff_X, coeff_one, coeff_X_pow, e2, e3]
    norm_num
  | succ n ih =>
    have h1 : (gnegPoly (n + 2)).coeff (3 * n + 2 + 3) = ((n + 2)! : ℚ) := by
      have := coeff_gnegPoly_top_one (n + 1)
      rwa [show 3 * (n + 1) + 2 = 3 * n + 2 + 3 by ring] at this
    have h2 : (gnegPoly (n + 2)).coeff (3 * n + 2 + 2) = -((Nat.stirlingFirst (n + 3) 2 : ℕ) : ℚ) := by
      have := coeff_gnegPoly_top_two (n + 1)
      rwa [show 3 * (n + 1) + 1 = 3 * n + 2 + 2 by ring] at this
    have s2 : Nat.stirlingFirst (n + 4) 2 = (n + 3) * Nat.stirlingFirst (n + 3) 2 + (n + 2)! := by
      rw [Nat.stirlingFirst_succ_succ (n + 3) 1, Nat.stirlingFirst_one_right]
    have s3 : Nat.stirlingFirst (n + 4) 3 = (n + 3) * Nat.stirlingFirst (n + 3) 3 + Nat.stirlingFirst (n + 3) 2 :=
      Nat.stirlingFirst_succ_succ (n + 3) 2
    show (gnegPoly (n + 2 + 1)).coeff (3 * n + 2 + 3) =
      ((Nat.stirlingFirst (n + 4) 2 : ℕ) : ℚ) + ((Nat.stirlingFirst (n + 4) 3 : ℕ) : ℚ)
    rw [coeff_gnegPoly_succ_add_three, ih, h1, h2, s2, s3]
    push_cast
    ring

/-- **T5.3(2)**（c5a 定理 4.3 的第 6 高项）：`[x^{3n+1}]G_{−(n+3)} = (n+2)! − c(n+3,2) − c(n+3,3)`，即
`g_{j,3j−8} = (j−1)! − c(j,2) − c(j,3)`（`j ≥ 3`）。 -/
theorem coeff_gnegPoly_top_five (n : ℕ) :
    (gnegPoly (n + 2)).coeff (3 * n + 1) =
      ((n + 2)! : ℚ) - ((Nat.stirlingFirst (n + 3) 2 : ℕ) : ℚ) - ((Nat.stirlingFirst (n + 3) 3 : ℕ) : ℚ) := by
  induction n with
  | zero =>
    rw [gnegPoly_two]
    have e2 : Nat.stirlingFirst 3 2 = 3 := by decide
    have e3 : Nat.stirlingFirst 3 3 = 1 := by decide
    simp [coeff_X, coeff_one, coeff_X_pow, e2, e3]
    norm_num
  | succ n ih =>
    have h1 : (gnegPoly (n + 2)).coeff (3 * n + 1 + 3) = -((Nat.stirlingFirst (n + 3) 2 : ℕ) : ℚ) := by
      have := coeff_gnegPoly_top_two (n + 1)
      rwa [show 3 * (n + 1) + 1 = 3 * n + 1 + 3 by ring] at this
    have h2 : (gnegPoly (n + 2)).coeff (3 * n + 1 + 2) = ((n + 2)! : ℚ) := by
      have := coeff_gnegPoly_top_three (n + 1)
      rwa [show 3 * (n + 1) = 3 * n + 1 + 2 by ring] at this
    have s2 : Nat.stirlingFirst (n + 4) 2 = (n + 3) * Nat.stirlingFirst (n + 3) 2 + (n + 2)! := by
      rw [Nat.stirlingFirst_succ_succ (n + 3) 1, Nat.stirlingFirst_one_right]
    have s3 : Nat.stirlingFirst (n + 4) 3 = (n + 3) * Nat.stirlingFirst (n + 3) 3 + Nat.stirlingFirst (n + 3) 2 :=
      Nat.stirlingFirst_succ_succ (n + 3) 2
    show (gnegPoly (n + 2 + 1)).coeff (3 * n + 1 + 3) =
      ((n + 3)! : ℚ) - ((Nat.stirlingFirst (n + 4) 2 : ℕ) : ℚ) - ((Nat.stirlingFirst (n + 4) 3 : ℕ) : ℚ)
    rw [coeff_gnegPoly_succ_add_three, ih, h1, h2, s2, s3, Nat.factorial_succ (n + 2)]
    push_cast
    ring

/-- 辅助引理：`(n+2)! < c(n+3, 2)`（`c(j,2) = (j−1)!·H_{j−1} > (j−1)!`，`j ≥ 3`）。 -/
theorem factorial_lt_stirlingFirst_two (n : ℕ) : (n + 2)! < Nat.stirlingFirst (n + 3) 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := stirlingFirst_two_succ_hs (n + 2)
    rw [show n + 2 + 2 = n + 1 + 3 by ring, show n + 2 + 1 = n + 3 by ring] at h
    rw [h, show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ (n + 2)]
    have hf := Nat.factorial_pos (n + 2)
    nlinarith

/-- **T5.3(2)(c)**：`u_k(−(s_k + 2)) ≠ 0`（`s_k = ⌊(k+2)/3⌋`，对一切 `k ≥ 0`）。 -/
theorem upoly_eval_neg_ne_zero_two (k : ℕ) :
    (upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 2)) ≠ 0 := by
  obtain ⟨a, ha | ha | ha⟩ : ∃ a, k = 3 * a ∨ k = 3 * a + 1 ∨ k = 3 * a + 2 := ⟨k / 3, by omega⟩
  · subst ha
    rw [show (3 * a + 2) / 3 = a by omega, show -((a : ℚ) + 2) = -(((a + 1 : ℕ) : ℚ) + 1) by push_cast; ring,
      upoly_eval_neg_succ, coeff_gnegPoly_top_three]
    exact_mod_cast Nat.factorial_ne_zero (a + 1)
  · subst ha
    rw [show (3 * a + 1 + 2) / 3 = a + 1 by omega,
      show -(((a + 1 : ℕ) : ℚ) + 2) = -(((a + 2 : ℕ) : ℚ) + 1) by push_cast; ring,
      upoly_eval_neg_succ, coeff_gnegPoly_top_five]
    have h : ((a + 2)! : ℚ) < ((Nat.stirlingFirst (a + 3) 2 : ℕ) : ℚ) := by
      exact_mod_cast factorial_lt_stirlingFirst_two a
    have h3 : (0 : ℚ) ≤ ((Nat.stirlingFirst (a + 3) 3 : ℕ) : ℚ) := Nat.cast_nonneg _
    exact ne_of_lt (by linarith)
  · subst ha
    rw [show (3 * a + 2 + 2) / 3 = a + 1 by omega,
      show -(((a + 1 : ℕ) : ℚ) + 2) = -(((a + 2 : ℕ) : ℚ) + 1) by push_cast; ring,
      upoly_eval_neg_succ, coeff_gnegPoly_top_four]
    have h : (0 : ℚ) < ((Nat.stirlingFirst (a + 3) 2 : ℕ) : ℚ) := by
      exact_mod_cast stirlingFirst_two_pos_hs (a + 1)
    have h3 : (0 : ℚ) ≤ ((Nat.stirlingFirst (a + 3) 3 : ℕ) : ℚ) := Nat.cast_nonneg _
    exact ne_of_gt (by linarith)

end A207123
