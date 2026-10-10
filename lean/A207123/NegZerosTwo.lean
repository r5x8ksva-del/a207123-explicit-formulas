import A207123.NegZeros

/-!
# 报告 T5.3(2)（猜想总表 A28 (i)）：`p = 2` 时同余条件的放宽

`NegZeros.lean` 的 `uInt_add_prime_pow`：`p` 素数、`p^e > k` 时 `u_k(m + p^e) ≡ u_k(m) (mod p)`。`notes/15` 注 1.1：
`p = 2` 时条件可放宽为 `2^e ≥ k − 1`（`k ≥ 4`）。原因：`q < 2^e` 的项照旧（`2 ∣ C(2^e, i)`，`0 < i < 2^e`）；
`q ≥ 2^e ≥ k − 1` 的项只有 `q ∈ {k − 1, k}`，而 `N(k,k) = 2`、`N(k,k−1) = k² − k − 4` 都是偶数。

* `N_even_top`：`k ≥ 4`、`k − 1 ≤ q ≤ k` 时 `2 ∣ N(k,q)`。
* `uInt_add_two_pow`：`k ≥ 4`、`2^e ≥ k − 1` 时 `u_k(m + 2^e) ≡ u_k(m) (mod 2)`；`uInt_add_mul_two_pow`。
* `uInt_neg_modEq_one_two`、`upoly_eval_neg_ne_zero_of_two_pow`：此时 `2^e ∣ j` 推出 `u_k(−j) ≡ 1 (mod 2)`，不为 0。
* `two_pow_factorization_lt_of_upoly_eval_neg_eq_zero`：`k ≥ 4`、`u_k(−j) = 0` 时 `j` 的 2-部分 `2^{v_2(j)} < k − 1`
  （`dvd_lcm_of_upoly_eval_neg_eq_zero` 只给出 `2^{v_2(j)} ≤ k`）。
-/

namespace A207123

open Polynomial Finset

/-- `k ≥ 4`、`k − 1 ≤ q ≤ k` 时 `N(k,q)` 是偶数（`N(k,k) = 2`，`N(k,k−1) = k² − k − 4`）。 -/
theorem N_even_top {k q : ℕ} (hk : 4 ≤ k) (hq1 : k - 1 ≤ q) (hq2 : q ≤ k) : (2 : ℤ) ∣ (N k q : ℤ) := by
  obtain rfl | rfl : q = k - 1 ∨ q = k := by omega
  · rw [N_subdiag k hk]
    rcases Int.even_or_odd (k : ℤ) with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨2 * t ^ 2 - t - 2, by rw [ht]; ring⟩
    · exact ⟨2 * t ^ 2 + t - 2, by rw [ht]; ring⟩
  · rw [N_diag _ (by omega)]
    norm_num

/-- **T5.3(2)(a)**（`p = 2` 的放宽）：`k ≥ 4`、`2^e ≥ k − 1` 时 `u_k(m + 2^e) ≡ u_k(m) (mod 2)`。 -/
theorem uInt_add_two_pow {k e : ℕ} (hk : 4 ≤ k) (he : k - 1 ≤ 2 ^ e) (m : ℤ) :
    uInt k (m + 2 ^ e) ≡ uInt k m [ZMOD 2] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd, uInt, uInt, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun q hq => ?_
  rw [← mul_sub]
  have hq' := Finset.mem_range.1 hq
  by_cases hlt : q < 2 ^ e
  · have h := choose_add_prime_pow_sub Nat.prime_two hlt (m + 1)
    rw [show m + 1 + ((2 ^ e : ℕ) : ℤ) = m + 2 ^ e + 1 by push_cast; ring] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _
  · exact Dvd.dvd.mul_right (N_even_top hk (by omega) (by omega)) _

theorem uInt_add_mul_two_pow {k e : ℕ} (hk : 4 ≤ k) (he : k - 1 ≤ 2 ^ e) (m : ℤ) (t : ℕ) :
    uInt k (m + t * 2 ^ e) ≡ uInt k m [ZMOD 2] := by
  induction t with
  | zero =>
    rw [Nat.cast_zero, zero_mul, add_zero]
  | succ t ih =>
    rw [show m + ((t + 1 : ℕ) : ℤ) * 2 ^ e = (m + t * 2 ^ e) + 2 ^ e by push_cast; ring]
    exact (uInt_add_two_pow hk he _).trans ih

/-- **T5.3(2)(a)**（`p = 2` 的放宽）：`k ≥ 4`、`2^e ≥ k − 1`、`2^e ∣ j` 时 `u_k(−j) ≡ 1 (mod 2)`。 -/
theorem uInt_neg_modEq_one_two {k e j : ℕ} (hk : 4 ≤ k) (he : k - 1 ≤ 2 ^ e) (hj : 2 ^ e ∣ j) :
    uInt k (-(j : ℤ)) ≡ 1 [ZMOD 2] := by
  obtain ⟨t, rfl⟩ := hj
  have h := uInt_add_mul_two_pow (k := k) hk he (-((2 ^ e * t : ℕ) : ℤ)) t
  rw [show -((2 ^ e * t : ℕ) : ℤ) + (t : ℤ) * 2 ^ e = 0 by push_cast; ring, uInt_zero] at h
  exact h.symm

/-- **T5.3(2)(a)**（`p = 2` 的放宽）：`k ≥ 4`、`2^e ≥ k − 1`、`2^e ∣ j` 时 `u_k(−j) ≠ 0`。 -/
theorem upoly_eval_neg_ne_zero_of_two_pow {k e j : ℕ} (hk : 4 ≤ k) (he : k - 1 ≤ 2 ^ e)
    (hj : 2 ^ e ∣ j) : (upoly k).eval (-(j : ℚ)) ≠ 0 := by
  rw [show -(j : ℚ) = ((-(j : ℤ) : ℤ) : ℚ) by push_cast; ring, upoly_eval_int]
  intro h0
  have h1 := uInt_neg_modEq_one_two hk he hj
  rw [show uInt k (-(j : ℤ)) = 0 by exact_mod_cast h0, Int.modEq_iff_dvd, sub_zero] at h1
  norm_num at h1

/-- **T5.3(2)(a)**（`p = 2` 的放宽）：`k ≥ 4`、`u_k(−j) = 0` 时 `j` 的 2-部分 `2^{v_2(j)} < k − 1`。 -/
theorem two_pow_factorization_lt_of_upoly_eval_neg_eq_zero {k j : ℕ} (hk : 4 ≤ k)
    (h : (upoly k).eval (-(j : ℚ)) = 0) : 2 ^ j.factorization 2 < k - 1 := by
  by_contra hlt
  exact upoly_eval_neg_ne_zero_of_two_pow hk (by omega) (Nat.ordProj_dvd j 2) h

end A207123
