import A207123.RootLocation

/-!
# 报告 T5.3(7)（猜想总表 A29 (iii) 的前两句）：`h_k(−1)` 的公式与符号

`notes/16` 命题 4：
* (i) `hpoly_eval_neg_one`：`k ≥ 1` 时 `h_k(−1) = Σ_{q=1}^{k} (−1)^{q−1}·2^{k−q}·N(k,q)`（`h_k(t) = Σ_q N(k,q)·t^{q−1}(1−t)^{k−q}`
  取 `t = −1`）；`hpoly_eval_neg_one_nrow`：`h_k(−1) = 2^{k−1}·n_k(−1/2)`（`n_k = Σ_q N(k,q)·z^{q−1}`，`nrowPoly`）。
* (ii) `hpoly_eval_neg_one_sign`：`h_k(−1) ≠ 0` 时 `h_k(−1)` 的符号是 `(−1)^{#{h_k 在 (−1,0) 中的根}}`（`h_k` 只有实根，
  `h_k(0) = 1`，所以 `h_k(−1)·h_k(0) = lc(h_k)²·∏_t t(t+1)`，而 `t(t+1) < 0` 恰当 `−1 < t < 0`；辅助引理
  `prod_mul_add_one_sign`）；`hpoly_two_eval_neg_one`：`h_2(−1) = 0`。
命题 4(i) 的乘积式 `h_k(−1) = 2(−1)^r∏_l(1+2z_l)`、(ii) 中 `3 ≤ k ≤ 1000` 时 `h_k(−1) ≠ 0` 的计算、(iii) 的 Gevrey 型上界与
(★)（猜想总表 A30）不在这里。
-/

namespace A207123

open Polynomial

/-- **`notes/16` 命题 4(i)**：`k ≥ 1` 时 `h_k(−1) = Σ_{q=1}^{k} (−1)^{q−1}·2^{k−q}·N(k,q)`。 -/
theorem hpoly_eval_neg_one {k : ℕ} (hk : 1 ≤ k) :
    (hpoly k).eval (-1) = ∑ q ∈ Finset.Icc 1 k, (-1) ^ (q - 1) * 2 ^ (k - q) * (N k q : ℚ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hpoly_succ, eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  rw [show (1 : ℚ) - -1 = 2 by norm_num]
  ring

/-- **`notes/16` 命题 4(i)**：`k ≥ 1` 时 `h_k(−1) = 2^{k−1}·n_k(−1/2)`。 -/
theorem hpoly_eval_neg_one_nrow {k : ℕ} (hk : 1 ≤ k) :
    (hpoly k).eval (-1) = 2 ^ (k - 1) * (nrowPoly k).eval (-1 / 2) := by
  rw [hpoly_eval_neg_one hk, nrowPoly, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_Icc] at hq
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have e : (2 : ℚ) ^ (q - 1) * (1 / 2) ^ (q - 1) = 1 := by rw [← mul_pow]; norm_num
  rw [show k - 1 = (k - q) + (q - 1) by omega, pow_add,
    show ((-1 : ℚ) / 2) = (-1) * (1 / 2) by ring, mul_pow]
  linear_combination (-((-1 : ℚ) ^ (q - 1) * 2 ^ (k - q) * (N k q : ℚ))) * e

/-- `h_2(−1) = 0`（`h_2 = 1 + t`）。 -/
theorem hpoly_two_eval_neg_one : (hpoly 2).eval (-1) = 0 := by
  rw [hpoly_eval_neg_one (by norm_num), show Finset.Icc 1 2 = {1, 2} by decide,
    Finset.sum_pair (by norm_num), N_init.2.2.1, N_init.2.2.2]
  norm_num

/-- 辅助引理：实数多重集 `r` 不含 `0` 与 `−1` 时，`(−1)^{#{t ∈ r : −1 < t < 0}}·∏_{t∈r} t(t+1) > 0`。 -/
theorem prod_mul_add_one_sign (r : Multiset ℝ) (h : ∀ t ∈ r, t ≠ 0 ∧ t ≠ -1) :
    0 < (-1) ^ Multiset.card (r.filter fun t => -1 < t ∧ t < 0)
      * (r.map fun t => t * (t + 1)).prod := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    have ha := h a (Multiset.mem_cons_self a r)
    have ih := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    rw [Multiset.map_cons, Multiset.prod_cons]
    by_cases hin : -1 < a ∧ a < 0
    · rw [Multiset.filter_cons_of_pos (p := fun t : ℝ => -1 < t ∧ t < 0) _ hin, Multiset.card_cons, pow_succ]
      have hneg : a * (a + 1) < 0 := mul_neg_of_neg_of_pos hin.2 (by linarith [hin.1])
      have e : (-1 : ℝ) ^ Multiset.card (r.filter fun t => -1 < t ∧ t < 0) * -1
          * (a * (a + 1) * (r.map fun t => t * (t + 1)).prod)
          = (-(a * (a + 1))) * ((-1) ^ Multiset.card (r.filter fun t => -1 < t ∧ t < 0)
            * (r.map fun t => t * (t + 1)).prod) := by ring
      rw [e]
      exact mul_pos (by linarith) ih
    · rw [Multiset.filter_cons_of_neg (p := fun t : ℝ => -1 < t ∧ t < 0) _ hin]
      have hpos : 0 < a * (a + 1) := by
        rcases lt_or_gt_of_ne ha.1 with h1 | h1
        · have h2 : a < -1 := by
            by_contra h3
            exact hin ⟨lt_of_le_of_ne (not_lt.1 h3) (Ne.symm ha.2), h1⟩
          exact mul_pos_of_neg_of_neg h1 (by linarith)
        · exact mul_pos h1 (by linarith)
      have e : (-1 : ℝ) ^ Multiset.card (r.filter fun t => -1 < t ∧ t < 0)
          * (a * (a + 1) * (r.map fun t => t * (t + 1)).prod)
          = (a * (a + 1)) * ((-1) ^ Multiset.card (r.filter fun t => -1 < t ∧ t < 0)
            * (r.map fun t => t * (t + 1)).prod) := by ring
      rw [e]
      exact mul_pos hpos ih

/-- **`notes/16` 命题 4(ii)**：`h_k(−1) ≠ 0` 时，`h_k(−1)` 的符号是 `(−1)^{#{h_k 在 (−1, 0) 中的根}}`（根计重数；
`h_k` 的根都是实单根，`HStruct`/`SimpleRoots` 的 `hR_realRooted_nodup`）。 -/
theorem hpoly_eval_neg_one_sign {k : ℕ} (h : (hpoly k).eval (-1) ≠ 0) :
    0 < (-1) ^ Multiset.card ((hR k).roots.filter fun t => -1 < t ∧ t < 0)
      * (((hpoly k).eval (-1) : ℚ) : ℝ) := by
  have hrr := (hR_realRooted_nodup k).1
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C hrr.2
  have hev : ∀ x : ℝ, (hR k).eval x
      = (hR k).leadingCoeff * ((hR k).roots.map fun a => x - a).prod := by
    intro x
    conv_lhs => rw [← hsplit]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub,
      eval_X]
  have h0 : (hR k).eval 0 = 1 := by
    have e : (0 : ℝ) = algebraMap ℚ ℝ 0 := by simp
    rw [hR, eval_map, e, eval₂_at_apply, hpoly_eval_zero_eq_one, map_one]
  have hm1 : (hR k).eval (-1) = (((hpoly k).eval (-1) : ℚ) : ℝ) := by
    have e : (-1 : ℝ) = algebraMap ℚ ℝ (-1) := by simp
    rw [hR, eval_map, e, eval₂_at_apply, eq_ratCast]
  have hroots : ∀ t ∈ (hR k).roots, t ≠ 0 ∧ t ≠ -1 := by
    intro t ht
    have hz := ((mem_roots (hR_ne_zero k)).1 ht).eq_zero
    refine ⟨fun h0' => ?_, fun h1' => ?_⟩
    · rw [h0', h0] at hz
      exact one_ne_zero hz
    · rw [h1', hm1] at hz
      exact h (by exact_mod_cast hz)
  have hprod := prod_mul_add_one_sign _ hroots
  have hlc : (hR k).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (hR_ne_zero k)
  have key : (hR k).eval (-1) * (hR k).eval 0
      = (hR k).leadingCoeff ^ 2 * ((hR k).roots.map fun t => t * (t + 1)).prod := by
    rw [hev, hev, mul_mul_mul_comm, ← Multiset.prod_map_mul, sq]
    congr 1
    congr 1
    exact Multiset.map_congr rfl fun t _ => by ring
  rw [h0, mul_one] at key
  rw [← hm1, key, mul_left_comm]
  have hl2 : 0 < (hR k).leadingCoeff ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hlc))
  exact mul_pos hl2 hprod

end A207123
