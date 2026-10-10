import A207123.HNegOne

/-!
# `notes/16` 命题 4(i) 的乘积式：`h_k(−1) = 2(−1)^r ∏_l (1 + 2z_l)`（猜想总表 A29 (iii) 的一部分）

`k ≥ 2` 时，设 `z_1, …, z_r` 是 `n_k = Σ_q N(k,q)·z^{q−1}`（`nR`）的 `r = ⌊2k/3⌋` 个不等于 `−1` 的根（`card_roots_nR_ne`：
它们两两不同，个数恰为 `⌊2k/3⌋`），则 `h_k(−1) = 2(−1)^r ∏_l (1 + 2z_l)`（`hpoly_eval_neg_one_prod`）。
证明：`n_k` 只有实根，首项系数 `N(k,k) = 2`（`N_diag`），`−1` 是 `⌈k/3⌉ − 1` 重根（`count_neg_one_nR`），其余的根都是单根；
在 `−1/2` 处展开 `n_k = 2∏(z − a)`，`−1/2 − a = −(1 + 2a)/2`，再用 `h_k(−1) = 2^{k−1}·n_k(−1/2)`
（`hpoly_eval_neg_one_nrow`）与 `k − 1 = (⌈k/3⌉ − 1) + ⌊2k/3⌋`。
`k = 1` 时首项系数是 `N(1,1) = 1`，乘积式不成立：`h_1(−1) = 1`，右边是 `2`（`hpoly_one_eval_neg_one`）。
-/

namespace A207123

open Polynomial

/-- `n_k` 的全部根上 `∏(1 + 2a) = (−1)^{⌈k/3⌉−1}·∏_{z ≠ −1}(1 + 2z)`（`−1` 的重数见 `count_neg_one_nR`，其余根都是单根）。 -/
theorem prod_roots_nR_one_add_two {k : ℕ} (hk : 1 ≤ k) :
    ((nR k).roots.map fun a => 1 + 2 * a).prod =
      (-1) ^ ((nR k).roots.count (-1)) * ∏ z ∈ (nR k).roots.toFinset.erase (-1), (1 + 2 * z) := by
  simp only [Finset.prod_multiset_map_count]
  have hone : ∀ x ∈ (nR k).roots.toFinset.erase (-1),
      (1 + 2 * x) ^ (nR k).roots.count x = 1 + 2 * x := by
    intro x hx
    rw [Finset.mem_erase, Multiset.mem_toFinset] at hx
    have h1 := count_roots_nR_le_one hk hx.1
    have h2 := Multiset.count_pos.2 hx.2
    rw [show (nR k).roots.count x = 1 by omega, pow_one]
  by_cases hmem : (-1 : ℝ) ∈ (nR k).roots.toFinset
  · rw [← Finset.mul_prod_erase _ _ hmem, Finset.prod_congr rfl hone]
    norm_num
  · rw [Finset.erase_eq_of_notMem hmem,
      Multiset.count_eq_zero.2 (fun h => hmem (Multiset.mem_toFinset.2 h)), pow_zero, one_mul]
    exact Finset.prod_congr rfl fun x hx => hone x (by rwa [Finset.erase_eq_of_notMem hmem])

/-- **`notes/16` 命题 4(i) 的乘积式**：`k ≥ 2` 时 `h_k(−1) = 2(−1)^r ∏_l (1 + 2z_l)`，`z_l` 取遍 `n_k` 的不等于 `−1` 的根
（共 `r = ⌊2k/3⌋` 个，两两不同：`card_roots_nR_ne`）。 -/
theorem hpoly_eval_neg_one_prod {k : ℕ} (hk : 2 ≤ k) :
    (((hpoly k).eval (-1) : ℚ) : ℝ) =
      2 * (-1) ^ (2 * k / 3) * ∏ z ∈ (nR k).roots.toFinset.erase (-1), (1 + 2 * z) := by
  have hk1 : 1 ≤ k := by omega
  have hrr := realRooted_nR hk1
  have h1 : (((hpoly k).eval (-1) : ℚ) : ℝ) = 2 ^ (k - 1) * (nR k).eval (-1 / 2) := by
    have hn : (nR k).eval (-1 / 2) = (((nrowPoly k).eval (-1 / 2) : ℚ) : ℝ) := by
      have e : (-1 / 2 : ℝ) = algebraMap ℚ ℝ (-1 / 2) := by simp
      rw [nR_eq_map, eval_map, e, eval₂_at_apply, eq_ratCast]
    rw [hn, hpoly_eval_neg_one_nrow hk1, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  have hev : (nR k).eval (-1 / 2) =
      (nR k).leadingCoeff * ((nR k).roots.map fun a => -1 / 2 - a).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hrr.2]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub,
      eval_X]
  have hmul : ((nR k).roots.map fun a => -1 / 2 - a).prod =
      (-1 / 2) ^ Multiset.card (nR k).roots * ((nR k).roots.map fun a => 1 + 2 * a).prod := by
    rw [show (fun a : ℝ => -1 / 2 - a) = fun a => (-1 / 2) * (1 + 2 * a) by funext a; ring,
      Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
  have hcard : Multiset.card (nR k).roots = k - 1 := hrr.2.trans (natDegree_nR hk1)
  have hlc : (nR k).leadingCoeff = 2 := by
    rw [leadingCoeff_nR hk1, N_diag k hk]
    norm_num
  have h2 : (2 : ℝ) ^ (k - 1) * (-1 / 2) ^ (k - 1) = (-1) ^ (k - 1) := by
    rw [← mul_pow]
    norm_num
  have hsign : (-1 : ℝ) ^ (k - 1) * (-1) ^ ((k + 2) / 3 - 1) = (-1) ^ (2 * k / 3) := by
    rw [← pow_add, show k - 1 + ((k + 2) / 3 - 1) = 2 * k / 3 + 2 * ((k + 2) / 3 - 1) by omega, pow_add,
      pow_mul]
    norm_num
  rw [h1, hev, hmul, prod_roots_nR_one_add_two hk1, hlc, hcard, count_neg_one_nR hk1]
  linear_combination
    (2 * (-1 : ℝ) ^ ((k + 2) / 3 - 1) * ∏ z ∈ (nR k).roots.toFinset.erase (-1), (1 + 2 * z)) * h2 +
      (2 * ∏ z ∈ (nR k).roots.toFinset.erase (-1), (1 + 2 * z)) * hsign

/-- `k = 1` 时乘积式不成立：`h_1(−1) = 1`（而 `n_1 = 1` 没有根，右边是 `2`）。 -/
theorem hpoly_one_eval_neg_one : (hpoly 1).eval (-1) = 1 := by
  rw [hpoly_one, eval_one]

end A207123
