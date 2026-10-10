import A207123.LogConcave

/-!
# 论文引理 8.12 中 `λ_k` 的符号与推论 8.13（`h_k` 的根的位置与系数的变号次数）

* 论文引理 8.12：`n_k = (1+z)^{a_k}·m_k`，`m_k(−1) ≠ 0`，`λ_k = m_k(−1)`。`a_k = ⌈k/3⌉ − 1`、`deg h_k = ⌊2k/3⌋` 与 `h_k`
  首项系数的符号原来已形式化（`HStruct.lean`，论文用的是另一个证明）；这里补上 `λ_k` 的符号：
  `lemma_minusone_sign`（对任何满足 `n_k = (1+z)^{a_k}·m` 的 `m`），`lemma_minusone`（引理 8.12 合在一起）。
  证明：`m_k = Σ_{i≤g} h_{k,i} z^i (1+z)^{g−i}`（`g = ⌊2k/3⌋`，由 `nrowPoly_eq` 与 `hpoly_coeff_vanish`），
  所以 `λ_k = (−1)^g·lc(h_k)`，再用 `lc(h_k)` 的符号 `(−1)^{⌊k/3⌋}`。
* 论文推论 8.13：`nBelow_nR`（`n_k` 在 `(−∞, −1)` 中恰有 `⌊k/3⌋` 个根）、`card_roots_hR_gt_one`（`h_k` 在 `(1, ∞)` 中恰有
  `⌊k/3⌋` 个根）、`card_roots_hR_neg`（其余 `⌊(k+1)/3⌋` 个根都是负数）、`signVariations_hpoly`（`h_k` 的系数序列恰变号
  `⌊k/3⌋` 次）；`cor_hk_signs` 合在一起。证明按论文：`ν_k`（`n_k` 在 `(−∞,−1)` 中的根数）由 (α_k) 每步增 0 或 1，
  奇偶性由 `λ_k` 的符号决定（`nBelow_nR_parity`；论文对 `k ≡ 1 (mod 3)` 改用 `−1` 的重数加一，这里三种情形都用奇偶性）；
  `h_k` 的根是 `z/(1+z)`（`z` 取 `n_k` 除 `−1` 外的根，`hR_roots_toFinset`）。变号次数：Mathlib 的 Descartes 法则
  `roots_countP_pos_le_signVariations` 给出 `≥`；`≤` 由组合引理 `signVariations_add_comp_neg_X_le`
  （常数项非零时 `V(P) + V(P(−x)) ≤ deg P`，对次数归纳，用 `signVariations_eq_eraseLead_add_ite`）与对 `P(−x)` 的
  Descartes 法则得到（实根多项式的 Descartes 法则取等号）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 论文引理 8.12：`λ_k` 的符号 -/

/-- 论文引理 8.12 的 `m_k`（有理系数）：`m_k = Σ_{i ≤ g} h_{k,i} z^i (1+z)^{g−i}`，`g = ⌊2k/3⌋ = deg h_k`。 -/
def mPoly (k : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (2 * k / 3 + 1), C ((hpoly k).coeff i) * X ^ i * (1 + X) ^ (2 * k / 3 - i)

/-- `n_k = (1+z)^{a_k}·m_k`，`a_k = ⌊(k+2)/3⌋ − 1 = ⌈k/3⌉ − 1`（`k ≥ 1`）。 -/
theorem nrowPoly_eq_mul_mPoly {k : ℕ} (hk : 1 ≤ k) :
    nrowPoly k = (1 + X) ^ ((k + 2) / 3 - 1) * mPoly k := by
  rw [nrowPoly_eq hk, mPoly, Finset.mul_sum]
  symm
  rw [Finset.sum_subset (s₁ := Finset.range (2 * k / 3 + 1)) (s₂ := Finset.range k)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hig : i ≤ 2 * k / 3
    · have hp : (1 + X : ℚ[X]) ^ (k - 1 - i) =
          (1 + X) ^ ((k + 2) / 3 - 1) * (1 + X) ^ (2 * k / 3 - i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring
    · rw [hpoly_coeff_vanish k ((k + 2) / 3) le_rfl i (by omega)]
      simp
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hni
    rw [Finset.mem_range] at hi hni
    rw [hpoly_coeff_vanish k ((k + 2) / 3) le_rfl i (by omega)]
    simp

/-- `m_k(−1) = (−1)^{⌊2k/3⌋}·lc(h_k)`。 -/
theorem mPoly_eval_neg_one (k : ℕ) :
    (mPoly k).eval (-1) = (-1) ^ (2 * k / 3) * (hpoly k).leadingCoeff := by
  rw [mPoly, eval_finsetSum, Finset.sum_eq_single (2 * k / 3)]
  · simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.sub_self, pow_zero, mul_one]
    rw [leadingCoeff, natDegree_hpoly]
    ring
  · intro i hi hne
    rw [Finset.mem_range] at hi
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
    rw [show (1 : ℚ) + -1 = 0 by norm_num, zero_pow (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- 关于 `⌊k/3⌋` 的几个恒等式（Hermite 恒等式 `⌊k/3⌋ + ⌊(k+1)/3⌋ + ⌊(k+2)/3⌋ = k` 等）。Lean 的 `omega` 没有实现完整
的 omega 算法，含几个不同的 `⌊·/3⌋` 时常常证不出来，所以先按 `k mod 3` 分情形证好。 -/
theorem div_three_identities (k : ℕ) :
    k / 3 + (k + 1) / 3 + (k + 2) / 3 = k ∧ 2 * k / 3 = k / 3 + (k + 1) / 3 ∧
    ((k + 1) / 3 + 2 * k / 3) % 2 = (k / 3) % 2 ∧ (k / 3 + if k % 3 = 2 then 1 else 0) = (k + 1) / 3 := by
  obtain ⟨b, rfl | rfl | rfl⟩ : ∃ b, k = 3 * b ∨ k = 3 * b + 1 ∨ k = 3 * b + 2 := ⟨k / 3, by omega⟩ <;>
    exact ⟨by omega, by omega, by omega, by split_ifs <;> omega⟩

/-- 论文引理 8.12 中 `λ_k` 的符号的一个等价写法：`k ≥ 1`，`n_k = (1+z)^{a_k}·m`，则 `λ_k := m(−1) ≠ 0`，符号为
`(−1)^{⌊(k+1)/3⌋}`。 -/
theorem lemma_minusone_sign_alt {k : ℕ} (hk : 1 ≤ k) {m : ℚ[X]}
    (hm : nrowPoly k = (1 + X) ^ ((k + 2) / 3 - 1) * m) :
    m.eval (-1) ≠ 0 ∧ 0 < (-1) ^ ((k + 1) / 3) * m.eval (-1) := by
  have h1X : (1 + X : ℚ[X]) ≠ 0 := by
    rw [add_comm, ← C_1]
    exact X_add_C_ne_zero 1
  have hmeq : m = mPoly k :=
    mul_left_cancel₀ (pow_ne_zero _ h1X) (hm.symm.trans (nrowPoly_eq_mul_mPoly hk))
  subst hmeq
  rw [mPoly_eval_neg_one]
  have hlc := leadingCoeff_hpoly_sign k
  have hlc0 : (hpoly k).leadingCoeff ≠ 0 := fun h => by
    rw [h, mul_zero] at hlc
    exact lt_irrefl _ hlc
  have hmod := (div_three_identities k).2.2.1
  have e : ((-1 : ℚ)) ^ ((k + 1) / 3) * ((-1) ^ (2 * k / 3) * (hpoly k).leadingCoeff) =
      (-1) ^ ((k + 1) / 3 + 2 * k / 3) * (hpoly k).leadingCoeff := by
    ring
  refine ⟨mul_ne_zero (pow_ne_zero _ (by norm_num)) hlc0, ?_⟩
  rw [e, neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two]
  exact hlc

/-- **论文引理 8.12 中 `λ_k` 的符号**：`k ≥ 1`，`n_k = (1+z)^{a_k}·m`（`a_k = ⌊(k+2)/3⌋ − 1 = ⌈k/3⌉ − 1`），则
`λ_k := m(−1) ≠ 0`，符号为 `(−1)^{⌊k/3⌋}`（`k ≢ 2 (mod 3)`）或 `(−1)^{⌊k/3⌋+1}`（`k ≡ 2 (mod 3)`）。 -/
theorem lemma_minusone_sign {k : ℕ} (hk : 1 ≤ k) {m : ℚ[X]}
    (hm : nrowPoly k = (1 + X) ^ ((k + 2) / 3 - 1) * m) :
    m.eval (-1) ≠ 0 ∧ 0 < (-1) ^ (k / 3 + if k % 3 = 2 then 1 else 0) * m.eval (-1) := by
  rw [(div_three_identities k).2.2.2]
  exact lemma_minusone_sign_alt hk hm

/-- **论文引理 8.12**（合在一起）：`k ≥ 1` 时 `n_k` 在 `−1` 处的重数 `a_k = ⌈k/3⌉ − 1`；对 `n_k = (1+z)^{a_k}·m`，
`λ_k = m(−1) ≠ 0` 且符号为 `(−1)^{⌊k/3⌋}`（`k ≢ 2`）或 `(−1)^{⌊k/3⌋+1}`（`k ≡ 2 (mod 3)`）；`deg h_k = ⌊2k/3⌋`；`h_k` 的
首项系数的符号为 `(−1)^{⌊k/3⌋}`。 -/
theorem lemma_minusone {k : ℕ} (hk : 1 ≤ k) :
    (nrowPoly k).rootMultiplicity (-1) = ⌈(k : ℚ) / 3⌉₊ - 1 ∧
    (∀ m : ℚ[X], nrowPoly k = (1 + X) ^ (⌈(k : ℚ) / 3⌉₊ - 1) * m →
      m.eval (-1) ≠ 0 ∧ 0 < (-1) ^ (k / 3 + if k % 3 = 2 then 1 else 0) * m.eval (-1)) ∧
    (hpoly k).natDegree = 2 * k / 3 ∧ 0 < (-1) ^ (k / 3) * (hpoly k).leadingCoeff := by
  refine ⟨rootMultiplicity_nrowPoly_ceil hk, fun m hm => ?_, natDegree_hpoly k, leadingCoeff_hpoly_sign k⟩
  rw [natCeil_div_three] at hm
  exact lemma_minusone_sign hk hm

/-! ## 2. 实系数的 `m_k` -/

/-- `m_k` 映到 `ℝ[X]`。 -/
def mR (k : ℕ) : ℝ[X] := (mPoly k).map (algebraMap ℚ ℝ)

theorem nR_eq_mul_mR {k : ℕ} (hk : 1 ≤ k) : nR k = (1 + X) ^ ((k + 2) / 3 - 1) * mR k := by
  rw [nR_eq_map, nrowPoly_eq_mul_mPoly hk, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, map_X, mR]

theorem realRooted_mR {k : ℕ} (hk : 1 ≤ k) : RealRooted (mR k) := by
  have h := realRooted_nR hk
  rw [nR_eq_mul_mR hk] at h
  exact h.of_mul_right

theorem leadingCoeff_mR_pos {k : ℕ} (hk : 1 ≤ k) : 0 < (mR k).leadingCoeff := by
  have h := leadingCoeff_nR_pos hk
  rw [nR_eq_mul_mR hk, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_one_add_X, one_pow, one_mul] at h
  exact h

theorem mR_eval_neg_one (k : ℕ) : (mR k).eval (-1) = (((mPoly k).eval (-1) : ℚ) : ℝ) := by
  have h : (-1 : ℝ) = algebraMap ℚ ℝ (-1) := by simp
  rw [mR, eval_map, h, eval₂_at_apply, eq_ratCast]

theorem nAbove_one_add_X_pow (a : ℕ) : nAbove ((1 + X : ℝ[X]) ^ a) (-1) = 0 := by
  induction a with
  | zero =>
    rw [pow_zero]
    unfold nAbove
    rw [roots_one]
    simp
  | succ a ih =>
    rw [pow_succ, nAbove_mul (pow_ne_zero _ realRooted_one_add_X.1) realRooted_one_add_X.1, ih,
      one_add_X_eq, nAbove_X_sub_C, ite_eq_right (lt_irrefl _)]

theorem nAbove_nR_eq_mR {k : ℕ} (hk : 1 ≤ k) : nAbove (nR k) (-1) = nAbove (mR k) (-1) := by
  rw [nR_eq_mul_mR hk, nAbove_mul (pow_ne_zero _ realRooted_one_add_X.1) (realRooted_mR hk).1,
    nAbove_one_add_X_pow, zero_add]

/-- 两个正的乘积 `(−1)^A·x`、`(−1)^B·x` 推出 `A ≡ B (mod 2)`。 -/
theorem neg_one_pow_mod_two {A B : ℕ} {x : ℝ} (h1 : 0 < (-1) ^ A * x) (h2 : 0 < (-1) ^ B * x) :
    A % 2 = B % 2 := by
  rcases Nat.even_or_odd A with hA | hA <;> rcases Nat.even_or_odd B with hB | hB
  · rw [Nat.even_iff.1 hA, Nat.even_iff.1 hB]
  · rw [hA.neg_one_pow, one_mul] at h1
    rw [hB.neg_one_pow, neg_one_mul] at h2
    linarith
  · rw [hA.neg_one_pow, neg_one_mul] at h1
    rw [hB.neg_one_pow, one_mul] at h2
    linarith
  · rw [Nat.odd_iff.1 hA, Nat.odd_iff.1 hB]

/-- `n_k` 在 `(−1, ∞)` 中的根数的奇偶性：`≡ ⌊(k+1)/3⌋`（由 `λ_k` 的符号与符号引理 `sign_eval`）。 -/
theorem nAbove_nR_parity {k : ℕ} (hk : 1 ≤ k) : nAbove (nR k) (-1) % 2 = ((k + 1) / 3) % 2 := by
  have hm := lemma_minusone_sign_alt hk (nrowPoly_eq_mul_mPoly hk)
  have hq : (0 : ℝ) < (((-1 : ℚ) ^ ((k + 1) / 3) * (mPoly k).eval (-1) : ℚ) : ℝ) := by
    exact_mod_cast hm.2
  push_cast at hq
  have hreal : 0 < (-1 : ℝ) ^ ((k + 1) / 3) * (mR k).eval (-1) := by
    rw [mR_eval_neg_one]
    exact hq
  have hne : (mR k).eval (-1) ≠ 0 := by
    rw [mR_eval_neg_one]
    exact_mod_cast hm.1
  have hs := sign_eval (realRooted_mR hk) (leadingCoeff_mR_pos hk) hne
  rw [nAbove_nR_eq_mR hk]
  exact neg_one_pow_mod_two hs hreal

/-! ## 3. `n_k` 在 `(−∞, −1)` 中的根数 -/

/-- `p` 在 `(−∞, a)` 中的根数（计重数）。 -/
def nBelow (p : ℝ[X]) (a : ℝ) : ℕ := Multiset.card (p.roots.filter (· < a))

theorem card_filter_lt_add_count_add (s : Multiset ℝ) (a : ℝ) :
    Multiset.card (s.filter (· < a)) + s.count a + Multiset.card (s.filter (a < ·)) = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rcases lt_trichotomy b a with h | h | h
    · rw [Multiset.filter_cons_of_pos (p := fun x => x < a) _ h,
        Multiset.filter_cons_of_neg (p := fun x => a < x) _ (not_lt.2 h.le),
        Multiset.count_cons_of_ne (ne_of_gt h), Multiset.card_cons, Multiset.card_cons]
      omega
    · rw [h, Multiset.filter_cons_of_neg (p := fun x => x < a) _ (lt_irrefl a),
        Multiset.filter_cons_of_neg (p := fun x => a < x) _ (lt_irrefl a),
        Multiset.count_cons_self, Multiset.card_cons]
      omega
    · rw [Multiset.filter_cons_of_neg (p := fun x => x < a) _ (not_lt.2 h.le),
        Multiset.filter_cons_of_pos (p := fun x => a < x) _ h,
        Multiset.count_cons_of_ne (ne_of_lt h), Multiset.card_cons, Multiset.card_cons]
      omega

theorem nBelow_add_count_add_nAbove (p : ℝ[X]) (a : ℝ) :
    nBelow p a + p.roots.count a + nAbove p a = Multiset.card p.roots :=
  card_filter_lt_add_count_add p.roots a

/-- `g ≪ f` 且 `f` 比 `g` 多一个根时，`f` 在 `(−∞, a)` 中的根数比 `g` 多 0 或 1。 -/
theorem Interlaces.nBelow_le {g f : ℝ[X]} (h : Interlaces g f)
    (hc : Multiset.card f.roots = Multiset.card g.roots + 1) (a : ℝ) :
    nBelow g a ≤ nBelow f a ∧ nBelow f a ≤ nBelow g a + 1 := by
  obtain ⟨x, hx, hxr⟩ := exists_just_below f g a
  have hf := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inl hr))
  have hg := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inr hr))
  have pf := nBelow_add_count_add_nAbove f a
  have pg := nBelow_add_count_add_nAbove g a
  have h1 := h.2.2 x
  omega

/-- `ν_k` 的奇偶性：`n_k` 在 `(−∞, −1)` 中的根数 `≡ ⌊k/3⌋ (mod 2)`。 -/
theorem nBelow_nR_parity {k : ℕ} (hk : 1 ≤ k) : nBelow (nR k) (-1) % 2 = (k / 3) % 2 := by
  have hp := nAbove_nR_parity hk
  have hsum := nBelow_add_count_add_nAbove (nR k) (-1)
  rw [count_neg_one_nR hk, (realRooted_nR hk).2, natDegree_nR hk] at hsum
  have hH := (div_three_identities k).1
  have h1 : 1 ≤ (k + 2) / 3 := by omega
  omega

/-- **论文推论 8.13 证明中的 `ν_k`**（也是注记 8.16 的最后一句）：`k ≥ 1` 时 `n_k` 在 `(−∞, −1)` 中恰有 `⌊k/3⌋` 个根
（计重数）。 -/
theorem nBelow_nR {k : ℕ} (hk : 1 ≤ k) : nBelow (nR k) (-1) = k / 3 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · show nBelow (nR 1) (-1) = 0
      rw [nR_one]
      unfold nBelow
      rw [roots_C]
      simp
    · have ih := ih hk0
      have hα := alpha_rel (k := k + 1) (by omega)
      rw [show k + 1 - 1 = k by omega] at hα
      have hc : Multiset.card (nR (k + 1)).roots = Multiset.card (nR k).roots + 1 := by
        rw [(realRooted_nR hk).2, (realRooted_nR hk0).2, natDegree_nR hk, natDegree_nR hk0]
        omega
      have hb := hα.nBelow_le hc (-1)
      have hp := nBelow_nR_parity hk
      omega

/-! ## 4. `h_k` 的根的位置（论文推论 8.13 的前两句） -/

theorem zToT_injOn (k : ℕ) : Set.InjOn zToT ((nR k).roots.toFinset.erase (-1) : Set ℝ) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_erase] at hx hy
  have hx1 : 1 + x ≠ 0 := fun h => hx.1 (by linarith)
  have hy1 : 1 + y ≠ 0 := fun h => hy.1 (by linarith)
  simp only [zToT] at hxy
  rw [div_eq_div_iff hx1 hy1] at hxy
  linear_combination hxy

/-- `h_k` 的根恰是 `z/(1+z)`，`z` 取 `n_k` 除 `−1` 外的不同的根（`k ≥ 1`）。 -/
theorem hR_roots_toFinset {k : ℕ} (hk : 1 ≤ k) :
    (hR k).roots.toFinset = ((nR k).roots.toFinset.erase (-1)).image zToT := by
  have hne := hR_ne_zero k
  have hsub : ((nR k).roots.toFinset.erase (-1)).image zToT ⊆ (hR k).roots.toFinset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [Finset.mem_erase, Multiset.mem_toFinset] at hz
    have hz1 : 1 + z ≠ 0 := fun h => hz.1 (by linarith)
    have h0 : (nR k).eval z = 0 := (isRoot_of_mem_roots hz.2).eq_zero
    rw [nR_eval_hR hk z hz1] at h0
    have h1 : (hR k).eval (zToT z) = 0 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hz1)
    exact Multiset.mem_toFinset.2 ((mem_roots hne).2 h1)
  have hcard : ((hR k).roots.toFinset).card ≤ (((nR k).roots.toFinset.erase (-1)).image zToT).card := by
    rw [Finset.card_image_of_injOn (zToT_injOn k), card_roots_nR_ne hk]
    calc ((hR k).roots.toFinset).card ≤ Multiset.card (hR k).roots := Multiset.toFinset_card_le _
      _ ≤ (hR k).natDegree := card_roots' _
      _ = 2 * k / 3 := by rw [hR, natDegree_map, natDegree_hpoly]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

theorem one_lt_zToT_iff {z : ℝ} (hz : z ≠ -1) : 1 < zToT z ↔ z < -1 := by
  unfold zToT
  rcases lt_or_gt_of_ne hz with h | h
  · have h1 : 1 + z < 0 := by linarith
    constructor
    · intro _
      exact h
    · intro _
      rw [lt_div_iff_of_neg h1]
      linarith
  · have h1 : 0 < 1 + z := by linarith
    constructor
    · intro hlt
      rw [lt_div_iff₀ h1] at hlt
      linarith
    · intro h'
      linarith

theorem zToT_neg_iff {z : ℝ} (hz : z ≠ -1) (hz0 : z < 0) : zToT z < 0 ↔ -1 < z := by
  unfold zToT
  rcases lt_or_gt_of_ne hz with h | h
  · have h1 : 1 + z < 0 := by linarith
    constructor
    · intro hlt
      have := div_pos_of_neg_of_neg hz0 h1
      linarith
    · intro h'
      linarith
  · have h1 : 0 < 1 + z := by linarith
    constructor
    · intro _
      exact h
    · intro _
      exact div_neg_of_neg_of_pos hz0 h1

/-- `h_k` 满足条件 `p` 的根数（计重数，根两两不同）等于 `n_k` 除 `−1` 外满足 `p(z/(1+z))` 的不同的根的个数。 -/
theorem card_filter_roots_hR {k : ℕ} (hk : 1 ≤ k) (p : ℝ → Prop) [DecidablePred p] :
    Multiset.card ((hR k).roots.filter p) =
      (((nR k).roots.toFinset.erase (-1)).filter fun z => p (zToT z)).card := by
  have hnd := (hR_realRooted_nodup k).2
  rw [← Multiset.toFinset_card_of_nodup (Multiset.Nodup.filter p hnd), Multiset.toFinset_filter,
    hR_roots_toFinset hk, Finset.filter_image,
    Finset.card_image_of_injOn ((zToT_injOn k).mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))]

/-- `n_k` 满足条件 `p`（`p(−1)` 不成立）的根数（计重数）等于满足 `p` 的不同的根的个数（这些根都是单根）。 -/
theorem card_filter_roots_nR {k : ℕ} (hk : 1 ≤ k) (p : ℝ → Prop) [DecidablePred p] (hp : ¬ p (-1)) :
    Multiset.card ((nR k).roots.filter p) = (((nR k).roots.toFinset.erase (-1)).filter p).card := by
  have hnd : ((nR k).roots.filter p).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro x
    rw [Multiset.count_filter]
    split_ifs with h
    · exact count_roots_nR_le_one hk fun hx => hp (hx ▸ h)
    · exact zero_le_one
  rw [← Multiset.toFinset_card_of_nodup hnd, Multiset.toFinset_filter, Finset.filter_erase,
    Finset.erase_eq_of_notMem (by rw [Finset.mem_filter]; exact fun h => hp h.2)]

/-- **论文推论 8.13**：`k ≥ 1` 时 `h_k` 在 `(1, ∞)` 中恰有 `⌊k/3⌋` 个根（计重数；根都是单根）。 -/
theorem card_roots_hR_gt_one {k : ℕ} (hk : 1 ≤ k) :
    Multiset.card ((hR k).roots.filter (1 < ·)) = k / 3 := by
  rw [card_filter_roots_hR hk]
  have e : (((nR k).roots.toFinset.erase (-1)).filter fun z => 1 < zToT z) =
      ((nR k).roots.toFinset.erase (-1)).filter (· < -1) :=
    Finset.filter_congr fun z hz => one_lt_zToT_iff (Finset.ne_of_mem_erase hz)
  rw [e, ← card_filter_roots_nR hk (· < -1) (lt_irrefl _)]
  exact nBelow_nR hk

/-- **论文推论 8.13**：`k ≥ 1` 时 `h_k` 的其余 `⌊(k+1)/3⌋` 个根都是负数。 -/
theorem card_roots_hR_neg {k : ℕ} (hk : 1 ≤ k) :
    Multiset.card ((hR k).roots.filter (· < 0)) = (k + 1) / 3 := by
  rw [card_filter_roots_hR hk]
  have e : (((nR k).roots.toFinset.erase (-1)).filter fun z => zToT z < 0) =
      ((nR k).roots.toFinset.erase (-1)).filter (-1 < ·) :=
    Finset.filter_congr fun z hz => zToT_neg_iff (Finset.ne_of_mem_erase hz)
      (root_neg_nR hk (Multiset.mem_toFinset.1 (Finset.mem_of_mem_erase hz)))
  rw [e, ← card_filter_roots_nR hk (-1 < ·) (lt_irrefl _)]
  have hsum := nBelow_add_count_add_nAbove (nR k) (-1)
  rw [count_neg_one_nR hk, (realRooted_nR hk).2, natDegree_nR hk, nBelow_nR hk] at hsum
  unfold nAbove at hsum
  have hH := (div_three_identities k).1
  have h1 : 1 ≤ (k + 2) / 3 := by omega
  omega

/-! ## 5. 系数的变号次数（论文推论 8.13 的最后一句） -/

theorem signVariations_C' (c : ℝ) : (C c).signVariations = 0 := by
  rw [← monomial_zero_left]
  exact signVariations_monomial 0 c

/-- 非零实数 `u, v`：`sign u = −sign v` 当且仅当 `u·v < 0`。 -/
theorem sign_eq_neg_sign_iff {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    SignType.sign u = -SignType.sign v ↔ u * v < 0 := by
  rcases lt_or_gt_of_ne hu with hu' | hu' <;> rcases lt_or_gt_of_ne hv with hv' | hv'
  · rw [sign_neg hu', sign_neg hv']
    constructor
    · intro h
      exact absurd h (by decide)
    · intro h
      nlinarith
  · rw [sign_neg hu', sign_pos hv']
    constructor
    · intro _
      exact mul_neg_of_neg_of_pos hu' hv'
    · intro _
      rfl
  · rw [sign_pos hu', sign_neg hv']
    constructor
    · intro _
      exact mul_neg_of_pos_of_neg hu' hv'
    · intro _
      rfl
  · rw [sign_pos hu', sign_pos hv']
    constructor
    · intro h
      exact absurd h (by decide)
    · intro h
      nlinarith

/-- **组合引理**（Descartes 法则取等号的一半）：常数项非零的实系数多项式 `P` 满足 `V(P) + V(P(−x)) ≤ deg P`，`V` 为
系数序列的变号次数（Mathlib 的 `signVariations`）。对次数归纳：`P = Q + a·x^n`（`Q` 为去掉首项后的多项式，次数
`m < n`），`P(−x)` 去掉首项后是 `Q(−x)`；两个首项比较各贡献 0 或 1 次变号，`n − m` 为奇数时恰贡献一次。 -/
theorem signVariations_add_comp_neg_X_le : ∀ (n : ℕ) (P : ℝ[X]), P.natDegree = n → P.coeff 0 ≠ 0 →
    P.signVariations + (P.comp (-X)).signVariations ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hn h0
    have hP : P ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
    by_cases hQ : P.eraseLead = 0
    · -- `P` 是单项式；常数项非零，所以是常数
      have e := P.eraseLead_add_C_mul_X_pow
      rw [hQ, zero_add] at e
      have hdeg : P.natDegree = 0 := by
        by_contra hd
        apply h0
        rw [← e, coeff_C_mul, coeff_X_pow, ite_eq_right (by omega), mul_zero]
      rw [eq_C_of_natDegree_eq_zero hdeg, C_comp, signVariations_C']
      omega
    · set Q := P.eraseLead with hQdef
      have hm : Q.natDegree < n := hn ▸ (P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right hQ)
      have hnpos : 0 < P.natDegree := natDegree_pos_of_eraseLead_ne_zero hQ
      have hQ0 : Q.coeff 0 ≠ 0 := by
        rw [hQdef, eraseLead_coeff_of_ne 0 (by omega)]
        exact h0
      have hIH := ih Q.natDegree hm Q rfl hQ0
      have ha : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP
      have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hQ
      have hP' : P.comp (-X) ≠ 0 := fun h => hP (comp_neg_X_eq_zero_iff.1 h)
      -- `P(−x) = Q(−x) + (a·(−1)^n)·x^n`，去掉首项后是 `Q(−x)`
      have hcomp : P.comp (-X) = Q.comp (-X) + C (P.leadingCoeff * (-1) ^ P.natDegree) * X ^ P.natDegree := by
        conv_lhs => rw [← P.eraseLead_add_C_mul_X_pow]
        rw [add_comp, mul_comp, C_comp, X_pow_comp, neg_pow, C_mul, C_pow, C_neg, C_1]
        ring
      have hc0 : P.leadingCoeff * (-1) ^ P.natDegree ≠ 0 := mul_ne_zero ha (pow_ne_zero _ (by norm_num))
      have hnatQ' : (Q.comp (-X)).natDegree = Q.natDegree := natDegree_eq_of_degree_eq degree_comp_neg_X
      have hE : (P.comp (-X)).eraseLead = Q.comp (-X) := by
        rw [hcomp, eraseLead_add_of_natDegree_lt_right, eraseLead_C_mul_X_pow, add_zero]
        rw [natDegree_C_mul_X_pow _ _ hc0, hnatQ']
        omega
      have hV := signVariations_eq_eraseLead_add_ite hP
      rw [← hQdef] at hV
      have hV' := signVariations_eq_eraseLead_add_ite hP'
      rw [hE, comp_neg_X_leadingCoeff_eq, comp_neg_X_leadingCoeff_eq] at hV'
      rw [hV, hV']
      have hu' : (-1 : ℝ) ^ P.natDegree * P.leadingCoeff ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) ha
      have hv' : (-1 : ℝ) ^ Q.natDegree * Q.leadingCoeff ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hb
      split_ifs with h1 h2 h2
      · -- 两处都变号：`n + m` 为偶数，所以 `n − m ≥ 2`
        have p1 := (sign_eq_neg_sign_iff ha hb).1 h1
        have p2 := (sign_eq_neg_sign_iff hu' hv').1 h2
        have hev : (P.natDegree + Q.natDegree) % 2 = 0 := by
          rcases Nat.even_or_odd (P.natDegree + Q.natDegree) with he | ho
          · exact Nat.even_iff.1 he
          · exfalso
            have e2 : (-1 : ℝ) ^ P.natDegree * P.leadingCoeff * ((-1) ^ Q.natDegree * Q.leadingCoeff) =
                -(P.leadingCoeff * Q.leadingCoeff) := by
              rw [show (-1 : ℝ) ^ P.natDegree * P.leadingCoeff * ((-1) ^ Q.natDegree * Q.leadingCoeff) =
                (-1) ^ (P.natDegree + Q.natDegree) * (P.leadingCoeff * Q.leadingCoeff) by ring, ho.neg_one_pow]
              ring
            rw [e2] at p2
            linarith
        omega
      · omega
      · omega
      · omega

/-- `ℚ` 系数多项式映到 `ℝ[X]` 不改变变号次数。 -/
theorem signVariations_map_rat (P : ℚ[X]) : (P.map (algebraMap ℚ ℝ)).signVariations = P.signVariations := by
  unfold Polynomial.signVariations
  have hc : (P.map (algebraMap ℚ ℝ)).coeffList = P.coeffList.map (algebraMap ℚ ℝ) := by
    unfold coeffList
    rw [degree_map, List.map_map]
    congr 1
    funext i
    simp [coeff_map]
  rw [hc]
  refine List.signVariations_map (fun x => ?_) _
  rw [eq_ratCast]
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

theorem hR_coeff_zero (k : ℕ) : (hR k).coeff 0 = 1 := by
  rw [hR, coeff_map, coeff_zero_eq_eval_zero, hpoly_eval_zero_eq_one, map_one]

/-- **论文推论 8.13 的最后一句**：`k ≥ 1` 时 `h_k` 的系数序列恰变号 `⌊k/3⌋` 次（Mathlib 的 `signVariations`，忽略零系数）。 -/
theorem signVariations_hR {k : ℕ} (hk : 1 ≤ k) : (hR k).signVariations = k / 3 := by
  have hdeg : (hR k).natDegree = 2 * k / 3 := by rw [hR, natDegree_map, natDegree_hpoly]
  have hpos : (hR k).roots.countP (0 < ·) = k / 3 := by
    rw [Multiset.countP_eq_card_filter]
    have e : (hR k).roots.filter (0 < ·) = (hR k).roots.filter (1 < ·) := by
      apply Multiset.filter_congr
      intro t ht
      constructor
      · intro h0
        by_contra h1
        apply hpoly_ne_zero_of_mem_Icc k h0.le (not_lt.1 h1)
        rw [aeval_def, ← eval_map]
        exact (isRoot_of_mem_roots ht).eq_zero
      · intro h1
        linarith
    rw [e, card_roots_hR_gt_one hk]
  have hD1 := roots_countP_pos_le_signVariations (hR k)
  have hD2 := roots_countP_pos_le_signVariations ((hR k).comp (-X))
  rw [roots_comp_neg_X, Multiset.countP_map] at hD2
  have e2 : (hR k).roots.filter (fun a => 0 < -a) = (hR k).roots.filter (· < 0) :=
    Multiset.filter_congr fun a _ => neg_pos
  rw [e2, card_roots_hR_neg hk] at hD2
  have hsum := signVariations_add_comp_neg_X_le (2 * k / 3) (hR k) hdeg (by rw [hR_coeff_zero]; exact one_ne_zero)
  rw [hpos] at hD1
  have h2 := (div_three_identities k).2.1
  omega

/-- **论文推论 8.13**（`h_k` 本身，`ℚ` 系数）：系数序列恰变号 `⌊k/3⌋` 次。 -/
theorem signVariations_hpoly {k : ℕ} (hk : 1 ≤ k) : (hpoly k).signVariations = k / 3 := by
  rw [← signVariations_map_rat]
  exact signVariations_hR hk

/-- **论文推论 8.13**（合在一起）：`k ≥ 1` 时 `h_k` 恰有 `⌊k/3⌋` 个根在 `(1, ∞)`，其余 `⌊(k+1)/3⌋` 个根都是负数
（`h_k` 只有实根、根都是单根，`deg h_k = ⌊2k/3⌋`），系数序列恰变号 `⌊k/3⌋` 次。 -/
theorem cor_hk_signs {k : ℕ} (hk : 1 ≤ k) :
    Multiset.card ((hR k).roots.filter (1 < ·)) = k / 3 ∧
    Multiset.card ((hR k).roots.filter (· < 0)) = (k + 1) / 3 ∧
    Multiset.card (hR k).roots = 2 * k / 3 ∧
    (hpoly k).signVariations = k / 3 := by
  refine ⟨card_roots_hR_gt_one hk, card_roots_hR_neg hk, ?_, signVariations_hpoly hk⟩
  rw [(hR_realRooted_nodup k).1.2, hR, natDegree_map, natDegree_hpoly]

end

end A207123
