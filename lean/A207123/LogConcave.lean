import A207123.SimpleRoots

/-!
# 论文推论 8.2：三角形 `N` 的每一行为正、严格对数凹、单峰

论文推论 8.2：对每个 `k ≥ 1`，`N(k,1), …, N(k,k)` 都是正数，且 `2 ≤ q ≤ k − 1` 时 `N(k,q)² > N(k,q−1)·N(k,q+1)`；
特别地这一行单峰。

论文的证明：`n_k` 只有实根（定理 8.1），系数非负，所以根都 `≤ 0`，而 `n_k(0) = 1`，所以 `n_k` 是 `N(k,k)` 乘以若干
`z + r`（`r > 0`）之积；再用 Newton 不等式。这里不用 Newton 不等式，改用更初等的一步：
`prod_X_add_C_coeff_props`——正数 `r_1, …, r_n` 的 `∏(X + r_i)` 的系数 `a_0, …, a_n` 都是正数，且 `a_i·a_{i+2} < a_{i+1}²`
（对因子个数归纳：乘以 `X + r` 后新系数是 `b_{j+1} = a_j + r·a_{j+1}`，
`b_{j+2}² − b_{j+1}b_{j+3} = (a_{j+1}² − a_ja_{j+2}) + r²(a_{j+2}² − a_{j+1}a_{j+3}) + r(a_{j+1}a_{j+2} − a_ja_{j+3})`，三项分别
`> 0`、`≥ 0`、`≥ 0`）。

* `root_neg_nR`：`n_k` 的根都是负数；`nR_eq_prod`：`n_k = N(k,k)·∏_r (z + r)`，`r` 取 `−(n_k 的根)`。
* `unimodal_of_pos_logconcave`：正的、严格对数凹的有限序列单峰（先不减、后不增）。
* `cor_logconcave`：论文推论 8.2。
-/

namespace A207123

open Polynomial

noncomputable section

/-- 正数 `r ∈ s` 的 `∏_{r∈s}(X + r)`：次数以上的系数为 0；`a_0, …, a_n`（`n = |s|`）都是正数；严格对数凹
`a_i·a_{i+2} < a_{i+1}²`（`i + 2 ≤ n`）。 -/
theorem prod_X_add_C_coeff_props (s : Multiset ℝ) (hs : ∀ r ∈ s, 0 < r) :
    (∀ i, Multiset.card s < i → ((s.map fun r => X + C r).prod).coeff i = 0) ∧
    (∀ i, i ≤ Multiset.card s → 0 < ((s.map fun r => X + C r).prod).coeff i) ∧
    (∀ i, i + 2 ≤ Multiset.card s →
      ((s.map fun r => X + C r).prod).coeff i * ((s.map fun r => X + C r).prod).coeff (i + 2) <
        ((s.map fun r => X + C r).prod).coeff (i + 1) ^ 2) := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero]
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [coeff_one]
      split_ifs with h
      · omega
      · rfl
    · rw [Nat.le_zero.1 hi, coeff_one_zero]
      exact one_pos
    · omega
  | cons r s ih =>
    have hr : 0 < r := hs r (Multiset.mem_cons_self r s)
    obtain ⟨ih0, ih1, ih2⟩ := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    have hnn : ∀ i, 0 ≤ ((s.map fun r => X + C r).prod).coeff i := fun i => by
      rcases le_or_gt i (Multiset.card s) with h | h
      · exact (ih1 i h).le
      · rw [ih0 i h]
    have c0 : ((X + C r) * (s.map fun r => X + C r).prod).coeff 0 =
        r * ((s.map fun r => X + C r).prod).coeff 0 := by
      rw [add_mul, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]
    have cs : ∀ j, ((X + C r) * (s.map fun r => X + C r).prod).coeff (j + 1) =
        ((s.map fun r => X + C r).prod).coeff j + r * ((s.map fun r => X + C r).prod).coeff (j + 1) := by
      intro j
      rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [cs, ih0 j (by omega), ih0 (j + 1) (by omega), mul_zero, add_zero]
    · rcases i with _ | j
      · rw [c0]
        exact mul_pos hr (ih1 0 (Nat.zero_le _))
      · rw [cs]
        exact add_pos_of_pos_of_nonneg (ih1 j (by omega)) (mul_nonneg hr.le (hnn _))
    · rcases i with _ | j
      · -- `b₁² − b₀b₂ = a₀² + r·a₀a₁ + r²(a₁² − a₀a₂)`
        have e1 : ((X + C r) * (s.map fun r => X + C r).prod).coeff (0 + 1) =
            ((s.map fun r => X + C r).prod).coeff 0 + r * ((s.map fun r => X + C r).prod).coeff 1 := cs 0
        have e2 : ((X + C r) * (s.map fun r => X + C r).prod).coeff (0 + 2) =
            ((s.map fun r => X + C r).prod).coeff 1 + r * ((s.map fun r => X + C r).prod).coeff 2 := cs 1
        rw [c0, e1, e2]
        have ha0 : 0 < ((s.map fun r => X + C r).prod).coeff 0 := ih1 0 (Nat.zero_le _)
        have h12 : ((s.map fun r => X + C r).prod).coeff 0 * ((s.map fun r => X + C r).prod).coeff 2 ≤
            ((s.map fun r => X + C r).prod).coeff 1 ^ 2 := by
          rcases le_or_gt 2 (Multiset.card s) with h | h
          · exact (ih2 0 h).le
          · rw [ih0 2 h, mul_zero]
            positivity
        have t1 : 0 < ((s.map fun r => X + C r).prod).coeff 0 ^ 2 := by positivity
        have t2 : 0 ≤ r * (((s.map fun r => X + C r).prod).coeff 0 *
            ((s.map fun r => X + C r).prod).coeff 1) := mul_nonneg hr.le (mul_nonneg ha0.le (hnn 1))
        have t3 : 0 ≤ r ^ 2 * (((s.map fun r => X + C r).prod).coeff 1 ^ 2 -
            ((s.map fun r => X + C r).prod).coeff 0 * ((s.map fun r => X + C r).prod).coeff 2) :=
          mul_nonneg (sq_nonneg r) (sub_nonneg.2 h12)
        nlinarith [t1, t2, t3]
      · -- `b_{j+2}² − b_{j+1}b_{j+3} = (a_{j+1}² − a_ja_{j+2}) + r²(a_{j+2}² − a_{j+1}a_{j+3}) + r(a_{j+1}a_{j+2} − a_ja_{j+3})`
        have e1 : ((X + C r) * (s.map fun r => X + C r).prod).coeff (j + 1) =
            ((s.map fun r => X + C r).prod).coeff j + r * ((s.map fun r => X + C r).prod).coeff (j + 1) :=
          cs j
        have e2 : ((X + C r) * (s.map fun r => X + C r).prod).coeff (j + 1 + 1) =
            ((s.map fun r => X + C r).prod).coeff (j + 1) +
              r * ((s.map fun r => X + C r).prod).coeff (j + 2) := cs (j + 1)
        have e3 : ((X + C r) * (s.map fun r => X + C r).prod).coeff (j + 1 + 2) =
            ((s.map fun r => X + C r).prod).coeff (j + 2) +
              r * ((s.map fun r => X + C r).prod).coeff (j + 3) := cs (j + 2)
        rw [e1, e2, e3]
        have hx0 : 0 < ((s.map fun r => X + C r).prod).coeff j := ih1 j (by omega)
        have hx1 : 0 < ((s.map fun r => X + C r).prod).coeff (j + 1) := ih1 (j + 1) (by omega)
        have hx2 : 0 < ((s.map fun r => X + C r).prod).coeff (j + 2) := ih1 (j + 2) (by omega)
        have h1 : ((s.map fun r => X + C r).prod).coeff j * ((s.map fun r => X + C r).prod).coeff (j + 2) <
            ((s.map fun r => X + C r).prod).coeff (j + 1) ^ 2 := ih2 j (by omega)
        have h2 : ((s.map fun r => X + C r).prod).coeff (j + 1) *
            ((s.map fun r => X + C r).prod).coeff (j + 3) ≤ ((s.map fun r => X + C r).prod).coeff (j + 2) ^ 2 := by
          rcases le_or_gt (j + 3) (Multiset.card s) with h | h
          · exact (ih2 (j + 1) (by omega)).le
          · rw [ih0 (j + 3) h, mul_zero]
            positivity
        have h3 : ((s.map fun r => X + C r).prod).coeff j * ((s.map fun r => X + C r).prod).coeff (j + 3) ≤
            ((s.map fun r => X + C r).prod).coeff (j + 1) * ((s.map fun r => X + C r).prod).coeff (j + 2) := by
          rcases le_or_gt (j + 3) (Multiset.card s) with h | h
          · have h2' : ((s.map fun r => X + C r).prod).coeff (j + 1) *
                ((s.map fun r => X + C r).prod).coeff (j + 3) <
                ((s.map fun r => X + C r).prod).coeff (j + 2) ^ 2 := ih2 (j + 1) (by omega)
            have hx3 : 0 < ((s.map fun r => X + C r).prod).coeff (j + 3) := ih1 (j + 3) h
            nlinarith [mul_lt_mul'' h1 h2' (mul_pos hx0 hx2).le (mul_pos hx1 hx3).le, mul_pos hx1 hx2]
          · rw [ih0 (j + 3) h, mul_zero]
            exact (mul_pos hx1 hx2).le
        have t1 : 0 < ((s.map fun r => X + C r).prod).coeff (j + 1) ^ 2 -
            ((s.map fun r => X + C r).prod).coeff j * ((s.map fun r => X + C r).prod).coeff (j + 2) :=
          sub_pos.2 h1
        have t2 : 0 ≤ r ^ 2 * (((s.map fun r => X + C r).prod).coeff (j + 2) ^ 2 -
            ((s.map fun r => X + C r).prod).coeff (j + 1) * ((s.map fun r => X + C r).prod).coeff (j + 3)) :=
          mul_nonneg (sq_nonneg r) (sub_nonneg.2 h2)
        have t3 : 0 ≤ r * (((s.map fun r => X + C r).prod).coeff (j + 1) *
            ((s.map fun r => X + C r).prod).coeff (j + 2) -
            ((s.map fun r => X + C r).prod).coeff j * ((s.map fun r => X + C r).prod).coeff (j + 3)) :=
          mul_nonneg hr.le (sub_nonneg.2 h3)
        nlinarith [t1, t2, t3]

/-- `n_k` 的根都是负数（`k ≥ 1`）：系数非负所以没有正根（`nAbove_nR_zero`），又 `n_k(0) = 1`。 -/
theorem root_neg_nR {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : a ∈ (nR k).roots) : a < 0 := by
  have h0 := nAbove_nR_zero hk
  have hne : a ≠ 0 := by
    rintro rfl
    have h := (isRoot_of_mem_roots ha).eq_zero
    rw [nR_eval_zero hk] at h
    exact one_ne_zero h
  by_contra hpos
  have hlt : 0 < a := lt_of_le_of_ne (not_lt.1 hpos) (Ne.symm hne)
  have : 0 < nAbove (nR k) 0 := by
    unfold nAbove
    exact Multiset.card_pos_iff_exists_mem.2 ⟨a, Multiset.mem_filter.2 ⟨ha, hlt⟩⟩
  omega

/-- `∏_r (z + r)`，`r` 取 `−(n_k 的根)`（都是正数，`root_neg_nR`）。 -/
def rowProd (k : ℕ) : ℝ[X] := (((nR k).roots.map Neg.neg).map fun r => X + C r).prod

/-- `n_k = N(k,k)·∏_r (z + r)`（`k ≥ 1`）。 -/
theorem nR_eq_prod {k : ℕ} (hk : 1 ≤ k) : nR k = C (N k k : ℝ) * rowProd k := by
  have e : ((nR k).roots.map fun a => X - C a) = (((nR k).roots.map Neg.neg).map fun r => X + C r) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun a _ => by simp [sub_eq_add_neg]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (realRooted_nR hk).2]
  rw [leadingCoeff_nR hk, e, rowProd]

theorem coeff_nR_eq_rowProd {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    (N k (i + 1) : ℝ) = (N k k : ℝ) * (rowProd k).coeff i := by
  rw [← coeff_nR, ← coeff_C_mul, ← nR_eq_prod hk]

/-- `rowProd k` 的系数 `a_0, …, a_{k−1}` 都是正数，且严格对数凹。 -/
theorem rowProd_props {k : ℕ} (hk : 1 ≤ k) :
    (∀ i, i ≤ k - 1 → 0 < (rowProd k).coeff i) ∧
    (∀ i, i + 2 ≤ k - 1 → (rowProd k).coeff i * (rowProd k).coeff (i + 2) < (rowProd k).coeff (i + 1) ^ 2) := by
  have hspos : ∀ r ∈ (nR k).roots.map Neg.neg, 0 < r := by
    intro r hr
    rw [Multiset.mem_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact neg_pos.2 (root_neg_nR hk ha)
  have hcard : Multiset.card ((nR k).roots.map Neg.neg) = k - 1 := by
    rw [Multiset.card_map, (realRooted_nR hk).2, natDegree_nR hk]
  obtain ⟨-, h1, h2⟩ := prod_X_add_C_coeff_props _ hspos
  rw [hcard] at h1 h2
  exact ⟨h1, h2⟩

/-- 正的、严格对数凹的有限序列 `a_1, …, a_k` 单峰：存在 `1 ≤ m ≤ k`，`a_1 ≤ … ≤ a_m ≥ a_{m+1} ≥ … ≥ a_k`。 -/
theorem unimodal_of_pos_logconcave {a : ℕ → ℕ} {k : ℕ} (hk : 1 ≤ k)
    (hpos : ∀ q, 1 ≤ q → q ≤ k → 0 < a q)
    (hlc : ∀ q, 2 ≤ q → q + 1 ≤ k → a (q - 1) * a (q + 1) < a q ^ 2) :
    ∃ m, 1 ≤ m ∧ m ≤ k ∧ (∀ q, 1 ≤ q → q < m → a q ≤ a (q + 1)) ∧
      (∀ q, m ≤ q → q < k → a (q + 1) ≤ a q) := by
  classical
  have hex : ∃ m, 1 ≤ m ∧ (m = k ∨ (m < k ∧ a (m + 1) ≤ a m)) := ⟨k, hk, Or.inl rfl⟩
  have hm := Nat.find_spec hex
  have hmk : Nat.find hex ≤ k := Nat.find_min' hex ⟨hk, Or.inl rfl⟩
  refine ⟨Nat.find hex, hm.1, hmk, fun q hq1 hqm => ?_, fun q hmq hqk => ?_⟩
  · have hq := Nat.find_min hex hqm
    by_contra hc
    exact hq ⟨hq1, Or.inr ⟨by omega, (not_le.1 hc).le⟩⟩
  · induction q, hmq using Nat.le_induction with
    | base =>
      rcases hm.2 with h | h
      · omega
      · exact h.2
    | succ q hmq ih =>
      have ih := ih (by omega)
      have hq1 : 1 ≤ q := le_trans hm.1 hmq
      have hl := hlc (q + 1) (by omega) (by omega)
      rw [show q + 1 - 1 = q by omega, sq] at hl
      have hp := hpos (q + 1) (by omega) (by omega)
      by_contra hc
      have e1 : a (q + 1) * a (q + 1) < a (q + 1) * a (q + 1 + 1) :=
        mul_lt_mul_of_pos_left (not_le.1 hc) hp
      have e2 : a (q + 1) * a (q + 1 + 1) ≤ a q * a (q + 1 + 1) :=
        mul_le_mul_of_nonneg_right ih (Nat.zero_le _)
      exact lt_asymm (e1.trans_le e2) hl

/-- **论文推论 8.2**：对每个 `k ≥ 1`，`N(k,1), …, N(k,k)` 都是正数；`2 ≤ q ≤ k − 1` 时
`N(k,q)² > N(k,q−1)·N(k,q+1)`；这一行单峰（存在 `1 ≤ m ≤ k`，`N(k,1) ≤ … ≤ N(k,m) ≥ … ≥ N(k,k)`）。 -/
theorem cor_logconcave {k : ℕ} (hk : 1 ≤ k) :
    (∀ q, 1 ≤ q → q ≤ k → 0 < N k q) ∧
    (∀ q, 2 ≤ q → q + 1 ≤ k → N k (q - 1) * N k (q + 1) < N k q ^ 2) ∧
    ∃ m, 1 ≤ m ∧ m ≤ k ∧ (∀ q, 1 ≤ q → q < m → N k q ≤ N k (q + 1)) ∧
      (∀ q, m ≤ q → q < k → N k (q + 1) ≤ N k q) := by
  obtain ⟨h1, h2⟩ := rowProd_props hk
  have hNk : (0 : ℝ) < N k k := by exact_mod_cast N_self_pos k
  have hpos : ∀ q, 1 ≤ q → q ≤ k → 0 < N k q := by
    intro q hq1 hqk
    obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
    have h : (0 : ℝ) < N k (i + 1) := by
      rw [coeff_nR_eq_rowProd hk i]
      exact mul_pos hNk (h1 i (by omega))
    exact_mod_cast h
  have hlc : ∀ q, 2 ≤ q → q + 1 ≤ k → N k (q - 1) * N k (q + 1) < N k q ^ 2 := by
    intro q hq2 hqk
    obtain ⟨i, rfl⟩ : ∃ i, q = i + 2 := ⟨q - 2, by omega⟩
    have e0 : (N k (i + 2 - 1) : ℝ) = N k k * (rowProd k).coeff i := by
      rw [show i + 2 - 1 = i + 1 by omega]
      exact coeff_nR_eq_rowProd hk i
    have e1 : (N k (i + 2) : ℝ) = N k k * (rowProd k).coeff (i + 1) := coeff_nR_eq_rowProd hk (i + 1)
    have e2 : (N k (i + 2 + 1) : ℝ) = N k k * (rowProd k).coeff (i + 2) := coeff_nR_eq_rowProd hk (i + 2)
    have key := h2 i (by omega)
    have h : (N k (i + 2 - 1) : ℝ) * N k (i + 2 + 1) < (N k (i + 2) : ℝ) ^ 2 := by
      rw [e0, e1, e2]
      have e3 : (N k k : ℝ) * (rowProd k).coeff i * (N k k * (rowProd k).coeff (i + 2)) =
          (N k k : ℝ) ^ 2 * ((rowProd k).coeff i * (rowProd k).coeff (i + 2)) := by ring
      rw [e3, mul_pow]
      exact mul_lt_mul_of_pos_left key (by positivity)
    exact_mod_cast h
  exact ⟨hpos, hlc, unimodal_of_pos_logconcave hk hpos hlc⟩

end

end A207123
