import A207123.RealRoots

/-!
# 论文 §8：行多项式除 `−1` 外只有单根；`h_k` 的根都是实数且互不相同（命题 8.11、定理 8.1）

接 `RealRoots.lean`（命题 8.10：`n_k` 只有实根；`nR k` 是 `n_k` 的实系数版本，`nR_eq_map`）。

* 交错的一个推论（论文 §8.1 定义 `≪` 之后的说明）：`Interlaces.eval_mul_derivative_nonneg`——`g ≪ f`、首项系数
  都为正、`a` 是 `f` 的单根时 `g(a)·f'(a) ≥ 0`。
* 实根多项式 `Q` 的导数在 `Q` 的非根处至多是单根（论文命题 8.11 证明中的一句）：`count_roots_of_derivative`——
  `Q'` 在 `a` 处至少二重，则 `a` 是 `Q` 的至少三重根（由 `Q' ≪ Q` 与 `rootMultiplicity a Q' = rootMultiplicity a Q − 1`）。
* 论文命题 8.11：`nR_no_common_root`（`j ≥ 2` 时 `n_j`、`n_{j−1}` 除 `−1` 外没有公共根；论文对最小的 `j` 反证，
  这里写成对 `j` 的强归纳，`j ≤ 4` 直接验证）与 `count_roots_nR_le_one`（`n_k` 除 `−1` 外的根都是单根）。
* 论文定理 8.1：`rootMultiplicity_nrowPoly_le_one`（`nrowPoly k` 在 `ℂ` 中除 `−1` 外的根的重数都 ≤ 1）；
  `hR_realRooted_nodup`（`h_k` 映到 `ℝ[X]` 后只有实根且根两两不同）、`hpoly_root_im_eq_zero`（`h_k` 的复根都是实数）、
  `separable_hpoly`（`h_k` 是可分多项式，即在代数闭包里没有重根）；`thm_realroots` 把这几条合在一起。
  `h_k` 一半的证明与论文相同：`n_k` 除 `−1` 外的 `k − 1 − (⌈k/3⌉ − 1) = ⌊2k/3⌋` 个不同的根 `z` 经 `z ↦ z/(1+z)` 映成
  `h_k` 的不同的根（`nR_eval_hR`：`n_k(z) = (1+z)^{k−1}·h_k(z/(1+z))`），而 `deg h_k = ⌊2k/3⌋`（`natDegree_hpoly`；
  `−1` 的重数 `⌈k/3⌉ − 1` 见 `rootMultiplicity_nrowPoly`）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 辅助引理 -/

/-- `N(k,1) = 1`（`k ≥ 1`；值域恰为 `{1}` 的好词只有常词。由三角递推 `N_tri` 在 `r = 0` 处归纳）。 -/
theorem N_one_right : ∀ {k : ℕ}, 1 ≤ k → N k 1 = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
    · exact N_init.2.1
    · exact N_init.2.2.1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have h := N_tri j 0
      have h0 : N (j + 2) 0 = 0 := N_succ_zero (j + 1)
      simp only [h0, zero_add, zero_mul, add_zero] at h
      rw [h]
      exact ih (j + 2) (by omega) (by omega)

/-- `n_k(0) = 1`（`k ≥ 1`）。 -/
theorem nR_eval_zero {k : ℕ} (hk : 1 ≤ k) : (nR k).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_nR, zero_add, N_one_right hk, Nat.cast_one]

/-- `n_3 = 2z² + 4z + 1`。 -/
theorem nR_three_eq : nR 3 = C 2 * X ^ 2 + C 4 * X + C 1 := by
  ext j
  rw [coeff_nR, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  obtain ⟨n1, n2, n3⟩ := N_three
  rcases j with _ | _ | _ | j
  · simp [n1]
  · simp [n2]
  · simp [n3]
  · rw [N_eq_zero_of_lt (by omega)]
    simp

theorem eval_one_add_X_mul (p : ℝ[X]) (a : ℝ) : ((1 + X) * p).eval a = (1 + a) * p.eval a := by
  rw [eval_mul, eval_add, eval_one, eval_X]

theorem count_roots_one_add_X_mul {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ} (ha : a ≠ -1) :
    ((1 + X) * p).roots.count a = p.roots.count a := by
  have h1 : a ∉ ({-1} : Multiset ℝ) := by
    rw [Multiset.mem_singleton]
    exact ha
  rw [roots_mul (mul_ne_zero realRooted_one_add_X.1 hp), Multiset.count_add, one_add_X_eq,
    roots_X_sub_C, Multiset.count_eq_zero.2 h1, zero_add]

theorem count_roots_X_mul {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    (X * p).roots.count a = p.roots.count a := by
  have h1 : a ∉ ({0} : Multiset ℝ) := by
    rw [Multiset.mem_singleton]
    exact ha
  rw [roots_mul (mul_ne_zero X_ne_zero hp), Multiset.count_add, roots_X, Multiset.count_eq_zero.2 h1,
    zero_add]

/-- `((1+z)²p)' = (1+z)·𝒟p`（论文 §8.1 中 `𝒟` 的第二个表达式）。 -/
theorem derivative_one_add_X_sq_mul (p : ℝ[X]) :
    derivative ((1 + X) * ((1 + X) * p)) = (1 + X) * opDz p := by
  have hC2 : (C 2 : ℝ[X]) = 2 := C_ofNat 2
  rw [opDz, hC2]
  simp only [derivative_mul, derivative_add, derivative_one, derivative_X]
  ring

/-- 在 `f` 的根 `a` 处，`f'(a) = (f/(X−a))(a)`。 -/
theorem eval_derivative_of_root {f : ℝ[X]} {a : ℝ} (ha : f.IsRoot a) :
    (derivative f).eval a = (f /ₘ (X - C a)).eval a := by
  conv_lhs => rw [← divByMonic_spec ha]
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
    eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-! ## 2. 交错与单根 -/

/-- 论文 §8.1 定义 `≪` 之后的说明：`g ≪ f`、两者首项系数都为正、`a` 是 `f` 的单根，则 `g(a)` 与 `f'(a)` 同号
（`g(a) = 0` 时乘积为 0），即 `g(a)·f'(a) ≥ 0`。 -/
theorem Interlaces.eval_mul_derivative_nonneg {g f : ℝ[X]} (h : Interlaces g f)
    (hlcf : 0 < f.leadingCoeff) (hlcg : 0 < g.leadingCoeff) {a : ℝ}
    (hfa : f.roots.count a = 1) : 0 ≤ g.eval a * (derivative f).eval a := by
  by_cases hg0 : g.eval a = 0
  · rw [hg0, zero_mul]
  have hfr : f.IsRoot a := isRoot_of_mem_roots (Multiset.count_pos.1 (by omega))
  have hga : g.roots.count a = 0 :=
    Multiset.count_eq_zero.2 fun hm => hg0 (isRoot_of_mem_roots hm).eq_zero
  have hn := h.nAbove_eq_of_simple hfa hga
  have h1 := sign_eval h.2.1 hlcg hg0
  have h2 := sign_divByMonic_eval h.1 hlcf hfr hfa
  rw [hn] at h1
  rw [eval_derivative_of_root hfr]
  have hs : ((-1 : ℝ) ^ nAbove f a) * ((-1) ^ nAbove f a) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have e : g.eval a * (f /ₘ (X - C a)).eval a =
      ((-1 : ℝ) ^ nAbove f a * g.eval a) * ((-1) ^ nAbove f a * (f /ₘ (X - C a)).eval a) := by
    linear_combination (-(g.eval a * (f /ₘ (X - C a)).eval a)) * hs
  rw [e]
  exact (mul_pos h1 h2).le

/-- 论文命题 8.11 证明中的一句：实根多项式 `Q` 的导数在 `Q` 的非根处至多是单根。写成：`Q'` 在 `a` 处的重数 `≥ 2`，
则 `a` 是 `Q` 的至少三重根（由 `Q' ≪ Q`（引理 8.7(1)）与 `rootMultiplicity a Q' = rootMultiplicity a Q − 1`）。 -/
theorem count_roots_of_derivative {Q : ℝ[X]} (hQ : RealRooted Q) (hlc : 0 < Q.leadingCoeff) {a : ℝ}
    (h2 : 2 ≤ (derivative Q).roots.count a) : 3 ≤ Q.roots.count a := by
  have hdeg : 1 ≤ Q.natDegree := by
    by_contra hd
    rw [derivative_of_natDegree_zero (p := Q) (by omega), roots_zero, Multiset.count_zero] at h2
    omega
  have hle := (interlaces_derivative hQ hlc hdeg).count_le' a
  by_cases hr : Q.IsRoot a
  · have hm := derivative_rootMultiplicity_of_root hr
    rw [← count_roots, ← count_roots] at hm
    omega
  · have : Q.roots.count a = 0 := Multiset.count_eq_zero.2 fun hm => hr (isRoot_of_mem_roots hm)
    omega

/-- (α_k)：`k ≥ 2` 时 `n_{k−1} ≪ n_k`（`alpha_two` 与命题 8.10）。 -/
theorem alpha_rel {k : ℕ} (hk : 2 ≤ k) : Interlaces (nR (k - 1)) (nR k) := by
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · exact alpha_two
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rw [show j + 3 - 1 = j + 2 by omega]
    exact (prop_four_relations j).1

/-- (β_k)：`k ≥ 2` 时 `n_k ≪ 𝒯n_{k−1}`（`beta_two` 与命题 8.10）。 -/
theorem beta_rel {k : ℕ} (hk : 2 ≤ k) : Interlaces (nR k) (opTz (nR (k - 1))) := by
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · exact beta_two
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rw [show j + 3 - 1 = j + 2 by omega]
    exact (prop_four_relations j).2.1

/-! ## 3. 论文命题 8.11 -/

/-- **论文命题 8.11 的第一句**：对每个 `j ≥ 2`，`n_j` 与 `n_{j−1}` 除 `−1` 外没有公共（实）根（`n_k` 的根都是实数，
见 `nrowPoly_root_im_eq_zero`）。证明按论文：论文对最小的 `j` 反证，这里写成对 `j` 的强归纳；`j ≤ 4` 直接验证，
`j ≥ 5` 时由引理 8.9 得 `𝒯n_{j−3}(a) = 0`、`n_{j−2}(a) + 𝒯n_{j−4}(a) = 0`，再按 `a` 是 `𝒯n_{j−3}` 的单根或重根分两种
情形（(β_{j−2})、(α_{j−3}) 与引理 8.8(2)）。 -/
theorem nR_no_common_root : ∀ {j : ℕ}, 2 ≤ j → ∀ {a : ℝ}, a ≠ -1 → (nR j).eval a = 0 →
    (nR (j - 1)).eval a ≠ 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj a ha h1 h2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [nR_eval_zero (by omega)] at h2
    exact one_ne_zero h2
  have h1a : 1 + a ≠ 0 := fun h => ha (by linarith)
  rcases (by omega : j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j) with rfl | rfl | rfl | hj5
  · -- `n_1 = 1`
    rw [show (2 : ℕ) - 1 = 1 from rfl, nR_one, eval_C] at h2
    exact one_ne_zero h2
  · -- `n_2 = 2z + 1` 的根 `−1/2` 不是 `n_3 = 2z² + 4z + 1` 的根
    rw [show (3 : ℕ) - 1 = 2 from rfl, nR_two] at h2
    simp only [eval_mul, eval_C, eval_sub, eval_X] at h2
    have ha2 : a = -1 / 2 := by linarith
    rw [nR_three_eq, ha2] at h1
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h1
    norm_num at h1
  · -- `n_4 = (1+z)(n_3 + 2z)` 在 `n_3` 的根处不为零
    have e : nR 4 = (1 + X) * (nR 3 + opTz (nR 1)) := nR_rec' (k := 1) le_rfl
    rw [show (4 : ℕ) - 1 = 3 from rfl] at h2
    rw [e, eval_one_add_X_mul, eval_add, h2, zero_add, opTz_nR_one] at h1
    simp only [eval_mul, eval_C, eval_sub, eval_X] at h1
    have h3 : (1 + a) * (2 * a) = 0 := by linear_combination h1
    exact mul_ne_zero h1a (mul_ne_zero two_ne_zero ha0) h3
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 5 := ⟨j - 5, by omega⟩
    rw [show i + 5 - 1 = i + 4 by omega] at h2
    have e5 : nR (i + 5) = (1 + X) * (nR (i + 4) + opTz (nR (i + 2))) :=
      nR_rec' (k := i + 2) (by omega)
    have e4 : nR (i + 4) = (1 + X) * (nR (i + 3) + opTz (nR (i + 1))) :=
      nR_rec' (k := i + 1) (by omega)
    -- 由引理 8.9：`𝒯n_{j−3}(a) = 0` 与 `n_{j−2}(a) + 𝒯n_{j−4}(a) = 0`
    have hT : (opTz (nR (i + 2))).eval a = 0 := by
      rw [e5, eval_one_add_X_mul, eval_add, h2, zero_add] at h1
      exact (mul_eq_zero.1 h1).resolve_left h1a
    have hTr : (opTz (nR (i + 2))).IsRoot a := hT
    have hsum : (nR (i + 3)).eval a + (opTz (nR (i + 1))).eval a = 0 := by
      have h2' := h2
      rw [e4, eval_one_add_X_mul, eval_add] at h2'
      exact (mul_eq_zero.1 h2').resolve_left h1a
    have l1 := leadingCoeff_nR_pos (k := i + 1) (by omega)
    have l2 := leadingCoeff_nR_pos (k := i + 2) (by omega)
    have l3 := leadingCoeff_nR_pos (k := i + 3) (by omega)
    have hβ : Interlaces (nR (i + 3)) (opTz (nR (i + 2))) := by
      have := beta_rel (k := i + 3) (by omega)
      rwa [show i + 3 - 1 = i + 2 by omega] at this
    have hα : Interlaces (nR (i + 1)) (nR (i + 2)) := by
      have := alpha_rel (k := i + 2) (by omega)
      rwa [show i + 2 - 1 = i + 1 by omega] at this
    have hTα : Interlaces (opTz (nR (i + 1))) (opTz (nR (i + 2))) := hα.opTz l2 l1
    have hf0 : opTz (nR (i + 2)) ≠ 0 := hβ.1.1
    have hpos : 0 < (opTz (nR (i + 2))).roots.count a :=
      Multiset.count_pos.2 ((mem_roots hf0).2 hTr)
    rcases (by omega : (opTz (nR (i + 2))).roots.count a = 1 ∨
        2 ≤ (opTz (nR (i + 2))).roots.count a) with hc | hc
    · -- `a` 是 `f = 𝒯n_{j−3}` 的单根：`n_{j−2}(a)` 与 `𝒯n_{j−4}(a)` 都与 `f'(a)` 同号或为零，两者之和为零，
      -- 所以 `n_{j−2}(a) = 0`，与 `n_{j−1}(a) = 0` 矛盾于 `j` 的归纳假设
      have hlf := opTz_lc l2
      have p1 := hβ.eval_mul_derivative_nonneg hlf l3 hc
      have p2 := hTα.eval_mul_derivative_nonneg hlf (opTz_lc l1) hc
      have hd : (derivative (opTz (nR (i + 2)))).eval a ≠ 0 := by
        rw [eval_derivative_of_root hTr]
        have hsg := sign_divByMonic_eval hβ.1 hlf hTr hc
        intro h0
        rw [h0, mul_zero] at hsg
        exact lt_irrefl _ hsg
      have hs : (nR (i + 3)).eval a * (derivative (opTz (nR (i + 2)))).eval a +
          (opTz (nR (i + 1))).eval a * (derivative (opTz (nR (i + 2)))).eval a = 0 := by
        rw [← add_mul, hsum, zero_mul]
      have hx : (nR (i + 3)).eval a * (derivative (opTz (nR (i + 2)))).eval a = 0 := by linarith
      have h3 : (nR (i + 3)).eval a = 0 := (mul_eq_zero.1 hx).resolve_right hd
      exact ih (i + 4) (by omega) (by omega) ha h2 (by rw [show i + 4 - 1 = i + 3 by omega]; exact h3)
    · -- `a` 是 `f = z·𝒟n_{j−3}` 的重根：`a ∉ {0, −1}`，所以是 `Q' = (1+z)·𝒟n_{j−3}`（`Q = (1+z)²n_{j−3}`）的重根，
      -- 于是是 `Q` 的至少三重根、`n_{j−3}` 的重根，由 (α_{j−3}) 也是 `n_{j−4}` 的根
      have hp := realRooted_nR (k := i + 2) (by omega)
      have hD0 : opDz (nR (i + 2)) ≠ 0 := (hp.opDz l2).1
      have hc' : 2 ≤ (opDz (nR (i + 2))).roots.count a := by
        rw [opTz, count_roots_X_mul hD0 ha0] at hc
        exact hc
      have hQr : RealRooted ((1 + X) * ((1 + X) * nR (i + 2))) :=
        realRooted_mul realRooted_one_add_X (realRooted_mul realRooted_one_add_X hp)
      have hQl : 0 < ((1 + X) * ((1 + X) * nR (i + 2))).leadingCoeff :=
        leadingCoeff_mul_pos leadingCoeff_one_add_X_pos
          (leadingCoeff_mul_pos leadingCoeff_one_add_X_pos l2)
      have hQ' : 2 ≤ (derivative ((1 + X) * ((1 + X) * nR (i + 2)))).roots.count a := by
        rw [derivative_one_add_X_sq_mul, count_roots_one_add_X_mul hD0 ha]
        exact hc'
      have h3 := count_roots_of_derivative hQr hQl hQ'
      rw [count_roots_one_add_X_mul (mul_ne_zero realRooted_one_add_X.1 hp.1) ha,
        count_roots_one_add_X_mul hp.1 ha] at h3
      have h4 := hα.count_le a
      have h5 : (nR (i + 1)).eval a = 0 := by
        have : 0 < (nR (i + 1)).roots.count a := by omega
        exact (isRoot_of_mem_roots (Multiset.count_pos.1 this)).eq_zero
      have h6 : (nR (i + 2)).eval a = 0 := by
        have : 0 < (nR (i + 2)).roots.count a := by omega
        exact (isRoot_of_mem_roots (Multiset.count_pos.1 this)).eq_zero
      exact ih (i + 2) (by omega) (by omega) ha h6 (by rw [show i + 2 - 1 = i + 1 by omega]; exact h5)

/-- **论文命题 8.11 的第二句**：`k ≥ 1` 时 `n_k` 除 `−1` 外的（实）根都是单根。 -/
theorem count_roots_nR_le_one {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : a ≠ -1) :
    (nR k).roots.count a ≤ 1 := by
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · rw [nR_one, roots_C, Multiset.count_zero]
    omega
  · by_contra hc
    have hle := (alpha_rel hk2).count_le a
    have hk1 : (nR (k - 1)).eval a = 0 := by
      have : 0 < (nR (k - 1)).roots.count a := by omega
      exact (isRoot_of_mem_roots (Multiset.count_pos.1 this)).eq_zero
    have hk0 : (nR k).eval a = 0 := by
      have : 0 < (nR k).roots.count a := by omega
      exact (isRoot_of_mem_roots (Multiset.count_pos.1 this)).eq_zero
    exact nR_no_common_root hk2 ha hk0 hk1

/-- **论文定理 8.1 第一句的「单根」部分**（复数形式）：`k ≥ 1` 时 `nrowPoly k` 在 `ℂ` 中除 `−1` 以外的根的重数都
`≤ 1`（根都是实数，`nrowPoly_root_im_eq_zero`；实根的重数在 `ℝ` 与 `ℂ` 中相同）。 -/
theorem rootMultiplicity_nrowPoly_le_one {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ≠ -1) :
    ((nrowPoly k).map (algebraMap ℚ ℂ)).rootMultiplicity z ≤ 1 := by
  have hmap : (nrowPoly k).map (algebraMap ℚ ℂ) = (nR k).map (algebraMap ℝ ℂ) := by
    rw [nR_eq_map, Polynomial.map_map]
    congr 1
  by_cases hroot : ((nrowPoly k).map (algebraMap ℚ ℂ)).IsRoot z
  · have him : z.im = 0 := by
      apply nrowPoly_root_im_eq_zero hk
      rw [aeval_def, eval₂_eq_eval_map]
      exact hroot
    have hz' : z = algebraMap ℝ ℂ z.re := by
      apply Complex.ext <;> simp [him]
    rw [hmap, hz', ← eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective, ← count_roots]
    apply count_roots_nR_le_one hk
    intro h
    apply hz
    rw [hz', h]
    simp
  · rw [rootMultiplicity_eq_zero hroot]
    exact zero_le_one

/-! ## 4. `h_k` 的根（论文定理 8.1 第二句） -/

/-- `h_k` 映到 `ℝ[X]`（`hpoly k` 见 `HNum.lean`：`Σ_m U_k(m)t^m = h_k(t)/(1−t)^{k+1}`）。 -/
def hR (k : ℕ) : ℝ[X] := (hpoly k).map (algebraMap ℚ ℝ)

theorem hR_ne_zero (k : ℕ) : hR k ≠ 0 := by
  rw [hR, Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective]
  intro h
  have := hpoly_eval_zero_eq_one k
  rw [h, eval_zero] at this
  exact zero_ne_one this

/-- 实数版的 `nrowPoly_eval`：`k ≥ 1`、`z ≠ −1` 时 `n_k(z) = (1+z)^{k−1}·h_k(z/(1+z))`。 -/
theorem nR_eval_hR {k : ℕ} (hk : 1 ≤ k) (z : ℝ) (hz : 1 + z ≠ 0) :
    (nR k).eval z = (1 + z) ^ (k - 1) * (hR k).eval (z / (1 + z)) := by
  rw [hR, hpoly_of_one_le hk, Polynomial.map_sum, nR, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_Icc] at hq
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, map_X,
    Polynomial.map_natCast, eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one, map_natCast]
  have h1 : 1 - z / (1 + z) = 1 / (1 + z) := by field_simp; ring
  have hp : (1 + z) ^ (k - 1) = (1 + z) ^ (q - 1) * (1 + z) ^ (k - q) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, hp, div_pow, div_pow, one_pow]
  field_simp

/-- `n_k` 在 `−1` 处的重数是 `⌈k/3⌉ − 1 = ⌊(k+2)/3⌋ − 1`（`rootMultiplicity_nrowPoly` 映到 `ℝ`）。 -/
theorem count_neg_one_nR {k : ℕ} (hk : 1 ≤ k) : (nR k).roots.count (-1) = (k + 2) / 3 - 1 := by
  rw [count_roots, nR_eq_map, ← rootMultiplicity_nrowPoly hk,
    eq_rootMultiplicity_map (p := nrowPoly k) (algebraMap ℚ ℝ).injective (-1), map_neg, map_one]

/-- `n_k` 除 `−1` 外恰有 `⌊2k/3⌋` 个不同的根（`k ≥ 1`）。 -/
theorem card_roots_nR_ne {k : ℕ} (hk : 1 ≤ k) :
    ((nR k).roots.toFinset.erase (-1)).card = 2 * k / 3 := by
  have hcard : Multiset.card (nR k).roots = k - 1 := by
    rw [(realRooted_nR hk).2, natDegree_nR hk]
  have hm := count_neg_one_nR hk
  have hsum := Multiset.toFinset_sum_count_eq (nR k).roots
  have hone : ∀ x ∈ (nR k).roots.toFinset.erase (-1), (nR k).roots.count x = 1 := by
    intro x hx
    rw [Finset.mem_erase, Multiset.mem_toFinset] at hx
    have h1 := count_roots_nR_le_one hk hx.1
    have h2 := Multiset.count_pos.2 hx.2
    omega
  have hsplit : (∑ x ∈ (nR k).roots.toFinset, (nR k).roots.count x) =
      (nR k).roots.count (-1) + ((nR k).roots.toFinset.erase (-1)).card := by
    by_cases hmem : (-1 : ℝ) ∈ (nR k).roots.toFinset
    · rw [← Finset.add_sum_erase _ _ hmem, Finset.card_eq_sum_ones, Finset.sum_congr rfl hone]
    · rw [Finset.erase_eq_of_notMem hmem,
        Multiset.count_eq_zero.2 (fun h => hmem (Multiset.mem_toFinset.2 h)), zero_add,
        Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun x hx => hone x ?_
      rw [Finset.erase_eq_of_notMem hmem]
      exact hx
  omega

/-- `z ↦ z/(1+z)`（把 `n_k` 的根换成 `h_k` 的根）。 -/
def zToT (z : ℝ) : ℝ := z / (1 + z)

/-- **论文定理 8.1 第二句**：对每个 `k ≥ 0`，`h_k`（映到 `ℝ[X]`）只有实根（实根计重数的个数等于次数），且根两两不同。 -/
theorem hR_realRooted_nodup (k : ℕ) : RealRooted (hR k) ∧ (hR k).roots.Nodup := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e : hR 0 = C 1 := by rw [hR, hpoly_zero, Polynomial.map_one, C_1]
    rw [e, roots_C]
    exact ⟨realRooted_C one_ne_zero, Multiset.nodup_zero⟩
  have hne := hR_ne_zero k
  have hdeg : (hR k).natDegree = 2 * k / 3 := by rw [hR, natDegree_map, natDegree_hpoly]
  have hinj : Set.InjOn zToT ((nR k).roots.toFinset.erase (-1) : Set ℝ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_erase] at hx hy
    have hx1 : 1 + x ≠ 0 := fun h => hx.1 (by linarith)
    have hy1 : 1 + y ≠ 0 := fun h => hy.1 (by linarith)
    simp only [zToT] at hxy
    rw [div_eq_div_iff hx1 hy1] at hxy
    linear_combination hxy
  have hsub : ((nR k).roots.toFinset.erase (-1)).image zToT ⊆ (hR k).roots.toFinset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [Finset.mem_erase, Multiset.mem_toFinset] at hz
    have hz1 : 1 + z ≠ 0 := fun h => hz.1 (by linarith)
    have h0 : (nR k).eval z = 0 := (isRoot_of_mem_roots hz.2).eq_zero
    rw [nR_eval_hR (by omega) z hz1] at h0
    have h1 : (hR k).eval (zToT z) = 0 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hz1)
    exact Multiset.mem_toFinset.2 ((mem_roots hne).2 h1)
  have h1 : 2 * k / 3 ≤ (hR k).roots.toFinset.card := by
    rw [← card_roots_nR_ne (by omega), ← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have h2 := Multiset.toFinset_card_le (hR k).roots
  have h3 := card_roots' (hR k)
  refine ⟨⟨hne, by omega⟩, ?_⟩
  rw [← Multiset.toFinset_card_eq_card_iff_nodup]
  omega

/-- 论文定理 8.1 第二句（复数形式）：`h_k` 的每个复根都是实数。 -/
theorem hpoly_root_im_eq_zero (k : ℕ) {z : ℂ} (hz : aeval z (hpoly k) = 0) : z.im = 0 := by
  apply (hR_realRooted_nodup k).1.im_eq_zero
  rw [hR, Polynomial.map_map]
  convert hz using 1
  rw [aeval_def, eval₂_eq_eval_map]
  congr 2

/-- 论文定理 8.1 第二句的「单根」：`h_k` 是 `ℚ` 上的可分多项式（与导数互素；等价地，在代数闭包里没有重根）。 -/
theorem separable_hpoly (k : ℕ) : (hpoly k).Separable := by
  have h := hR_realRooted_nodup k
  have hs : (hR k).Splits := splits_iff_card_roots.2 h.1.2
  have hsep : ((hpoly k).map (algebraMap ℚ ℝ)).Separable := (nodup_roots_iff_of_splits h.1.1 hs).1 h.2
  exact (separable_map (algebraMap ℚ ℝ)).1 hsep

/-- **论文定理 8.1**（合在一起）：对每个 `k ≥ 1`，`n_k` 的复根都是实数，除 `−1` 外都是单根；对每个 `k ≥ 0`，`h_k` 的
复根都是实数，且 `h_k` 是可分多项式（根都是单根）。 -/
theorem thm_realroots :
    (∀ k, 1 ≤ k → ∀ z : ℂ, aeval z (nrowPoly k) = 0 → z.im = 0) ∧
    (∀ k, 1 ≤ k → ∀ z : ℂ, z ≠ -1 → ((nrowPoly k).map (algebraMap ℚ ℂ)).rootMultiplicity z ≤ 1) ∧
    (∀ k, ∀ z : ℂ, aeval z (hpoly k) = 0 → z.im = 0) ∧ (∀ k, (hpoly k).Separable) :=
  ⟨fun _ hk _ hz => nrowPoly_root_im_eq_zero hk hz, fun _ hk _ hz => rootMultiplicity_nrowPoly_le_one hk hz,
    fun k _ hz => hpoly_root_im_eq_zero k hz, separable_hpoly⟩

end

end A207123
