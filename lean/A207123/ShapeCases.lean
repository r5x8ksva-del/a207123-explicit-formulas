import A207123.ShapeNT
import A207123.SingleSum

/-!
# 论文定理 6.3：单族二项式形状的分类

论文定理 6.3：`m ≥ 1`，`α, β ≥ 0` 不全为 0。存在整数 `c, d, s₀, k₀ ≥ 0` 与复数 `A(s)`（`s ≥ s₀`，与 `k` 无关）使
`U_k(m) = Σ_{s≥s₀} A(s)·C(k+c−αs, βs+d)` 对所有 `k ≥ k₀` 成立，当且仅当 `α + β = 1`（主定理 `thm_shapes`；表示的
定义 `ShapeRep` 在 `ShapeFibre.lean`）。

* `α + β = 1`：对任何数列 `f` 都有表示。`(0,1)` 是 Newton 前向差分公式（Mathlib 的 `shift_eq_sum_fwdDiff_iter`，
  `shape_01`），`(1,0)` 是 `f(k) = Σ_{s≤k}(f(s) − f(s−1))`（`shape_10`）。
* `(2,1)` 是定理 6.1（`not_shape_21`，由 `thm_S`）。其余 `α + β ≥ 2` 的形状用 `ShapeFibre.lean` 的纤维引理：`b_1` 的
  根 `ξ` 所在的纤维上每个点都是某个 `b_w` 的根（`exists_b_root_of_Ppoly`），再分情形：
  - `α, β ≥ 1`、`α ≠ 2β`（`not_shape_a`）：纤维多项式 `ψ = X^{α+β} − v₀(1−X)^β` 的根 `η_i` 满足 `w_iη_i³ = 1 − η_i`，
    `∏ w_i · (∏ η_i)³ = ψ(1) = 1`、`∏ η_i = ±v₀`，`v₀ = ξ^{α−2β}`，所以 `ξ^{3|α−2β|}` 是有理数，与 `real_root_pow_not_rat`
    矛盾（论文同此）。
  - `β = 0`、`α ≥ 2`（`not_shape_b`）：纤维含 `z = ξζ`（`ζ = e^{2πi/α}`）。论文用「分圆域是 Abel 扩张而 `ℚ(ξ)` 不正规」；
    这里直接算：`z` 是实数时 `z = −ξ`，`b_w(−ξ) > 0`；否则 `z, z̄` 都是 `b_w` 的根，韦达关系给出
    `w²ξ⁶ − wξ⁴ − 1 = 0`，化成 `ξ` 的有理二次关系，只能 `w = 0`。
  - `α = 2β`、`β ≥ 2`（`not_shape_c`）：纤维含 `u(η) = ζ`（`ζ ≠ 1` 是 `β` 次单位根）的点，而 `b_w(η) = 0` 要 `wζ = 1`。
  - `α = 0`、`β ≥ 2`（`not_shape_d`）：`β` 偶时纤维含 `x = 1/(1 − ξ²) > 1`，`b_w(x) < 0`；`β` 奇时 `∏_ζ w_ζ = χ(ξ)²`，
    `χ = X^{3β} + X^β`，于是复根 `ξ₂` 也满足 `χ(ξ₂)² = χ(ξ)²`（`aeval_root_b1_eq_zero`），而 `|χ(ξ₂)| > |χ(ξ)|`。
    论文还用「三次域没有二次子域」得 `χ(ξ) ∈ ℚ`，这里不需要。
-/

namespace A207123

open Polynomial

noncomputable section

/-- `P_m(η) = 0` 时 `η` 是某个 `b_w`（`w ≤ m`）的根：`w·η³ = 1 − η`。 -/
theorem exists_b_root_of_Ppoly {m : ℕ} {η : ℂ} (h : (Ppoly ℂ m).eval η = 0) :
    ∃ w : ℕ, w ≤ m ∧ (w : ℂ) * η ^ 3 = 1 - η := by
  rw [Ppoly, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨w, hw, hb⟩ := h
  refine ⟨w, Nat.lt_succ_iff.1 (Finset.mem_range.1 hw), ?_⟩
  simp only [bpoly, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow] at hb
  linear_combination -hb

theorem real_root_facts :
    ∃ r : ℝ, r ^ 3 + r - 1 = 0 ∧ 2 / 3 < r ∧ r < 1 ∧ (r : ℂ) ^ 3 + (r : ℂ) - 1 = 0 := by
  obtain ⟨r, hr, h1, h2⟩ := exists_real_root_b1
  exact ⟨r, hr, h1, h2, by exact_mod_cast hr⟩

theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have h1 := congrArg norm h
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).1 h1

/-! ## 1. 情形 `α = 2β ≥ 4` -/

theorem not_shape_c {m β : ℕ} (hm : 1 ≤ m) (hβ : 2 ≤ β) :
    ¬ ShapeRep (fun k => (U k m : ℂ)) (2 * β) β := by
  intro hrep
  obtain ⟨r, -, -, -, hξ⟩ := real_root_facts
  have hζp := Complex.isPrimitiveRoot_exp β (by omega)
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (2 * Real.pi * Complex.I / β) := ⟨_, rfl⟩
  rw [← hζdef] at hζp
  have hζβ : ζ ^ β = 1 := hζp.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζp.ne_one (by omega)
  have hζn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (by omega) hζβ
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζn
    norm_num at hζn
  -- `η` 是 `T³ + ζT − ζ` 的根：`u(η) = η³/(1−η) = ζ`
  obtain ⟨η, hη⟩ : ∃ η : ℂ, η ^ 3 = ζ * (1 - η) := by
    have hdeg : (X ^ 3 + C ζ * X - C ζ : ℂ[X]).degree = 3 := by compute_degree!
    obtain ⟨η, hη⟩ := Complex.exists_root (f := X ^ 3 + C ζ * X - C ζ) (by rw [hdeg]; norm_num)
    refine ⟨η, ?_⟩
    simp only [IsRoot, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hη
    linear_combination hη
  have hη0 : η ≠ 0 := by
    intro h
    rw [h] at hη
    exact hζ0 (by linear_combination -hη)
  have h1η : 1 - η ≠ 0 := by
    intro h
    have e : η = 1 := by linear_combination -h
    rw [e] at hη
    exact one_ne_zero (by linear_combination hη : (1 : ℂ) = 0)
  have hfib : η ^ (2 * β + β) * (1 - (r : ℂ)) ^ β = (r : ℂ) ^ (2 * β + β) * (1 - η) ^ β := by
    have h1 : 1 - (r : ℂ) = (r : ℂ) ^ 3 := by linear_combination -hξ
    rw [h1, show 2 * β + β = 3 * β by ring, pow_mul, pow_mul, hη, mul_pow, hζβ, one_mul]
    ring
  obtain ⟨w, -, hw⟩ := exists_b_root_of_Ppoly (shape_fibre_x hm (by omega) hrep hξ hη0 hfib)
  have hwζ : (w : ℂ) * ζ = 1 := by
    have h2 : (1 - η) * ((w : ℂ) * ζ - 1) = 0 := by linear_combination hw - (w : ℂ) * hη
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h h1η
    · linear_combination h
  have hw1 : (w : ℝ) = 1 := by
    have h3 := congrArg norm hwζ
    rw [norm_mul, hζn, mul_one, norm_one, Complex.norm_natCast] at h3
    exact h3
  have hw1' : (w : ℂ) = 1 := by exact_mod_cast hw1
  rw [hw1', one_mul] at hwζ
  exact hζ1 hwζ

/-! ## 2. 情形 `α, β ≥ 1`、`α ≠ 2β` -/

theorem not_shape_a {m α β : ℕ} (hm : 1 ≤ m) (hα : 1 ≤ α) (hβ : 1 ≤ β) (he : α ≠ 2 * β) :
    ¬ ShapeRep (fun k => (U k m : ℂ)) α β := by
  intro hrep
  obtain ⟨r, hr, hr23, hr1, hξ⟩ := real_root_facts
  have hr0 : 0 < r := by linarith
  obtain ⟨hξ0, h1ξ, -⟩ := ne_zero_of_root_b1 hξ
  have h1ξ3 : 1 - (r : ℂ) = (r : ℂ) ^ 3 := by linear_combination -hξ
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℂ, v = (r : ℂ) ^ (α + β) / (1 - (r : ℂ)) ^ β := ⟨_, rfl⟩
  have hv : v₀ * (1 - (r : ℂ)) ^ β = (r : ℂ) ^ (α + β) := by
    rw [hv₀, div_mul_cancel₀ _ (pow_ne_zero _ h1ξ)]
  have hv0 : v₀ ≠ 0 := by
    rw [hv₀]
    exact div_ne_zero (pow_ne_zero _ hξ0) (pow_ne_zero _ h1ξ)
  -- 纤维多项式 `ψ = X^{α+β} − v₀(1−X)^β`（首一、`α+β` 次）
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ[X], ψ = X ^ (α + β) - C v₀ * (1 - X) ^ β := ⟨_, rfl⟩
  have hlowN : (C v₀ * (1 - X) ^ β : ℂ[X]).natDegree ≤ β := by
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_pow_le.trans ?_
    have h2 : (1 - X : ℂ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    calc β * (1 - X : ℂ[X]).natDegree ≤ β * 1 := Nat.mul_le_mul_left β h2
      _ = β := mul_one β
  have hψm : ψ.Monic := by
    rw [hψ]
    exact monic_X_pow_sub ((degree_le_of_natDegree_le hlowN).trans_lt
      (by exact_mod_cast (show β < α + β by omega)))
  have hψd : ψ.natDegree = α + β := by
    rw [hψ, natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega), natDegree_X_pow]
  have hcard : Multiset.card ψ.roots = ψ.natDegree := splits_iff_card_roots.1 (IsAlgClosed.splits ψ)
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hψm.leadingCoeff, C_1, one_mul] at hprod
  have hψ0 : ψ.eval 0 = -v₀ := by
    rw [hψ]
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one, sub_zero, one_pow, mul_one]
    rw [zero_pow (by omega), zero_sub]
  have hψ1 : ψ.eval 1 = 1 := by
    rw [hψ]
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one, sub_self, one_pow]
    rw [zero_pow (by omega), mul_zero, sub_zero]
  -- 每个根都在纤维上，是某个 `b_w` 的根
  have hroot : ∀ η ∈ ψ.roots, ∃ w : ℕ, (w : ℂ) * η ^ 3 = 1 - η := by
    intro η hη
    have hev : ψ.eval η = 0 := (mem_roots hψm.ne_zero).1 hη
    rw [hψ] at hev
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one] at hev
    have hη0 : η ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega), sub_zero, one_pow, mul_one, zero_sub, neg_eq_zero] at hev
      exact hv0 hev
    have hfib : η ^ (α + β) * (1 - (r : ℂ)) ^ β = (r : ℂ) ^ (α + β) * (1 - η) ^ β := by
      linear_combination (1 - (r : ℂ)) ^ β * hev + (1 - η) ^ β * hv
    obtain ⟨w, -, hw⟩ := exists_b_root_of_Ppoly (shape_fibre_x hm hα hrep hξ hη0 hfib)
    exact ⟨w, hw⟩
  choose! wf hwf using hroot
  -- `(∏ w)·(∏ η)³ = ∏(1 − η) = ψ(1) = 1`，`(−1)^{α+β} ∏ η = ψ(0) = −v₀`
  have hP1 : (ψ.roots.map (fun η => (wf η : ℂ))).prod * ψ.roots.prod ^ 3 = 1 := by
    have e1 : (ψ.roots.map (fun η => (wf η : ℂ) * η ^ 3)).prod = (ψ.roots.map (fun η => 1 - η)).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl fun η hη => hwf η hη)
    have e2 : (ψ.roots.map (fun η => 1 - η)).prod = ψ.eval 1 := by
      conv_rhs => rw [← hprod]
      rw [eval_multiset_prod, Multiset.map_map]
      simp only [Function.comp_def, eval_sub, eval_X, eval_C]
    rw [Multiset.prod_map_mul, Multiset.prod_map_pow, Multiset.map_id', e2, hψ1] at e1
    exact e1
  have hP0 : (-1 : ℂ) ^ (α + β) * ψ.roots.prod = -v₀ := by
    rw [← hψ0]
    conv_rhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub]
    rw [Multiset.prod_map_neg, hcard, hψd]
  obtain ⟨W, hW⟩ : ∃ W : ℕ, (W : ℂ) = (ψ.roots.map (fun η => (wf η : ℂ))).prod :=
    ⟨(ψ.roots.map wf).prod, by rw [Nat.cast_multiset_prod, Multiset.map_map]; try rfl⟩
  rw [← hW] at hP1
  obtain ⟨t, ht⟩ : ∃ t : ℚ, (t : ℂ) = (-1 : ℂ) ^ (α + β) := ⟨(-1) ^ (α + β), by norm_num⟩
  have hsq : (t : ℂ) ^ 2 = 1 := by rw [ht, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hRp : ψ.roots.prod = -(t : ℂ) * v₀ := by
    have h2 : ((-1 : ℂ) ^ (α + β)) ^ 2 = 1 := by rw [← ht]; exact hsq
    rw [ht]
    linear_combination (-1 : ℂ) ^ (α + β) * hP0 - ψ.roots.prod * h2
  rw [hRp] at hP1
  have hrv : v₀ * (r : ℂ) ^ (3 * β) = (r : ℂ) ^ (α + β) := by rw [pow_mul, ← h1ξ3]; exact hv
  rcases lt_or_gt_of_ne he with hlt | hgt
  · -- `α < 2β`：`v₀ r^k = 1`，`k = 2β − α`
    obtain ⟨k, hk⟩ : ∃ k, 2 * β = α + k := ⟨2 * β - α, by omega⟩
    have hvk : v₀ * (r : ℂ) ^ k = 1 := by
      have e : (r : ℂ) ^ (3 * β) = (r : ℂ) ^ (α + β) * (r : ℂ) ^ k := by
        rw [← pow_add]
        congr 1
        omega
      rw [e] at hrv
      have hne : (r : ℂ) ^ (α + β) ≠ 0 := pow_ne_zero _ hξ0
      apply mul_right_cancel₀ hne
      linear_combination hrv
    apply real_root_pow_not_rat hr hr0 hr1 (N := 3 * k) (by omega) (-t * W)
    push_cast
    rw [mul_comm 3 k, pow_mul]
    linear_combination (-((r : ℂ) ^ k) ^ 3) * hP1 -
      (W : ℂ) * (t : ℂ) ^ 3 * ((v₀ * (r : ℂ) ^ k) ^ 2 + v₀ * (r : ℂ) ^ k + 1) * hvk - (W : ℂ) * t * hsq
  · -- `α > 2β`：`v₀ = r^k`，`k = α − 2β`
    obtain ⟨k, hk⟩ : ∃ k, α = 2 * β + k := ⟨α - 2 * β, by omega⟩
    have hvk : v₀ = (r : ℂ) ^ k := by
      have e : (r : ℂ) ^ (α + β) = (r : ℂ) ^ (3 * β) * (r : ℂ) ^ k := by
        rw [← pow_add]
        congr 1
        omega
      rw [e] at hrv
      have hne : (r : ℂ) ^ (3 * β) ≠ 0 := pow_ne_zero _ hξ0
      apply mul_right_cancel₀ hne
      linear_combination hrv
    rw [hvk] at hP1
    have hW0 : (W : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hP1
      exact zero_ne_one hP1
    apply real_root_pow_not_rat hr hr0 hr1 (N := 3 * k) (by omega) (-t / W)
    push_cast
    rw [eq_div_iff hW0, mul_comm 3 k, pow_mul]
    linear_combination (-(t : ℂ)) * hP1 - ((r : ℂ) ^ k) ^ 3 * W * ((t : ℂ) ^ 2 + 1) * hsq

/-! ## 3. 情形 `β = 0`、`α ≥ 2` -/

theorem not_shape_b {m α : ℕ} (hm : 1 ≤ m) (hα : 2 ≤ α) : ¬ ShapeRep (fun k => (U k m : ℂ)) α 0 := by
  intro hrep
  obtain ⟨r, hr, hr23, hr1, hξ⟩ := real_root_facts
  have hr0 : 0 < r := by linarith
  have hζp := Complex.isPrimitiveRoot_exp α (by omega)
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (2 * Real.pi * Complex.I / α) := ⟨_, rfl⟩
  rw [← hζdef] at hζp
  have hζα : ζ ^ α = 1 := hζp.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζp.ne_one (by omega)
  have hζn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (by omega) hζα
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (r : ℂ) * ζ := ⟨_, rfl⟩
  have hzn : ‖z‖ = r := by
    rw [hz, norm_mul, hζn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzn
    linarith
  have hfib : z ^ (α + 0) * (1 - (r : ℂ)) ^ 0 = (r : ℂ) ^ (α + 0) * (1 - z) ^ 0 := by
    rw [add_zero, pow_zero, pow_zero, mul_one, mul_one, hz, mul_pow, hζα, mul_one]
  obtain ⟨w, -, hw⟩ := exists_b_root_of_Ppoly (shape_fibre_x hm (by omega) hrep hξ hz0 hfib)
  have hP : z * (starRingEnd ℂ) z = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj', hzn]
  by_cases hreal : (starRingEnd ℂ) z = z
  · -- `z` 是实数：`z² = r²`
    rw [hreal] at hP
    have h2 : (z - r) * (z + r) = 0 := by linear_combination hP
    rcases mul_eq_zero.1 h2 with h | h
    · apply hζ1
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      apply mul_left_cancel₀ hrc
      rw [mul_one, ← hz]
      linear_combination h
    · have hzr : z = -(r : ℂ) := by linear_combination h
      rw [hzr] at hw
      have hwr : (w : ℝ) * (-r) ^ 3 = 1 - (-r) := by exact_mod_cast hw
      nlinarith [pow_pos hr0 3, (Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  · -- `z` 不是实数：`z, z̄` 都是 `b_w` 的根
    obtain ⟨zb, hzb⟩ : ∃ zb : ℂ, zb = (starRingEnd ℂ) z := ⟨_, rfl⟩
    rw [← hzb] at hP hreal
    have hwb : (w : ℂ) * zb ^ 3 = 1 - zb := by
      have h3 := congrArg (starRingEnd ℂ) hw
      simp only [map_mul, map_pow, map_sub, map_one, map_natCast] at h3
      rw [← hzb] at h3
      exact h3
    have hne : z - zb ≠ 0 := sub_ne_zero.2 (Ne.symm hreal)
    have E3 : 1 + (w : ℂ) * (z ^ 2 + z * zb + zb ^ 2) = 0 := by
      have h3 : (z - zb) * (1 + (w : ℂ) * (z ^ 2 + z * zb + zb ^ 2)) = 0 := by
        linear_combination hw - hwb
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hne
      · exact h
    have E4 : (w : ℂ) * (z * zb) * (z + zb) + 1 = 0 := by
      linear_combination (1 / 2 : ℂ) * (z + zb) * E3 - (1 / 2 : ℂ) * hw - (1 / 2 : ℂ) * hwb
    have G : (w : ℂ) ^ 2 * (z * zb) ^ 3 - (w : ℂ) * (z * zb) ^ 2 - 1 = 0 := by
      linear_combination (-(w : ℂ) * (z * zb) ^ 2) * E3 + ((w : ℂ) * (z * zb) * (z + zb) - 1) * E4
    rw [hP] at G
    have Q : (((w : ℚ) ^ 2 - 1 : ℚ) : ℂ) + ((-(2 * (w : ℚ) ^ 2 + w) : ℚ) : ℂ) * (r : ℂ) +
        (((w : ℚ) ^ 2 + w : ℚ) : ℂ) * (r : ℂ) ^ 2 = 0 := by
      push_cast
      linear_combination G - ((w : ℂ) ^ 2 * ((r : ℂ) ^ 3 - r + 1) - (w : ℂ) * r) * hξ
    obtain ⟨-, -, hc⟩ := quad_rel_root_b1 hξ Q
    have hw0 : w = 0 := by
      have h4 : (w : ℚ) * (w + 1) = 0 := by linear_combination hc
      rcases mul_eq_zero.1 h4 with h | h
      · exact_mod_cast h
      · have : (0 : ℚ) ≤ w := Nat.cast_nonneg w
        linarith
    rw [hw0, Nat.cast_zero, zero_mul] at hw
    have hz1 : z = 1 := by linear_combination hw
    apply hreal
    rw [hzb, hz1, map_one]

/-! ## 4. 情形 `α = 0`、`β ≥ 2` -/

theorem not_shape_d {m β : ℕ} (hm : 1 ≤ m) (hβ : 2 ≤ β) : ¬ ShapeRep (fun k => (U k m : ℂ)) 0 β := by
  intro hrep
  obtain ⟨r, hr, hr23, hr1, hξ⟩ := real_root_facts
  have hr0 : 0 < r := by linarith
  have hrc0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have h1ξ3 : 1 - (r : ℂ) = (r : ℂ) ^ 3 := by linear_combination -hξ
  rcases Nat.even_or_odd β with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- `β` 偶：`y = −1/ξ²`，`x = y/(1+y) = 1/(1 − ξ²) > 1`
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y = -1 / (r : ℂ) ^ 2 := ⟨_, rfl⟩
    have hyr : y * (r : ℂ) ^ 2 = -1 := by rw [hy, div_mul_cancel₀ _ (pow_ne_zero _ hrc0)]
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_mul] at hyr
      norm_num at hyr
    have hr2 : 1 - r ^ 2 ≠ 0 := by
      intro h
      nlinarith
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (1 - r ^ 2) := ⟨_, rfl⟩
    have hxr : x * (1 - r ^ 2) = 1 := by rw [hx, div_mul_cancel₀ _ hr2]
    have hxrc : (x : ℂ) * (1 - (r : ℂ) ^ 2) = 1 := by exact_mod_cast hxr
    have hy1 : 1 + y ≠ 0 := by
      intro h
      have : (r : ℂ) ^ 2 - 1 = 0 := by linear_combination (r : ℂ) ^ 2 * h - hyr
      apply hr2
      have h5 : r ^ 2 - 1 = 0 := by exact_mod_cast this
      linarith
    have hfib : y ^ β * (1 - (r : ℂ)) ^ β = (r : ℂ) ^ β := by
      have hneg : (-1 : ℂ) ^ β = 1 := Even.neg_one_pow ⟨j, hj⟩
      have e1 : y ^ β * (r : ℂ) ^ (2 * β) = 1 := by
        rw [pow_mul, ← mul_pow, hyr, hneg]
      rw [h1ξ3]
      calc y ^ β * ((r : ℂ) ^ 3) ^ β = (y ^ β * (r : ℂ) ^ (2 * β)) * (r : ℂ) ^ β := by ring
        _ = (r : ℂ) ^ β := by rw [e1, one_mul]
    have hP := shape_fibre_y hm (by omega) hrep hξ hy0 hy1 hfib
    have hxy : y / (1 + y) = (x : ℂ) := by
      rw [div_eq_iff hy1]
      linear_combination (-y) * hxrc - (x : ℂ) * hyr
    rw [hxy] at hP
    obtain ⟨w, -, hw⟩ := exists_b_root_of_Ppoly hP
    have hwx : (w : ℝ) * x ^ 3 = 1 - x := by exact_mod_cast hw
    have hx1 : 1 < x := by
      rw [hx, lt_div_iff₀ (by nlinarith)]
      nlinarith
    nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 3, (Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  · -- `β` 奇：对一切 `β` 次单位根 `ζ`，`x_ζ = ζ/(ξ² + ζ)`
    have hζp := Complex.isPrimitiveRoot_exp β (by omega)
    obtain ⟨μ, hμ⟩ : ∃ μ : Finset ℂ, μ = Polynomial.nthRootsFinset β (1 : ℂ) := ⟨_, rfl⟩
    have hμmem : ∀ ζ ∈ μ, ζ ^ β = 1 := fun ζ hζ => by
      rw [hμ, Polynomial.mem_nthRootsFinset (by omega)] at hζ
      exact hζ
    have hμcard : μ.card = β := by rw [hμ]; exact hζp.card_nthRootsFinset
    have hprodX : ∀ t : ℂ, t ^ β - 1 = ∏ ζ ∈ μ, (t - ζ) := by
      intro t
      have h0 := congrArg (eval t) (X_pow_sub_one_eq_prod (by omega) hζp)
      rw [hμ]
      simpa [eval_prod] using h0
    have hodd : (-1 : ℂ) ^ β = -1 := Odd.neg_one_pow ⟨j, hj⟩
    have hprodζ : ∏ ζ ∈ μ, ζ = 1 := by
      have h0 := hprodX 0
      rw [Finset.prod_congr rfl (fun ζ _ => (show (0 : ℂ) - ζ = (-1) * ζ by ring)), Finset.prod_mul_distrib,
        Finset.prod_const, hμcard, hodd, zero_pow (by omega)] at h0
      linear_combination h0
    have hprodξ : ∏ ζ ∈ μ, ((r : ℂ) ^ 2 + ζ) = (r : ℂ) ^ (2 * β) + 1 := by
      have h0 := hprodX (-(r : ℂ) ^ 2)
      rw [Finset.prod_congr rfl (fun ζ _ => (show -(r : ℂ) ^ 2 - ζ = (-1) * ((r : ℂ) ^ 2 + ζ) by ring)),
        Finset.prod_mul_distrib, Finset.prod_const, hμcard, hodd, neg_pow, hodd, ← pow_mul] at h0
      linear_combination h0
    -- 每个 `ζ` 给出 `w_ζ ζ³ = ξ²(ξ² + ζ)²`
    have hw : ∀ ζ ∈ μ, ∃ w : ℕ, (w : ℂ) * ζ ^ 3 = (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + ζ) ^ 2 := by
      intro ζ hζ
      have hζβ := hμmem ζ hζ
      have hζn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (by omega) hζβ
      have hζ0 : ζ ≠ 0 := by
        intro h
        rw [h, norm_zero] at hζn
        norm_num at hζn
      have hsum0 : (r : ℂ) ^ 2 + ζ ≠ 0 := by
        intro h
        have e : ζ = -(r : ℂ) ^ 2 := by linear_combination h
        rw [e, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le] at hζn
        nlinarith
      obtain ⟨y, hy⟩ : ∃ y : ℂ, y = ζ / (r : ℂ) ^ 2 := ⟨_, rfl⟩
      have hyr : y * (r : ℂ) ^ 2 = ζ := by rw [hy, div_mul_cancel₀ _ (pow_ne_zero _ hrc0)]
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, zero_mul] at hyr
        exact hζ0 hyr.symm
      have hy1 : 1 + y ≠ 0 := by
        intro h
        apply hsum0
        linear_combination (r : ℂ) ^ 2 * h - hyr
      have hfib : y ^ β * (1 - (r : ℂ)) ^ β = (r : ℂ) ^ β := by
        have e1 : y ^ β * (r : ℂ) ^ (2 * β) = 1 := by
          rw [pow_mul, ← mul_pow, hyr, hζβ]
        rw [h1ξ3]
        calc y ^ β * ((r : ℂ) ^ 3) ^ β = (y ^ β * (r : ℂ) ^ (2 * β)) * (r : ℂ) ^ β := by ring
          _ = (r : ℂ) ^ β := by rw [e1, one_mul]
      have hP := shape_fibre_y hm (by omega) hrep hξ hy0 hy1 hfib
      have hx : y / (1 + y) = ζ / ((r : ℂ) ^ 2 + ζ) := by
        rw [div_eq_div_iff hy1 hsum0]
        linear_combination hyr
      rw [hx] at hP
      obtain ⟨w, -, hwx⟩ := exists_b_root_of_Ppoly hP
      refine ⟨w, ?_⟩
      have hS3 : ((r : ℂ) ^ 2 + ζ) ^ 3 ≠ 0 := pow_ne_zero _ hsum0
      have e2 : (w : ℂ) * ζ ^ 3 = (w : ℂ) * (ζ / ((r : ℂ) ^ 2 + ζ)) ^ 3 * ((r : ℂ) ^ 2 + ζ) ^ 3 := by
        rw [div_pow, mul_assoc, div_mul_cancel₀ _ hS3]
      have e4 : ζ / ((r : ℂ) ^ 2 + ζ) * ((r : ℂ) ^ 2 + ζ) = ζ := div_mul_cancel₀ ζ hsum0
      have e3 : (1 - ζ / ((r : ℂ) ^ 2 + ζ)) * ((r : ℂ) ^ 2 + ζ) ^ 3 =
          (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + ζ) ^ 2 := by
        linear_combination (-(((r : ℂ) ^ 2 + ζ) ^ 2)) * e4
      rw [e2, hwx, e3]
    choose! wf hwf using hw
    have hL : ∏ ζ ∈ μ, ((wf ζ : ℂ) * ζ ^ 3) = (∏ ζ ∈ μ, (wf ζ : ℂ)) * (∏ ζ ∈ μ, ζ) ^ 3 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]
    have hR : ∏ ζ ∈ μ, ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + ζ) ^ 2) =
        (r : ℂ) ^ (2 * β) * (∏ ζ ∈ μ, ((r : ℂ) ^ 2 + ζ)) ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hμcard, Finset.prod_pow, ← pow_mul]
    have e := Finset.prod_congr rfl hwf
    rw [hL, hR, hprodζ, one_pow, mul_one, hprodξ] at e
    obtain ⟨W, hW⟩ : ∃ W : ℕ, (W : ℂ) = ∏ ζ ∈ μ, (wf ζ : ℂ) := ⟨∏ ζ ∈ μ, wf ζ, Nat.cast_prod _ _⟩
    rw [← hW] at e
    -- `χ(ξ)² = W`，所以复根 `ξ₂` 也满足 `χ(ξ₂)² = W`
    have hχ : ((r : ℂ) ^ (3 * β) + (r : ℂ) ^ β) ^ 2 = W := by
      rw [e]
      ring
    obtain ⟨z, hz, hnz⟩ := complex_root_b1 hr
    have hg : aeval (r : ℂ) ((X ^ (3 * β) + X ^ β) ^ 2 - C (W : ℚ) : ℚ[X]) = 0 := by
      simp only [map_sub, map_pow, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_natCast]
      rw [hχ, sub_self]
    have hgz := aeval_root_b1_eq_zero hξ hz hg
    simp only [map_sub, map_pow, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_natCast, sub_eq_zero] at hgz
    -- 取模比较
    have hAB : ‖z ^ (3 * β) + z ^ β‖ = r ^ (3 * β) + r ^ β := by
      have h6 : ‖z ^ (3 * β) + z ^ β‖ ^ 2 = (r ^ (3 * β) + r ^ β) ^ 2 := by
        have h7 := congrArg norm (hgz.trans hχ.symm)
        rw [norm_pow, norm_pow] at h7
        rw [h7]
        congr 1
        rw [show ((r : ℂ) ^ (3 * β) + (r : ℂ) ^ β) = ((r ^ (3 * β) + r ^ β : ℝ) : ℂ) by norm_cast,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h6
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ‖z‖ ^ β := ⟨_, rfl⟩
    have hz2 : ‖z‖ ^ 2 = r ^ 2 + 1 := by rw [← Complex.normSq_eq_norm_sq, hnz]
    have hρ2 : ρ ^ 2 * r ^ β = 1 := by
      rw [hρ, ← pow_mul, mul_comm β 2, pow_mul, hz2, ← mul_pow]
      rw [show (r ^ 2 + 1) * r = 1 by linear_combination hr, one_pow]
    have hρ3 : 3 < ρ ^ 2 := by
      have h8 : ρ ^ 2 = (r ^ 2 + 1) ^ β := by rw [hρ, ← pow_mul, mul_comm β 2, pow_mul, hz2]
      have h9 : (r ^ 2 + 1) ^ 3 ≤ (r ^ 2 + 1) ^ β := pow_le_pow_right₀ (by nlinarith) (by omega)
      have hs : 13 / 9 < r ^ 2 + 1 := by nlinarith
      have h10 : 3 < (r ^ 2 + 1) ^ 3 := by
        have h11 := pow_lt_pow_left₀ hs (by norm_num) (show (3 : ℕ) ≠ 0 by norm_num)
        norm_num at h11
        linarith
      linarith
    have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
    have hlow : ρ ^ 3 - ρ ≤ ‖z ^ (3 * β) + z ^ β‖ := by
      have h11 := norm_sub_le (z ^ (3 * β) + z ^ β) (z ^ β)
      rw [add_sub_cancel_right, norm_pow, norm_pow] at h11
      rw [hρ, ← pow_mul, mul_comm β 3]
      linarith
    have hup : r ^ (3 * β) + r ^ β ≤ 2 * r ^ β := by
      have := pow_le_pow_of_le_one hr0.le hr1.le (show β ≤ 3 * β by omega)
      linarith
    have h12 : (ρ ^ 3 - ρ) * ρ ^ 2 ≤ 2 * r ^ β * ρ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ρ)
    have h13 : 2 * r ^ β * ρ ^ 2 = 2 := by linear_combination 2 * hρ2
    have hρ1 : 1 < ρ := by nlinarith
    have hρ1' : 1 < ρ ^ 3 := one_lt_pow₀ hρ1 (by norm_num)
    nlinarith

/-! ## 5. 定理 6.3 -/

/-- `(2,1)` 是定理 6.1。 -/
theorem not_shape_21 {m : ℕ} (hm : 1 ≤ m) : ¬ ShapeRep (fun k => (U k m : ℂ)) 2 1 := by
  rintro ⟨c, d, s₀, k₀, A, hA⟩
  apply thm_S hm
  refine ⟨c, d - m, k₀, fun s => if s₀ ≤ s then A s else 0, fun k hk => (hA k hk).trans ?_⟩
  refine finsum_congr fun s => ?_
  have e1 : (k : ℤ) + c - ((2 : ℕ) : ℤ) * s = (k : ℤ) + c - 2 * s := by norm_num
  have e2 : ((1 : ℕ) : ℤ) * s + d = (m : ℤ) + s + (d - m) := by push_cast; ring
  dsimp only
  split_ifs
  · rw [e1, e2]
  · rw [zero_mul]

/-- `(1,0)`：每个数列都有 `f(k) = Σ_{0≤s≤k} (f(s) − f(s−1))·C(k−s, 0)`（`f(−1) = 0`）。 -/
theorem shape_10 (f : ℕ → ℂ) : ShapeRep f 1 0 := by
  refine ⟨0, 0, 0, 0, fun s => f s.toNat - if 1 ≤ s then f (s - 1).toNat else 0,
    fun k hk => ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (k + 1)).map Nat.castEmbedding) ?_]
  · rw [Finset.sum_map]
    have hterm : ∀ t ∈ Finset.range (k + 1),
        (if (0 : ℤ) ≤ (Nat.castEmbedding t : ℤ) then (f (Nat.castEmbedding t : ℤ).toNat -
          if 1 ≤ (Nat.castEmbedding t : ℤ) then f ((Nat.castEmbedding t : ℤ) - 1).toNat else 0) *
          (binomZ (k + 0 - ((1 : ℕ) : ℤ) * (Nat.castEmbedding t : ℤ)) (((0 : ℕ) : ℤ) * (Nat.castEmbedding t : ℤ) + 0) : ℂ)
          else 0) = f t - if 1 ≤ t then f (t - 1) else 0 := by
      intro t ht
      have htk : t ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
      simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
      rw [ite_eq_left (by omega)]
      have hb : binomZ ((k : ℤ) + 0 - ((1 : ℕ) : ℤ) * (t : ℤ)) (((0 : ℕ) : ℤ) * (t : ℤ) + 0) = 1 := by
        unfold binomZ
        rw [ite_eq_left (by push_cast; omega)]
        simp
      rw [hb, Nat.cast_one, mul_one]
      by_cases h1 : 1 ≤ t
      · rw [ite_eq_left (by exact_mod_cast h1), ite_eq_left h1, show ((t : ℤ) - 1).toNat = t - 1 by omega]
      · rw [ite_eq_right (by exact_mod_cast h1), ite_eq_right h1]
    rw [Finset.sum_congr rfl hterm]
    clear hterm hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih, ite_eq_left (by omega), Nat.add_sub_cancel]
      ring
  · intro s hs
    simp only [Function.mem_support, ne_eq] at hs
    have hs0 : 0 ≤ s := by
      by_contra h
      exact hs (by rw [ite_eq_right h])
    rw [ite_eq_left hs0] at hs
    have hb : binomZ ((k : ℤ) + 0 - ((1 : ℕ) : ℤ) * s) (((0 : ℕ) : ℤ) * s + 0) ≠ 0 := by
      intro h0
      apply hs
      rw [h0, Nat.cast_zero, mul_zero]
    unfold binomZ at hb
    have hsk : s ≤ k := by
      by_contra h
      apply hb
      rw [ite_eq_right (by push_cast; omega)]
    rw [Finset.mem_coe, Finset.mem_map]
    exact ⟨s.toNat, Finset.mem_range.2 (by omega), by simp; omega⟩

/-- `(0,1)`：Newton 前向差分公式，每个数列都有 `f(k) = Σ_{s≤k} C(k, s)·Δ^s f(0)`。 -/
theorem shape_01 (f : ℕ → ℂ) : ShapeRep f 0 1 := by
  refine ⟨0, 0, 0, 0, fun s => (fwdDiff 1)^[s.toNat] f 0, fun k _ => ?_⟩
  have hN := shift_eq_sum_fwdDiff_iter 1 f k 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at hN
  rw [hN]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (k + 1)).map Nat.castEmbedding) ?_]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htk : t ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
    rw [ite_eq_left (by omega)]
    have hb : binomZ ((k : ℤ) + 0 - ((0 : ℕ) : ℤ) * (t : ℤ)) (((1 : ℕ) : ℤ) * (t : ℤ) + 0) = k.choose t := by
      unfold binomZ
      rw [ite_eq_left (by push_cast; omega)]
      congr 1
      · push_cast
        omega
      · push_cast
        omega
    rw [hb]
    ring
  · intro s hs
    simp only [Function.mem_support, ne_eq] at hs
    have hs0 : 0 ≤ s := by
      by_contra h
      exact hs (by rw [ite_eq_right h])
    rw [ite_eq_left hs0] at hs
    have hb : binomZ ((k : ℤ) + 0 - ((0 : ℕ) : ℤ) * s) (((1 : ℕ) : ℤ) * s + 0) ≠ 0 := by
      intro h0
      apply hs
      rw [h0, Nat.cast_zero, mul_zero]
    unfold binomZ at hb
    have hsk : s ≤ k := by
      by_contra h
      apply hb
      rw [ite_eq_right (by push_cast; omega)]
    rw [Finset.mem_coe, Finset.mem_map]
    exact ⟨s.toNat, Finset.mem_range.2 (by omega), by simp; omega⟩

/-- **论文定理 6.3**：`m ≥ 1`，`α, β ≥ 0` 不全为 0。`U_k(m)` 有形状 `C(k+c−αs, βs+d)` 的单族表示
（`ShapeRep`：`k ≥ k₀` 时 `U_k(m) = Σ_{s≥s₀} A(s)·C(k+c−αs, βs+d)`）当且仅当 `α + β = 1`。 -/
theorem thm_shapes {m α β : ℕ} (hm : 1 ≤ m) (hαβ : α + β ≠ 0) :
    ShapeRep (fun k => (U k m : ℂ)) α β ↔ α + β = 1 := by
  constructor
  · intro hrep
    by_contra h1
    rcases Nat.eq_zero_or_pos α with hα0 | hα
    · subst hα0
      exact not_shape_d hm (by omega) hrep
    rcases Nat.eq_zero_or_pos β with hβ0 | hβ
    · subst hβ0
      exact not_shape_b hm (by omega) hrep
    by_cases he : α = 2 * β
    · subst he
      rcases (by omega : β = 1 ∨ 2 ≤ β) with rfl | hβ2
      · exact not_shape_21 hm hrep
      · exact not_shape_c hm hβ2 hrep
    · exact not_shape_a hm hα hβ he hrep
  · intro h
    rcases (by omega : (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact shape_10 _
    · exact shape_01 _

end

end A207123
