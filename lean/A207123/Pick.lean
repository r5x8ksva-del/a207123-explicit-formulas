import A207123.InterlaceDeriv

/-!
# 论文引理 8.5：交错关系与上半平面上虚部的符号（Pick 判据）

论文引理 8.5：`f` 实根，`lc(f) > 0`、`lc(g) > 0`。
1. 若 `deg g ≤ deg f`，则 `g ≪ f` 当且仅当在上半平面 `H` 上处处 `Im(g(z)/f(z)) ≤ 0`（`lemma_il_pick_one`）；
2. 若 `deg f ≤ deg g ≤ deg f + 1`，则 `f ≪ g` 当且仅当在 `H` 上处处 `Im(g(z)/f(z)) ≥ 0`（`lemma_il_pick_two`）；
两种情形下 `H` 上的条件都推出 `g` 实根（`realRooted_of_im_nonpos`、`realRooted_of_im_nonneg`）。

`Interlace.lean` 用下锥 `g = c·f + Σ_a w(a)·f/(X−a)` 与上锥 `g = (aX+b)·f − Σ_t e(t)·f/(X−t)` 代替了这条引理
（`cone_of_interlaces`、`interlaces_coneSum`、`ucone_of_interlaces`、`interlaces_uconeSum`），这里补上引理本身：
* 「⇒」：`g/f = c + Σ_a w(a)/(z−a)`，`Im(1/(z−a)) = −Im z/|z−a|² ≤ 0`（`im_div_coneSum_nonpos`）；上锥同理
  （`im_div_uconeSum_nonneg`）。
* 「⇐」：按论文，在 `f` 的根 `a` 附近看 `g/f`。局部引理 `exists_im_pos_of_local`：`f = (X−a)^L·q`、`q(a) ≠ 0` 时，
  在 `z = a + εω`（`Im ω > 0`，`ε → 0+`）处 `g/f = ε^{−L}·ω^{−L}·(g/q)(z)`，而 `g/q` 在 `a` 连续，所以只要
  `Im(ω^{−L}·g(a)/q(a)) > 0`，就有上半平面的点使 `Im(g/f) > 0`。`L ≥ 2` 时取 `ω = e^{iπ/(2L)}` 或 `e^{3iπ/(2L)}`
  （`ω^{−L} = −i` 或 `i`），所以重根处必有 `g(a) = 0`（`isRoot_of_im_nonpos`）；`L = 1` 时取 `ω = i`，得
  `g(a)/q(a) ≥ 0`（`weight_nonneg_of_im_nonpos`）。对 `deg f` 归纳：有公共根就同除 `X − a`（条件不变），否则 `f`
  只有单根，插值得到锥的表示，权重的符号由局部引理给出（`cone_of_im_nonpos`、`ucone_of_im_nonneg`），再用
  `interlaces_coneSum`、`interlaces_uconeSum`。论文先除以最大公因式再做同样的局部分析；这里逐个除去公共根。
-/

namespace A207123

open Polynomial Filter Topology Complex
open scoped Real

noncomputable section

/-! ## 1. 实系数多项式在复数点的值 -/

theorem aeval_ofReal (p : ℝ[X]) (x : ℝ) : aeval (x : ℂ) p = ((p.eval x : ℝ) : ℂ) := by
  have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) x p
  rwa [Complex.coe_algebraMap] at this

theorem aeval_X_sub_C_complex (z : ℂ) (a : ℝ) : aeval z (X - C a) = z - a := by
  rw [map_sub, aeval_X, aeval_C, Complex.coe_algebraMap]

theorem sub_ofReal_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) (a : ℝ) : z - a ≠ 0 := fun h => by
  have := congrArg Complex.im h
  rw [sub_im, ofReal_im, sub_zero, zero_im] at this
  exact hz.ne' this

/-- 实根多项式在上半平面没有零点。 -/
theorem aeval_ne_zero_of_im_pos {f : ℝ[X]} (hf : RealRooted f) {z : ℂ} (hz : 0 < z.im) :
    aeval z f ≠ 0 := by
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hf.2
  rw [← hprod, map_mul, aeval_C, map_multiset_prod, Multiset.map_map]
  refine mul_ne_zero ?_ (Multiset.prod_ne_zero fun h0 => ?_)
  · rw [Complex.coe_algebraMap]
    exact_mod_cast leadingCoeff_ne_zero.2 hf.1
  · obtain ⟨r, -, e⟩ := Multiset.mem_map.1 h0
    rw [Function.comp_apply, aeval_X_sub_C_complex] at e
    exact sub_ofReal_ne_zero_of_im_pos hz r e

theorem im_inv_sub_ofReal_nonpos {z : ℂ} (hz : 0 < z.im) (a : ℝ) : (z - a)⁻¹.im ≤ 0 := by
  rw [inv_im, sub_im, ofReal_im, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hz.le) (normSq_nonneg _)

/-- `a` 是 `f` 的根、`f(z) ≠ 0` 时 `(f/(X−a))(z) / f(z) = 1/(z−a)`。 -/
theorem aeval_divByMonic_div {f : ℝ[X]} {a : ℝ} (ha : f.IsRoot a) {z : ℂ} (hfz : aeval z f ≠ 0) :
    aeval z (f /ₘ (X - C a)) / aeval z f = (z - a)⁻¹ := by
  have e := congrArg (aeval z) (divByMonic_spec ha)
  rw [map_mul, aeval_X_sub_C_complex] at e
  rw [← e] at hfz ⊢
  have hza : z - a ≠ 0 := left_ne_zero_of_mul hfz
  have hq : aeval z (f /ₘ (X - C a)) ≠ 0 := right_ne_zero_of_mul hfz
  field_simp

/-! ## 2. 「⇒」：锥中元素与 `f` 之比的虚部 -/

/-- `f` 实根，`w ≥ 0`（在根上）：上半平面上 `Im(coneSum f c w / f) ≤ 0`。 -/
theorem im_div_coneSum_nonpos {f : ℝ[X]} (hf : RealRooted f) (c : ℝ) {w : ℝ → ℝ}
    (hw : ∀ a ∈ f.roots, 0 ≤ w a) {z : ℂ} (hz : 0 < z.im) :
    (aeval z (coneSum f c w) / aeval z f).im ≤ 0 := by
  have hfz := aeval_ne_zero_of_im_pos hf hz
  have key : aeval z (coneSum f c w) / aeval z f =
      (c : ℂ) + ∑ a ∈ f.roots.toFinset, (w a : ℂ) * (z - a)⁻¹ := by
    rw [coneSum, map_add, map_mul, aeval_C, Complex.coe_algebraMap, map_sum, add_div, Finset.sum_div,
      mul_div_assoc, div_self hfz, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    have hr : f.IsRoot a := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ha)
    rw [map_mul, aeval_C, Complex.coe_algebraMap, mul_div_assoc, aeval_divByMonic_div hr hfz]
  rw [key, add_im, ofReal_im, zero_add, im_sum]
  refine Finset.sum_nonpos fun a ha => ?_
  rw [im_ofReal_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (hw a (Multiset.mem_toFinset.1 ha)) (im_inv_sub_ofReal_nonpos hz a)

/-- `f` 实根，`a ≥ 0`，`e ≥ 0`（在根上）：上半平面上 `Im(uconeSum f a b e / f) ≥ 0`。 -/
theorem im_div_uconeSum_nonneg {f : ℝ[X]} (hf : RealRooted f) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    {e : ℝ → ℝ} (he : ∀ t ∈ f.roots, 0 ≤ e t) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (aeval z (uconeSum f a b e) / aeval z f).im := by
  have hfz := aeval_ne_zero_of_im_pos hf hz
  have key : aeval z (uconeSum f a b e) / aeval z f =
      (a : ℂ) * z + b - ∑ t ∈ f.roots.toFinset, (e t : ℂ) * (z - t)⁻¹ := by
    rw [uconeSum, map_sub, map_mul, map_add, map_mul, aeval_C, aeval_C, aeval_X, Complex.coe_algebraMap,
      map_sum, sub_div, Finset.sum_div, mul_div_assoc, div_self hfz, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have hr : f.IsRoot t := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ht)
    rw [map_mul, aeval_C, Complex.coe_algebraMap, mul_div_assoc, aeval_divByMonic_div hr hfz]
  rw [key, sub_im, add_im, im_ofReal_mul, ofReal_im, add_zero, im_sum]
  have h1 : 0 ≤ a * z.im := mul_nonneg ha hz.le
  have h2 : ∑ t ∈ f.roots.toFinset, ((e t : ℂ) * (z - t)⁻¹).im ≤ 0 :=
    Finset.sum_nonpos fun t ht => by
      rw [im_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (he t (Multiset.mem_toFinset.1 ht))
        (im_inv_sub_ofReal_nonpos hz t)
  linarith

/-! ## 3. 「⇐」：根附近的局部分析 -/

theorem div_mul_pow_eq (P Q e w : ℂ) (L : ℕ) :
    P / ((e * w) ^ L * Q) = (e ^ L)⁻¹ * ((w ^ L)⁻¹ * (P / Q)) := by
  ring

/-- 局部引理：`Im ω > 0`，`q(a) ≠ 0`，`Im(ω^{−L}·p(a)/q(a)) > 0`，则有 `Im z > 0` 使
`Im(p(z)/((z−a)^L q(z))) > 0`（取 `z = a + εω`，`ε > 0` 足够小）。 -/
theorem exists_im_pos_of_local {p q : ℝ[X]} {a : ℝ} {ω : ℂ} (hω : 0 < ω.im) (L : ℕ)
    (hq : q.eval a ≠ 0) (hpos : 0 < ((ω ^ L)⁻¹ * ((p.eval a / q.eval a : ℝ) : ℂ)).im) :
    ∃ z : ℂ, 0 < z.im ∧ 0 < (aeval z p / ((z - a) ^ L * aeval z q)).im := by
  have hqa : aeval (a : ℂ) q ≠ 0 := by
    rw [aeval_ofReal]
    exact_mod_cast hq
  have hTa : 0 < ((ω ^ L)⁻¹ * (aeval (a : ℂ) p / aeval (a : ℂ) q)).im := by
    rw [aeval_ofReal, aeval_ofReal, ← ofReal_div]
    exact hpos
  have hcont : ContinuousAt (fun z : ℂ => ((ω ^ L)⁻¹ * (aeval z p / aeval z q)).im) (a : ℂ) :=
    Complex.continuous_im.continuousAt.comp (continuousAt_const.mul
      ((Polynomial.continuousAt_aeval (p := p)).div (Polynomial.continuousAt_aeval (p := q)) hqa))
  have hpath : Tendsto (fun ε : ℝ => (a : ℂ) + (ε : ℂ) * ω) (𝓝[>] 0) (𝓝 (a : ℂ)) := by
    have h0 : Continuous fun ε : ℝ => (a : ℂ) + (ε : ℂ) * ω :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h1 : Tendsto (fun ε : ℝ => (a : ℂ) + (ε : ℂ) * ω) (𝓝 0) (𝓝 (a : ℂ)) := by
      simpa using h0.tendsto 0
    exact h1.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ (ε : ℝ) in 𝓝[>] 0,
      0 < ((ω ^ L)⁻¹ * (aeval ((a : ℂ) + (ε : ℂ) * ω) p / aeval ((a : ℂ) + (ε : ℂ) * ω) q)).im :=
    (hcont.tendsto.comp hpath).eventually (lt_mem_nhds hTa)
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  refine ⟨(a : ℂ) + ε * ω, ?_, ?_⟩
  · rw [add_im, ofReal_im, zero_add, im_ofReal_mul]
    exact mul_pos hε0 hω
  · rw [add_sub_cancel_left, div_mul_pow_eq, ← ofReal_pow, ← ofReal_inv, im_ofReal_mul]
    exact mul_pos (inv_pos.2 (pow_pos hε0 L)) hε

theorem exp_mul_I_pow (θ : ℝ) (L : ℕ) :
    Complex.exp (θ * I) ^ L = Complex.exp ((L * θ : ℝ) * I) := by
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem exp_mul_I_im_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : 0 < (Complex.exp (θ * I)).im := by
  rw [exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi h0 hπ

theorem exp_pi_div_two_mul_I' : Complex.exp ((π / 2 : ℝ) * I) = I := by
  apply Complex.ext
  · rw [exp_ofReal_mul_I_re, Real.cos_pi_div_two, I_re]
  · rw [exp_ofReal_mul_I_im, Real.sin_pi_div_two, I_im]

theorem exp_three_pi_div_two_mul_I : Complex.exp ((π / 2 + π : ℝ) * I) = -I := by
  apply Complex.ext
  · rw [exp_ofReal_mul_I_re, Real.cos_add_pi, Real.cos_pi_div_two, neg_re, I_re, neg_zero]
  · rw [exp_ofReal_mul_I_im, Real.sin_add_pi, Real.sin_pi_div_two, neg_im, I_im]

/-- `L ≥ 2`、实数 `γ ≠ 0`：有 `Im ω > 0` 使 `Im(ω^{−L}·γ) > 0`（`ω = e^{iπ/(2L)}` 或 `e^{3iπ/(2L)}`）。 -/
theorem exists_omega_of_two_le {L : ℕ} (hL : 2 ≤ L) {γ : ℝ} (hγ : γ ≠ 0) :
    ∃ ω : ℂ, 0 < ω.im ∧ 0 < ((ω ^ L)⁻¹ * (γ : ℂ)).im := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := hL0.ne'
  rcases hγ.lt_or_gt with hneg | hpos
  · refine ⟨Complex.exp (((π / 2) / L : ℝ) * I), exp_mul_I_im_pos (by positivity) ?_, ?_⟩
    · rw [div_lt_iff₀ hL0]
      nlinarith [Real.pi_pos]
    · rw [exp_mul_I_pow, show (L : ℝ) * ((π / 2) / L) = π / 2 by field_simp, exp_pi_div_two_mul_I', inv_I]
      have : (-I * (γ : ℂ)).im = -γ := by simp
      rw [this]
      linarith
  · refine ⟨Complex.exp (((π / 2 + π) / L : ℝ) * I), exp_mul_I_im_pos (by positivity) ?_, ?_⟩
    · rw [div_lt_iff₀ hL0]
      nlinarith [Real.pi_pos]
    · rw [exp_mul_I_pow, show (L : ℝ) * ((π / 2 + π) / L) = π / 2 + π by field_simp,
        exp_three_pi_div_two_mul_I, inv_neg, inv_I, neg_neg]
      have : (I * (γ : ℂ)).im = γ := by simp
      rw [this]
      exact hpos

/-- 论文引理 8.5(1) 证明的第一步：上半平面上 `Im(g/f) ≤ 0`，则 `f` 的重根（重数 `≥ 2`）都是 `g` 的根。 -/
theorem isRoot_of_im_nonpos {g f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (hcount : 2 ≤ f.roots.count a)
    (hH : ∀ z : ℂ, 0 < z.im → (aeval z g / aeval z f).im ≤ 0) : g.IsRoot a := by
  by_contra hga
  have hfac := pow_mul_divByMonic_rootMultiplicity_eq f a
  have hq := eval_divByMonic_pow_rootMultiplicity_ne_zero a hf
  rw [count_roots] at hcount
  obtain ⟨ω, hω, hpos⟩ := exists_omega_of_two_le hcount (div_ne_zero hga hq)
  obtain ⟨z, hz, hzpos⟩ := exists_im_pos_of_local hω _ hq hpos
  have e : aeval z f =
      (z - a) ^ f.rootMultiplicity a * aeval z (f /ₘ (X - C a) ^ f.rootMultiplicity a) := by
    conv_lhs => rw [← hfac]
    rw [map_mul, map_pow, aeval_X_sub_C_complex]
  have := hH z hz
  rw [e] at this
  linarith

/-- 单根处的权重：`a` 是 `f` 的根，`q = f/(X−a)` 满足 `q(a) ≠ 0`，上半平面上 `Im(g/f) ≤ 0`，则
`g(a)/q(a) ≥ 0`（取 `ω = i`）。 -/
theorem weight_nonneg_of_im_nonpos {g f : ℝ[X]} {a : ℝ} (ha : f.IsRoot a)
    (hq : (f /ₘ (X - C a)).eval a ≠ 0)
    (hH : ∀ z : ℂ, 0 < z.im → (aeval z g / aeval z f).im ≤ 0) :
    0 ≤ g.eval a / (f /ₘ (X - C a)).eval a := by
  by_contra hneg
  have hneg := not_le.1 hneg
  have hpos : 0 < ((I ^ 1)⁻¹ * ((g.eval a / (f /ₘ (X - C a)).eval a : ℝ) : ℂ)).im := by
    rw [pow_one, inv_I, neg_mul, neg_im, mul_comm, im_ofReal_mul, I_im, mul_one]
    linarith
  obtain ⟨z, hz, hzpos⟩ := exists_im_pos_of_local (by rw [I_im]; exact one_pos) 1 hq hpos
  have e : aeval z f = (z - a) ^ 1 * aeval z (f /ₘ (X - C a)) := by
    conv_lhs => rw [← divByMonic_spec ha]
    rw [map_mul, aeval_X_sub_C_complex, pow_one]
  have := hH z hz
  rw [e] at this
  linarith

/-- 把 `Im(g/f) ≥ 0` 写成 `Im((−g)/f) ≤ 0`。 -/
theorem im_neg_div_nonpos {g f : ℝ[X]} (hH : ∀ z : ℂ, 0 < z.im → 0 ≤ (aeval z g / aeval z f).im) :
    ∀ z : ℂ, 0 < z.im → (aeval z (-g) / aeval z f).im ≤ 0 := by
  intro z hz
  rw [map_neg, neg_div, neg_im]
  exact neg_nonpos.2 (hH z hz)

/-- 除去公共根 `a` 不改变 `g/f` 在上半平面的值。 -/
theorem div_divByMonic_eq {g f : ℝ[X]} {a : ℝ} (hfa : f.IsRoot a) (hga : g.IsRoot a) {z : ℂ}
    (hz : 0 < z.im) :
    aeval z (g /ₘ (X - C a)) / aeval z (f /ₘ (X - C a)) = aeval z g / aeval z f := by
  have e1 := congrArg (aeval z) (divByMonic_spec hfa)
  have e2 := congrArg (aeval z) (divByMonic_spec hga)
  rw [map_mul, aeval_X_sub_C_complex] at e1 e2
  rw [← e1, ← e2, mul_div_mul_left _ _ (sub_ofReal_ne_zero_of_im_pos hz a)]

/-! ## 4. 「⇐」：归纳与插值 -/

/-- 论文引理 8.5(1) 的「⇐」（锥的形式）：`f` 实根，首项系数都为正，`deg g ≤ deg f`，上半平面上
`Im(g/f) ≤ 0`，则 `g = coneSum f c w`，`c ≥ 0`，`w ≥ 0`（在 `f` 的根上）。 -/
theorem cone_of_im_nonpos {g f : ℝ[X]} (hf : RealRooted f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) (hdeg : g.natDegree ≤ f.natDegree)
    (hH : ∀ z : ℂ, 0 < z.im → (aeval z g / aeval z f).im ≤ 0) :
    ∃ c, 0 ≤ c ∧ ∃ w : ℝ → ℝ, (∀ a ∈ f.roots, 0 ≤ w a) ∧ g = coneSum f c w := by
  have key : ∀ n, ∀ f g : ℝ[X], f.natDegree = n → RealRooted f → 0 < f.leadingCoeff →
      0 < g.leadingCoeff → g.natDegree ≤ f.natDegree →
      (∀ z : ℂ, 0 < z.im → (aeval z g / aeval z f).im ≤ 0) →
      ∃ c, 0 ≤ c ∧ ∃ w : ℝ → ℝ, (∀ a ∈ f.roots, 0 ≤ w a) ∧ g = coneSum f c w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f g hn hf hlcf hlcg hdeg hH
      have hg0 : g ≠ 0 := leadingCoeff_ne_zero.1 hlcg.ne'
      by_cases hbad : ∃ a ∈ f.roots, 2 ≤ f.roots.count a ∨ g.IsRoot a
      · obtain ⟨a, ham, hcase⟩ := hbad
        have hfa := isRoot_of_mem_roots ham
        have hga : g.IsRoot a := by
          rcases hcase with hc | hc
          · exact isRoot_of_im_nonpos hf.1 hc hH
          · exact hc
        have hsg := divByMonic_spec hga
        have hdeg₁ : (f /ₘ (X - C a)).natDegree < n := by
          have := natDegree_divByMonic' hf.1 hfa
          omega
        have hdegq : (g /ₘ (X - C a)).natDegree ≤ (f /ₘ (X - C a)).natDegree := by
          have h1 := natDegree_divByMonic' hf.1 hfa
          have h2 := natDegree_divByMonic' hg0 hga
          omega
        obtain ⟨c, hc, w, hw, hgw⟩ := ih _ hdeg₁ _ _ rfl (realRooted_divByMonic hf hfa)
          (by rw [leadingCoeff_divByMonic' hfa]; exact hlcf)
          (by rw [leadingCoeff_divByMonic' hga]; exact hlcg) hdegq
          (fun z hz => by rw [div_divByMonic_eq hfa hga hz]; exact hH z hz)
        set w' : ℝ → ℝ := fun t => if t ∈ (f /ₘ (X - C a)).roots then w t else 0 with hw'
        refine ⟨c, hc, w', fun t ht => ?_, ?_⟩
        · simp only [hw']
          split_ifs with h'
          · exact hw t h'
          · exact le_rfl
        · have hfac := coneSum_factor hf.1 hfa c w' fun h1 => by
            simp only [hw']
            rw [ite_eq_right]
            intro hmem
            rw [roots_divByMonic hf.1 hfa, Multiset.count_cons_self] at h1
            have := Multiset.count_pos.2 hmem
            omega
          have hcongr : coneSum (f /ₘ (X - C a)) c w' = coneSum (f /ₘ (X - C a)) c w :=
            coneSum_congr c fun t ht => by
              simp only [hw']
              rw [ite_eq_left ht]
          rw [hfac, hcongr, ← hgw, hsg]
      · have hsimple : ∀ a ∈ f.roots, f.roots.count a = 1 := fun a ha => by
          have h1 := Multiset.count_pos.2 ha
          have h2 : ¬ 2 ≤ f.roots.count a := fun h2 => hbad ⟨a, ha, Or.inl h2⟩
          omega
        have hnd : f.roots.Nodup := Multiset.nodup_iff_count_le_one.2 fun a => by
          by_cases ha : a ∈ f.roots
          · rw [hsimple a ha]
          · rw [Multiset.count_eq_zero.2 ha]
            exact zero_le_one
        set S := f.roots.toFinset with hS
        have hSn : S.card = f.natDegree := by
          rw [hS, Multiset.toFinset_card_of_nodup hnd, hf.2]
        set c := g.coeff f.natDegree / f.leadingCoeff with hc
        set w : ℝ → ℝ := fun a => g.eval a / (f /ₘ (X - C a)).eval a with hw
        have hq : ∀ a ∈ f.roots, (f /ₘ (X - C a)).eval a ≠ 0 := fun a ha h0 => by
          have := sign_divByMonic_eval hf hlcf (isRoot_of_mem_roots ha) (hsimple a ha)
          rw [h0, mul_zero] at this
          exact lt_irrefl _ this
        refine ⟨c, div_nonneg (coeff_nonneg_of_natDegree_le hlcg hdeg) hlcf.le, w,
          fun a ha => weight_nonneg_of_im_nonpos (isRoot_of_mem_roots ha) (hq a ha) hH, ?_⟩
        refine eq_of_degree_sub_lt_of_eval_finset_eq S ?_ ?_
        · rw [hSn, degree_lt_iff_coeff_zero]
          intro m hm
          rw [coeff_sub]
          rcases hm.lt_or_eq with hm | hm
          · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hm),
              coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_coneSum_le hf.1 c w) hm),
              sub_zero]
          · rw [← hm, coneSum_coeff hf.1 c w, hc, div_mul_cancel₀ _ hlcf.ne', sub_self]
        · intro a ha
          have ha' := Multiset.mem_toFinset.1 ha
          rw [coneSum_eval_root hf.1 c w (isRoot_of_mem_roots ha'), hw,
            div_mul_cancel₀ _ (hq a ha')]
  exact key _ f g rfl hf hlcf hlcg hdeg hH

/-- 论文引理 8.5(2) 的「⇐」（上锥的形式）：`f` 实根，首项系数都为正，`deg f ≤ deg g ≤ deg f + 1`，
上半平面上 `Im(g/f) ≥ 0`，则 `g = uconeSum f a b e`，`a ≥ 0`，`e ≥ 0`（在 `f` 的根上）。 -/
theorem ucone_of_im_nonneg {f g : ℝ[X]} (hf : RealRooted f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) (hdeg₁ : f.natDegree ≤ g.natDegree)
    (hdeg₂ : g.natDegree ≤ f.natDegree + 1)
    (hH : ∀ z : ℂ, 0 < z.im → 0 ≤ (aeval z g / aeval z f).im) :
    ∃ a, 0 ≤ a ∧ ∃ b, ∃ e : ℝ → ℝ, (∀ t ∈ f.roots, 0 ≤ e t) ∧ g = uconeSum f a b e := by
  have key : ∀ n, ∀ f g : ℝ[X], f.natDegree = n → RealRooted f → 0 < f.leadingCoeff →
      0 < g.leadingCoeff → f.natDegree ≤ g.natDegree → g.natDegree ≤ f.natDegree + 1 →
      (∀ z : ℂ, 0 < z.im → 0 ≤ (aeval z g / aeval z f).im) →
      ∃ a, 0 ≤ a ∧ ∃ b, ∃ e : ℝ → ℝ, (∀ t ∈ f.roots, 0 ≤ e t) ∧ g = uconeSum f a b e := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f g hn hf hlcf hlcg hdeg₁ hdeg₂ hH
      have hg0 : g ≠ 0 := leadingCoeff_ne_zero.1 hlcg.ne'
      by_cases hbad : ∃ t ∈ f.roots, 2 ≤ f.roots.count t ∨ g.IsRoot t
      · obtain ⟨t, htm, hcase⟩ := hbad
        have hft := isRoot_of_mem_roots htm
        have hgt : g.IsRoot t := by
          rcases hcase with hc | hc
          · have := isRoot_of_im_nonpos hf.1 hc (im_neg_div_nonpos hH)
            rwa [IsRoot, eval_neg, neg_eq_zero] at this
          · exact hc
        have hsg := divByMonic_spec hgt
        have hdeg₀ : (f /ₘ (X - C t)).natDegree < n := by
          have := natDegree_divByMonic' hf.1 hft
          omega
        have h1 := natDegree_divByMonic' hf.1 hft
        have h2 := natDegree_divByMonic' hg0 hgt
        obtain ⟨a, ha, b, e, he, hge⟩ := ih _ hdeg₀ _ _ rfl (realRooted_divByMonic hf hft)
          (by rw [leadingCoeff_divByMonic' hft]; exact hlcf)
          (by rw [leadingCoeff_divByMonic' hgt]; exact hlcg) (by omega) (by omega)
          (fun z hz => by rw [div_divByMonic_eq hft hgt hz]; exact hH z hz)
        set e' : ℝ → ℝ := fun s => if s ∈ (f /ₘ (X - C t)).roots then e s else 0 with he'
        refine ⟨a, ha, b, e', fun s hs => ?_, ?_⟩
        · simp only [he']
          split_ifs with h'
          · exact he s h'
          · exact le_rfl
        · have hfac := uconeSum_factor hf.1 hft a b e' fun h1 => by
            simp only [he']
            rw [ite_eq_right]
            intro hmem
            rw [roots_divByMonic hf.1 hft, Multiset.count_cons_self] at h1
            have := Multiset.count_pos.2 hmem
            omega
          have hcongr : uconeSum (f /ₘ (X - C t)) a b e' = uconeSum (f /ₘ (X - C t)) a b e :=
            uconeSum_congr a b fun s hs => by
              simp only [he']
              rw [ite_eq_left hs]
          rw [hfac, hcongr, ← hge, hsg]
      · have hsimple : ∀ t ∈ f.roots, f.roots.count t = 1 := fun t ht => by
          have h1 := Multiset.count_pos.2 ht
          have h2 : ¬ 2 ≤ f.roots.count t := fun h2 => hbad ⟨t, ht, Or.inl h2⟩
          omega
        have hnd : f.roots.Nodup := Multiset.nodup_iff_count_le_one.2 fun t => by
          by_cases ht : t ∈ f.roots
          · rw [hsimple t ht]
          · rw [Multiset.count_eq_zero.2 ht]
            exact zero_le_one
        set S := f.roots.toFinset with hS
        have hSn : S.card = f.natDegree := by
          rw [hS, Multiset.toFinset_card_of_nodup hnd, hf.2]
        set a := g.coeff (f.natDegree + 1) / f.leadingCoeff with ha
        set b := (g.coeff f.natDegree - (C a * X * f).coeff f.natDegree) / f.leadingCoeff with hb
        set e : ℝ → ℝ := fun t => -(g.eval t / (f /ₘ (X - C t)).eval t) with he
        have hq : ∀ t ∈ f.roots, (f /ₘ (X - C t)).eval t ≠ 0 := fun t ht h0 => by
          have := sign_divByMonic_eval hf hlcf (isRoot_of_mem_roots ht) (hsimple t ht)
          rw [h0, mul_zero] at this
          exact lt_irrefl _ this
        refine ⟨a, div_nonneg (coeff_nonneg_of_natDegree_le hlcg hdeg₂) hlcf.le, b, e,
          fun t ht => ?_, ?_⟩
        · have := weight_nonneg_of_im_nonpos (isRoot_of_mem_roots ht) (hq t ht) (im_neg_div_nonpos hH)
          rw [eval_neg, neg_div] at this
          exact this
        · refine eq_of_degree_sub_lt_of_eval_finset_eq S ?_ ?_
          · rw [hSn, degree_lt_iff_coeff_zero]
            intro m hm
            rw [coeff_sub]
            rcases hm.lt_or_eq with hm | hm
            · rcases (Nat.lt_iff_add_one_le.1 hm).lt_or_eq with hm2 | hm2
              · rw [coeff_eq_zero_of_natDegree_lt (by omega),
                  coeff_eq_zero_of_natDegree_lt
                    (lt_of_le_of_lt (natDegree_uconeSum_le hf.1 a b e) (by omega)), sub_zero]
              · rw [← hm2, uconeSum_coeff_succ hf.1 a b e, ha, div_mul_cancel₀ _ hlcf.ne', sub_self]
            · rw [← hm, uconeSum, coeff_sub, coeff_sum_divByMonic hf.1 e le_rfl, sub_zero, add_mul,
                coeff_add, coeff_C_mul, hb]
              have hl : f.coeff f.natDegree = f.leadingCoeff := rfl
              rw [hl, div_mul_cancel₀ _ hlcf.ne']
              ring
          · intro t ht
            have ht' := Multiset.mem_toFinset.1 ht
            rw [uconeSum_eval_root hf.1 a b e (isRoot_of_mem_roots ht'), he, neg_mul,
              div_mul_cancel₀ _ (hq t ht'), neg_neg]
  exact key _ f g rfl hf hlcf hlcg hdeg₁ hdeg₂ hH

/-! ## 5. 论文引理 8.5 -/

/-- 论文引理 8.5(1)：`f` 实根，`lc(f) > 0`、`lc(g) > 0`，`deg g ≤ deg f`，则 `g ≪ f` 当且仅当上半平面上处处
`Im(g(z)/f(z)) ≤ 0`。 -/
theorem lemma_il_pick_one {g f : ℝ[X]} (hf : RealRooted f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) (hdeg : g.natDegree ≤ f.natDegree) :
    Interlaces g f ↔ ∀ z : ℂ, 0 < z.im → (aeval z g / aeval z f).im ≤ 0 := by
  constructor
  · intro h z hz
    obtain ⟨c, -, w, hw, rfl⟩ := cone_of_interlaces h hlcf hlcg
    exact im_div_coneSum_nonpos hf c hw hz
  · intro hH
    obtain ⟨c, hc, w, hw, rfl⟩ := cone_of_im_nonpos hf hlcf hlcg hdeg hH
    exact interlaces_coneSum hf hlcf hc hw (leadingCoeff_ne_zero.1 hlcg.ne')

/-- 论文引理 8.5(2)：`f` 实根，`lc(f) > 0`、`lc(g) > 0`，`deg f ≤ deg g ≤ deg f + 1`，则 `f ≪ g` 当且仅当上半平面
上处处 `Im(g(z)/f(z)) ≥ 0`。 -/
theorem lemma_il_pick_two {g f : ℝ[X]} (hf : RealRooted f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) (hdeg₁ : f.natDegree ≤ g.natDegree)
    (hdeg₂ : g.natDegree ≤ f.natDegree + 1) :
    Interlaces f g ↔ ∀ z : ℂ, 0 < z.im → 0 ≤ (aeval z g / aeval z f).im := by
  constructor
  · intro h z hz
    obtain ⟨a, ha, b, e, he, rfl⟩ := ucone_of_interlaces h hlcf hlcg
    exact im_div_uconeSum_nonneg hf ha b he hz
  · intro hH
    obtain ⟨a, ha, b, e, he, rfl⟩ := ucone_of_im_nonneg hf hlcf hlcg hdeg₁ hdeg₂ hH
    exact interlaces_uconeSum hf hlcf ha b he hlcg

/-- 论文引理 8.5 的最后一句（情形 (1)）：上半平面的条件推出 `g` 实根。 -/
theorem realRooted_of_im_nonpos {g f : ℝ[X]} (hf : RealRooted f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) (hdeg : g.natDegree ≤ f.natDegree)
    (hH : ∀ z : ℂ, 0 < z.im → (aeval z g / aeval z f).im ≤ 0) : RealRooted g :=
  ((lemma_il_pick_one hf hlcf hlcg hdeg).2 hH).2.1

/-- 论文引理 8.5 的最后一句（情形 (2)）：上半平面的条件推出 `g` 实根。 -/
theorem realRooted_of_im_nonneg {g f : ℝ[X]} (hf : RealRooted f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) (hdeg₁ : f.natDegree ≤ g.natDegree)
    (hdeg₂ : g.natDegree ≤ f.natDegree + 1)
    (hH : ∀ z : ℂ, 0 < z.im → 0 ≤ (aeval z g / aeval z f).im) : RealRooted g :=
  ((lemma_il_pick_two hf hlcf hlcg hdeg₁ hdeg₂).2 hH).1

end

end A207123
