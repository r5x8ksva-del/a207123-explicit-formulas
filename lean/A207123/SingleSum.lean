import A207123.NonDFinite

/-!
# 论文定理 6.1：`U_k(m)` 没有 `(2,1)` 形状的单族和

论文定理 6.1：`m ≥ 1` 时不存在整数 `c, d, k₀ ≥ 0` 与复数 `A(s)`（`s ∈ ℤ`，与 `k` 无关），使对所有 `k ≥ k₀`
`U_k(m) = Σ_s A(s)·C(k+c−2s, m+s+d)`（论文的二项式约定：`0 ≤ b ≤ a` 之外 `C(a,b) = 0`，`binomZ`）。主定理 `thm_S`。

证明按论文的三步，但第二、三步改写成不用 Laurent 级数域、留数与 Galois 理论的形式：
* 第一步（母函数）：令 `t = s + m + d`、`a_t = A(t − m − d)`、`K = c + 2(m+d)`，则 `C(k+c−2s, m+s+d) = C(n−2t, t)`
  （`n = k + K`），而 `Σ_n C(n−2t, t)x^n = u^t/(1−x)`，`u = x³/(1−x)`（`coeff_uS_pow_mul_mk_one`）。所以
  `x^{K₁}G_m − x^{K₂}·ã(u)/(1−x)` 是多项式（`K = K₁ − K₂`，`ã = Σ a_t u^t`，代入用 Mathlib 的 `PowerSeries.subst`）。
* 第二步（坐标）：在 `ℂ[u][T]` 中对首一多项式 `q = T³ + uT − u` 取余（`x³ = u(1−x)`），每个多项式 `F(x)` 写成
  `Σ_{i<3} r_i(u)x^i`（`coe_eq_coords`）；`1, x, x²` 在 `ℂ⟦u⟧` 上线性无关，因为 `ℂ⟦u⟧` 中非零元代入后的 `x`-进阶是 3 的
  倍数（`substU_coords_unique`，论文用 Eisenstein 判别法）。由 `P_m = (1−x)^{m+1}·∏_{v≤m}(1 − vu)` 比较坐标、消去
  未知的 `ã`，得到 `u = 1`（即 `b_1 = 0`）处坐标向量成比例。
* 第三步（纤维 `u = 1`）：在 `b_1` 的三个根 `ξ` 处，`ξ^{K₁}W_m(ξ)(1−ξ) = λ·ξ^{K₂}(1−ξ)^{m+1}`，`λ` 与根无关；
  `W_m(ξ) = ξ(1+ξ)`、`1 − ξ = ξ³`，所以 `ξ^p(1+ξ) = λξ^r`。论文用留数与范数；这里直接对三个根 `a, b, c`（`X³+X−1`
  的韦达关系）：`λ³ = (1+a)(1+b)(1+c)/(abc)^{r−p} = 3`，而 `3λ = h(a)+h(b)+h(c)` 是根的幂和的有理组合，是有理数；
  `81` 不是有理数的立方（`no_common_value`）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 代入 `u = x³/(1−x)` -/

/-- `u = x³/(1−x)`（`x` 的幂级数；`mk 1 = 1/(1−x)`）。 -/
def uS : PowerSeries ℂ := PowerSeries.X ^ 3 * PowerSeries.mk 1

theorem uS_mul_one_sub : uS * (1 - PowerSeries.X) = PowerSeries.X ^ 3 := by
  rw [uS, mul_assoc, PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]

theorem constantCoeff_uS : PowerSeries.constantCoeff uS = 0 := by
  rw [uS, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by norm_num), zero_mul]

theorem hasSubst_uS : PowerSeries.HasSubst uS :=
  PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_uS

/-- 代入 `u ↦ x³/(1−x)`：`ℂ⟦u⟧ → ℂ⟦x⟧`（Mathlib 的 `PowerSeries.subst`）。 -/
def substU : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := PowerSeries.substAlgHom hasSubst_uS

theorem substU_apply (f : PowerSeries ℂ) : substU f = PowerSeries.subst uS f := by
  rw [substU, PowerSeries.coe_substAlgHom]

theorem substU_X : substU PowerSeries.X = uS := PowerSeries.substAlgHom_X hasSubst_uS

theorem substU_coe (p : ℂ[X]) : substU (p : PowerSeries ℂ) = Polynomial.aeval uS p :=
  PowerSeries.substAlgHom_coe hasSubst_uS p

theorem coeff_substU (f : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.coeff j (substU f) = ∑ᶠ d, PowerSeries.coeff d f • PowerSeries.coeff j (uS ^ d) := by
  rw [substU_apply, PowerSeries.coeff_subst' hasSubst_uS]

theorem coeff_uS_pow (d j : ℕ) :
    PowerSeries.coeff j (uS ^ d) =
      if 3 * d ≤ j then PowerSeries.coeff (j - 3 * d) (PowerSeries.mk (1 : ℕ → ℂ) ^ d) else 0 := by
  rw [uS, mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul']

theorem coeff_uS_pow_of_lt {d j : ℕ} (h : j < 3 * d) : PowerSeries.coeff j (uS ^ d) = 0 := by
  rw [coeff_uS_pow, ite_eq_right (by omega)]

theorem coeff_uS_pow_self (d : ℕ) : PowerSeries.coeff (3 * d) (uS ^ d) = 1 := by
  rw [coeff_uS_pow, ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  simp

/-- `f` 的前 `n` 个系数为 0 时，`f(u)` 的前 `3n` 个系数为 0，第 `3n` 个系数是 `f` 的第 `n` 个系数。 -/
theorem coeff_substU_of_vanish {f : PowerSeries ℂ} {n : ℕ} (hf : ∀ i < n, PowerSeries.coeff i f = 0) :
    (∀ j < 3 * n, PowerSeries.coeff j (substU f) = 0) ∧
      PowerSeries.coeff (3 * n) (substU f) = PowerSeries.coeff n f := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [coeff_substU]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : d < n
    · rw [hf d hd, zero_smul]
    · rw [coeff_uS_pow_of_lt (by omega), smul_zero]
  · rw [coeff_substU, finsum_eq_single _ n (fun d hd => ?_), coeff_uS_pow_self, smul_eq_mul, mul_one]
    rcases Nat.lt_or_gt_of_ne hd with hd | hd
    · rw [hf d hd, zero_smul]
    · rw [coeff_uS_pow_of_lt (by omega), smul_zero]

theorem coeff_mul_X' (p : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.coeff j (p * PowerSeries.X) = if 1 ≤ j then PowerSeries.coeff (j - 1) p else 0 := by
  have := PowerSeries.coeff_mul_X_pow' p 1 j
  rwa [pow_one] at this

/-- `1, x, x²` 在 `ℂ⟦u⟧` 上线性无关（代入后的 `x`-进阶分别 `≡ 0, 1, 2 (mod 3)`）。 -/
theorem substU_coords_unique {α β γ : PowerSeries ℂ}
    (h : substU α + substU β * PowerSeries.X + substU γ * PowerSeries.X ^ 2 = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hc : ∀ j, PowerSeries.coeff j (substU α) +
      (if 1 ≤ j then PowerSeries.coeff (j - 1) (substU β) else 0) +
      (if 2 ≤ j then PowerSeries.coeff (j - 2) (substU γ) else 0) = 0 := by
    intro j
    have := congrArg (PowerSeries.coeff j) h
    rwa [map_add, map_add, coeff_mul_X', PowerSeries.coeff_mul_X_pow', map_zero] at this
  have key : ∀ n, (∀ i < n, PowerSeries.coeff i α = 0 ∧ PowerSeries.coeff i β = 0 ∧
      PowerSeries.coeff i γ = 0) →
      PowerSeries.coeff n α = 0 ∧ PowerSeries.coeff n β = 0 ∧ PowerSeries.coeff n γ = 0 := by
    intro n hlt
    obtain ⟨hα1, hα2⟩ := coeff_substU_of_vanish (f := α) (n := n) fun i hi => (hlt i hi).1
    obtain ⟨hβ1, hβ2⟩ := coeff_substU_of_vanish (f := β) (n := n) fun i hi => (hlt i hi).2.1
    obtain ⟨hγ1, hγ2⟩ := coeff_substU_of_vanish (f := γ) (n := n) fun i hi => (hlt i hi).2.2
    have ha : PowerSeries.coeff n α = 0 := by
      have h0 := hc (3 * n)
      rw [hα2] at h0
      have e1 : (if 1 ≤ 3 * n then PowerSeries.coeff (3 * n - 1) (substU β) else 0) = 0 := by
        split_ifs with h1
        · exact hβ1 _ (by omega)
        · rfl
      have e2 : (if 2 ≤ 3 * n then PowerSeries.coeff (3 * n - 2) (substU γ) else 0) = 0 := by
        split_ifs with h1
        · exact hγ1 _ (by omega)
        · rfl
      rw [e1, e2, add_zero, add_zero] at h0
      exact h0
    have hα' := (coeff_substU_of_vanish (f := α) (n := n + 1) fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact (hlt i hi).1
      · exact ha).1
    have hb : PowerSeries.coeff n β = 0 := by
      have h0 := hc (3 * n + 1)
      rw [hα' _ (by omega), zero_add, ite_eq_left (by omega), show 3 * n + 1 - 1 = 3 * n by omega, hβ2] at h0
      have e2 : (if 2 ≤ 3 * n + 1 then PowerSeries.coeff (3 * n + 1 - 2) (substU γ) else 0) = 0 := by
        split_ifs with h1
        · exact hγ1 _ (by omega)
        · rfl
      rw [e2, add_zero] at h0
      exact h0
    have hβ' := (coeff_substU_of_vanish (f := β) (n := n + 1) fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact (hlt i hi).2.1
      · exact hb).1
    have hg : PowerSeries.coeff n γ = 0 := by
      have h0 := hc (3 * n + 2)
      rw [hα' _ (by omega), zero_add, ite_eq_left (by omega), hβ' _ (by omega), zero_add, ite_eq_left (by omega),
        show 3 * n + 2 - 2 = 3 * n by omega, hγ2] at h0
      exact h0
    exact ⟨ha, hb, hg⟩
  have all : ∀ n, PowerSeries.coeff n α = 0 ∧ PowerSeries.coeff n β = 0 ∧ PowerSeries.coeff n γ = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => exact key n ih
  refine ⟨?_, ?_, ?_⟩ <;> ext n <;> simp [(all n).1, (all n).2.1, (all n).2.2]

/-! ## 2. 坐标：在 `ℂ[u][T]` 中对 `q = T³ + uT − u` 取余 -/

/-- `q = T³ + u·T − u ∈ ℂ[u][T]`（`x³ = u(1−x)`）。 -/
def qU : Polynomial (Polynomial ℂ) :=
  Polynomial.X ^ 3 + (Polynomial.C Polynomial.X * Polynomial.X - Polynomial.C Polynomial.X)

theorem degree_qU_low :
    (Polynomial.C Polynomial.X * Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial ℂ)).degree < 3 := by
  have h1 : (Polynomial.C Polynomial.X * Polynomial.X - Polynomial.C Polynomial.X :
      Polynomial (Polynomial ℂ)).degree ≤ 1 :=
    (Polynomial.degree_sub_le _ _).trans
      (max_le (Polynomial.degree_C_mul_X_le _) (Polynomial.degree_C_le.trans zero_le_one))
  exact h1.trans_lt (by norm_num)

theorem qU_monic : qU.Monic := Polynomial.monic_X_pow_add degree_qU_low

theorem natDegree_qU : qU.natDegree = 3 := by
  rw [qU, Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact degree_qU_low),
    Polynomial.natDegree_X_pow]

theorem natDegree_mod_qU_lt (p : Polynomial (Polynomial ℂ)) : (p %ₘ qU).natDegree < 3 := by
  by_cases h0 : p %ₘ qU = 0
  · rw [h0, Polynomial.natDegree_zero]
    norm_num
  · have h1 : qU ≠ 1 := by
      intro h
      have := natDegree_qU
      rw [h, Polynomial.natDegree_one] at this
      omega
    have := Polynomial.natDegree_modByMonic_lt p qU_monic h1
    rwa [natDegree_qU] at this

/-- `ℂ[u][T] → ℂ⟦x⟧`：`T ↦ x`，`u ↦ x³/(1−x)`。 -/
def evU : Polynomial (Polynomial ℂ) →+* PowerSeries ℂ :=
  Polynomial.eval₂RingHom (Polynomial.aeval uS).toRingHom PowerSeries.X

theorem evU_apply (p : Polynomial (Polynomial ℂ)) :
    evU p = p.eval₂ (Polynomial.aeval uS).toRingHom PowerSeries.X := rfl

theorem evU_map_C (F : ℂ[X]) : evU (F.map Polynomial.C) = (F : PowerSeries ℂ) := by
  rw [evU_apply, Polynomial.eval₂_map]
  have : (Polynomial.aeval uS).toRingHom.comp Polynomial.C = PowerSeries.C := by
    ext c
    simp
  rw [this, Polynomial.eval₂_C_X_eq_coe]

theorem evU_qU : evU qU = 0 := by
  rw [evU_apply, qU]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
  have := uS_mul_one_sub
  linear_combination -this

theorem evU_modByMonic (p : Polynomial (Polynomial ℂ)) : evU p = evU (p %ₘ qU) := by
  conv_lhs => rw [← Polynomial.modByMonic_add_div p qU]
  rw [map_add, map_mul, evU_qU, zero_mul, add_zero]

/-- 多项式 `F` 的坐标：`F(T) mod q` 的系数（`ℂ[u]` 中）。 -/
def coordU (F : ℂ[X]) (i : ℕ) : ℂ[X] := ((F.map Polynomial.C) %ₘ qU).coeff i

theorem coe_eq_coords (F : ℂ[X]) :
    (F : PowerSeries ℂ) =
      ∑ i ∈ Finset.range 3, substU (coordU F i : PowerSeries ℂ) * PowerSeries.X ^ i := by
  rw [← evU_map_C, evU_modByMonic, evU_apply, Polynomial.eval₂_eq_sum_range' _ (natDegree_mod_qU_lt _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordU, substU_coe]
  rfl

/-- 在 `u = 1` 处：`F(ξ) = Σ_i r_i(1) ξ^i`（`ξ` 是 `T³ + T − 1` 的根）。 -/
theorem eval_eq_coords {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) (F : ℂ[X]) :
    F.eval ξ = ∑ i ∈ Finset.range 3, (coordU F i).eval 1 * ξ ^ i := by
  let ev1 : Polynomial (Polynomial ℂ) →+* ℂ := Polynomial.eval₂RingHom (Polynomial.evalRingHom 1) ξ
  have hq : ev1 qU = 0 := by
    simp only [ev1, Polynomial.coe_eval₂RingHom, qU, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.coe_evalRingHom, Polynomial.eval_X]
    linear_combination hξ
  have hmap : ev1 (F.map Polynomial.C) = F.eval ξ := by
    simp only [ev1, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
    rw [show (Polynomial.evalRingHom (1 : ℂ)).comp Polynomial.C = RingHom.id ℂ by ext; simp]
    rfl
  have hmod : ev1 (F.map Polynomial.C) = ev1 ((F.map Polynomial.C) %ₘ qU) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div (F.map Polynomial.C) qU]
    rw [map_add, map_mul, hq, zero_mul, add_zero]
  rw [← hmap, hmod]
  simp only [ev1, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_eq_sum_range' _ (natDegree_mod_qU_lt _)]
  rfl

/-! ## 3. `P_m` 与 `W_m` -/

/-- `D = ∏_{v ≤ m} (1 − v·u) ∈ ℂ[u]`。 -/
def Dpoly (m : ℕ) : ℂ[X] := ∏ i ∈ Finset.range (m + 1), (1 - Polynomial.C (i : ℂ) * Polynomial.X)

theorem Dpoly_eval_one {m : ℕ} (hm : 1 ≤ m) : (Dpoly m).eval 1 = 0 := by
  rw [Dpoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (i := 1) (Finset.mem_range.2 (by omega)) (by simp)

theorem coe_bpoly_uS (i : ℕ) :
    (bpoly ℂ i : PowerSeries ℂ) = (1 - PowerSeries.X) * (1 - PowerSeries.C (i : ℂ) * uS) := by
  have h := uS_mul_one_sub
  have e : (bpoly ℂ i : PowerSeries ℂ) =
      1 - PowerSeries.X - PowerSeries.C (i : ℂ) * PowerSeries.X ^ 3 := by
    simp only [bpoly, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow]
  rw [e]
  linear_combination (PowerSeries.C (i : ℂ)) * h

theorem coe_Ppoly_uS (m : ℕ) :
    (Ppoly ℂ m : PowerSeries ℂ) = (1 - PowerSeries.X) ^ (m + 1) * substU (Dpoly m : PowerSeries ℂ) := by
  have h1 : (Ppoly ℂ m : PowerSeries ℂ) = ∏ i ∈ Finset.range (m + 1), (bpoly ℂ i : PowerSeries ℂ) := by
    rw [Ppoly]
    exact map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) _ _
  have h2 : substU (Dpoly m : PowerSeries ℂ) =
      ∏ i ∈ Finset.range (m + 1), (1 - PowerSeries.C (i : ℂ) * uS) := by
    rw [substU_coe, Dpoly, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [h1, h2, show (1 - PowerSeries.X : PowerSeries ℂ) ^ (m + 1) =
      ∏ _i ∈ Finset.range (m + 1), (1 - PowerSeries.X) by rw [Finset.prod_const, Finset.card_range],
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => coe_bpoly_uS i

theorem eval_bpoly_one {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) : (bpoly ℂ 1).eval ξ = 0 := by
  simp only [bpoly, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Nat.cast_one, one_mul]
  linear_combination -hξ

/-- `b_1(ξ) = 0` 时 `W_m(ξ) = ξ + ξ²`（`m ≥ 1`）。 -/
theorem eval_Wpoly_root {m : ℕ} (hm : 1 ≤ m) {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) :
    (Wpoly ℂ m).eval ξ = ξ + ξ ^ 2 := by
  rw [Wpoly, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finsetSum, Finset.sum_eq_single 1]
  · have h0 : (Ppoly ℂ (1 - 1)).eval ξ = 1 - ξ := by
      rw [Nat.sub_self, Ppoly, zero_add, Finset.prod_range_one, bpoly]
      simp
    rw [Polynomial.eval_mul, Polynomial.eval_C, h0, Nat.cast_one]
    linear_combination -hξ
  · intro j hj hj1
    rw [Finset.mem_Icc] at hj
    rw [Polynomial.eval_mul, Ppoly, Polynomial.eval_prod,
      Finset.prod_eq_zero (i := 1) (Finset.mem_range.2 (by omega)) (eval_bpoly_one hξ), mul_zero]
  · intro h1
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hm⟩) h1

/-! ## 4. `X³ + X − 1` 的三个根 -/

theorem cubic_roots : ∃ a b c : ℂ, ∀ z : ℂ, z ^ 3 + z - 1 = (z - a) * (z - b) * (z - c) := by
  set f : ℂ[X] := Polynomial.X ^ 3 + (Polynomial.X - 1) with hf
  have hlow : (Polynomial.X - 1 : ℂ[X]).degree < 3 := by
    have h1 : (Polynomial.X - 1 : ℂ[X]).degree ≤ 1 :=
      (Polynomial.degree_sub_le _ _).trans
        (max_le Polynomial.degree_X_le (Polynomial.degree_one_le.trans zero_le_one))
    exact h1.trans_lt (by norm_num)
  have hmonic : f.Monic := Polynomial.monic_X_pow_add hlow
  have hdeg : f.natDegree = 3 := by
    rw [hf, Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact hlow),
      Polynomial.natDegree_X_pow]
  have hcard : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.1 (IsAlgClosed.splits f)
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.1 (hcard.trans hdeg)
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul, habc] at hprod
  refine ⟨a, b, c, fun z => ?_⟩
  have := congrArg (Polynomial.eval z) hprod
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, hf, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_one] at this
  linear_combination -this

theorem powsum_rat {a b c : ℂ} (ha : a ^ 3 + a - 1 = 0) (hb : b ^ 3 + b - 1 = 0) (hc : c ^ 3 + c - 1 = 0)
    (h1 : a + b + c = 0) (h2 : a * b + b * c + c * a = 1) :
    ∀ n : ℕ, ∃ q : ℚ, a ^ n + b ^ n + c ^ n = q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · exact ⟨3, by norm_num⟩
    · exact ⟨0, by push_cast; linear_combination h1⟩
    · exact ⟨-2, by push_cast; linear_combination (a + b + c) * h1 - 2 * h2⟩
    · obtain ⟨q1, hq1⟩ := ih n (by omega)
      obtain ⟨q2, hq2⟩ := ih (n + 1) (by omega)
      refine ⟨q1 - q2, ?_⟩
      push_cast
      linear_combination a ^ n * ha + b ^ n * hb + c ^ n * hc + hq1 - hq2

theorem sum_eval_rat {a b c : ℂ} (hs : ∀ n : ℕ, ∃ q : ℚ, a ^ n + b ^ n + c ^ n = q) (h : ℚ[X]) :
    ∃ q : ℚ, h.eval₂ (algebraMap ℚ ℂ) a + h.eval₂ (algebraMap ℚ ℂ) b + h.eval₂ (algebraMap ℚ ℂ) c = q := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨x, hx⟩ := hp
    obtain ⟨y, hy⟩ := hq
    refine ⟨x + y, ?_⟩
    simp only [Polynomial.eval₂_add]
    push_cast
    linear_combination hx + hy
  | monomial n r =>
    obtain ⟨x, hx⟩ := hs n
    refine ⟨r * x, ?_⟩
    simp only [Polynomial.eval₂_monomial]
    push_cast
    rw [eq_ratCast]
    linear_combination (r : ℂ) * hx

theorem not_rat_cube_81 (q : ℚ) : q ^ 3 ≠ 81 := by
  intro hq
  have hr : ((q : ℝ)) ^ 3 = ((81 : ℤ) : ℝ) := by exact_mod_cast hq
  have hirr := irrational_nrt_of_notint_nrt 3 81 hr ?_ (by norm_num)
  · exact hirr.ne_rat q rfl
  · rintro ⟨y, hy⟩
    have h3 : (y : ℝ) ^ 3 = 81 := by rw [← hy]; exact_mod_cast hq
    have hy3 : y ^ 3 = 81 := by exact_mod_cast h3
    have hpos : 0 < y := by
      by_contra h
      have : y ^ 3 ≤ 0 := (Odd.pow_nonpos_iff (by decide)).2 (not_lt.1 h)
      linarith
    rcases (by omega : y ≤ 4 ∨ 5 ≤ y) with h | h
    · have := pow_le_pow_left₀ hpos.le h 3
      norm_num at this
      linarith
    · have := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 5) h 3
      norm_num at this
      linarith

/-- `X³ + X − 1` 的根上 `ξ^p(1+ξ) = λ·ξ^r` 不可能对所有根成立（`λ³ = 3` 且 `3λ ∈ ℚ`）。 -/
theorem no_common_value (p r : ℕ) (lam : ℂ) :
    ¬ ∀ ξ : ℂ, ξ ^ 3 + ξ - 1 = 0 → ξ ^ p * (1 + ξ) = lam * ξ ^ r := by
  intro H
  obtain ⟨a, b, c, hz⟩ := cubic_roots
  have ha : a ^ 3 + a - 1 = 0 := by rw [hz a]; ring
  have hb : b ^ 3 + b - 1 = 0 := by rw [hz b]; ring
  have hc : c ^ 3 + c - 1 = 0 := by rw [hz c]; ring
  have z0 := hz 0
  have z1 := hz 1
  have z2 := hz 2
  have zm := hz (-1)
  have e1 : a + b + c = 0 := by linear_combination (1 / 2 : ℂ) * z0 - z1 + (1 / 2 : ℂ) * z2
  have e2 : a * b + b * c + c * a = 1 := by linear_combination (3 / 2 : ℂ) * z0 - 2 * z1 + (1 / 2 : ℂ) * z2
  have e3 : a * b * c = 1 := by linear_combination z0
  have e4 : (1 + a) * (1 + b) * (1 + c) = 3 := by linear_combination zm
  have hs := powsum_rat ha hb hc e1 e2
  have Ha := H a ha
  have Hb := H b hb
  have Hc := H c hc
  have hlam3 : lam ^ 3 = 3 := by
    have hmul : (a * b * c) ^ p * ((1 + a) * (1 + b) * (1 + c)) = lam ^ 3 * (a * b * c) ^ r := by
      calc _ = (a ^ p * (1 + a)) * (b ^ p * (1 + b)) * (c ^ p * (1 + c)) := by ring
        _ = (lam * a ^ r) * (lam * b ^ r) * (lam * c ^ r) := by rw [Ha, Hb, Hc]
        _ = _ := by ring
    rw [e3, e4, one_pow, one_pow, mul_one, one_mul] at hmul
    exact hmul.symm
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; norm_num at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; norm_num at hb
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc; norm_num at hc
  -- `λ` 是某个有理系数多项式在每个根处的值
  obtain ⟨h, hh⟩ : ∃ h : ℚ[X], ∀ x : ℂ, x ^ 3 + x - 1 = 0 → x ^ p * (1 + x) = lam * x ^ r →
      h.eval₂ (algebraMap ℚ ℂ) x = lam := by
    rcases le_or_gt r p with hrp | hrp
    · refine ⟨Polynomial.X ^ (p - r) * (1 + Polynomial.X), fun x hx Hx => ?_⟩
      have hx0 : x ≠ 0 := fun h => by rw [h] at hx; norm_num at hx
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_add,
        Polynomial.eval₂_one]
      have e : x ^ p = x ^ (p - r) * x ^ r := by rw [← pow_add, Nat.sub_add_cancel hrp]
      rw [e] at Hx
      have hxr : x ^ r ≠ 0 := pow_ne_zero _ hx0
      apply mul_right_cancel₀ hxr
      linear_combination Hx
    · refine ⟨(Polynomial.X ^ 2 + 1) ^ (r - p) * (1 + Polynomial.X), fun x hx Hx => ?_⟩
      have hx0 : x ≠ 0 := fun h => by rw [h] at hx; norm_num at hx
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_add,
        Polynomial.eval₂_one]
      have e : x ^ r = x ^ p * x ^ (r - p) := by rw [← pow_add, Nat.add_sub_cancel' hrp.le]
      rw [e] at Hx
      have hxp : x ^ p ≠ 0 := pow_ne_zero _ hx0
      have H1 : 1 + x = lam * x ^ (r - p) := by
        apply mul_left_cancel₀ hxp
        linear_combination Hx
      have H2 : (x * (x ^ 2 + 1)) ^ (r - p) = 1 := by
        rw [show x * (x ^ 2 + 1) = 1 by linear_combination hx, one_pow]
      calc (x ^ 2 + 1) ^ (r - p) * (1 + x) = (x ^ 2 + 1) ^ (r - p) * (lam * x ^ (r - p)) := by rw [H1]
        _ = lam * (x * (x ^ 2 + 1)) ^ (r - p) := by rw [mul_pow]; ring
        _ = lam := by rw [H2, mul_one]
  obtain ⟨q, hq⟩ := sum_eval_rat hs h
  rw [hh a ha Ha, hh b hb Hb, hh c hc Hc] at hq
  have hq3 : (q : ℂ) ^ 3 = 81 := by
    rw [← hq]
    linear_combination 27 * hlam3
  exact not_rat_cube_81 q (by exact_mod_cast hq3)

/-! ## 5. 定理 6.1 -/

/-- 论文第 2 节的二项式约定：`0 ≤ b ≤ a` 之外 `C(a, b) = 0`（`a < 0` 时也是）。 -/
def binomZ (a b : ℤ) : ℕ := if 0 ≤ b ∧ b ≤ a then a.toNat.choose b.toNat else 0

theorem binomZ_sub_two_mul (n t : ℕ) :
    binomZ ((n : ℤ) - 2 * t) t = if 3 * t ≤ n then (n - 2 * t).choose t else 0 := by
  unfold binomZ
  by_cases h : 3 * t ≤ n
  · rw [ite_eq_left (show (0 : ℤ) ≤ t ∧ (t : ℤ) ≤ n - 2 * t by omega), ite_eq_left h,
      show ((n : ℤ) - 2 * t).toNat = n - 2 * t by omega, show (t : ℤ).toNat = t by omega]
  · rw [ite_eq_right (show ¬ ((0 : ℤ) ≤ t ∧ (t : ℤ) ≤ n - 2 * t) by omega), ite_eq_right h]

/-- `u^t/(1−x) = Σ_n C(n−2t, t) x^n`（`n ≥ 3t`）。 -/
theorem coeff_uS_pow_mul_mk_one (t n : ℕ) :
    PowerSeries.coeff n (uS ^ t * PowerSeries.mk 1) =
      if 3 * t ≤ n then ((n - 2 * t).choose t : ℂ) else 0 := by
  rw [uS, mul_pow, ← pow_mul, mul_assoc, ← pow_succ, PowerSeries.coeff_X_pow_mul',
    PowerSeries.mk_one_pow_eq_mk_choose_add]
  split_ifs with h
  · rw [PowerSeries.coeff_mk, show t + (n - 3 * t) = n - 2 * t by omega]
  · rfl

/-- `ã(u)/(1−x)` 的 `x^n` 系数是 `Σ_t a_t C(n−2t, t)`。 -/
theorem coeff_substU_mk_mul_mk_one (a : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (substU (PowerSeries.mk a) * PowerSeries.mk 1) =
      ∑ t ∈ Finset.range (n + 1), a t * (if 3 * t ≤ n then ((n - 2 * t).choose t : ℂ) else 0) := by
  obtain ⟨R, hR⟩ : PowerSeries.X ^ (n + 1) ∣
      PowerSeries.mk a - (PowerSeries.trunc (n + 1) (PowerSeries.mk a) : PowerSeries ℂ) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [map_sub, PowerSeries.coeff_coe_trunc_of_lt hj, sub_self]
  have hsplit : PowerSeries.mk a =
      (PowerSeries.trunc (n + 1) (PowerSeries.mk a) : PowerSeries ℂ) + PowerSeries.X ^ (n + 1) * R := by
    rw [← hR]
    ring
  have htail : PowerSeries.coeff n (uS ^ (n + 1) * substU R * PowerSeries.mk 1) = 0 := by
    rw [uS, mul_pow, ← pow_mul, mul_assoc, mul_assoc, PowerSeries.coeff_X_pow_mul',
      ite_eq_right (by omega)]
  rw [hsplit, map_add substU, map_mul substU, map_pow substU, substU_X, add_mul, map_add, htail, add_zero,
    substU_coe, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [PowerSeries.coeff_mk, mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul, smul_eq_mul,
    coeff_uS_pow_mul_mk_one]

/-- **论文定理 6.1**：`m ≥ 1` 时 `U_k(m)` 不能对所有 `k ≥ k₀` 写成 `Σ_s A(s)·C(k+c−2s, m+s+d)`
（整数 `c, d`，复数 `A(s)` 与 `k` 无关，二项式按 `binomZ` 的约定；对每个 `k` 只有有限个 `s` 的项非零，
`∑ᶠ` 就是这个有限和）。 -/
theorem thm_S {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ (c d : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
      (U k m : ℂ) = ∑ᶠ s : ℤ, A s * (binomZ (k + c - 2 * s) (m + s + d) : ℂ) := by
  rintro ⟨c, d, k₀, A, hA⟩
  -- 第一步：令 `t = s + m + d`，`a_t = A(t − m − d)`，`K = c + 2(m + d)`
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = m + d := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = c + 2 * e := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, ∀ t, a t = A (t - e) := ⟨_, fun _ => rfl⟩
  have hcoef : ∀ k : ℕ, k₀ ≤ k → 0 ≤ (k : ℤ) + K →
      (U k m : ℂ) =
        PowerSeries.coeff ((k : ℤ) + K).toNat (substU (PowerSeries.mk a) * PowerSeries.mk 1) := by
    intro k hk hkK
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k + K := ⟨((k : ℤ) + K).toNat, by omega⟩
    rw [show ((k : ℤ) + K).toNat = n by omega, hA k hk, coeff_substU_mk_mul_mk_one]
    rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (n + 1)).map
      ⟨fun t : ℕ => (t : ℤ) - e, fun x y h => by simpa using h⟩) ?_]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun t _ => ?_
      show A ((t : ℤ) - e) * (binomZ ((k : ℤ) + c - 2 * ((t : ℤ) - e)) ((m : ℤ) + ((t : ℤ) - e) + d) : ℂ) =
        a t * (if 3 * t ≤ n then ((n - 2 * t).choose t : ℂ) else 0)
      rw [show (k : ℤ) + c - 2 * ((t : ℤ) - e) = (n : ℤ) - 2 * t by omega,
        show (m : ℤ) + ((t : ℤ) - e) + d = t by omega, binomZ_sub_two_mul, Nat.cast_ite, Nat.cast_zero,
        ha t]
    · intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      have hb : binomZ ((k : ℤ) + c - 2 * s) ((m : ℤ) + s + d) ≠ 0 := by
        intro h0
        apply hs
        rw [h0, Nat.cast_zero, mul_zero]
      unfold binomZ at hb
      have hcond : 0 ≤ (m : ℤ) + s + d ∧ (m : ℤ) + s + d ≤ (k : ℤ) + c - 2 * s := by
        by_contra hc
        exact hb (ite_eq_right hc)
      rw [Finset.mem_coe, Finset.mem_map]
      refine ⟨((m : ℤ) + s + d).toNat, Finset.mem_range.2 (by omega), ?_⟩
      show ((((m : ℤ) + s + d).toNat : ℕ) : ℤ) - e = s
      omega
  -- 两边的母函数只差有限项：`x^{K₁} G_m − x^{K₂} ã(u)/(1−x)` 是多项式 `E`
  obtain ⟨K₁, K₂, hK12⟩ : ∃ K₁ K₂ : ℕ, K = (K₁ : ℤ) - K₂ := ⟨K.toNat, (-K).toNat, by omega⟩
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries ℂ, S = substU (PowerSeries.mk a) * PowerSeries.mk 1 := ⟨_, rfl⟩
  have hlarge : ∀ j, k₀ + K₁ + K₂ ≤ j →
      PowerSeries.coeff j (PowerSeries.X ^ K₁ * Gc m) = PowerSeries.coeff j (PowerSeries.X ^ K₂ * S) := by
    intro j hj
    rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
      ite_eq_left (by omega), Gc, PowerSeries.coeff_mk, hS]
    have h1 := hcoef (j - K₁) (by omega) (by omega)
    rw [show (((j - K₁ : ℕ) : ℤ) + K).toNat = j - K₂ by omega] at h1
    exact h1
  obtain ⟨Epoly, hE⟩ : ∃ Epoly : ℂ[X],
      PowerSeries.X ^ K₁ * Gc m - PowerSeries.X ^ K₂ * S = (Epoly : PowerSeries ℂ) := by
    refine ⟨PowerSeries.trunc (k₀ + K₁ + K₂) (PowerSeries.X ^ K₁ * Gc m - PowerSeries.X ^ K₂ * S), ?_⟩
    ext j
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hj
    · rfl
    · rw [map_sub, hlarge j (by omega), sub_self]
  -- 乘以 `P_m = (1−x)^{m+1} D(u)`：`x^{K₁} W_m = x^{K₂}(1−x)^m·(Dã)(u) + D(u)·(1−x)^{m+1} E`
  obtain ⟨bS, hbS⟩ : ∃ bS : PowerSeries ℂ, bS = (Dpoly m : PowerSeries ℂ) * PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁⟩ : ∃ F : ℂ[X], F = Polynomial.X ^ K₁ * Wpoly ℂ m := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F : ℂ[X], F = Polynomial.X ^ K₂ * (1 - Polynomial.X) ^ m := ⟨_, rfl⟩
  obtain ⟨F₃, hF₃⟩ : ∃ F : ℂ[X], F = (1 - Polynomial.X) ^ (m + 1) * Epoly := ⟨_, rfl⟩
  have hmain : (F₁ : PowerSeries ℂ) =
      (F₂ : PowerSeries ℂ) * substU bS + substU (Dpoly m : PowerSeries ℂ) * (F₃ : PowerSeries ℂ) := by
    have hPG := P_mul_Gc m
    have hP := coe_Ppoly_uS m
    have hmk : PowerSeries.mk (1 : ℕ → ℂ) * (1 - PowerSeries.X) = 1 :=
      PowerSeries.mk_one_mul_one_sub_eq_one ℂ
    rw [hS] at hE
    rw [hF₁, hF₂, hF₃, hbS]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_sub,
      Polynomial.coe_one, map_mul substU]
    linear_combination (substU (Dpoly m : PowerSeries ℂ) * (1 - PowerSeries.X) ^ (m + 1)) * hE -
      PowerSeries.X ^ K₁ * hPG + (PowerSeries.X ^ K₁ * Gc m) * hP +
      (substU (Dpoly m : PowerSeries ℂ) * PowerSeries.X ^ K₂ * substU (PowerSeries.mk a) *
        (1 - PowerSeries.X) ^ m) * hmk
  -- 第二步：比较坐标，`r_i(F₁) = r_i(F₂)·Dã + D·r_i(F₃)`（`i = 0, 1, 2`）
  have c1 := coe_eq_coords F₁
  have c2 := coe_eq_coords F₂
  have c3 := coe_eq_coords F₃
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
    at c1 c2 c3
  have hzero := substU_coords_unique
    (α := (coordU F₁ 0 : PowerSeries ℂ) - coordU F₂ 0 * bS - Dpoly m * coordU F₃ 0)
    (β := (coordU F₁ 1 : PowerSeries ℂ) - coordU F₂ 1 * bS - Dpoly m * coordU F₃ 1)
    (γ := (coordU F₁ 2 : PowerSeries ℂ) - coordU F₂ 2 * bS - Dpoly m * coordU F₃ 2) (by
      simp only [map_sub substU, map_mul substU]
      linear_combination hmain - c1 + substU bS * c2 + substU (Dpoly m : PowerSeries ℂ) * c3)
  have hrel : ∀ i, i < 3 →
      (coordU F₁ i : PowerSeries ℂ) = coordU F₂ i * bS + Dpoly m * coordU F₃ i := by
    intro i hi
    interval_cases i
    · linear_combination hzero.1
    · linear_combination hzero.2.1
    · linear_combination hzero.2.2
  -- 消去 `ã`，在 `u = 1`（`D(1) = 0`）处坐标向量成比例
  have hminor : ∀ i j, i < 3 → j < 3 →
      (coordU F₁ i).eval 1 * (coordU F₂ j).eval 1 = (coordU F₁ j).eval 1 * (coordU F₂ i).eval 1 := by
    intro i j hi hj
    have hp : coordU F₁ i * coordU F₂ j - coordU F₁ j * coordU F₂ i =
        Dpoly m * (coordU F₃ i * coordU F₂ j - coordU F₃ j * coordU F₂ i) := by
      apply Polynomial.coe_injective
      simp only [Polynomial.coe_sub, Polynomial.coe_mul]
      linear_combination (coordU F₂ j : PowerSeries ℂ) * hrel i hi -
        (coordU F₂ i : PowerSeries ℂ) * hrel j hj
    have h1 := congrArg (Polynomial.eval 1) hp
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Dpoly_eval_one hm, zero_mul] at h1
    linear_combination h1
  -- 第三步：在 `X³ + X − 1` 的根 `ξ` 处，`F₁(ξ) = ξ^{K₁+1}(1+ξ)`，`F₂(ξ) = ξ^{K₂+3m}`
  have hF₁root : ∀ ξ : ℂ, ξ ^ 3 + ξ - 1 = 0 → F₁.eval ξ = ξ ^ (K₁ + 1) * (1 + ξ) := by
    intro ξ hξ
    rw [hF₁, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_Wpoly_root hm hξ]
    ring
  have hF₂root : ∀ ξ : ℂ, ξ ^ 3 + ξ - 1 = 0 → F₂.eval ξ = ξ ^ (K₂ + 3 * m) := by
    intro ξ hξ
    rw [hF₂, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      show 1 - ξ = ξ ^ 3 by linear_combination -hξ, ← pow_mul, ← pow_add]
  obtain ⟨ξ₀, b₀, c₀, hz⟩ := cubic_roots
  have hξ₀ : ξ₀ ^ 3 + ξ₀ - 1 = 0 := by rw [hz ξ₀]; ring
  have hξ₀0 : ξ₀ ≠ 0 := fun h => by rw [h] at hξ₀; norm_num at hξ₀
  have hex : ∃ j, j < 3 ∧ (coordU F₂ j).eval 1 ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ i, i < 3 → (coordU F₂ i).eval 1 = 0 := fun i hi => by
      by_contra hne
      exact hcon ⟨i, hi, hne⟩
    have h0 : ∑ i ∈ Finset.range 3, (coordU F₂ i).eval 1 * ξ₀ ^ i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hcon' i (Finset.mem_range.1 hi), zero_mul]
    have h1 := eval_eq_coords hξ₀ F₂
    rw [h0, hF₂root ξ₀ hξ₀] at h1
    exact pow_ne_zero _ hξ₀0 h1
  obtain ⟨j, hj, hvj⟩ := hex
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = (coordU F₁ j).eval 1 / (coordU F₂ j).eval 1 := ⟨_, rfl⟩
  apply no_common_value (K₁ + 1) (K₂ + 3 * m) lam
  intro ξ hξ
  rw [← hF₁root ξ hξ, ← hF₂root ξ hξ, eval_eq_coords hξ F₁, eval_eq_coords hξ F₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h := hminor i j (Finset.mem_range.1 hi) hj
  have hv : (coordU F₁ i).eval 1 = lam * (coordU F₂ i).eval 1 := by
    rw [hlam, div_mul_eq_mul_div, eq_div_iff hvj]
    linear_combination h
  rw [hv, mul_assoc]

end

end A207123
