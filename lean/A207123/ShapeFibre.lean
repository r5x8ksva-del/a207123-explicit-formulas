import A207123.SingleSum

/-!
# 论文定理 6.3 的第 1–3 步：一般形状 `(α, β)` 的母函数与纤维

论文定理 6.3 的证明前三步，对一般的形状 `C(k+c−αs, βs+d)`（`α, β ≥ 0`，`n = α + β ≥ 1`）：
* 第 1 步（`shape_gf`）：`Σ_k C(k+c−αs, βs+d) x^k = x^{d−c}(1−x)^{−d−1} v^s`，`v = x^n/(1−x)^β`（`vS`）。所以若 `f(k)`
  有这种表示（`ShapeRep`），则要么 `f` 最终为 0，要么 `x^{K₁}F − x^{K₂}(1−x)^{−h−1}ã(v)` 是多项式（`F = Σ f(k)x^k`，
  代入用 Mathlib 的 `PowerSeries.subst`，`substV`）。
* 第 2 步：`z = x`（`α ≥ 1`，`b = β`）或 `z = x/(1−x)`（`α = 0`，`b = 0`）满足 `z^n = v(1−z)^b`；`1, z, …, z^{n−1}` 在
  `ℂ⟦v⟧` 上线性无关（`subst_coords_unique_gen`：代入后的 `x` 进阶模 `n` 两两不同），多项式在 `ℂ[v][T]` 中对
  `T^n − v(1−T)^b` 取余得到坐标（`aeval_eq_coordsV`）。`cross_of_eq`：若 `F₁(z) = F₂(z)·ã(v)`，则
  `T^n − v₀(1−T)^b` 的任意两个根 `η, η'` 满足 `F₁(η)F₂(η') = F₁(η')F₂(η)`。
* 第 3 步：论文说 `G_m` 在 `b_1` 的根 `ξ` 处有极点，所以 `ã` 在 `v(ξ)` 有极点、`G_m` 在纤维 `v = v(ξ)` 的每一点都有极点。
  这里不用极点：取 `F₂ = x^{K₂}P_m`、`F₁ = (1−x)^{h+1}(x^{K₁}W_m − P_m E)`，在 `ξ` 处 `F₂(ξ) = 0`、`F₁(ξ) ≠ 0`，由
  `cross_of_eq` 得纤维上每个点 `η ≠ 0` 都是 `P_m` 的根（`shape_fibre_x`；`α = 0` 时纤维用 `y = x/(1−x)` 描述，
  `shape_fibre_y`，多项式先乘 `(1+y)^D` 化成 `y` 的多项式 `homogY`）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 代入 `v = x^n/(1−x)^β` -/

/-- `v = x^n/(1−x)^β`（`x` 的幂级数）。 -/
def vS (n β : ℕ) : PowerSeries ℂ := PowerSeries.X ^ n * PowerSeries.mk 1 ^ β

theorem vS_mul_one_sub_pow (n β : ℕ) : vS n β * (1 - PowerSeries.X) ^ β = PowerSeries.X ^ n := by
  rw [vS, mul_assoc, ← mul_pow, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow, mul_one]

theorem hasSubst_vS {n : ℕ} (hn : 1 ≤ n) (β : ℕ) : PowerSeries.HasSubst (vS n β) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
  rw [vS, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), zero_mul]

/-- 代入 `v ↦ x^n/(1−x)^β`：`ℂ⟦v⟧ → ℂ⟦x⟧`。 -/
def substV {n : ℕ} (hn : 1 ≤ n) (β : ℕ) : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom (hasSubst_vS hn β)

theorem substV_X {n : ℕ} (hn : 1 ≤ n) (β : ℕ) : substV hn β PowerSeries.X = vS n β :=
  PowerSeries.substAlgHom_X (hasSubst_vS hn β)

theorem substV_coe {n : ℕ} (hn : 1 ≤ n) (β : ℕ) (p : ℂ[X]) :
    substV hn β (p : PowerSeries ℂ) = Polynomial.aeval (vS n β) p :=
  PowerSeries.substAlgHom_coe (hasSubst_vS hn β) p

theorem coeff_substV {n : ℕ} (hn : 1 ≤ n) (β : ℕ) (f : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.coeff j (substV hn β f) =
      ∑ᶠ d, PowerSeries.coeff d f • PowerSeries.coeff j (vS n β ^ d) := by
  rw [substV, PowerSeries.coe_substAlgHom, PowerSeries.coeff_subst' (hasSubst_vS hn β)]

theorem coeff_vS_pow (n β d j : ℕ) :
    PowerSeries.coeff j (vS n β ^ d) =
      if n * d ≤ j then PowerSeries.coeff (j - n * d) (PowerSeries.mk (1 : ℕ → ℂ) ^ (β * d)) else 0 := by
  rw [vS, mul_pow, ← pow_mul, ← pow_mul, PowerSeries.coeff_X_pow_mul']

theorem coeff_vS_pow_of_lt {n β d j : ℕ} (h : j < n * d) : PowerSeries.coeff j (vS n β ^ d) = 0 := by
  rw [coeff_vS_pow, ite_eq_right (by omega)]

theorem coeff_vS_pow_self (n β d : ℕ) : PowerSeries.coeff (n * d) (vS n β ^ d) = 1 := by
  rw [coeff_vS_pow, ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  simp

/-- `f` 的前 `k` 个系数为 0 时，`f(v)` 的前 `nk` 个系数为 0，第 `nk` 个系数是 `f` 的第 `k` 个。 -/
theorem vanish_substV {n : ℕ} (hn : 1 ≤ n) (β : ℕ) {f : PowerSeries ℂ} {k : ℕ}
    (hf : ∀ i < k, PowerSeries.coeff i f = 0) :
    (∀ j < n * k, PowerSeries.coeff j (substV hn β f) = 0) ∧
      PowerSeries.coeff (n * k) (substV hn β f) = PowerSeries.coeff k f := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [coeff_substV]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : d < k
    · rw [hf d hd, zero_smul]
    · rw [coeff_vS_pow_of_lt (lt_of_lt_of_le hj (Nat.mul_le_mul_left n (not_lt.1 hd))), smul_zero]
  · rw [coeff_substV, finsum_eq_single _ k (fun d hd => ?_), coeff_vS_pow_self, smul_eq_mul, mul_one]
    rcases Nat.lt_or_gt_of_ne hd with hd | hd
    · rw [hf d hd, zero_smul]
    · rw [coeff_vS_pow_of_lt (by nlinarith), smul_zero]

/-- `g` 的前 `L` 个系数为 0、`w` 的常数项为 1 时，`g·(Xw)^i` 的前 `L+i` 个系数为 0，第 `L+i` 个系数是 `g` 的第 `L` 个。 -/
theorem vanish_mul_Xw_pow {w : PowerSeries ℂ} (hw : PowerSeries.constantCoeff w = 1) {g : PowerSeries ℂ}
    {L : ℕ} (hg : ∀ j < L, PowerSeries.coeff j g = 0) (i : ℕ) :
    (∀ j < L + i, PowerSeries.coeff j (g * (PowerSeries.X * w) ^ i) = 0) ∧
      PowerSeries.coeff (L + i) (g * (PowerSeries.X * w) ^ i) = PowerSeries.coeff L g := by
  obtain ⟨g', hg'⟩ := PowerSeries.X_pow_dvd_iff.2 hg
  have e : g * (PowerSeries.X * w) ^ i = PowerSeries.X ^ (L + i) * (g' * w ^ i) := by
    rw [hg', mul_pow, pow_add]
    ring
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [e, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  · rw [e, PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, hg', PowerSeries.coeff_X_pow_mul',
      ite_eq_left le_rfl, Nat.sub_self]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hw]

/-- `1, z, …, z^{n−1}`（`z = Xw`，`w` 的常数项为 1）在 `ℂ⟦v⟧` 上线性无关：`α_i(v)·z^i` 的 `x` 进阶模 `n` 余 `i`。 -/
theorem subst_coords_unique_gen {n : ℕ} (hn : 1 ≤ n) (β : ℕ) {w : PowerSeries ℂ}
    (hw : PowerSeries.constantCoeff w = 1) (α : ℕ → PowerSeries ℂ)
    (h : ∑ i ∈ Finset.range n, substV hn β (α i) * (PowerSeries.X * w) ^ i = 0) :
    ∀ i < n, α i = 0 := by
  have key : ∀ k, ∀ i < n, PowerSeries.coeff k (α i) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro hi
        have hsum := congrArg (PowerSeries.coeff (n * k + i)) h
        rw [map_sum, map_zero, Finset.sum_eq_single i] at hsum
        · have hv := vanish_substV hn β (f := α i) (k := k) (fun j hj => ihk j hj i hi)
          rw [(vanish_mul_Xw_pow hw hv.1 i).2, hv.2] at hsum
          exact hsum
        · intro j hj hji
          rw [Finset.mem_range] at hj
          rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
          · have hv := vanish_substV hn β (f := α j) (k := k + 1) (fun l hl => by
              rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
              · exact ihk l hl j hj
              · exact ihi j hlt hj)
            have e : n * (k + 1) = n * k + n := by ring
            exact (vanish_mul_Xw_pow hw hv.1 j).1 _ (by omega)
          · have hv := vanish_substV hn β (f := α j) (k := k) (fun l hl => ihk l hl j hj)
            exact (vanish_mul_Xw_pow hw hv.1 j).1 _ (by omega)
        · intro hi'
          exact absurd (Finset.mem_range.2 hi) hi'
  intro i hi
  ext k
  simp [key k i hi]

/-! ## 2. 坐标：在 `ℂ[v][T]` 中对 `T^n − v(1−T)^b` 取余 -/

/-- `q = T^n − v·(1−T)^b ∈ ℂ[v][T]`。 -/
def qV (n b : ℕ) : Polynomial (Polynomial ℂ) :=
  Polynomial.X ^ n - Polynomial.C Polynomial.X * (1 - Polynomial.X) ^ b

theorem natDegree_qV_low (b : ℕ) :
    (Polynomial.C Polynomial.X * (1 - Polynomial.X) ^ b : Polynomial (Polynomial ℂ)).natDegree ≤ b := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  have h2 : (1 - Polynomial.X : Polynomial (Polynomial ℂ)).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  calc b * (1 - Polynomial.X : Polynomial (Polynomial ℂ)).natDegree ≤ b * 1 := Nat.mul_le_mul_left b h2
    _ = b := mul_one b

theorem qV_monic {n b : ℕ} (hbn : b < n) : (qV n b).Monic :=
  Polynomial.monic_X_pow_sub ((Polynomial.degree_le_of_natDegree_le (natDegree_qV_low b)).trans_lt
    (by exact_mod_cast hbn))

theorem natDegree_qV {n b : ℕ} (hbn : b < n) : (qV n b).natDegree = n := by
  rw [qV, Polynomial.natDegree_sub_eq_left_of_natDegree_lt
    (by rw [Polynomial.natDegree_X_pow]; exact lt_of_le_of_lt (natDegree_qV_low b) hbn),
    Polynomial.natDegree_X_pow]

theorem natDegree_mod_qV_lt {n b : ℕ} (hn : 1 ≤ n) (hbn : b < n) (p : Polynomial (Polynomial ℂ)) :
    (p %ₘ qV n b).natDegree < n := by
  by_cases h0 : p %ₘ qV n b = 0
  · rw [h0, Polynomial.natDegree_zero]
    omega
  · have h1 : qV n b ≠ 1 := by
      intro h
      have := natDegree_qV hbn
      rw [h, Polynomial.natDegree_one] at this
      omega
    have := Polynomial.natDegree_modByMonic_lt p (qV_monic hbn) h1
    rwa [natDegree_qV hbn] at this

/-- 多项式 `F` 的坐标：`F(T) mod q` 的系数（`ℂ[v]` 中）。 -/
def coordV (n b : ℕ) (F : ℂ[X]) (i : ℕ) : ℂ[X] := ((F.map Polynomial.C) %ₘ qV n b).coeff i

/-- `z^n = v(1−z)^b` 时 `F(z) = Σ_{i<n} r_i(v) z^i`。 -/
theorem aeval_eq_coordsV {n b : ℕ} (hn : 1 ≤ n) (hbn : b < n) (β : ℕ) {z : PowerSeries ℂ}
    (hz : z ^ n = vS n β * (1 - z) ^ b) (F : ℂ[X]) :
    Polynomial.aeval z F =
      ∑ i ∈ Finset.range n, substV hn β (coordV n b F i : PowerSeries ℂ) * z ^ i := by
  let ev : Polynomial (Polynomial ℂ) →+* PowerSeries ℂ :=
    Polynomial.eval₂RingHom (Polynomial.aeval (vS n β)).toRingHom z
  have hq : ev (qV n b) = 0 := by
    simp only [ev, Polynomial.coe_eval₂RingHom, qV, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_one,
      Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
    rw [hz, sub_self]
  have hmap : ev (F.map Polynomial.C) = Polynomial.aeval z F := by
    simp only [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def]
    congr 1
    ext c
    simp
  have hmod : ev (F.map Polynomial.C) = ev ((F.map Polynomial.C) %ₘ qV n b) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div (F.map Polynomial.C) (qV n b)]
    rw [map_add, map_mul, hq, zero_mul, add_zero]
  rw [← hmap, hmod]
  simp only [ev, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_eq_sum_range' _ (natDegree_mod_qV_lt hn hbn _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordV, substV_coe]
  rfl

/-- 在 `v = v₀` 处：`F(η) = Σ_{i<n} r_i(v₀) η^i`（`η` 是 `T^n − v₀(1−T)^b` 的根）。 -/
theorem eval_eq_coordsV {n b : ℕ} (hn : 1 ≤ n) (hbn : b < n) {v₀ η : ℂ} (hη : η ^ n = v₀ * (1 - η) ^ b)
    (F : ℂ[X]) :
    F.eval η = ∑ i ∈ Finset.range n, (coordV n b F i).eval v₀ * η ^ i := by
  let ev1 : Polynomial (Polynomial ℂ) →+* ℂ := Polynomial.eval₂RingHom (Polynomial.evalRingHom v₀) η
  have hq : ev1 (qV n b) = 0 := by
    simp only [ev1, Polynomial.coe_eval₂RingHom, qV, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_one,
      Polynomial.eval₂_X, Polynomial.coe_evalRingHom, Polynomial.eval_X]
    rw [hη, sub_self]
  have hmap : ev1 (F.map Polynomial.C) = F.eval η := by
    simp only [ev1, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
    rw [show (Polynomial.evalRingHom v₀).comp Polynomial.C = RingHom.id ℂ by ext; simp]
    rfl
  have hmod : ev1 (F.map Polynomial.C) = ev1 ((F.map Polynomial.C) %ₘ qV n b) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div (F.map Polynomial.C) (qV n b)]
    rw [map_add, map_mul, hq, zero_mul, add_zero]
  rw [← hmap, hmod]
  simp only [ev1, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_eq_sum_range' _ (natDegree_mod_qV_lt hn hbn _)]
  rfl

/-- 第 2 步的结论：`F₁(z) = F₂(z)·f(v)`（`f ∈ ℂ⟦v⟧`）时，`T^n − v₀(1−T)^b` 的任意两个根 `η, η'` 满足
`F₁(η)F₂(η') = F₁(η')F₂(η)`（坐标向量的 2×2 子式在 `ℂ[v]` 中全为 0）。 -/
theorem cross_of_eq {n b : ℕ} (hn : 1 ≤ n) (hbn : b < n) (β : ℕ) {w : PowerSeries ℂ}
    (hw : PowerSeries.constantCoeff w = 1)
    (hz : (PowerSeries.X * w) ^ n = vS n β * (1 - PowerSeries.X * w) ^ b)
    {F₁ F₂ : ℂ[X]} {f : PowerSeries ℂ}
    (h : Polynomial.aeval (PowerSeries.X * w) F₁ = Polynomial.aeval (PowerSeries.X * w) F₂ * substV hn β f)
    {v₀ η η' : ℂ} (hη : η ^ n = v₀ * (1 - η) ^ b) (hη' : η' ^ n = v₀ * (1 - η') ^ b) :
    F₁.eval η * F₂.eval η' = F₁.eval η' * F₂.eval η := by
  have c1 := aeval_eq_coordsV hn hbn β hz F₁
  have c2 := aeval_eq_coordsV hn hbn β hz F₂
  have hsum : ∑ i ∈ Finset.range n, substV hn β ((coordV n b F₁ i : PowerSeries ℂ) - coordV n b F₂ i * f) *
      (PowerSeries.X * w) ^ i = 0 := by
    have e : ∀ i, substV hn β ((coordV n b F₁ i : PowerSeries ℂ) - coordV n b F₂ i * f) *
        (PowerSeries.X * w) ^ i =
        substV hn β (coordV n b F₁ i : PowerSeries ℂ) * (PowerSeries.X * w) ^ i -
          substV hn β (coordV n b F₂ i : PowerSeries ℂ) * (PowerSeries.X * w) ^ i * substV hn β f := by
      intro i
      rw [map_sub, map_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib, ← Finset.sum_mul, ← c1, ← c2, h, sub_self]
  have hzero := subst_coords_unique_gen hn β hw
    (fun i => (coordV n b F₁ i : PowerSeries ℂ) - coordV n b F₂ i * f) hsum
  have hminor : ∀ i j, i < n → j < n →
      (coordV n b F₁ i).eval v₀ * (coordV n b F₂ j).eval v₀ =
        (coordV n b F₁ j).eval v₀ * (coordV n b F₂ i).eval v₀ := by
    intro i j hi hj
    have hzi : (coordV n b F₁ i : PowerSeries ℂ) - coordV n b F₂ i * f = 0 := hzero i hi
    have hzj : (coordV n b F₁ j : PowerSeries ℂ) - coordV n b F₂ j * f = 0 := hzero j hj
    have hp : coordV n b F₁ i * coordV n b F₂ j = coordV n b F₁ j * coordV n b F₂ i := by
      apply Polynomial.coe_injective
      simp only [Polynomial.coe_mul]
      linear_combination (coordV n b F₂ j : PowerSeries ℂ) * hzi - (coordV n b F₂ i : PowerSeries ℂ) * hzj
    have h1 := congrArg (Polynomial.eval v₀) hp
    simp only [Polynomial.eval_mul] at h1
    exact h1
  rw [eval_eq_coordsV hn hbn hη F₁, eval_eq_coordsV hn hbn hη' F₂, eval_eq_coordsV hn hbn hη' F₁,
    eval_eq_coordsV hn hbn hη F₂, Finset.sum_mul_sum, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  linear_combination (η ^ i * η' ^ j) * hminor i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)

/-! ## 3. 第 1 步：一般形状的母函数 -/

/-- 论文定理 6.3 中的表示：对 `k ≥ k₀`，`f(k) = Σ_{s ≥ s₀} A(s)·C(k+c−αs, βs+d)`（二项式按 `binomZ` 的约定；对每个
`k` 只有有限个 `s` 的项非零，`∑ᶠ` 就是这个有限和）。 -/
def ShapeRep (f : ℕ → ℂ) (α β : ℕ) : Prop :=
  ∃ (c d s₀ : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
    f k = ∑ᶠ s : ℤ, if s₀ ≤ s then A s * (binomZ (k + c - α * s) (β * s + d) : ℂ) else 0

/-- `(1−x)^{−h−1} v^t = Σ_N C(N − nt + h + βt, h + βt) x^N`（`N ≥ nt`）。 -/
theorem coeff_mk_one_pow_mul_vS_pow (n β h t N : ℕ) :
    PowerSeries.coeff N (PowerSeries.mk 1 ^ (h + 1) * vS n β ^ t) =
      if n * t ≤ N then ((N - n * t + (h + β * t)).choose (h + β * t) : ℂ) else 0 := by
  have e : PowerSeries.mk (1 : ℕ → ℂ) ^ (h + 1) * vS n β ^ t =
      PowerSeries.X ^ (n * t) * PowerSeries.mk 1 ^ (h + β * t + 1) := by
    rw [vS, mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [e, PowerSeries.coeff_X_pow_mul', PowerSeries.mk_one_pow_eq_mk_choose_add]
  split_ifs with hle
  · rw [PowerSeries.coeff_mk, add_comm (h + β * t)]
  · rfl

/-- `(1−x)^{−h−1} ã(v)` 的 `x^N` 系数是 `Σ_t a_t C(N − nt + h + βt, h + βt)`。 -/
theorem coeff_mk_one_pow_mul_substV {n : ℕ} (hn : 1 ≤ n) (β h : ℕ) (a : ℕ → ℂ) (N : ℕ) :
    PowerSeries.coeff N (PowerSeries.mk 1 ^ (h + 1) * substV hn β (PowerSeries.mk a)) =
      ∑ t ∈ Finset.range (N + 1),
        a t * (if n * t ≤ N then ((N - n * t + (h + β * t)).choose (h + β * t) : ℂ) else 0) := by
  obtain ⟨R, hR⟩ : PowerSeries.X ^ (N + 1) ∣
      PowerSeries.mk a - (PowerSeries.trunc (N + 1) (PowerSeries.mk a) : PowerSeries ℂ) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [map_sub, PowerSeries.coeff_coe_trunc_of_lt hj, sub_self]
  have hsplit : PowerSeries.mk a =
      (PowerSeries.trunc (N + 1) (PowerSeries.mk a) : PowerSeries ℂ) + PowerSeries.X ^ (N + 1) * R := by
    rw [← hR]
    ring
  have htail : PowerSeries.coeff N (PowerSeries.mk 1 ^ (h + 1) * (vS n β ^ (N + 1) * substV hn β R)) = 0 := by
    have e : PowerSeries.mk (1 : ℕ → ℂ) ^ (h + 1) * (vS n β ^ (N + 1) * substV hn β R) =
        PowerSeries.X ^ (n * (N + 1)) *
          (PowerSeries.mk 1 ^ (h + 1) * PowerSeries.mk 1 ^ (β * (N + 1)) * substV hn β R) := by
      rw [vS, mul_pow, ← pow_mul, ← pow_mul]
      ring
    have hle := Nat.mul_le_mul_right (N + 1) hn
    rw [e, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  rw [hsplit, map_add (substV hn β), map_mul (substV hn β), map_pow (substV hn β), substV_X, mul_add, map_add,
    htail, add_zero, substV_coe, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [PowerSeries.coeff_mk, ← mul_assoc, mul_comm (PowerSeries.mk 1 ^ (h + 1)), mul_assoc, ← Algebra.smul_def,
    PowerSeries.coeff_smul, smul_eq_mul, coeff_mk_one_pow_mul_vS_pow]

/-- `binomZ(N + h − αt, h + βt) = [nt ≤ N]·C(N − nt + h + βt, h + βt)`（`n = α + β`）。 -/
theorem binomZ_shape (N h α β t : ℕ) :
    binomZ ((N : ℤ) + h - α * t) ((h : ℤ) + β * t) =
      if (α + β) * t ≤ N then (N - (α + β) * t + (h + β * t)).choose (h + β * t) else 0 := by
  have e1 : ((α : ℤ) * t) = ((α * t : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((β : ℤ) * t) = ((β * t : ℕ) : ℤ) := by push_cast; ring
  have e3 : (α + β) * t = α * t + β * t := by ring
  rw [e1, e2, e3]
  generalize α * t = A' at *
  generalize β * t = B' at *
  unfold binomZ
  by_cases hle : A' + B' ≤ N
  · rw [ite_eq_left (show (0 : ℤ) ≤ (h : ℤ) + (B' : ℤ) ∧ (h : ℤ) + (B' : ℤ) ≤ (N : ℤ) + h - (A' : ℤ) by omega),
      ite_eq_left hle]
    congr 1
    all_goals omega
  · rw [ite_eq_right (show ¬ ((0 : ℤ) ≤ (h : ℤ) + (B' : ℤ) ∧ (h : ℤ) + (B' : ℤ) ≤ (N : ℤ) + h - (A' : ℤ)) by omega),
      ite_eq_right hle]

/-- 第 1 步：若 `f` 有形状 `(α, β)` 的表示，则要么 `f` 最终为 0，要么
`x^{K₁}F − x^{K₂}(1−x)^{−h−1}ã(v)` 是多项式（`F = Σ_k f(k)x^k`）。 -/
theorem shape_gf {f : ℕ → ℂ} {α β : ℕ} (hn : 1 ≤ α + β) (hrep : ShapeRep f α β) :
    (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → f k = 0) ∨
    ∃ (K₁ K₂ h₀ : ℕ) (a : ℕ → ℂ) (E : ℂ[X]),
      PowerSeries.X ^ K₁ * PowerSeries.mk f -
        PowerSeries.X ^ K₂ * (PowerSeries.mk 1 ^ (h₀ + 1) * substV hn β (PowerSeries.mk a)) =
          (E : PowerSeries ℂ) := by
  classical
  obtain ⟨c, d, s₀, k₀, A, hA⟩ := hrep
  by_cases hex : ∃ t : ℕ, 0 ≤ (β : ℤ) * (s₀ + t) + d
  swap
  · -- 每一项都是 0（`β = 0` 且 `d < 0`）
    left
    refine ⟨k₀, fun k hk => ?_⟩
    rw [hA k hk]
    refine finsum_eq_zero_of_forall_eq_zero fun s => ?_
    split_ifs with hs
    · have hneg : (β : ℤ) * s + d < 0 := by
        by_contra hge
        refine hex ⟨(s - s₀).toNat, ?_⟩
        rw [show (s₀ : ℤ) + ((s - s₀).toNat : ℕ) = s by omega]
        omega
      unfold binomZ
      rw [ite_eq_right (by omega), Nat.cast_zero, mul_zero]
    · rfl
  right
  -- `s₁ = s₀ + t₁` 是使 `βs + d ≥ 0` 的最小的 `s ≥ s₀`
  have ht₁spec : 0 ≤ (β : ℤ) * (s₀ + (Nat.find hex : ℕ)) + d := Nat.find_spec hex
  have ht₁min : ∀ t < Nat.find hex, (β : ℤ) * (s₀ + t) + d < 0 := fun t ht => not_le.1 (Nat.find_min hex ht)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : ℤ, s₁ = s₀ + (Nat.find hex : ℕ) := ⟨_, rfl⟩
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ℕ, (h₀ : ℤ) = β * s₁ + d := ⟨((β : ℤ) * s₁ + d).toNat, by rw [hs₁]; omega⟩
  obtain ⟨g, hg⟩ : ∃ g : ℤ, g = (α : ℤ) * s₁ + β * s₁ + d - c := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, ∀ t, a t = A (s₁ + t) := ⟨_, fun _ => rfl⟩
  have hcoef : ∀ k : ℕ, k₀ ≤ k → 0 ≤ (k : ℤ) - g →
      f k = PowerSeries.coeff ((k : ℤ) - g).toNat
        (PowerSeries.mk 1 ^ (h₀ + 1) * substV hn β (PowerSeries.mk a)) := by
    intro k hk hkg
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = k - g := ⟨((k : ℤ) - g).toNat, by omega⟩
    rw [show ((k : ℤ) - g).toNat = N by omega, hA k hk, coeff_mk_one_pow_mul_substV]
    rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (N + 1)).map
      ⟨fun t : ℕ => s₁ + t, fun x y hxy => by simpa using hxy⟩) ?_]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun t _ => ?_
      show (if s₀ ≤ s₁ + t then A (s₁ + t) *
          (binomZ ((k : ℤ) + c - α * (s₁ + t)) (β * (s₁ + t) + d) : ℂ) else 0) =
        a t * (if (α + β) * t ≤ N then ((N - (α + β) * t + (h₀ + β * t)).choose (h₀ + β * t) : ℂ) else 0)
      have e1 : (k : ℤ) + c - α * (s₁ + t) = (N : ℤ) + h₀ - α * t := by
        have : (α : ℤ) * (s₁ + t) = α * s₁ + α * t := by ring
        omega
      have e2 : (β : ℤ) * (s₁ + t) + d = (h₀ : ℤ) + β * t := by
        have : (β : ℤ) * (s₁ + t) = β * s₁ + β * t := by ring
        omega
      rw [ite_eq_left (by omega), e1, e2, binomZ_shape, Nat.cast_ite, Nat.cast_zero, ha t]
    · intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      have hs0 : s₀ ≤ s := by
        by_contra hlt
        exact hs (by rw [ite_eq_right hlt])
      rw [ite_eq_left hs0] at hs
      have hb : binomZ ((k : ℤ) + c - α * s) (β * s + d) ≠ 0 := by
        intro h0
        apply hs
        rw [h0, Nat.cast_zero, mul_zero]
      unfold binomZ at hb
      have hcond : 0 ≤ (β : ℤ) * s + d ∧ (β : ℤ) * s + d ≤ (k : ℤ) + c - α * s := by
        by_contra hc
        exact hb (ite_eq_right hc)
      -- `s ≥ s₁`（`t₁` 的最小性）
      have hs1 : s₁ ≤ s := by
        by_contra hlt
        have := ht₁min (s - s₀).toNat (by omega)
        rw [show (s₀ : ℤ) + ((s - s₀).toNat : ℕ) = s by omega] at this
        omega
      -- `s − s₁ ≤ N`
      have hsN : s - s₁ ≤ N := by
        have e : ((α : ℤ) + β) * (s - s₁) = (α * s + β * s) - (α * s₁ + β * s₁) := by ring
        have hpos : (s - s₁) ≤ ((α : ℤ) + β) * (s - s₁) := by
          have : (1 : ℤ) ≤ (α : ℤ) + β := by exact_mod_cast hn
          nlinarith
        omega
      rw [Finset.mem_coe, Finset.mem_map]
      refine ⟨(s - s₁).toNat, Finset.mem_range.2 (by omega), ?_⟩
      show s₁ + (((s - s₁).toNat : ℕ) : ℤ) = s
      omega
  -- 两边的系数在 `j` 足够大时相同
  obtain ⟨K₁, K₂, hK⟩ : ∃ K₁ K₂ : ℕ, (K₂ : ℤ) - K₁ = g := ⟨(-g).toNat, g.toNat, by omega⟩
  refine ⟨K₁, K₂, h₀, a, PowerSeries.trunc (k₀ + K₁ + K₂)
    (PowerSeries.X ^ K₁ * PowerSeries.mk f -
      PowerSeries.X ^ K₂ * (PowerSeries.mk 1 ^ (h₀ + 1) * substV hn β (PowerSeries.mk a))), ?_⟩
  ext j
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hj
  · rfl
  · rw [map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
      ite_eq_left (by omega), PowerSeries.coeff_mk, hcoef (j - K₁) (by omega) (by omega),
      show (((j - K₁ : ℕ) : ℤ) - g).toNat = j - K₂ by omega, sub_self]

/-! ## 4. 第 3 步：纤维 -/

theorem U_pos (k m : ℕ) : 0 < U k m := by
  unfold U
  exact Finset.card_pos.2 ⟨List.replicate k 0, mem_L.2 ⟨by simp, by simp, legal_replicate k⟩⟩

theorem aeval_PX_eq_coe (F : ℂ[X]) :
    Polynomial.aeval (PowerSeries.X : PowerSeries ℂ) F = (F : PowerSeries ℂ) := by
  rw [Polynomial.aeval_def, ← Polynomial.eval₂_C_X_eq_coe]
  have : algebraMap ℂ (PowerSeries ℂ) = PowerSeries.C := by
    ext c n
    simp
  rw [this]

theorem Ppoly_eval_root_b1 {m : ℕ} (hm : 1 ≤ m) {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) : (Ppoly ℂ m).eval ξ = 0 := by
  rw [Ppoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (i := 1) (Finset.mem_range.2 (by omega)) (eval_bpoly_one hξ)

/-- `P_m·(1−x)^{h+1}` 乘第 1 步的恒等式：`(1−x)^{h+1}(x^{K₁}W_m − P_m E) = x^{K₂}P_m·ã(v)`。 -/
theorem shape_main_identity {m α β : ℕ} (hn : 1 ≤ α + β) {K₁ K₂ h₀ : ℕ} {a : ℕ → ℂ} {E : ℂ[X]}
    (hE : PowerSeries.X ^ K₁ * PowerSeries.mk (fun k => (U k m : ℂ)) -
        PowerSeries.X ^ K₂ * (PowerSeries.mk 1 ^ (h₀ + 1) * substV hn β (PowerSeries.mk a)) =
          (E : PowerSeries ℂ)) :
    (((1 - Polynomial.X) ^ (h₀ + 1) * (Polynomial.X ^ K₁ * Wpoly ℂ m - Ppoly ℂ m * E) : ℂ[X]) : PowerSeries ℂ) =
      ((Polynomial.X ^ K₂ * Ppoly ℂ m : ℂ[X]) : PowerSeries ℂ) * substV hn β (PowerSeries.mk a) := by
  have hPG := P_mul_Gc m
  have hmk : PowerSeries.mk (1 : ℕ → ℂ) ^ (h₀ + 1) * (1 - PowerSeries.X) ^ (h₀ + 1) = 1 := by
    rw [← mul_pow, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow]
  have hG : PowerSeries.mk (fun k => (U k m : ℂ)) = Gc m := rfl
  rw [hG] at hE
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_one]
  linear_combination (-(1 - PowerSeries.X) ^ (h₀ + 1) * PowerSeries.X ^ K₁) * hPG +
    ((Ppoly ℂ m : PowerSeries ℂ) * PowerSeries.X ^ K₂ * substV hn β (PowerSeries.mk a)) * hmk +
    ((1 - PowerSeries.X) ^ (h₀ + 1) * (Ppoly ℂ m : PowerSeries ℂ)) * hE

theorem ne_zero_of_root_b1 {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) : ξ ≠ 0 ∧ 1 - ξ ≠ 0 ∧ 1 + ξ ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at hξ; norm_num at hξ
  · rw [show ξ = 1 by linear_combination -h] at hξ; norm_num at hξ
  · rw [show ξ = -1 by linear_combination h] at hξ; norm_num at hξ

/-- 第 3 步（`α ≥ 1`）：`U_k(m)` 有形状 `(α, β)` 的表示时，对 `b_1` 的根 `ξ`，纤维
`η^{α+β}(1−ξ)^β = ξ^{α+β}(1−η)^β` 上每个 `η ≠ 0` 都是 `P_m` 的根。 -/
theorem shape_fibre_x {m α β : ℕ} (hm : 1 ≤ m) (hα : 1 ≤ α) (hrep : ShapeRep (fun k => (U k m : ℂ)) α β)
    {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) {η : ℂ} (hη0 : η ≠ 0)
    (hη : η ^ (α + β) * (1 - ξ) ^ β = ξ ^ (α + β) * (1 - η) ^ β) :
    (Ppoly ℂ m).eval η = 0 := by
  have hn : 1 ≤ α + β := by omega
  obtain ⟨hξ0, h1ξ, h1ξ'⟩ := ne_zero_of_root_b1 hξ
  rcases shape_gf hn hrep with ⟨k₀, hk₀⟩ | ⟨K₁, K₂, h₀, a, E, hE⟩
  · have h := hk₀ k₀ le_rfl
    have hpos := U_pos k₀ m
    simp only [Nat.cast_eq_zero] at h
    omega
  have hmain := shape_main_identity hn hE
  have hz : (PowerSeries.X * 1) ^ (α + β) = vS (α + β) β * (1 - PowerSeries.X * 1) ^ β := by
    rw [mul_one, vS_mul_one_sub_pow]
  have hξfib : ξ ^ (α + β) = ξ ^ (α + β) / (1 - ξ) ^ β * (1 - ξ) ^ β := by
    rw [div_mul_cancel₀ _ (pow_ne_zero _ h1ξ)]
  have hηfib : η ^ (α + β) = ξ ^ (α + β) / (1 - ξ) ^ β * (1 - η) ^ β := by
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ h1ξ)]
    exact hη
  have hcross := cross_of_eq hn (b := β) (by omega) β (w := 1) (by simp) hz
    (F₁ := (1 - Polynomial.X) ^ (h₀ + 1) * (Polynomial.X ^ K₁ * Wpoly ℂ m - Ppoly ℂ m * E))
    (F₂ := Polynomial.X ^ K₂ * Ppoly ℂ m) (f := PowerSeries.mk a)
    (by rw [mul_one, aeval_PX_eq_coe, aeval_PX_eq_coe]; exact hmain) hξfib hηfib
  have hP0 := Ppoly_eval_root_b1 hm hξ
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, hP0, mul_zero, zero_mul, sub_zero, eval_Wpoly_root hm hξ] at hcross
  have hF1 : (1 - ξ) ^ (h₀ + 1) * (ξ ^ K₁ * (ξ + ξ ^ 2)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ h1ξ) (mul_ne_zero (pow_ne_zero _ hξ0) ?_)
    rw [show ξ + ξ ^ 2 = ξ * (1 + ξ) by ring]
    exact mul_ne_zero hξ0 h1ξ'
  have h2 : η ^ K₂ * (Ppoly ℂ m).eval η = 0 := by
    rcases mul_eq_zero.1 hcross with h | h
    · exact absurd h hF1
    · exact h
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h (pow_ne_zero _ hη0)
  · exact h

/-- `F(x)` 写成 `y = x/(1−x)` 的多项式：`(1+y)^D·F(y/(1+y)) = Σ_{j≤D} f_j y^j (1+y)^{D−j}`。 -/
def homogY (D : ℕ) (F : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (D + 1), Polynomial.C (F.coeff j) * Polynomial.X ^ j * (1 + Polynomial.X) ^ (D - j)

theorem one_add_y : (1 : PowerSeries ℂ) + PowerSeries.X * PowerSeries.mk 1 = PowerSeries.mk 1 := by
  have := PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  linear_combination -this

theorem aeval_homogY {D : ℕ} {F : ℂ[X]} (hD : F.natDegree ≤ D) :
    Polynomial.aeval (PowerSeries.X * PowerSeries.mk 1) (homogY D F) =
      PowerSeries.mk 1 ^ D * (F : PowerSeries ℂ) := by
  have hF : (F : PowerSeries ℂ) = ∑ j ∈ Finset.range (D + 1),
      PowerSeries.C (F.coeff j) * PowerSeries.X ^ j := by
    have e2 : F = ∑ j ∈ Finset.range (D + 1), Polynomial.C (F.coeff j) * Polynomial.X ^ j := by
      conv_lhs => rw [Polynomial.as_sum_range' F (D + 1) (by omega)]
      exact Finset.sum_congr rfl fun j _ => Polynomial.C_mul_X_pow_eq_monomial.symm
    calc (F : PowerSeries ℂ) = Polynomial.coeToPowerSeries.ringHom
          (∑ j ∈ Finset.range (D + 1), Polynomial.C (F.coeff j) * Polynomial.X ^ j) := by
            rw [← e2]
            rfl
      _ = ∑ j ∈ Finset.range (D + 1), PowerSeries.C (F.coeff j) * PowerSeries.X ^ j := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            change ((Polynomial.C (F.coeff j) * Polynomial.X ^ j : ℂ[X]) : PowerSeries ℂ) = _
            rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hF, homogY, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_add, map_one, one_add_y,
    PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [show PowerSeries.mk (1 : ℕ → ℂ) ^ D = PowerSeries.mk 1 ^ j * PowerSeries.mk 1 ^ (D - j) by
    rw [← pow_add, Nat.add_sub_cancel' hjD]]
  ring

theorem eval_homogY {D : ℕ} {F : ℂ[X]} (hD : F.natDegree ≤ D) {η : ℂ} (h1 : 1 + η ≠ 0) :
    (homogY D F).eval η = (1 + η) ^ D * F.eval (η / (1 + η)) := by
  rw [homogY, Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (p := F) (n := D + 1) (by omega),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one]
  rw [show (1 + η) ^ D = (1 + η) ^ j * (1 + η) ^ (D - j) by rw [← pow_add, Nat.add_sub_cancel' hjD], div_pow]
  field_simp

/-- 第 3 步（`α = 0`）：`U_k(m)` 有形状 `(0, β)` 的表示时，对 `b_1` 的根 `ξ`，`y^β(1−ξ)^β = ξ^β`（`y ≠ 0`，
`1 + y ≠ 0`）的每个 `y` 给出 `P_m` 的根 `y/(1+y)`。 -/
theorem shape_fibre_y {m β : ℕ} (hm : 1 ≤ m) (hβ : 1 ≤ β) (hrep : ShapeRep (fun k => (U k m : ℂ)) 0 β)
    {ξ : ℂ} (hξ : ξ ^ 3 + ξ - 1 = 0) {y : ℂ} (hy0 : y ≠ 0) (hy1 : 1 + y ≠ 0)
    (hy : y ^ β * (1 - ξ) ^ β = ξ ^ β) :
    (Ppoly ℂ m).eval (y / (1 + y)) = 0 := by
  have hn : 1 ≤ 0 + β := by omega
  obtain ⟨hξ0, h1ξ, h1ξ'⟩ := ne_zero_of_root_b1 hξ
  rcases shape_gf hn hrep with ⟨k₀, hk₀⟩ | ⟨K₁, K₂, h₀, a, E, hE⟩
  · have h := hk₀ k₀ le_rfl
    have hpos := U_pos k₀ m
    simp only [Nat.cast_eq_zero] at h
    omega
  have hmain := shape_main_identity hn hE
  obtain ⟨F₁, hF₁⟩ : ∃ F : ℂ[X], F = (1 - Polynomial.X) ^ (h₀ + 1) * (Polynomial.X ^ K₁ * Wpoly ℂ m - Ppoly ℂ m * E) :=
    ⟨_, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F : ℂ[X], F = Polynomial.X ^ K₂ * Ppoly ℂ m := ⟨_, rfl⟩
  rw [← hF₁, ← hF₂] at hmain
  obtain ⟨D, hD1, hD2⟩ : ∃ D, F₁.natDegree ≤ D ∧ F₂.natDegree ≤ D :=
    ⟨max F₁.natDegree F₂.natDegree, le_max_left _ _, le_max_right _ _⟩
  have hz : (PowerSeries.X * PowerSeries.mk 1) ^ (0 + β) = vS (0 + β) β * (1 - PowerSeries.X * PowerSeries.mk 1) ^ 0 := by
    rw [pow_zero, mul_one, vS, zero_add, mul_pow]
  -- `η = ξ/(1−ξ)` 对应 `ξ`
  obtain ⟨η, hη⟩ : ∃ η : ℂ, η = ξ / (1 - ξ) := ⟨_, rfl⟩
  have hηmul : η * (1 - ξ) = ξ := by rw [hη, div_mul_cancel₀ _ h1ξ]
  have h1η : 1 + η ≠ 0 := by
    intro h
    have e : (1 + η) * (1 - ξ) = 1 := by linear_combination hηmul
    rw [h, zero_mul] at e
    exact zero_ne_one e
  have hηξ : η / (1 + η) = ξ := by
    rw [div_eq_iff h1η]
    linear_combination hηmul
  have hηfib : η ^ (0 + β) = η ^ β * (1 - η) ^ 0 := by rw [zero_add, pow_zero, mul_one]
  have hyfib : y ^ (0 + β) = η ^ β * (1 - y) ^ 0 := by
    rw [zero_add, pow_zero, mul_one, hη, div_pow, eq_div_iff (pow_ne_zero _ h1ξ)]
    exact hy
  have hcross := cross_of_eq hn (b := 0) (by omega) β (w := PowerSeries.mk 1) (by simp) hz
    (F₁ := homogY D F₁) (F₂ := homogY D F₂) (f := PowerSeries.mk a)
    (by rw [aeval_homogY hD1, aeval_homogY hD2, hmain]; ring) hηfib hyfib
  rw [eval_homogY hD1 h1η, eval_homogY hD2 hy1, eval_homogY hD1 hy1, eval_homogY hD2 h1η, hηξ] at hcross
  have hF2ξ : F₂.eval ξ = 0 := by
    rw [hF₂, Polynomial.eval_mul, Ppoly_eval_root_b1 hm hξ, mul_zero]
  have hF1ξ : F₁.eval ξ ≠ 0 := by
    rw [hF₁]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Ppoly_eval_root_b1 hm hξ, zero_mul, sub_zero, eval_Wpoly_root hm hξ]
    refine mul_ne_zero (pow_ne_zero _ h1ξ) (mul_ne_zero (pow_ne_zero _ hξ0) ?_)
    rw [show ξ + ξ ^ 2 = ξ * (1 + ξ) by ring]
    exact mul_ne_zero hξ0 h1ξ'
  rw [hF2ξ, mul_zero, mul_zero] at hcross
  have h2 : F₂.eval (y / (1 + y)) = 0 := by
    have hA : (1 + η) ^ D * F₁.eval ξ ≠ 0 := mul_ne_zero (pow_ne_zero _ h1η) hF1ξ
    rcases mul_eq_zero.1 hcross with h | h
    · exact absurd h hA
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (pow_ne_zero _ hy1)
      · exact h
  rw [hF₂, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h (pow_ne_zero _ (div_ne_zero hy0 hy1))
  · exact h

end

end A207123
