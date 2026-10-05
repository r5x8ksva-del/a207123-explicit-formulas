import A207123.NonDFinite

/-!
# 报告 T3.7(1) 的最后一步：`F` 不是 D-finite

`NonDFinite.lean` 已经证明了 T3.7(1) 的 ODE 部分（`no_x_ODE_poly`）：不存在不全为 0 的
`p_0, …, p_r ∈ ℂ[x,t]` 使 `Σ_j p_j·∂_x^j F = 0`。本文件形式化报告接下来的一步「所以 `F` 不是
D-finite」：给出 D-finite 的定义，证明引理 D1，并推出 `F` 在任何系数域 `K ⊆ ℂ` 上都不是 D-finite。

## 定义（`notes/c3b.md` §4，即 Lipshitz 1989 Def. 2.1，取 `n = 2`，变量为 `x, t`）

c3b §4 的原文：`f ∈ K[[x_1..x_n]]` 称为 D-finite，若 `f` 的全部偏导数在 `Frac(K[[x]])` 中张成的
`K(x_1..x_n)`-向量空间有限维。对应的 Lean 定义：

* `PS2 K = K[[x]][[t]]`：二元形式幂级数环 `K[[x,t]]`，以 `t` 为外层变量（与 `Fxt` 的写法一致；
  `K[[x]][[t]]` 与 `K[[x,t]]` 典范同构，这是标准事实，本文件不形式化）。它是整环，
  `Frac(K[[x,t]])` 写成 `FractionRing (PS2 K)`。外围域按 c3b 原文取 `Frac(K[[x,t]])`；任何包含
  `K[[x,t]]` 的域都含有它的一个拷贝，而这些元素在 `K(x,t)` 上是否线性相关与外围域的选取无关。
* `dXK K`（`∂_x`）：对每个 `t^m` 系数求 `x` 导数；`dTK K`（`∂_t`）：外层变量 `t` 的形式导数。
  两者可交换（`dXK_dTK_comm`），所以 `∂_x^i ∂_t^j f`（`i, j ≥ 0`）就是 `f` 的全部偏导数。
* `polyToPS2 K : K[x,t] →+* K[[x,t]]`：多项式环（写成 `Polynomial (Polynomial K)`，外层变量 `t`、
  内层变量 `x`）到幂级数环的标准嵌入，单射（`polyToPS2_injective`）。
* `ratFn K`：`Frac(K[[x,t]])` 中由 `K[x,t]` 的像生成的子域，这就是 `K(x,t)`：
  `mem_ratFn_iff` 说明它恰由「多项式 / 非零多项式」组成，`isFractionRing_ratFn` 说明它是
  `K[x,t]` 的分式域（`IsFractionRing`）。
* `IsDFinite K f`：全部偏导数 `∂_x^i ∂_t^j f` 在 `Frac(K[[x,t]])` 中张成的 `K(x,t)`-子空间有限维。
  这个谓词不是恒假的：常数 `1` 满足它（`isDFinite_one`），所以主定理不是空洞的。
* `FK K = Σ_{k,m} U_k(m)·x^k·t^m ∈ K[[x,t]]`；`FK ℂ` 就是 `NonDFinite.lean` 中的 `Fxt`
  （`FK_complex_eq_Fxt`，定义上相等）。

Lipshitz 假定 `K` 的特征为 0；本文件的定义对任意域 `K` 都有意义，主定理只对 `K ⊆ ℂ`（带一个
环同态 `σ : K →+* ℂ`）陈述，此时特征自动为 0。

## 结论

* `exists_x_ODE_of_isDFinite`（引理 D1，`x` 方向）：`f` D-finite ⇒ 存在不全为 0 的
  `p_0, …, p_r ∈ K[x,t]` 使 `Σ_j p_j·∂_x^j f = 0`；`exists_t_ODE_of_isDFinite` 是 `t` 方向。
* `not_isDFinite_FK`（T3.7(1)）：对任何域 `K` 与 `σ : K →+* ℂ`，`F` 在 `K` 上不是 D-finite。
* `not_isDFinite_F`、`not_isDFinite_Fxt`：`K = ℂ` 的情形。

## 证明路线

* 引理 D1（`exists_poly_relation`）：设张成的空间 `V` 的维数为 `d`，则 `f, ∂_x f, …, ∂_x^d f`
  这 `d + 1` 个向量线性相关（`LinearIndependent.fintype_card_le_finrank`），得到不全为 0 的
  `g_j ∈ K(x,t)` 使 `Σ_j g_j·∂_x^j f = 0`。由 `Subfield.mem_closure_iff`，每个
  `g_j = φ(a_j)/φ(b_j)`（`φ : K[x,t] → Frac(K[[x,t]])`，`φ(b_j) ≠ 0`，
  `exists_eq_div_of_mem_ratFn`）。乘以公分母 `φ(∏_i b_i)`：`p_j = a_j·∏_{i≠j} b_i`，再沿单射
  `K[[x,t]] → Frac(K[[x,t]])` 拉回。`g_{j0} ≠ 0` ⇒ `a_{j0} ≠ 0`，`K[x,t]` 是整环 ⇒ `p_{j0} ≠ 0`。
* 主定理：用 `σ` 逐系数把 `K[[x,t]]` 映到 `ℂ[[x,t]]`（`mapPS2`），它与乘法、`∂_x`、`polyToPS2`
  交换，并把 `FK K` 映成 `FK ℂ = Fxt`；`σ` 单射，所以映射后的多项式系数仍不全为 0，与
  `no_x_ODE_poly` 矛盾。
-/

open Finset

namespace A207123

/-! ### 定义 -/

section Defs

variable (K : Type*) [Field K]

/-- 二元形式幂级数环 `K[[x,t]]`，写成 `K[[x]][[t]]`（以 `t` 为外层变量，与 `Fxt` 一致）。 -/
abbrev PS2 := PowerSeries (PowerSeries K)

/-- `∂_x`：对每个 `t^m` 系数求 `x` 导数（`ℂ` 上就是 `NonDFinite.lean` 的 `dX`）。 -/
noncomputable def dXK (f : PS2 K) : PS2 K :=
  PowerSeries.mk fun m => PowerSeries.derivative (R := K) (PowerSeries.coeff m f)

/-- `∂_t`：外层变量 `t` 的形式导数。 -/
noncomputable def dTK (f : PS2 K) : PS2 K := PowerSeries.derivative (R := PowerSeries K) f

/-- 标准嵌入 `K[x,t] → K[[x,t]]`。`K[x,t]` 写成 `Polynomial (Polynomial K)`（外层变量 `t`、内层
变量 `x`）：先把外层多项式看成 `t` 的幂级数，再把每个系数（`x` 的多项式）看成 `x` 的幂级数。 -/
noncomputable def polyToPS2 : Polynomial (Polynomial K) →+* PS2 K :=
  (PowerSeries.map (Polynomial.coeToPowerSeries.ringHom (R := K))).comp
    (Polynomial.coeToPowerSeries.ringHom (R := Polynomial K))

/-- `K(x,t)`：`Frac(K[[x,t]])` 中由 `K[x,t]` 的像生成的子域（见 `mem_ratFn_iff`、
`isFractionRing_ratFn`）。 -/
noncomputable def ratFn : Subfield (FractionRing (PS2 K)) :=
  Subfield.closure
    (Set.range fun p => algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K p))

/-- Lipshitz 1989 Def. 2.1（`notes/c3b.md` §4，`n = 2`）意义下的 D-finite：`f` 的全部偏导数
`∂_x^i ∂_t^j f`（`i, j ≥ 0`）在 `Frac(K[[x,t]])` 中张成的 `K(x,t)`-向量空间有限维。 -/
def IsDFinite (f : PS2 K) : Prop :=
  FiniteDimensional (ratFn K) (Submodule.span (ratFn K) (Set.range fun ij : ℕ × ℕ =>
    algebraMap (PS2 K) (FractionRing (PS2 K)) ((dXK K)^[ij.1] ((dTK K)^[ij.2] f))))

/-- `F(x,t) = Σ_{k,m} U_k(m)·x^k·t^m`，系数取在域 `K` 中（`[t^m]F = G_m(x)`）。 -/
noncomputable def FK : PS2 K := PowerSeries.mk fun m => PowerSeries.mk fun k => (U k m : K)

end Defs

/-! ### 定义的忠实性：`∂_x ∂_t = ∂_t ∂_x`，`ratFn K` 就是 `K(x,t)` -/

section Faithful

variable (K : Type*) [Field K]

/-- 辅助引理（T3.7(1)）：`∂_x` 与 `∂_t` 可交换，所以 `∂_x^i ∂_t^j f` 穷尽 `f` 的全部偏导数。 -/
theorem dXK_dTK_comm (f : PS2 K) : dXK K (dTK K f) = dTK K (dXK K f) := by
  ext m n
  simp [dXK, dTK, PowerSeries.coeff_derivative, mul_add]
  ring

/-- 辅助引理（T3.7(1)）：标准嵌入 `K[x,t] → K[[x,t]]` 是单射。 -/
theorem polyToPS2_injective : Function.Injective (polyToPS2 K) := by
  intro p q h
  have h' : PowerSeries.map (Polynomial.coeToPowerSeries.ringHom (R := K))
        (p : PowerSeries (Polynomial K)) =
      PowerSeries.map (Polynomial.coeToPowerSeries.ringHom (R := K))
        (q : PowerSeries (Polynomial K)) := h
  exact Polynomial.coe_injective _ (PowerSeries.map_injective
    (Polynomial.coeToPowerSeries.ringHom (R := K)) (Polynomial.coe_injective K) h')

variable {K}

/-- 辅助引理（T3.7(1)）：`K(x,t)` 的元素都是两个多项式像之商，且分母的像非零。 -/
theorem exists_eq_div_of_mem_ratFn {g : FractionRing (PS2 K)} (hg : g ∈ ratFn K) :
    ∃ a b : Polynomial (Polynomial K),
      algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K b) ≠ 0 ∧
      g = algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K a) /
        algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K b) := by
  set φ : Polynomial (Polynomial K) →+* FractionRing (PS2 K) :=
    (algebraMap (PS2 K) (FractionRing (PS2 K))).comp (polyToPS2 K)
  -- `K[x,t]` 的像本身是子环，所以它生成的子环就是它自己
  have hle : Subring.closure
      (Set.range fun p => algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K p)) ≤
      φ.range := by
    rw [Subring.closure_le]
    rintro _ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.mp hg
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp (hle hy)
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp (hle hz)
  by_cases hb : φ b = 0
  · -- 分母为 0 时 `g = 0 = 0 / 1`
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    · rw [← hyz, hb, div_zero]
      simp
  · exact ⟨a, b, hb, hyz.symm⟩

/-- 辅助引理（T3.7(1)）：`ratFn K` 恰由「`K[x,t]` 的元素 / `K[x,t]` 的非零元素」组成，即 `K(x,t)`。 -/
theorem mem_ratFn_iff {g : FractionRing (PS2 K)} :
    g ∈ ratFn K ↔ ∃ a b : Polynomial (Polynomial K), b ≠ 0 ∧
      g = algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K a) /
        algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K b) := by
  constructor
  · intro hg
    obtain ⟨a, b, hb, hab⟩ := exists_eq_div_of_mem_ratFn hg
    exact ⟨a, b, fun h => hb (by rw [h, map_zero, map_zero]), hab⟩
  · rintro ⟨a, b, -, rfl⟩
    exact div_mem (Subfield.subset_closure ⟨a, rfl⟩) (Subfield.subset_closure ⟨b, rfl⟩)

variable (K)

/-- 辅助定义（T3.7(1)）：`K[x,t] → K(x,t)`（`polyToPS2` 的像落在 `ratFn K` 中）。 -/
noncomputable def polyToRatFn : Polynomial (Polynomial K) →+* ratFn K :=
  ((algebraMap (PS2 K) (FractionRing (PS2 K))).comp (polyToPS2 K)).codRestrict (ratFn K)
    fun p => Subfield.subset_closure ⟨p, rfl⟩

/-- 辅助引理（T3.7(1)）：`K[x,t] → K(x,t)` 是单射。 -/
theorem polyToRatFn_injective : Function.Injective (polyToRatFn K) := fun _ _ h =>
  polyToPS2_injective K
    (IsFractionRing.injective (PS2 K) (FractionRing (PS2 K)) (congrArg Subtype.val h))

/-- 辅助引理（T3.7(1)）：`ratFn K` 是 `K[x,t]` 的分式域，即 `ratFn K ≅ K(x,t)`。 -/
theorem isFractionRing_ratFn :
    letI := (polyToRatFn K).toAlgebra
    IsFractionRing (Polynomial (Polynomial K)) (ratFn K) := by
  let := (polyToRatFn K).toAlgebra
  have : FaithfulSMul (Polynomial (Polynomial K)) (ratFn K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (polyToRatFn_injective K)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨a, b, -, hz⟩ := mem_ratFn_iff.mp z.2
  exact ⟨a, b, Subtype.ext (by rw [Subfield.coe_div]; exact hz)⟩

/-- 辅助引理（T3.7(1)）：`∂_x 0 = 0`。 -/
theorem dXK_zero : dXK K 0 = 0 := by
  ext m n
  simp [dXK]

/-- 辅助引理（T3.7(1)）：`∂_x 1 = 0`。 -/
theorem dXK_one : dXK K 1 = 0 := by
  ext m n
  by_cases hm : m = 0 <;> simp [dXK, hm, PowerSeries.coeff_one]

/-- 辅助引理（T3.7(1)）：`∂_t 0 = 0`。 -/
theorem dTK_zero : dTK K 0 = 0 := by simp [dTK]

/-- 辅助引理（T3.7(1)）：`∂_t 1 = 0`。 -/
theorem dTK_one : dTK K 1 = 0 := by simp [dTK]

/-- 辅助引理（T3.7(1)，检查定义不是空的）：常数 `1` 是 D-finite（它的偏导数只有 `1` 和 `0`），
所以 `IsDFinite` 不是恒假的谓词，主定理不是空洞的。 -/
theorem isDFinite_one : IsDFinite K 1 := by
  have hx0 : ∀ i, (dXK K)^[i] 0 = 0 := fun i => Function.iterate_fixed (dXK_zero K) i
  have hx : ∀ i, (dXK K)^[i + 1] 1 = 0 := fun i => by
    rw [Function.iterate_succ_apply, dXK_one, hx0]
  have ht : ∀ j, (dTK K)^[j + 1] 1 = 0 := fun j => by
    rw [Function.iterate_succ_apply, dTK_one, Function.iterate_fixed (dTK_zero K)]
  unfold IsDFinite
  apply FiniteDimensional.span_of_finite
  apply (Set.toFinite ({1, 0} : Set (FractionRing (PS2 K)))).subset
  rintro _ ⟨⟨i, j⟩, rfl⟩
  have key : (dXK K)^[i] ((dTK K)^[j] 1) = 1 ∨ (dXK K)^[i] ((dTK K)^[j] 1) = 0 := by
    rcases j with _ | j
    · rcases i with _ | i
      · exact Or.inl rfl
      · exact Or.inr (hx i)
    · rw [ht j]
      exact Or.inr (hx0 i)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases key with h | h
  · left
    rw [h, map_one]
  · right
    rw [h, map_zero]

end Faithful

/-! ### 引理 D1 -/

section D1

variable {K : Type*} [Field K]

/-- 辅助引理（T3.7(1)）：`K(x,t)` 在 `Frac(K[[x,t]])` 上的数乘就是乘法。 -/
theorem smul_ratFn_eq_mul (c : ratFn K) (x : FractionRing (PS2 K)) :
    c • x = (c : FractionRing (PS2 K)) * x := rfl

/-- 辅助引理（T3.7(1)，引理 D1 的核心）：若 `w_0, w_1, …` 在 `Frac(K[[x,t]])` 中的像都落在同一个
有限维 `K(x,t)`-子空间 `V` 中，则存在不全为 0 的 `p_0, …, p_r ∈ K[x,t]` 使 `Σ_j p_j·w_j = 0`。 -/
theorem exists_poly_relation (V : Submodule (ratFn K) (FractionRing (PS2 K)))
    (hV : FiniteDimensional (ratFn K) V) (w : ℕ → PS2 K)
    (hw : ∀ j, algebraMap (PS2 K) (FractionRing (PS2 K)) (w j) ∈ V) :
    ∃ (r : ℕ) (p : ℕ → Polynomial (Polynomial K)), (∃ j ≤ r, p j ≠ 0) ∧
      ∑ j ∈ range (r + 1), polyToPS2 K (p j) * w j = 0 := by
  classical
  set ι := algebraMap (PS2 K) (FractionRing (PS2 K))
  set d := Module.finrank (ratFn K) V
  -- `w_0, …, w_d` 这 `d + 1` 个向量在 `d` 维空间 `V` 中线性相关
  set v : Fin (d + 1) → V := fun j => ⟨ι (w j), hw j⟩ with hv
  have hnli : ¬ LinearIndependent (ratFn K) v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnli
  have hg' : ∑ i, (g i : FractionRing (PS2 K)) * ι (w i) = 0 := by
    have := congrArg Subtype.val hg
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, smul_ratFn_eq_mul,
      hv] using this
  -- 每个系数 `g_i = φ(a_i)/φ(b_i)`
  choose a b hb hab using fun i => exists_eq_div_of_mem_ratFn (g i).2
  -- 乘公分母 `φ(∏_i b_i)`：`p_j = a_j·∏_{i≠j} b_i`
  set q : Fin (d + 1) → Polynomial (Polynomial K) := fun j => a j * ∏ i ∈ univ.erase j, b i
    with hq
  have hqval : ∀ j, ι (polyToPS2 K (q j)) =
      (g j : FractionRing (PS2 K)) * ι (polyToPS2 K (∏ i, b i)) := by
    intro j
    rw [← Finset.mul_prod_erase univ b (mem_univ j), hq]
    simp only [map_mul, hab j]
    rw [← mul_assoc, div_mul_cancel₀ _ (hb j)]
  -- 拉回 `K[[x,t]]`（`K[[x,t]] → Frac(K[[x,t]])` 单射）
  have hsum : ∑ j, polyToPS2 K (q j) * w j = 0 := by
    apply IsFractionRing.injective (PS2 K) (FractionRing (PS2 K))
    rw [map_sum, map_zero]
    calc ∑ j, ι (polyToPS2 K (q j) * w j)
        = ∑ j, ι (polyToPS2 K (∏ i, b i)) * ((g j : FractionRing (PS2 K)) * ι (w j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, hqval j]
          ring
      _ = 0 := by rw [← Finset.mul_sum, hg', mul_zero]
  -- `p_{i0} ≠ 0`：`a_{i0} ≠ 0`、各 `b_i ≠ 0`，`K[x,t]` 是整环
  have hbne : ∀ i, b i ≠ 0 := fun i h => hb i (by rw [h, map_zero, map_zero])
  have hane : a i0 ≠ 0 := fun h => hi0 (by
    rw [← ZeroMemClass.coe_eq_zero, hab i0, h, map_zero, map_zero, zero_div])
  have hq0 : q i0 ≠ 0 := mul_ne_zero hane (Finset.prod_ne_zero_iff.mpr fun i _ => hbne i)
  refine ⟨d, fun j => if h : j < d + 1 then q ⟨j, h⟩ else 0,
    ⟨i0, Nat.lt_succ_iff.mp i0.isLt, ?_⟩, ?_⟩
  · simpa [i0.isLt] using hq0
  · rw [Finset.sum_range]
    simpa [Fin.is_le] using hsum

/-- **T3.7(1)**（引理 D1，`notes/c3b.md` §4，`x` 方向）：若 `f ∈ K[[x,t]]` 是 D-finite，则存在
不全为 0 的 `p_0, …, p_r ∈ K[x,t]` 使 `Σ_j p_j·∂_x^j f = 0`。 -/
theorem exists_x_ODE_of_isDFinite {f : PS2 K} (hf : IsDFinite K f) :
    ∃ (r : ℕ) (p : ℕ → Polynomial (Polynomial K)), (∃ j ≤ r, p j ≠ 0) ∧
      ∑ j ∈ range (r + 1), polyToPS2 K (p j) * (dXK K)^[j] f = 0 :=
  exists_poly_relation _ hf (fun j => (dXK K)^[j] f)
    (fun j => Submodule.subset_span ⟨(j, 0), rfl⟩)

/-- **T3.7(1)**（引理 D1，`notes/c3b.md` §4，`t` 方向）：若 `f ∈ K[[x,t]]` 是 D-finite，则存在
不全为 0 的 `p_0, …, p_r ∈ K[x,t]` 使 `Σ_j p_j·∂_t^j f = 0`。 -/
theorem exists_t_ODE_of_isDFinite {f : PS2 K} (hf : IsDFinite K f) :
    ∃ (r : ℕ) (p : ℕ → Polynomial (Polynomial K)), (∃ j ≤ r, p j ≠ 0) ∧
      ∑ j ∈ range (r + 1), polyToPS2 K (p j) * (dTK K)^[j] f = 0 :=
  exists_poly_relation _ hf (fun j => (dTK K)^[j] f)
    (fun j => Submodule.subset_span ⟨(0, j), rfl⟩)

end D1

/-! ### 换系数域：`σ : K →+* L` 逐系数作用 -/

section Map

variable {K : Type*} [Field K] {L : Type*} [Field L] (σ : K →+* L)

/-- 辅助定义（T3.7(1)）：`σ : K →+* L` 逐系数诱导的 `K[[x,t]] →+* L[[x,t]]`。 -/
noncomputable def mapPS2 : PS2 K →+* PS2 L := PowerSeries.map (PowerSeries.map σ)

/-- 辅助引理（T3.7(1)）：换系数与 `∂_x` 交换。 -/
theorem mapPS2_dXK (f : PS2 K) : mapPS2 σ (dXK K f) = dXK L (mapPS2 σ f) := by
  ext m n
  simp [mapPS2, dXK, PowerSeries.coeff_derivative]

/-- 辅助引理（T3.7(1)）：换系数与 `∂_x^j` 交换。 -/
theorem mapPS2_dXK_iter (j : ℕ) (f : PS2 K) :
    mapPS2 σ ((dXK K)^[j] f) = (dXK L)^[j] (mapPS2 σ f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, mapPS2_dXK]

/-- 辅助引理（T3.7(1)）：换系数与嵌入 `K[x,t] → K[[x,t]]` 交换。 -/
theorem mapPS2_polyToPS2 (p : Polynomial (Polynomial K)) :
    mapPS2 σ (polyToPS2 K p) = polyToPS2 L (p.map (Polynomial.mapRingHom σ)) := by
  ext m n
  simp [mapPS2, polyToPS2, Polynomial.coeff_coe]

/-- 辅助引理（T3.7(1)）：换系数把 `K` 上的 `F` 映成 `L` 上的 `F`。 -/
theorem mapPS2_FK : mapPS2 σ (FK K) = FK L := by
  ext m k
  simp [mapPS2, FK]

end Map

/-! ### 主定理 -/

section Main

/-- 辅助引理（T3.7(1)）：`FK ℂ` 就是 `NonDFinite.lean` 中的 `Fxt`（定义上相等）。 -/
theorem FK_complex_eq_Fxt : FK ℂ = Fxt := rfl

/-- 辅助引理（T3.7(1)）：`ℂ` 上的 `dXK` 就是 `NonDFinite.lean` 中的 `dX`（定义上相等）。 -/
theorem dXK_complex_eq_dX : dXK ℂ = dX := rfl

/-- 辅助引理（T3.7(1)）：`ℂ` 上的 `polyToPS2` 就是 `NonDFinite.lean` 中的 `embedC`
（先把 `ℂ[x,t]` 看成 `ℂ[x][[t]]`）。 -/
theorem polyToPS2_complex_eq_embedC (p : Polynomial (Polynomial ℂ)) :
    polyToPS2 ℂ p = embedC (p : PowerSeries (Polynomial ℂ)) := rfl

/-- **T3.7(1)**（最后一步「所以 `F` 不是 D-finite」）：对任何域 `K` 与环同态 `σ : K →+* ℂ`（即
`K ⊆ ℂ`；域上的环同态自动单射），`F = Σ_{k,m} U_k(m)·x^k·t^m ∈ K[[x,t]]` 不是 D-finite
（Lipshitz 1989 Def. 2.1，`IsDFinite`）。证明：若是，引理 D1（`exists_x_ODE_of_isDFinite`）给出
`K[x,t]` 系数、不全为 0 的 `Σ_j p_j·∂_x^j F = 0`；用 `σ` 把系数映到 `ℂ`，得到 `ℂ[x,t]` 系数、
不全为 0 的同一方程，与 `no_x_ODE_poly` 矛盾。 -/
theorem not_isDFinite_FK {K : Type*} [Field K] (σ : K →+* ℂ) : ¬ IsDFinite K (FK K) := by
  intro hD
  obtain ⟨r, p, ⟨j, hj, hpj⟩, hode⟩ := exists_x_ODE_of_isDFinite hD
  have hinj : Function.Injective (Polynomial.map (Polynomial.mapRingHom σ)) :=
    Polynomial.map_injective _ (Polynomial.map_injective _ σ.injective)
  refine no_x_ODE_poly r (fun i => (p i).map (Polynomial.mapRingHom σ))
    ⟨j, hj, fun h => hpj (hinj (by rw [h, Polynomial.map_zero]))⟩ ?_
  have h := congrArg (mapPS2 σ) hode
  rw [map_sum, map_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mapPS2_polyToPS2, mapPS2_dXK_iter, mapPS2_FK, FK_complex_eq_Fxt,
    dXK_complex_eq_dX, polyToPS2_complex_eq_embedC]

/-- **T3.7(1)**（`K = ℂ`）：`F = Σ_{k,m} U_k(m)·x^k·t^m ∈ ℂ[[x,t]]` 不是 D-finite。 -/
theorem not_isDFinite_F : ¬ IsDFinite ℂ (FK ℂ) := not_isDFinite_FK (RingHom.id ℂ)

/-- **T3.7(1)**（`K = ℂ`，用 `NonDFinite.lean` 的记号）：`Fxt` 不是 D-finite。 -/
theorem not_isDFinite_Fxt : ¬ IsDFinite ℂ Fxt := not_isDFinite_F

end Main

end A207123
