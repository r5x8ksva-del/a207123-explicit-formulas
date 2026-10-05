import A207123.OreRelN

/-!
# 报告 T3.8 的维数公式

T3.8 的计数部分：支撑在 `[0..A] × [0..B]`（`X` 的次数 `≤ A`，`E^{−1}`（`N` 的版本里是 `Y`）的次数
`≤ B`）、系数次数受限的关系空间的维数。

* `U` 的版本：总次数 `≤ D` 时（`finrank_relU_tot`），`A ≥ 3`、`B ≥ 1`、`D ≥ 1` 则维数为
  `(A−2)·B·D(D+1)/2`，否则为 0；分次版（`finrank_relU_gr`，关于 `k` 的次数 `≤ D_k`、关于 `m` 的次数
  `≤ D_m`）在 `A ≥ 3`、`B ≥ 1`、`D_m ≥ 1` 时为 `(A−2)·B·(D_k+1)·D_m`，否则为 0。
* `N` 的版本：总次数版（`finrank_relN_tot`）在 `A ≥ 3`、`B ≥ 2`、`D ≥ 1` 时为 `(A−2)(B−1)·D(D+1)/2`，
  分次版（`finrank_relN_gr`）在 `A ≥ 3`、`B ≥ 2`、`D_q ≥ 1` 时为 `(A−2)(B−1)(D_k+1)·D_q`，否则为 0。

「关系空间」取为盒子空间（正规形单项 `k^i·m^j·X^a·E^{−b}` 张成的子空间 `boxSp`）与「在某个象限上零化
`U`（或 `N`）的算子」之交；`mem_relBoxU_iff`、`mem_relBoxN_iff` 说明它就是盒子与 `Rel(U)`（或 `Rel(N)`）
之交。

**证明**（报告的计数论证）：由 `RelU_eq`，盒子里的关系是 `Q·L1`；角点论证说明 `Q` 的正规形支撑在
`[0..A−3] × [0..B−1]`、系数次数 `≤ D−1`（`relU_box_iff`）；右乘 `L1` 是单射，单项算子线性无关，所以
维数等于小盒子里单项式的个数。`N` 的版本相同，小盒子是 `[0..A−3] × [0..B−2]`（`relN_box_iff`）。
-/

open Polynomial Finset

namespace A207123

/-! ### 单项算子、盒子空间与次数集合 -/

/-- 单项算子 `k^i·m^j·X^a·E^{−b}`，下标 `x = (a, b, i, j)`（T3.8 的维数公式）。 -/
noncomputable def mono (x : ℕ × ℕ × ℕ × ℕ) : Module.End ℂ Arr :=
  mulOp (Polynomial.C (Polynomial.X ^ x.2.2.1) * Polynomial.X ^ x.2.2.2) * opX ^ x.1 * opEinv ^ x.2.1

/-- 下标集 `s` 中的单项算子张成的子空间。 -/
noncomputable def spanBox (s : Finset (ℕ × ℕ × ℕ × ℕ)) : Submodule ℂ (Module.End ℂ Arr) :=
  Submodule.span ℂ (mono '' (s : Set (ℕ × ℕ × ℕ × ℕ)))

/-- 盒子空间（T3.8）：正规形支撑在 `[0..A] × [0..B]`（`X` 的次数 `≤ A`，`E^{−1}` 的次数 `≤ B`），
系数只含单项式 `k^i·m^j`，`(i, j) ∈ T`。 -/
noncomputable def boxSp (A B : ℕ) (T : Finset (ℕ × ℕ)) : Submodule ℂ (Module.End ℂ Arr) :=
  spanBox (range (A + 1) ×ˢ range (B + 1) ×ˢ T)

/-- 指数 `(i, j)` 满足 `i + j < n`。 -/
def degLt (n : ℕ) : Finset (ℕ × ℕ) := (range n).biUnion antidiagonal

/-- 系数总次数 `≤ D`：`i + j ≤ D`。 -/
def degLe (D : ℕ) : Finset (ℕ × ℕ) := degLt (D + 1)

/-- 分次：关于 `k` 的次数 `≤ Dk`、关于 `m` 的次数 `≤ Dm`。 -/
def grT (Dk Dm : ℕ) : Finset (ℕ × ℕ) := range (Dk + 1) ×ˢ range (Dm + 1)

/-- 辅助引理（T3.8）。 -/
theorem mem_degLt {n : ℕ} {ij : ℕ × ℕ} : ij ∈ degLt n ↔ ij.1 + ij.2 < n := by
  simp only [degLt, mem_biUnion, mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
  exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun h => ⟨_, h, rfl⟩⟩

/-- 辅助引理（T3.8）。 -/
theorem mem_degLe {D : ℕ} {ij : ℕ × ℕ} : ij ∈ degLe D ↔ ij.1 + ij.2 ≤ D := by
  rw [degLe, mem_degLt]; omega

/-- 辅助引理（T3.8）。 -/
theorem mem_grT {Dk Dm : ℕ} {ij : ℕ × ℕ} : ij ∈ grT Dk Dm ↔ ij.1 ≤ Dk ∧ ij.2 ≤ Dm := by
  simp only [grT, mem_product, mem_range]; omega

/-- 辅助引理（T3.8）：`i + j < n` 的指数共 `n(n+1)/2` 个。 -/
theorem card_degLt (n : ℕ) : (degLt n).card = n * (n + 1) / 2 := by
  rw [degLt, card_biUnion]
  · simp only [Finset.Nat.card_antidiagonal]
    have h := Finset.sum_range_succ' (fun i => i) n
    simp only [add_zero] at h
    rw [← h, sum_range_id, Nat.add_sub_cancel, mul_comm]
  · intro a _ b _ hab
    exact Finset.disjoint_left.mpr fun x ha hb =>
      hab ((Finset.HasAntidiagonal.mem_antidiagonal.mp ha).symm.trans
        (Finset.HasAntidiagonal.mem_antidiagonal.mp hb))

/-! ### 单项式系数 -/

/-- `p ∈ ℂ[k, m]` 中 `k^i·m^j` 的系数。 -/
noncomputable def cf (p : Coef) (i j : ℕ) : ℂ := (p.coeff j).coeff i

/-- 辅助引理（T3.8）。 -/
@[simp] theorem cf_zero (i j : ℕ) : cf 0 i j = 0 := by simp [cf]

/-- 辅助引理（T3.8）。 -/
theorem cf_add (p q : Coef) (i j : ℕ) : cf (p + q) i j = cf p i j + cf q i j := by simp [cf]

/-- 辅助引理（T3.8）。 -/
theorem cf_sub (p q : Coef) (i j : ℕ) : cf (p - q) i j = cf p i j - cf q i j := by simp [cf]

/-- 辅助引理（T3.8）。 -/
theorem cf_neg (p : Coef) (i j : ℕ) : cf (-p) i j = -cf p i j := by simp [cf]

/-- 辅助引理（T3.8）。 -/
theorem cf_smul (c : ℂ) (p : Coef) (i j : ℕ) : cf (c • p) i j = c * cf p i j := by simp [cf]

/-- 辅助引理（T3.8）。 -/
theorem cf_ite (P : Prop) [Decidable P] (p : Coef) (i j : ℕ) :
    cf (if P then p else 0) i j = if P then cf p i j else 0 := by
  split_ifs <;> simp

/-- 辅助引理（T3.8）。 -/
theorem cf_sum {ι : Type*} (t : Finset ι) (g : ι → Coef) (i j : ℕ) :
    cf (∑ y ∈ t, g y) i j = ∑ y ∈ t, cf (g y) i j := by
  simp only [cf, Polynomial.finsetSum_coeff]

/-- 辅助引理（T3.8）：`k^i·m^j` 的系数。 -/
theorem cf_mono (i j i' j' : ℕ) :
    cf (Polynomial.C (Polynomial.X ^ i) * Polynomial.X ^ j) i' j' =
      if i' = i ∧ j' = j then 1 else 0 := by
  unfold cf
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hj : j' = j
  · by_cases hi : i' = i
    · simp [hj, hi, Polynomial.coeff_X_pow]
    · simp [hj, hi, Polynomial.coeff_X_pow]
  · simp [hj]

/-- 辅助引理（T3.8）：`(m − n)·p` 的展开。 -/
theorem cM_sub_natCast_mul (n : ℕ) (p : Coef) :
    (cM - (n : Coef)) * p = Polynomial.X * p - Polynomial.C (Polynomial.C (n : ℂ)) * p := by
  rw [sub_mul, cM]; simp

/-- 辅助引理（T3.8）：`[k^i m^{j+1}] ((m − n)·p) = [k^i m^j] p − n·[k^i m^{j+1}] p`。 -/
theorem cf_mulM_succ (n : ℕ) (p : Coef) (i j : ℕ) :
    cf ((cM - (n : Coef)) * p) i (j + 1) = cf p i j - n * cf p i (j + 1) := by
  rw [cM_sub_natCast_mul]
  unfold cf
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul]

/-- 辅助引理（T3.8）：`[k^i m^0] ((m − n)·p) = −n·[k^i m^0] p`。 -/
theorem cf_mulM_zero (n : ℕ) (p : Coef) (i : ℕ) :
    cf ((cM - (n : Coef)) * p) i 0 = -(n * cf p i 0) := by
  rw [cM_sub_natCast_mul]
  unfold cf
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub,
    Polynomial.coeff_neg, Polynomial.coeff_C_mul]

/-- 辅助引理（T3.8）：非零系数必有非零单项式系数。 -/
theorem exists_cf_ne_zero {p : Coef} (hp : p ≠ 0) : ∃ i j, cf p i j ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  ext j i
  simpa [cf] using h i j

/-! ### 正规形的单项式支撑 -/

/-- 正规形 `r` 的单项式支撑：`(a, b, i, j)` 使 `r_{ab}` 中 `k^i·m^j` 的系数非零。 -/
noncomputable def msupp (r : ℕ × ℕ →₀ Coef) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  r.support.biUnion fun ab => (r ab).support.biUnion fun j =>
    ((r ab).coeff j).support.image fun i => (ab.1, ab.2, i, j)

/-- 辅助引理（T3.8）。 -/
theorem mem_msupp {r : ℕ × ℕ →₀ Coef} {x : ℕ × ℕ × ℕ × ℕ} :
    x ∈ msupp r ↔ cf (r (x.1, x.2.1)) x.2.2.1 x.2.2.2 ≠ 0 := by
  obtain ⟨a, b, i, j⟩ := x
  simp only [msupp, mem_biUnion, mem_image, Finsupp.mem_support_iff, Polynomial.mem_support_iff, cf]
  constructor
  · rintro ⟨⟨a', b'⟩, -, j', -, i', h3, h4⟩
    simp only [Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h4
    exact h3
  · intro h
    refine ⟨(a, b), ?_, j, ?_, i, h, rfl⟩
    · intro h0; rw [h0] at h; simp at h
    · intro h0; rw [h0] at h; simp at h

/-- 辅助引理（T3.8）：单项式支撑为空则正规形为 0。 -/
theorem eq_zero_of_msupp {r : ℕ × ℕ →₀ Coef} (h : msupp r = ∅) : r = 0 := by
  by_contra hr
  obtain ⟨ab, hab⟩ := Finsupp.support_nonempty_iff.mpr hr
  obtain ⟨i, j, hij⟩ := exists_cf_ne_zero (Finsupp.mem_support_iff.mp hab)
  have : (ab.1, ab.2, i, j) ∈ msupp r := mem_msupp.mpr hij
  rw [h] at this
  simp at this

/-- 辅助引理（T3.8）。 -/
theorem mem_msupp_sub {f g : ℕ × ℕ →₀ Coef} {x : ℕ × ℕ × ℕ × ℕ} (h : x ∈ msupp (f - g)) :
    x ∈ msupp f ∨ x ∈ msupp g := by
  rw [mem_msupp, Finsupp.sub_apply, cf_sub] at h
  by_contra H
  rw [not_or, mem_msupp, mem_msupp, not_not, not_not] at H
  exact h (by rw [H.1, H.2, sub_zero])

/-- 辅助引理（T3.8）。 -/
theorem mem_msupp_add {f g : ℕ × ℕ →₀ Coef} {x : ℕ × ℕ × ℕ × ℕ} (h : x ∈ msupp (f + g)) :
    x ∈ msupp f ∨ x ∈ msupp g := by
  rw [mem_msupp, Finsupp.add_apply, cf_add] at h
  by_contra H
  rw [not_or, mem_msupp, mem_msupp, not_not, not_not] at H
  exact h (by rw [H.1, H.2, add_zero])

/-! ### 正规形的线性 -/

/-- 辅助引理（T3.8）。 -/
theorem normOp_sub (r s : ℕ × ℕ →₀ Coef) : normOp (r - s) = normOp r - normOp s :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul, sub_mul])

/-- 辅助引理（T3.8）。 -/
theorem mulOp_smul (c : ℂ) (p : Coef) : mulOp (c • p) = c • mulOp p := by
  ext f k m
  simp only [mulOp_apply, evalEval_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- 辅助引理（T3.8）。 -/
theorem mulOp_CC_mul (c : ℂ) (q : Coef) :
    mulOp (Polynomial.C (Polynomial.C c) * q) = c • mulOp q := by
  rw [map_mul, mulOp_CC, ← Algebra.smul_def]

/-- 辅助引理（T3.8）。 -/
theorem normOp_smul (c : ℂ) (r : ℕ × ℕ →₀ Coef) : normOp (c • r) = c • normOp r := by
  induction r using Finsupp.induction_linear with
  | zero => rw [smul_zero, normOp_zero, smul_zero]
  | add r s hr hs => rw [smul_add, normOp_add, normOp_add, hr, hs, smul_add]
  | single ab p =>
    rw [Finsupp.smul_single, normOp_single, normOp_single, mulOp_smul, smul_mul_assoc,
      smul_mul_assoc]

/-- 辅助引理（T3.8）。 -/
theorem normOp_sum {ι : Type*} (t : Finset ι) (g : ι → ℕ × ℕ →₀ Coef) :
    normOp (∑ y ∈ t, g y) = ∑ y ∈ t, normOp (g y) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, normOp_zero]
  | insert y t hy ih => rw [sum_insert hy, sum_insert hy, normOp_add, ih]

/-- 辅助引理（T3.8）：单项算子是单项正规形。 -/
theorem mono_eq (x : ℕ × ℕ × ℕ × ℕ) :
    mono x = normOp (Finsupp.single (x.1, x.2.1)
      (Polynomial.C (Polynomial.X ^ x.2.2.1) * Polynomial.X ^ x.2.2.2)) := by
  rw [normOp_single]; rfl

/-! ### 盒子空间与单项式支撑 -/

/-- 辅助引理（T3.8）：盒子空间都在 `O_U` 里。 -/
theorem spanBox_le_OU (s : Finset (ℕ × ℕ × ℕ × ℕ)) : spanBox s ≤ Subalgebra.toSubmodule OU := by
  rw [spanBox, Submodule.span_le]
  rintro _ ⟨x, _, rfl⟩
  show mono x ∈ OU
  exact mul_mem (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem _)) (pow_mem opEinv_mem _)

/-- 辅助引理（T3.8）。 -/
theorem mulOp_mem_spanBox {s : Finset (ℕ × ℕ × ℕ × ℕ)} (a b : ℕ) (p : Coef)
    (h : ∀ i j, cf p i j ≠ 0 → (a, b, i, j) ∈ s) :
    mulOp p * opX ^ a * opEinv ^ b ∈ spanBox s := by
  rw [p.as_sum_support_C_mul_X_pow, map_sum, sum_mul, sum_mul]
  apply Submodule.sum_mem
  intro j _
  rw [(p.coeff j).as_sum_support_C_mul_X_pow, map_sum, sum_mul, map_sum, sum_mul, sum_mul]
  apply Submodule.sum_mem
  intro i hi
  have hne : cf p i j ≠ 0 := Polynomial.mem_support_iff.mp hi
  have e : mulOp (Polynomial.C (Polynomial.C ((p.coeff j).coeff i) * Polynomial.X ^ i) *
      Polynomial.X ^ j) * opX ^ a * opEinv ^ b = cf p i j • mono (a, b, i, j) := by
    rw [map_mul Polynomial.C, mul_assoc (Polynomial.C (Polynomial.C _)), mulOp_CC_mul,
      smul_mul_assoc, smul_mul_assoc]
    rfl
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b, i, j), h i j hne, rfl⟩)

/-- 辅助引理（T3.8）：单项式支撑在 `s` 里的正规形属于 `spanBox s`。 -/
theorem normOp_mem_spanBox {s : Finset (ℕ × ℕ × ℕ × ℕ)} {r : ℕ × ℕ →₀ Coef}
    (h : ∀ x ∈ msupp r, x ∈ s) : normOp r ∈ spanBox s := by
  simp only [normOp, Finsupp.sum]
  apply Submodule.sum_mem
  intro ab _
  exact mulOp_mem_spanBox ab.1 ab.2 (r ab) fun i j hij => h _ (mem_msupp.mpr hij)

/-- 辅助引理（T3.8）：`spanBox s` 里的正规形，单项式支撑在 `s` 里。 -/
theorem msupp_subset_of_mem_spanBox {s : Finset (ℕ × ℕ × ℕ × ℕ)} {r : ℕ × ℕ →₀ Coef}
    (h : normOp r ∈ spanBox s) : ∀ x ∈ msupp r, x ∈ s := by
  have key : ∀ T ∈ spanBox s, ∃ r' : ℕ × ℕ →₀ Coef, T = normOp r' ∧ ∀ x ∈ msupp r', x ∈ s := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨x, hx, rfl⟩ := hT
      refine ⟨_, mono_eq x, fun y hy => ?_⟩
      obtain ⟨a, b, i, j⟩ := x
      obtain ⟨a', b', i', j'⟩ := y
      rw [mem_msupp] at hy
      simp only [Finsupp.single_apply] at hy
      split_ifs at hy with hab
      · rw [cf_mono] at hy
        split_ifs at hy with hij
        · simp only [Prod.mk.injEq] at hab
          obtain ⟨rfl, rfl⟩ := hab
          obtain ⟨rfl, rfl⟩ := hij
          exact hx
        · exact absurd rfl hy
      · exact absurd (cf_zero _ _) hy
    | zero =>
      exact ⟨0, normOp_zero.symm, fun y hy => by rw [mem_msupp] at hy; simp at hy⟩
    | add T1 T2 _ _ h1 h2 =>
      obtain ⟨r1, rfl, h1⟩ := h1
      obtain ⟨r2, rfl, h2⟩ := h2
      refine ⟨r1 + r2, (normOp_add r1 r2).symm, fun y hy => ?_⟩
      rcases mem_msupp_add hy with hy | hy
      · exact h1 y hy
      · exact h2 y hy
    | smul c T _ hT =>
      obtain ⟨r1, rfl, h1⟩ := hT
      refine ⟨c • r1, (normOp_smul c r1).symm, fun y hy => ?_⟩
      rw [mem_msupp, Finsupp.smul_apply, cf_smul] at hy
      exact h1 y (mem_msupp.mpr (right_ne_zero_of_mul hy))
  obtain ⟨r', hr', hs⟩ := key _ h
  have : r = r' := by
    have h0 : normOp (r - r') = 0 := by rw [normOp_sub, hr', sub_self]
    exact sub_eq_zero.mp (normal_form_unique _ h0)
  subst this
  exact hs

/-- 辅助引理（T3.8）：单项算子线性无关（正规形唯一的推论）。 -/
theorem mono_linearIndependent (s : Finset (ℕ × ℕ × ℕ × ℕ)) :
    LinearIndependent ℂ (fun x : s => mono x) := by
  classical
  rw [linearIndependent_iff']
  intro t g hg y hy
  set r : ℕ × ℕ →₀ Coef := ∑ x ∈ t, Finsupp.single ((x : ℕ × ℕ × ℕ × ℕ).1, (x : ℕ × ℕ × ℕ × ℕ).2.1)
    (g x • (Polynomial.C (Polynomial.X ^ (x : ℕ × ℕ × ℕ × ℕ).2.2.1) *
      Polynomial.X ^ (x : ℕ × ℕ × ℕ × ℕ).2.2.2)) with hr
  have h0 : normOp r = 0 := by
    rw [hr, normOp_sum, ← hg]
    apply sum_congr rfl
    intro x _
    rw [← Finsupp.smul_single, normOp_smul, ← mono_eq]
  have hr0 := normal_form_unique r h0
  have hval := congrArg (fun r' : ℕ × ℕ →₀ Coef =>
    cf (r' ((y : ℕ × ℕ × ℕ × ℕ).1, (y : ℕ × ℕ × ℕ × ℕ).2.1)) (y : ℕ × ℕ × ℕ × ℕ).2.2.1
      (y : ℕ × ℕ × ℕ × ℕ).2.2.2) hr0
  simp only [Finsupp.coe_zero, Pi.zero_apply, cf_zero] at hval
  rw [hr, Finsupp.finsetSum_apply, cf_sum, sum_eq_single y] at hval
  · rw [Finsupp.single_eq_same, cf_smul, cf_mono] at hval
    simpa using hval
  · intro x _ hxy
    rw [Finsupp.single_apply]
    split_ifs with h
    · have hne : ¬((y : ℕ × ℕ × ℕ × ℕ).2.2.1 = (x : ℕ × ℕ × ℕ × ℕ).2.2.1 ∧
          (y : ℕ × ℕ × ℕ × ℕ).2.2.2 = (x : ℕ × ℕ × ℕ × ℕ).2.2.2) := by
        rintro ⟨e3, e4⟩
        apply hxy
        apply Subtype.ext
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.ext h.2 (Prod.ext e3.symm e4.symm))
      rw [cf_smul, cf_mono]
      simp only [hne, ↓reduceIte, mul_zero]
    · exact cf_zero _ _
  · intro h
    exact absurd hy h

/-- 辅助引理（T3.8）：`spanBox s` 的维数等于 `s` 的元素个数。 -/
theorem finrank_spanBox (s : Finset (ℕ × ℕ × ℕ × ℕ)) :
    Module.finrank ℂ (spanBox s) = s.card := by
  have h := finrank_span_eq_card (mono_linearIndependent s)
  have hr : Set.range (fun x : s => mono x) = mono '' (s : Set (ℕ × ℕ × ℕ × ℕ)) := by
    ext T
    simp
  rw [hr, Fintype.card_coe] at h
  exact h

/-- 在某个象限上零化 `F` 的算子全体（子空间）。 -/
def vanSub (F : Arr) : Submodule ℂ (Module.End ℂ Arr) where
  carrier := {R | ∃ k0 m0 : ℕ, VanishOn (R F) k0 m0}
  add_mem' := by
    rintro R S ⟨k0, m0, hR⟩ ⟨k1, m1, hS⟩
    exact ⟨max k0 k1, max m0 m1, fun k m hk hm => by
      rw [LinearMap.add_apply, Pi.add_apply, Pi.add_apply,
        hR k m (le_of_max_le_left hk) (le_of_max_le_left hm),
        hS k m (le_of_max_le_right hk) (le_of_max_le_right hm), add_zero]⟩
  zero_mem' := ⟨0, 0, fun _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c R ⟨k0, m0, hR⟩
    exact ⟨k0, m0, fun k m hk hm => by
      rw [LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hR k m hk hm, smul_zero]⟩

/-! ### `Q·L1` 与 `Q·L_N` 的正规形 -/

/-- 平移 `(a, b) ↦ (a + s, b + t)`。 -/
def sh (s t : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := (ab.1 + s, ab.2 + t)

/-- 辅助引理（T3.8）。 -/
theorem sh_injective (s t : ℕ) : Function.Injective (sh s t) := by
  intro x y h
  simp only [sh, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

/-- 辅助引理（T3.8）。 -/
theorem mapDomain_sh_apply (q : ℕ × ℕ →₀ Coef) (s t a b : ℕ) :
    q.mapDomain (sh s t) (a, b) = if s ≤ a ∧ t ≤ b then q (a - s, b - t) else 0 := by
  split_ifs with h
  · have e : (a, b) = sh s t (a - s, b - t) := by
      simp only [sh, Prod.mk.injEq]; omega
    rw [e, Finsupp.mapDomain_apply_of_injective (sh_injective s t)]
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨a', b'⟩, h'⟩
    simp only [sh, Prod.mk.injEq] at h'
    omega

/-- 辅助引理（T3.8）。 -/
theorem mem_msupp_mapDomain {q : ℕ × ℕ →₀ Coef} {s t : ℕ} {x : ℕ × ℕ × ℕ × ℕ}
    (h : x ∈ msupp (q.mapDomain (sh s t))) :
    s ≤ x.1 ∧ t ≤ x.2.1 ∧ (x.1 - s, x.2.1 - t, x.2.2) ∈ msupp q := by
  rw [mem_msupp, mapDomain_sh_apply] at h
  split_ifs at h with hst
  · exact ⟨hst.1, hst.2, mem_msupp.mpr h⟩
  · exact absurd (cf_zero _ _) h

/-- 系数乘以 `m − (b + c)`，`b` 是所在位置的第二个下标。 -/
noncomputable def mulMB (c : ℕ) (q : ℕ × ℕ →₀ Coef) : ℕ × ℕ →₀ Coef :=
  Finsupp.onFinset q.support (fun ab => (cM - ((ab.2 + c : ℕ) : Coef)) * q ab) (fun ab h => by
    rw [Finsupp.mem_support_iff]; intro h0; apply h; rw [h0, mul_zero])

/-- 辅助引理（T3.8）。 -/
theorem mulMB_apply (c : ℕ) (q : ℕ × ℕ →₀ Coef) (ab : ℕ × ℕ) :
    mulMB c q ab = (cM - ((ab.2 + c : ℕ) : Coef)) * q ab := Finsupp.onFinset_apply

/-- 辅助引理（T3.8）。 -/
theorem mulMB_zero (c : ℕ) : mulMB c 0 = 0 :=
  Finsupp.ext fun ab => by rw [mulMB_apply, Finsupp.coe_zero, Pi.zero_apply, mul_zero]

/-- 辅助引理（T3.8）。 -/
theorem mulMB_add (c : ℕ) (q q' : ℕ × ℕ →₀ Coef) : mulMB c (q + q') = mulMB c q + mulMB c q' :=
  Finsupp.ext fun ab => by
    rw [Finsupp.add_apply, mulMB_apply, mulMB_apply, mulMB_apply, Finsupp.add_apply, mul_add]

/-- 辅助引理（T3.8）。 -/
theorem mulMB_single (c : ℕ) (ab : ℕ × ℕ) (p : Coef) :
    mulMB c (Finsupp.single ab p) = Finsupp.single ab ((cM - ((ab.2 + c : ℕ) : Coef)) * p) := by
  refine Finsupp.ext fun ab' => ?_
  rw [mulMB_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-- 辅助引理（T3.8）。 -/
theorem mem_msupp_mulMB {q : ℕ × ℕ →₀ Coef} {c : ℕ} {x : ℕ × ℕ × ℕ × ℕ}
    (h : x ∈ msupp (mulMB c q)) :
    x ∈ msupp q ∨ (1 ≤ x.2.2.2 ∧ (x.1, x.2.1, x.2.2.1, x.2.2.2 - 1) ∈ msupp q) := by
  obtain ⟨a, b, i, j⟩ := x
  rw [mem_msupp, mulMB_apply] at h
  simp only at h
  rcases j with _ | j
  · rw [cf_mulM_zero] at h
    left
    rw [mem_msupp]
    intro h0
    apply h
    simp only at h0
    rw [h0, mul_zero, neg_zero]
  · rw [cf_mulM_succ] at h
    by_cases h1 : cf (q (a, b)) i j = 0
    · left
      rw [mem_msupp]
      intro h0
      apply h
      simp only at h0
      rw [h1, h0, mul_zero, sub_zero]
    · right
      refine ⟨by simp, mem_msupp.mpr ?_⟩
      simpa using h1

/-- 辅助引理（T3.8）：`X^a·E^{−b}·(m − c) = (m − b − c)·X^a·E^{−b}`。 -/
theorem XY_mul_cM_sub (a b c : ℕ) :
    opX ^ a * opEinv ^ b * mulOp (cM - (c : Coef)) =
      mulOp (cM - ((b + c : ℕ) : Coef)) * opX ^ a * opEinv ^ b := by
  ext f k m
  simp only [Module.End.mul_apply, opX_pow_apply, opEinv_pow_apply, mulOp_apply, evalEval_sub,
    evalEval_cM, evalEval_natCast]
  split_ifs with h1 h2
  · push_cast [Nat.cast_sub h2]; ring
  · simp
  · simp

/-- 辅助引理（T3.8）：右乘 `X^s·E^{−t}`。 -/
theorem normOp_mul_XY (q : ℕ × ℕ →₀ Coef) (s t : ℕ) :
    normOp q * (opX ^ s * opEinv ^ t) = normOp (q.mapDomain (sh s t)) := by
  induction q using Finsupp.induction_linear with
  | zero => rw [normOp_zero, zero_mul, Finsupp.mapDomain_zero, normOp_zero]
  | add q q' hq hq' => rw [normOp_add, add_mul, hq, hq', Finsupp.mapDomain_add, normOp_add]
  | single ab p =>
    rw [Finsupp.mapDomain_single, normOp_single, normOp_single]
    have hc : opEinv ^ ab.2 * opX ^ s = opX ^ s * opEinv ^ ab.2 :=
      (commute_opX_opEinv.pow_pow s ab.2).eq.symm
    simp only [sh, pow_add]
    simp only [mul_assoc]
    rw [← mul_assoc (opEinv ^ ab.2), hc]
    simp only [mul_assoc]

/-- 辅助引理（T3.8）：右乘 `m − c`。 -/
theorem normOp_mul_cM (q : ℕ × ℕ →₀ Coef) (c : ℕ) :
    normOp q * mulOp (cM - (c : Coef)) = normOp (mulMB c q) := by
  induction q using Finsupp.induction_linear with
  | zero => rw [normOp_zero, zero_mul, mulMB_zero, normOp_zero]
  | add q q' hq hq' => rw [normOp_add, add_mul, hq, hq', mulMB_add, normOp_add]
  | single ab p =>
    rw [mulMB_single, normOp_single, normOp_single]
    calc mulOp p * opX ^ ab.1 * opEinv ^ ab.2 * mulOp (cM - (c : Coef))
        = mulOp p * (opX ^ ab.1 * opEinv ^ ab.2 * mulOp (cM - (c : Coef))) := by
          simp only [mul_assoc]
      _ = mulOp p * (mulOp (cM - ((ab.2 + c : ℕ) : Coef)) * opX ^ ab.1 * opEinv ^ ab.2) := by
          rw [XY_mul_cM_sub]
      _ = mulOp ((cM - ((ab.2 + c : ℕ) : Coef)) * p) * opX ^ ab.1 * opEinv ^ ab.2 := by
          rw [mul_comm (cM - _) p, map_mul]; simp only [mul_assoc]

/-- `Q·L1` 的正规形（`Q` 的正规形为 `q`）：
`r_{ab} = q_{ab} − q_{a,b−1} − q_{a−1,b} − (m − b)·q_{a−3,b}`。 -/
noncomputable def TU (q : ℕ × ℕ →₀ Coef) : ℕ × ℕ →₀ Coef :=
  q - q.mapDomain (sh 0 1) - q.mapDomain (sh 1 0) - (mulMB 0 q).mapDomain (sh 3 0)

/-- 辅助引理（T3.8）。 -/
theorem normOp_mul_L1 (q : ℕ × ℕ →₀ Coef) : normOp q * L1 = normOp (TU q) := by
  have e1 : normOp q * opEinv = normOp (q.mapDomain (sh 0 1)) := by
    rw [← normOp_mul_XY, pow_zero, pow_one, one_mul]
  have e2 : normOp q * opX = normOp (q.mapDomain (sh 1 0)) := by
    rw [← normOp_mul_XY, pow_one, pow_zero, mul_one]
  have e3 : normOp q * (mulOp cM * opX ^ 3) = normOp ((mulMB 0 q).mapDomain (sh 3 0)) := by
    rw [← normOp_mul_XY, ← normOp_mul_cM, Nat.cast_zero, sub_zero, pow_zero, mul_one, mul_assoc]
  rw [TU, normOp_sub, normOp_sub, normOp_sub, ← e1, ← e2, ← e3, L1]
  simp only [mul_sub, mul_one]

/-- 辅助引理（T3.8）：`TU` 的分量。 -/
theorem TU_apply (q : ℕ × ℕ →₀ Coef) (a b : ℕ) :
    TU q (a, b) = q (a, b) - (if 1 ≤ b then q (a, b - 1) else 0)
      - (if 1 ≤ a then q (a - 1, b) else 0)
      - (if 3 ≤ a then (cM - ((b + 0 : ℕ) : Coef)) * q (a - 3, b) else 0) := by
  simp only [TU, Finsupp.coe_sub, Pi.sub_apply, mapDomain_sh_apply, mulMB_apply, zero_le, true_and,
    and_true, Nat.sub_zero]

/-! ### 字典序最大元 -/

/-- 辅助引理（T3.8）：有限集上关于四个指标的字典序最大元。 -/
theorem exists_lex_max {α : Type*} (S : Finset α) (hS : S.Nonempty) (f1 f2 f3 f4 : α → ℕ) :
    ∃ x0 ∈ S, ∀ x ∈ S, f1 x ≤ f1 x0 ∧ (f1 x = f1 x0 → f2 x ≤ f2 x0 ∧
      (f2 x = f2 x0 → f3 x ≤ f3 x0 ∧ (f3 x = f3 x0 → f4 x ≤ f4 x0))) := by
  classical
  obtain ⟨x1, hx1, h1⟩ := S.exists_max_image f1 hS
  obtain ⟨x2, hx2, h2⟩ := (S.filter fun x => f1 x = f1 x1).exists_max_image f2
    ⟨x1, mem_filter.mpr ⟨hx1, rfl⟩⟩
  obtain ⟨x3, hx3, h3⟩ := ((S.filter fun x => f1 x = f1 x1).filter fun x => f2 x = f2 x2).exists_max_image
    f3 ⟨x2, mem_filter.mpr ⟨hx2, rfl⟩⟩
  obtain ⟨x4, hx4, h4⟩ := (((S.filter fun x => f1 x = f1 x1).filter fun x => f2 x = f2 x2).filter
    fun x => f3 x = f3 x3).exists_max_image f4 ⟨x3, mem_filter.mpr ⟨hx3, rfl⟩⟩
  rw [mem_filter, mem_filter, mem_filter] at hx4
  obtain ⟨⟨⟨hx4S, e1⟩, e2⟩, e3⟩ := hx4
  refine ⟨x4, hx4S, fun x hx => ⟨(h1 x hx).trans_eq e1.symm, fun g1 => ?_⟩⟩
  have m1 : x ∈ S.filter fun x => f1 x = f1 x1 := mem_filter.mpr ⟨hx, g1.trans e1⟩
  refine ⟨(h2 x m1).trans_eq e2.symm, fun g2 => ?_⟩
  have m2 : x ∈ (S.filter fun x => f1 x = f1 x1).filter fun x => f2 x = f2 x2 :=
    mem_filter.mpr ⟨m1, g2.trans e2⟩
  refine ⟨(h3 x m2).trans_eq e3.symm, fun g3 => ?_⟩
  exact h4 x (mem_filter.mpr ⟨m2, g3.trans e3⟩)

/-- 辅助引理（T3.8）：字典序更大的点不在集合里。 -/
theorem not_mem_of_lex_gt {α : Type*} {S : Finset α} {f1 f2 f3 f4 : α → ℕ} {x0 y : α}
    (hmax : ∀ x ∈ S, f1 x ≤ f1 x0 ∧ (f1 x = f1 x0 → f2 x ≤ f2 x0 ∧
      (f2 x = f2 x0 → f3 x ≤ f3 x0 ∧ (f3 x = f3 x0 → f4 x ≤ f4 x0))))
    (h1 : f1 x0 ≤ f1 y)
    (h : f2 x0 < f2 y ∨ (f2 x0 = f2 y ∧ (f3 x0 < f3 y ∨ (f3 x0 = f3 y ∧ f4 x0 < f4 y)))) :
    y ∉ S := by
  intro hy
  obtain ⟨g1, g2⟩ := hmax y hy
  obtain ⟨g2', g3⟩ := g2 (le_antisymm g1 h1)
  rcases h with h | ⟨e2, h⟩
  · omega
  · obtain ⟨g3', g4⟩ := g3 e2.symm
    rcases h with h | ⟨e3, h⟩
    · omega
    · have := g4 e3.symm
      omega

/-- 辅助引理（T3.8）：第一个指标更大的点不在集合里。 -/
theorem not_mem_of_f1_gt {α : Type*} {S : Finset α} {f1 f2 f3 f4 : α → ℕ} {x0 y : α}
    (hmax : ∀ x ∈ S, f1 x ≤ f1 x0 ∧ (f1 x = f1 x0 → f2 x ≤ f2 x0 ∧
      (f2 x = f2 x0 → f3 x ≤ f3 x0 ∧ (f3 x = f3 x0 → f4 x ≤ f4 x0))))
    (h : f1 x0 < f1 y) : y ∉ S := by
  intro hy
  have := (hmax y hy).1
  omega

/-! ### `U` 的角点论证 -/

/-- 辅助引理（T3.8）：`TU` 的角点 `(a0+3, b0)`、单项式 `k^{i0} m^{j0+1}`。 -/
theorem TU_corner_core (q : ℕ × ℕ →₀ Coef) (a0 b0 i0 j0 : ℕ) (h0 : cf (q (a0, b0)) i0 j0 ≠ 0)
    (n1 : ∀ b, cf (q (a0 + 3, b)) i0 (j0 + 1) = 0)
    (n2 : cf (q (a0 + 2, b0)) i0 (j0 + 1) = 0)
    (n3 : cf (q (a0, b0)) i0 (j0 + 1) = 0) :
    (a0 + 3, b0, i0, j0 + 1) ∈ msupp (TU q) := by
  rw [mem_msupp]
  simp only
  have c1 : 1 ≤ a0 + 3 := by omega
  have c3 : 3 ≤ a0 + 3 := by omega
  have e1 : a0 + 3 - 1 = a0 + 2 := by omega
  have e3 : a0 + 3 - 3 = a0 := by omega
  rw [TU_apply]
  simp only [c1, c3, e1, e3, ↓reduceIte, cf_sub, cf_ite, cf_mulM_succ, n1, n2, n3, ite_self,
    mul_zero, sub_zero, zero_sub]
  simpa using h0

/-- 辅助引理（T3.8）：`TU` 的角点 `(a0, b0+1)`，`b0` 是最大的 `b`。 -/
theorem TU_bcorner_core (q : ℕ × ℕ →₀ Coef) (a0 b0 i0 j0 : ℕ) (h0 : cf (q (a0, b0)) i0 j0 ≠ 0)
    (hb : ∀ a, q (a, b0 + 1) = 0) : (a0, b0 + 1, i0, j0) ∈ msupp (TU q) := by
  rw [mem_msupp]
  simp only
  rw [TU_apply]
  simp only [hb, Nat.add_sub_cancel, show 1 ≤ b0 + 1 by omega, ↓reduceIte, mul_zero, ite_self,
    sub_zero, zero_sub, cf_neg]
  simpa using h0

/-- 辅助引理（T3.8）：`U` 的角点论证（按权 `w` 取最高次项）。 -/
theorem corner_TU (q : ℕ × ℕ →₀ Coef) (w : ℕ → ℕ → ℕ) (hw : ∀ i j, w i j ≤ w i (j + 1))
    (hq : (msupp q).Nonempty) :
    ∃ x0 ∈ msupp q, (∀ x ∈ msupp q, w x.2.2.1 x.2.2.2 ≤ w x0.2.2.1 x0.2.2.2) ∧
      (∀ x ∈ msupp q, w x.2.2.1 x.2.2.2 = w x0.2.2.1 x0.2.2.2 → x.1 ≤ x0.1) ∧
      (x0.1 + 3, x0.2.1, x0.2.2.1, x0.2.2.2 + 1) ∈ msupp (TU q) := by
  obtain ⟨x0, hx0, hmax⟩ := exists_lex_max (msupp q) hq (fun x => w x.2.2.1 x.2.2.2)
    (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2.2)
  refine ⟨x0, hx0, fun x hx => (hmax x hx).1, fun x hx he => ((hmax x hx).2 he).1, ?_⟩
  obtain ⟨a0, b0, i0, j0⟩ := x0
  have hz : ∀ y, y ∉ msupp q → cf (q (y.1, y.2.1)) y.2.2.1 y.2.2.2 = 0 := fun y hy => by
    rw [mem_msupp, not_not] at hy; exact hy
  apply TU_corner_core q a0 b0 i0 j0 (mem_msupp.mp hx0)
  · intro b
    exact hz (a0 + 3, b, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inl (by dsimp only; omega)))
  · exact hz (a0 + 2, b0, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inl (by dsimp only; omega)))
  · exact hz (a0, b0, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inr ⟨rfl, Or.inr ⟨rfl, by dsimp only; omega⟩⟩))

/-- 辅助引理（T3.8）：`U` 的角点论证（`b` 方向）。 -/
theorem bcorner_TU (q : ℕ × ℕ →₀ Coef) (hq : (msupp q).Nonempty) :
    ∃ x0 ∈ msupp q, (∀ x ∈ msupp q, x.2.1 ≤ x0.2.1) ∧
      (x0.1, x0.2.1 + 1, x0.2.2.1, x0.2.2.2) ∈ msupp (TU q) := by
  obtain ⟨x0, hx0, hmax⟩ := (msupp q).exists_max_image (fun x => x.2.1) hq
  refine ⟨x0, hx0, hmax, ?_⟩
  obtain ⟨a0, b0, i0, j0⟩ := x0
  apply TU_bcorner_core q a0 b0 i0 j0 (mem_msupp.mp hx0)
  intro a
  by_contra hne
  obtain ⟨i, j, hij⟩ := exists_cf_ne_zero hne
  have := hmax (a, b0 + 1, i, j) (mem_msupp.mpr hij)
  dsimp only at this
  omega

/-- 辅助引理（T3.8）：盒子里的关系 `Q·L1`，`Q` 的支撑在 `[0..A−3] × [0..B−1]`。 -/
theorem TU_box_bounds {q : ℕ × ℕ →₀ Coef} {A B : ℕ} {T : Finset (ℕ × ℕ)}
    (h : ∀ x ∈ msupp (TU q), x ∈ range (A + 1) ×ˢ range (B + 1) ×ˢ T) :
    ∀ x ∈ msupp q, x.1 + 3 ≤ A ∧ x.2.1 + 1 ≤ B := by
  intro x hx
  have hq : (msupp q).Nonempty := ⟨x, hx⟩
  obtain ⟨x0, _, _, ha, hc⟩ := corner_TU q (fun _ _ => 0) (fun _ _ => le_rfl) hq
  obtain ⟨x1, _, hb, hc1⟩ := bcorner_TU q hq
  have h1 := h _ hc
  have h2 := h _ hc1
  simp only [mem_product, mem_range] at h1 h2
  obtain ⟨h1a, -, -⟩ := h1
  obtain ⟨-, h2b, -⟩ := h2
  have := ha x hx rfl
  have := hb x hx
  omega

/-- 辅助引理（T3.8）：盒子里的关系 `Q·L1`，`Q` 的系数次数比盒子低（按权 `w`）。 -/
theorem TU_box_deg {q : ℕ × ℕ →₀ Coef} {A B : ℕ} {T : Finset (ℕ × ℕ)}
    (h : ∀ x ∈ msupp (TU q), x ∈ range (A + 1) ×ˢ range (B + 1) ×ˢ T)
    (w : ℕ → ℕ → ℕ) (hw : ∀ i j, w i j ≤ w i (j + 1)) :
    ∀ x ∈ msupp q, ∃ i0 j0, (i0, j0 + 1) ∈ T ∧ w x.2.2.1 x.2.2.2 ≤ w i0 j0 := by
  intro x hx
  obtain ⟨x0, _, hw0, _, hc⟩ := corner_TU q w hw ⟨x, hx⟩
  have h1 := h _ hc
  simp only [mem_product, mem_range] at h1
  exact ⟨x0.2.2.1, x0.2.2.2, h1.2.2, hw0 x hx⟩

/-- 辅助引理（T3.8）：`Q·L1 = 0`（`Q ∈ O_U`）蕴含 `Q = 0`。 -/
theorem eq_zero_of_mul_L1 {Q : Module.End ℂ Arr} (hQ : Q ∈ OU) (h : Q * L1 = 0) : Q = 0 := by
  obtain ⟨q, rfl⟩ := exists_normal_form hQ
  rw [normOp_mul_L1] at h
  have h0 := normal_form_unique _ h
  by_cases hq : (msupp q).Nonempty
  · obtain ⟨x0, _, _, _, hc⟩ := corner_TU q (fun _ _ => 0) (fun _ _ => le_rfl) hq
    rw [h0] at hc
    rw [mem_msupp] at hc
    simp at hc
  · rw [not_nonempty_iff_eq_empty] at hq
    rw [eq_zero_of_msupp hq, normOp_zero]

/-! ### `U` 的盒子关系与维数 -/

/-- **T3.8**（`U` 的盒子关系）：盒子 `[0..A] × [0..B]`、系数单项式取自 `T` 的关系空间就是
`Rel(U)` 与盒子之交。 -/
theorem mem_relBoxU_iff (A B : ℕ) (T : Finset (ℕ × ℕ)) (R : Module.End ℂ Arr) :
    R ∈ boxSp A B T ⊓ vanSub Uarr ↔ R ∈ boxSp A B T ∧ R ∈ RelU := by
  constructor
  · rintro ⟨hb, hv⟩
    exact ⟨hb, spanBox_le_OU _ hb, hv⟩
  · rintro ⟨hb, -, hv⟩
    exact ⟨hb, hv⟩

/-- **T3.8**（`U` 的计数论证）：设 `T'` 满足 `(i, j) ∈ T' ⇒ (i, j), (i, j+1) ∈ T`，并且「对每个权 `w`
（`W w`）都有 `(i0, j0+1) ∈ T`、`w(i, j) ≤ w(i0, j0)` 的 `(i0, j0)` ⇒ `(i, j) ∈ T'`」。则盒子关系恰为
`Q·L1`，`Q` 是小盒子 `[0..A−3] × [0..B−1]`、系数单项式取自 `T'` 的算子。 -/
theorem relU_box_iff {A B : ℕ} {T T' : Finset (ℕ × ℕ)}
    (hT' : ∀ i j, (i, j) ∈ T' → (i, j) ∈ T ∧ (i, j + 1) ∈ T)
    (W : (ℕ → ℕ → ℕ) → Prop) (hW : ∀ w, W w → ∀ i j, w i j ≤ w i (j + 1))
    (hWT : ∀ i j, (∀ w, W w → ∃ i0 j0, (i0, j0 + 1) ∈ T ∧ w i j ≤ w i0 j0) → (i, j) ∈ T')
    (R : Module.End ℂ Arr) :
    R ∈ boxSp A B T ⊓ vanSub Uarr ↔
      ∃ Q ∈ spanBox (range (A - 2) ×ˢ range B ×ˢ T'), R = Q * L1 := by
  constructor
  · rintro ⟨hbox, hvan⟩
    have hRel : R ∈ RelU := ⟨spanBox_le_OU _ hbox, hvan⟩
    rw [RelU_eq] at hRel
    obtain ⟨Q, hQ, rfl⟩ := hRel
    obtain ⟨q, rfl⟩ := exists_normal_form hQ
    refine ⟨normOp q, normOp_mem_spanBox fun x hx => ?_, rfl⟩
    rw [normOp_mul_L1] at hbox
    have hsub := msupp_subset_of_mem_spanBox hbox
    obtain ⟨ha, hb⟩ := TU_box_bounds hsub x hx
    have hdeg : (x.2.2.1, x.2.2.2) ∈ T' :=
      hWT _ _ fun w hw => TU_box_deg hsub w (hW w hw) x hx
    simp only [mem_product, mem_range]
    exact ⟨by omega, by omega, hdeg⟩
  · rintro ⟨Q, hQ, rfl⟩
    have hQOU : Q ∈ OU := spanBox_le_OU _ hQ
    refine ⟨?_, ?_⟩
    · obtain ⟨q, rfl⟩ := exists_normal_form hQOU
      have hs : ∀ y ∈ msupp q, y.1 + 3 ≤ A ∧ y.2.1 + 1 ≤ B ∧ (y.2.2.1, y.2.2.2) ∈ T' := by
        intro y hy
        have := msupp_subset_of_mem_spanBox hQ y hy
        simp only [mem_product, mem_range] at this
        exact ⟨by omega, by omega, this.2.2⟩
      rw [normOp_mul_L1]
      apply normOp_mem_spanBox
      intro x hx
      simp only [mem_product, mem_range]
      unfold TU at hx
      rcases mem_msupp_sub hx with hx | hx
      · rcases mem_msupp_sub hx with hx | hx
        · rcases mem_msupp_sub hx with hx | hx
          · obtain ⟨h1, h2, h3⟩ := hs x hx
            exact ⟨by omega, by omega, (hT' _ _ h3).1⟩
          · obtain ⟨-, hb1, hy⟩ := mem_msupp_mapDomain hx
            obtain ⟨h1, h2, h3⟩ := hs _ hy
            dsimp only at h1 h2 h3
            exact ⟨by omega, by omega, (hT' _ _ h3).1⟩
        · obtain ⟨ha1, -, hy⟩ := mem_msupp_mapDomain hx
          obtain ⟨h1, h2, h3⟩ := hs _ hy
          dsimp only at h1 h2 h3
          exact ⟨by omega, by omega, (hT' _ _ h3).1⟩
      · obtain ⟨ha3, -, hy⟩ := mem_msupp_mapDomain hx
        rcases mem_msupp_mulMB hy with hy | ⟨hj, hy⟩
        · obtain ⟨h1, h2, h3⟩ := hs _ hy
          dsimp only at h1 h2 h3
          exact ⟨by omega, by omega, (hT' _ _ h3).1⟩
        · obtain ⟨h1, h2, h3⟩ := hs _ hy
          dsimp only at h1 h2 h3 hj
          have e : x.2.2.2 - 1 + 1 = x.2.2.2 := by omega
          have := (hT' _ _ h3).2
          rw [e] at this
          exact ⟨by omega, by omega, this⟩
    · have : Q * L1 ∈ RelU := by rw [RelU_eq]; exact ⟨Q, hQOU, rfl⟩
      exact this.2

/-- 辅助引理（T3.8）：`U` 的盒子关系空间的维数等于小盒子里单项式的个数。 -/
theorem finrank_relU {A B : ℕ} {T T' : Finset (ℕ × ℕ)}
    (hT' : ∀ i j, (i, j) ∈ T' → (i, j) ∈ T ∧ (i, j + 1) ∈ T)
    (W : (ℕ → ℕ → ℕ) → Prop) (hW : ∀ w, W w → ∀ i j, w i j ≤ w i (j + 1))
    (hWT : ∀ i j, (∀ w, W w → ∃ i0 j0, (i0, j0 + 1) ∈ T ∧ w i j ≤ w i0 j0) → (i, j) ∈ T') :
    Module.finrank ℂ ↥(boxSp A B T ⊓ vanSub Uarr) = (A - 2) * B * T'.card := by
  have heq : boxSp A B T ⊓ vanSub Uarr = LinearMap.range
      ((LinearMap.mulRight ℂ L1).domRestrict (spanBox (range (A - 2) ×ˢ range B ×ˢ T'))) := by
    rw [LinearMap.range_domRestrict]
    ext R
    rw [relU_box_iff hT' W hW hWT, Submodule.mem_map]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
  rw [heq, LinearMap.finrank_range_of_inj, finrank_spanBox, card_product, card_product, card_range,
    card_range, mul_assoc]
  rintro ⟨Q1, h1⟩ ⟨Q2, h2⟩ h
  simp only [LinearMap.domRestrict_apply, LinearMap.mulRight_apply] at h
  have h0 : (Q1 - Q2) * L1 = 0 := by rw [sub_mul, h, sub_self]
  have := eq_zero_of_mul_L1 (sub_mem (spanBox_le_OU _ h1) (spanBox_le_OU _ h2)) h0
  exact Subtype.ext (sub_eq_zero.mp this)

/-! ### 两种次数限制满足的条件 -/

/-- 辅助引理（T3.8）：总次数版的小盒子指数 `i + j < D` 满足 `relU_box_iff` 的第一个条件。 -/
theorem degLe_hT' (D : ℕ) : ∀ i j, (i, j) ∈ degLt D → (i, j) ∈ degLe D ∧ (i, j + 1) ∈ degLe D := by
  intro i j h
  rw [mem_degLt] at h
  rw [mem_degLe, mem_degLe]
  dsimp only at h ⊢
  omega

/-- 辅助引理（T3.8）：总次数的权 `w(i, j) = i + j` 关于 `j` 单调。 -/
theorem degLe_hW : ∀ w, w = (fun i j : ℕ => i + j) → ∀ i j, w i j ≤ w i (j + 1) := by
  rintro w rfl i j
  dsimp only
  omega

/-- 辅助引理（T3.8）：总次数版满足 `relU_box_iff` 的第二个条件。 -/
theorem degLe_hWT (D : ℕ) : ∀ i j, (∀ w, w = (fun i j : ℕ => i + j) →
    ∃ i0 j0, (i0, j0 + 1) ∈ degLe D ∧ w i j ≤ w i0 j0) → (i, j) ∈ degLt D := by
  intro i j h
  obtain ⟨i0, j0, h1, h2⟩ := h _ rfl
  rw [mem_degLe] at h1
  rw [mem_degLt]
  dsimp only at h1 h2 ⊢
  omega

/-- 辅助引理（T3.8）：分次版的小盒子指数 `i ≤ Dk`、`j < Dm` 满足第一个条件。 -/
theorem grT_hT' (Dk Dm : ℕ) : ∀ i j, (i, j) ∈ range (Dk + 1) ×ˢ range Dm →
    (i, j) ∈ grT Dk Dm ∧ (i, j + 1) ∈ grT Dk Dm := by
  intro i j h
  simp only [mem_product, mem_range] at h
  rw [mem_grT, mem_grT]
  dsimp only
  omega

/-- 辅助引理（T3.8）：分次版的两个权 `w = i`、`w = j` 关于 `j` 单调。 -/
theorem grT_hW : ∀ w, (w = (fun i _ : ℕ => i) ∨ w = (fun _ j : ℕ => j)) →
    ∀ i j, w i j ≤ w i (j + 1) := by
  rintro w (rfl | rfl) i j <;> dsimp only <;> omega

/-- 辅助引理（T3.8）：分次版满足第二个条件。 -/
theorem grT_hWT (Dk Dm : ℕ) : ∀ i j, (∀ w, (w = (fun i _ : ℕ => i) ∨ w = (fun _ j : ℕ => j)) →
    ∃ i0 j0, (i0, j0 + 1) ∈ grT Dk Dm ∧ w i j ≤ w i0 j0) →
    (i, j) ∈ range (Dk + 1) ×ˢ range Dm := by
  intro i j h
  obtain ⟨i0, j0, h1, h2⟩ := h _ (Or.inl rfl)
  obtain ⟨i1, j1, h3, h4⟩ := h _ (Or.inr rfl)
  rw [mem_grT] at h1 h3
  simp only [mem_product, mem_range]
  dsimp only at h1 h2 h3 h4
  omega

/-- **T3.8**（`U` 的维数公式，总次数版）：支撑在 `[0..A] × [0..B]`、系数总次数 `≤ D` 的关系空间
（盒子与 `Rel(U)` 之交，见 `mem_relBoxU_iff`）的维数，在 `A ≥ 3`、`B ≥ 1`、`D ≥ 1` 时为
`(A−2)·B·D(D+1)/2`，否则为 0。 -/
theorem finrank_relU_tot (A B D : ℕ) :
    Module.finrank ℂ ↥(boxSp A B (degLe D) ⊓ vanSub Uarr) =
      if 3 ≤ A ∧ 1 ≤ B ∧ 1 ≤ D then (A - 2) * B * (D * (D + 1) / 2) else 0 := by
  rw [finrank_relU (degLe_hT' D) _ degLe_hW (degLe_hWT D), card_degLt]
  split_ifs with h
  · rfl
  · rcases (by omega : A < 3 ∨ B = 0 ∨ D = 0) with h1 | h1 | h1
    · rw [show A - 2 = 0 by omega]; simp
    · subst h1; simp
    · subst h1; simp

/-- **T3.8**（`U` 的维数公式，分次版）：支撑在 `[0..A] × [0..B]`、系数关于 `k` 的次数 `≤ D_k`、
关于 `m` 的次数 `≤ D_m` 的关系空间的维数，在 `A ≥ 3`、`B ≥ 1`、`D_m ≥ 1` 时为 `(A−2)·B·(D_k+1)·D_m`，
否则为 0。 -/
theorem finrank_relU_gr (A B Dk Dm : ℕ) :
    Module.finrank ℂ ↥(boxSp A B (grT Dk Dm) ⊓ vanSub Uarr) =
      if 3 ≤ A ∧ 1 ≤ B ∧ 1 ≤ Dm then (A - 2) * B * ((Dk + 1) * Dm) else 0 := by
  rw [finrank_relU (grT_hT' Dk Dm) _ grT_hW (grT_hWT Dk Dm), card_product, card_range, card_range]
  split_ifs with h
  · rfl
  · rcases (by omega : A < 3 ∨ B = 0 ∨ Dm = 0) with h1 | h1 | h1
    · rw [show A - 2 = 0 by omega]; simp
    · subst h1; simp
    · subst h1; simp

/-! ### `N` 的版本：`Q·L_N` 的正规形 -/

/-- `Q·L_N` 的正规形（`Q` 的正规形为 `q`，`L_N = 1 − X − X·Y − (q−1)·X³·(1+Y)²`）：
`r_{ab} = q_{ab} − q_{a−1,b} − q_{a−1,b−1} − (q−1−b)·q_{a−3,b} − 2(q−b)·q_{a−3,b−1} − (q+1−b)·q_{a−3,b−2}`。 -/
noncomputable def TN (q : ℕ × ℕ →₀ Coef) : ℕ × ℕ →₀ Coef :=
  q - q.mapDomain (sh 1 0) - q.mapDomain (sh 1 1) - (mulMB 1 q).mapDomain (sh 3 0)
    - ((mulMB 1 q).mapDomain (sh 3 1) + (mulMB 1 q).mapDomain (sh 3 1))
    - (mulMB 1 q).mapDomain (sh 3 2)

/-- 辅助引理（T3.8）。 -/
theorem normOp_mul_LN (q : ℕ × ℕ →₀ Coef) : normOp q * LN = normOp (TN q) := by
  have e1 : normOp q * opX = normOp (q.mapDomain (sh 1 0)) := by
    rw [← normOp_mul_XY, pow_one, pow_zero, mul_one]
  have e2 : normOp q * (opX * opEinv) = normOp (q.mapDomain (sh 1 1)) := by
    rw [← normOp_mul_XY, pow_one, pow_one]
  have eM : normOp q * mulOp (cM - 1) = normOp (mulMB 1 q) := by
    rw [← normOp_mul_cM, Nat.cast_one]
  have e3 : normOp q * (mulOp (cM - 1) * opX ^ 3 * (1 + opEinv) ^ 2) =
      normOp ((mulMB 1 q).mapDomain (sh 3 0)) + (normOp ((mulMB 1 q).mapDomain (sh 3 1)) +
        normOp ((mulMB 1 q).mapDomain (sh 3 1))) + normOp ((mulMB 1 q).mapDomain (sh 3 2)) := by
    rw [← normOp_mul_XY, ← normOp_mul_XY, ← normOp_mul_XY, ← eM]
    simp only [pow_zero, pow_one, mul_one, sq, add_mul, mul_add, one_mul, mul_assoc]
    abel
  rw [LN, mul_sub, mul_sub, mul_sub, mul_one, e1, e2, e3, TN, normOp_sub, normOp_sub, normOp_sub,
    normOp_sub, normOp_sub, normOp_add]
  abel

/-- 辅助引理（T3.8）：`TN` 的分量。 -/
theorem TN_apply (q : ℕ × ℕ →₀ Coef) (a b : ℕ) :
    TN q (a, b) = q (a, b) - (if 1 ≤ a then q (a - 1, b) else 0)
      - (if 1 ≤ a ∧ 1 ≤ b then q (a - 1, b - 1) else 0)
      - (if 3 ≤ a then (cM - ((b + 1 : ℕ) : Coef)) * q (a - 3, b) else 0)
      - ((if 3 ≤ a ∧ 1 ≤ b then (cM - ((b - 1 + 1 : ℕ) : Coef)) * q (a - 3, b - 1) else 0)
        + (if 3 ≤ a ∧ 1 ≤ b then (cM - ((b - 1 + 1 : ℕ) : Coef)) * q (a - 3, b - 1) else 0))
      - (if 3 ≤ a ∧ 2 ≤ b then (cM - ((b - 2 + 1 : ℕ) : Coef)) * q (a - 3, b - 2) else 0) := by
  simp only [TN, Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, mapDomain_sh_apply,
    mulMB_apply, zero_le, and_true, Nat.sub_zero]

/-! ### `N` 的角点论证 -/

/-- 辅助引理（T3.8）：`TN` 的角点 `(a0+3, b0+2)`、单项式 `k^{i0} q^{j0+1}`。 -/
theorem TN_corner_core (q : ℕ × ℕ →₀ Coef) (a0 b0 i0 j0 : ℕ) (h0 : cf (q (a0, b0)) i0 j0 ≠ 0)
    (n1 : cf (q (a0 + 3, b0 + 2)) i0 (j0 + 1) = 0)
    (n2 : cf (q (a0 + 2, b0 + 2)) i0 (j0 + 1) = 0)
    (n3 : cf (q (a0 + 2, b0 + 1)) i0 (j0 + 1) = 0)
    (n4 : cf (q (a0, b0 + 2)) i0 j0 = 0)
    (n5 : cf (q (a0, b0 + 2)) i0 (j0 + 1) = 0)
    (n6 : cf (q (a0, b0 + 1)) i0 j0 = 0)
    (n7 : cf (q (a0, b0 + 1)) i0 (j0 + 1) = 0)
    (n8 : cf (q (a0, b0)) i0 (j0 + 1) = 0) :
    (a0 + 3, b0 + 2, i0, j0 + 1) ∈ msupp (TN q) := by
  rw [mem_msupp]
  simp only
  have c1 : 1 ≤ a0 + 3 := by omega
  have c3 : 3 ≤ a0 + 3 := by omega
  have d1 : 1 ≤ b0 + 2 := by omega
  have d2 : 2 ≤ b0 + 2 := by omega
  have e1 : a0 + 3 - 1 = a0 + 2 := by omega
  have e3 : a0 + 3 - 3 = a0 := by omega
  have f1 : b0 + 2 - 1 = b0 + 1 := by omega
  have f2 : b0 + 2 - 2 = b0 := by omega
  rw [TN_apply]
  simp only [c1, c3, d1, d2, e1, e3, f1, f2, and_self, ↓reduceIte, cf_sub, cf_add, cf_mulM_succ,
    n1, n2, n3, n4, n5, n6, n7, n8, mul_zero, sub_zero, zero_sub, add_zero, sub_self]
  simpa using h0

/-- 辅助引理（T3.8）：`N` 的角点论证（按权 `w` 取最高次项）。 -/
theorem corner_TN (q : ℕ × ℕ →₀ Coef) (w : ℕ → ℕ → ℕ) (hw : ∀ i j, w i j ≤ w i (j + 1))
    (hq : (msupp q).Nonempty) :
    ∃ x0 ∈ msupp q, (∀ x ∈ msupp q, w x.2.2.1 x.2.2.2 ≤ w x0.2.2.1 x0.2.2.2) ∧
      (∀ x ∈ msupp q, w x.2.2.1 x.2.2.2 = w x0.2.2.1 x0.2.2.2 → x.1 ≤ x0.1) ∧
      (x0.1 + 3, x0.2.1 + 2, x0.2.2.1, x0.2.2.2 + 1) ∈ msupp (TN q) := by
  obtain ⟨x0, hx0, hmax⟩ := exists_lex_max (msupp q) hq (fun x => w x.2.2.1 x.2.2.2)
    (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2.2)
  refine ⟨x0, hx0, fun x hx => (hmax x hx).1, fun x hx he => ((hmax x hx).2 he).1, ?_⟩
  obtain ⟨a0, b0, i0, j0⟩ := x0
  have hz : ∀ y, y ∉ msupp q → cf (q (y.1, y.2.1)) y.2.2.1 y.2.2.2 = 0 := fun y hy => by
    rw [mem_msupp, not_not] at hy; exact hy
  apply TN_corner_core q a0 b0 i0 j0 (mem_msupp.mp hx0)
  · exact hz (a0 + 3, b0 + 2, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inl (by dsimp only; omega)))
  · exact hz (a0 + 2, b0 + 2, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inl (by dsimp only; omega)))
  · exact hz (a0 + 2, b0 + 1, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inl (by dsimp only; omega)))
  · exact hz (a0, b0 + 2, i0, j0)
      (not_mem_of_lex_gt hmax le_rfl (Or.inr ⟨rfl, Or.inl (by dsimp only; omega)⟩))
  · exact hz (a0, b0 + 2, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inr ⟨rfl, Or.inl (by dsimp only; omega)⟩))
  · exact hz (a0, b0 + 1, i0, j0)
      (not_mem_of_lex_gt hmax le_rfl (Or.inr ⟨rfl, Or.inl (by dsimp only; omega)⟩))
  · exact hz (a0, b0 + 1, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inr ⟨rfl, Or.inl (by dsimp only; omega)⟩))
  · exact hz (a0, b0, i0, j0 + 1)
      (not_mem_of_lex_gt hmax (hw i0 j0) (Or.inr ⟨rfl, Or.inr ⟨rfl, by dsimp only; omega⟩⟩))

/-- 辅助引理（T3.8）：`N` 的角点论证（`b` 方向）。 -/
theorem bcorner_TN (q : ℕ × ℕ →₀ Coef) (hq : (msupp q).Nonempty) :
    ∃ x0 ∈ msupp q, (∀ x ∈ msupp q, x.2.1 ≤ x0.2.1) ∧
      (x0.1 + 3, x0.2.1 + 2, x0.2.2.1, x0.2.2.2 + 1) ∈ msupp (TN q) := by
  obtain ⟨x0, hx0, hmax⟩ := exists_lex_max (msupp q) hq (fun x => x.2.1) (fun x => x.1)
    (fun _ => 0) (fun x => x.2.2.2)
  refine ⟨x0, hx0, fun x hx => (hmax x hx).1, ?_⟩
  obtain ⟨a0, b0, i0, j0⟩ := x0
  have hz : ∀ y, y ∉ msupp q → cf (q (y.1, y.2.1)) y.2.2.1 y.2.2.2 = 0 := fun y hy => by
    rw [mem_msupp, not_not] at hy; exact hy
  apply TN_corner_core q a0 b0 i0 j0 (mem_msupp.mp hx0)
  · exact hz (a0 + 3, b0 + 2, i0, j0 + 1) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0 + 2, b0 + 2, i0, j0 + 1) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0 + 2, b0 + 1, i0, j0 + 1) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0, b0 + 2, i0, j0) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0, b0 + 2, i0, j0 + 1) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0, b0 + 1, i0, j0) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0, b0 + 1, i0, j0 + 1) (not_mem_of_f1_gt hmax (by dsimp only; omega))
  · exact hz (a0, b0, i0, j0 + 1)
      (not_mem_of_lex_gt hmax le_rfl (Or.inr ⟨rfl, Or.inr ⟨rfl, by dsimp only; omega⟩⟩))

/-- 辅助引理（T3.8）：盒子里的关系 `Q·L_N`，`Q` 的支撑在 `[0..A−3] × [0..B−2]`。 -/
theorem TN_box_bounds {q : ℕ × ℕ →₀ Coef} {A B : ℕ} {T : Finset (ℕ × ℕ)}
    (h : ∀ x ∈ msupp (TN q), x ∈ range (A + 1) ×ˢ range (B + 1) ×ˢ T) :
    ∀ x ∈ msupp q, x.1 + 3 ≤ A ∧ x.2.1 + 2 ≤ B := by
  intro x hx
  have hq : (msupp q).Nonempty := ⟨x, hx⟩
  obtain ⟨x0, _, _, ha, hc⟩ := corner_TN q (fun _ _ => 0) (fun _ _ => le_rfl) hq
  obtain ⟨x1, _, hb, hc1⟩ := bcorner_TN q hq
  have h1 := h _ hc
  have h2 := h _ hc1
  simp only [mem_product, mem_range] at h1 h2
  obtain ⟨h1a, -, -⟩ := h1
  obtain ⟨-, h2b, -⟩ := h2
  have := ha x hx rfl
  have := hb x hx
  omega

/-- 辅助引理（T3.8）：盒子里的关系 `Q·L_N`，`Q` 的系数次数比盒子低（按权 `w`）。 -/
theorem TN_box_deg {q : ℕ × ℕ →₀ Coef} {A B : ℕ} {T : Finset (ℕ × ℕ)}
    (h : ∀ x ∈ msupp (TN q), x ∈ range (A + 1) ×ˢ range (B + 1) ×ˢ T)
    (w : ℕ → ℕ → ℕ) (hw : ∀ i j, w i j ≤ w i (j + 1)) :
    ∀ x ∈ msupp q, ∃ i0 j0, (i0, j0 + 1) ∈ T ∧ w x.2.2.1 x.2.2.2 ≤ w i0 j0 := by
  intro x hx
  obtain ⟨x0, _, hw0, _, hc⟩ := corner_TN q w hw ⟨x, hx⟩
  have h1 := h _ hc
  simp only [mem_product, mem_range] at h1
  exact ⟨x0.2.2.1, x0.2.2.2, h1.2.2, hw0 x hx⟩

/-- 辅助引理（T3.8）：`Q·L_N = 0`（`Q ∈ O_N`）蕴含 `Q = 0`。 -/
theorem eq_zero_of_mul_LN {Q : Module.End ℂ Arr} (hQ : Q ∈ OU) (h : Q * LN = 0) : Q = 0 := by
  obtain ⟨q, rfl⟩ := exists_normal_form hQ
  rw [normOp_mul_LN] at h
  have h0 := normal_form_unique _ h
  by_cases hq : (msupp q).Nonempty
  · obtain ⟨x0, _, _, _, hc⟩ := corner_TN q (fun _ _ => 0) (fun _ _ => le_rfl) hq
    rw [h0] at hc
    rw [mem_msupp] at hc
    simp at hc
  · rw [not_nonempty_iff_eq_empty] at hq
    rw [eq_zero_of_msupp hq, normOp_zero]

/-! ### `N` 的盒子关系与维数 -/

/-- **T3.8**（`N` 的盒子关系）：盒子 `[0..A] × [0..B]`（`Y` 的次数 `≤ B`）、系数单项式取自 `T` 的关系空间
就是 `Rel(N)` 与盒子之交。 -/
theorem mem_relBoxN_iff (A B : ℕ) (T : Finset (ℕ × ℕ)) (R : Module.End ℂ Arr) :
    R ∈ boxSp A B T ⊓ vanSub Narr ↔ R ∈ boxSp A B T ∧ R ∈ RelN := by
  constructor
  · rintro ⟨hb, hv⟩
    exact ⟨hb, spanBox_le_OU _ hb, hv⟩
  · rintro ⟨hb, -, hv⟩
    exact ⟨hb, hv⟩

/-- **T3.8**（`N` 的计数论证）：条件同 `relU_box_iff`。则 `N` 的盒子关系恰为 `Q·L_N`，`Q` 是小盒子
`[0..A−3] × [0..B−2]`、系数单项式取自 `T'` 的算子。 -/
theorem relN_box_iff {A B : ℕ} {T T' : Finset (ℕ × ℕ)}
    (hT' : ∀ i j, (i, j) ∈ T' → (i, j) ∈ T ∧ (i, j + 1) ∈ T)
    (W : (ℕ → ℕ → ℕ) → Prop) (hW : ∀ w, W w → ∀ i j, w i j ≤ w i (j + 1))
    (hWT : ∀ i j, (∀ w, W w → ∃ i0 j0, (i0, j0 + 1) ∈ T ∧ w i j ≤ w i0 j0) → (i, j) ∈ T')
    (R : Module.End ℂ Arr) :
    R ∈ boxSp A B T ⊓ vanSub Narr ↔
      ∃ Q ∈ spanBox (range (A - 2) ×ˢ range (B - 1) ×ˢ T'), R = Q * LN := by
  constructor
  · rintro ⟨hbox, hvan⟩
    have hRel : R ∈ RelN := ⟨spanBox_le_OU _ hbox, hvan⟩
    rw [RelN_eq] at hRel
    obtain ⟨Q, hQ, rfl⟩ := hRel
    obtain ⟨q, rfl⟩ := exists_normal_form hQ
    refine ⟨normOp q, normOp_mem_spanBox fun x hx => ?_, rfl⟩
    rw [normOp_mul_LN] at hbox
    have hsub := msupp_subset_of_mem_spanBox hbox
    obtain ⟨ha, hb⟩ := TN_box_bounds hsub x hx
    have hdeg : (x.2.2.1, x.2.2.2) ∈ T' :=
      hWT _ _ fun w hw => TN_box_deg hsub w (hW w hw) x hx
    simp only [mem_product, mem_range]
    exact ⟨by omega, by omega, hdeg⟩
  · rintro ⟨Q, hQ, rfl⟩
    have hQOU : Q ∈ OU := spanBox_le_OU _ hQ
    refine ⟨?_, ?_⟩
    · obtain ⟨q, rfl⟩ := exists_normal_form hQOU
      have hs : ∀ y ∈ msupp q, y.1 + 3 ≤ A ∧ y.2.1 + 2 ≤ B ∧ (y.2.2.1, y.2.2.2) ∈ T' := by
        intro y hy
        have := msupp_subset_of_mem_spanBox hQ y hy
        simp only [mem_product, mem_range] at this
        exact ⟨by omega, by omega, this.2.2⟩
      rw [normOp_mul_LN]
      apply normOp_mem_spanBox
      intro x hx
      simp only [mem_product, mem_range]
      have hS : ∀ s t, s ≤ 3 → t ≤ 2 → x ∈ msupp (q.mapDomain (sh s t)) →
          x.1 < A + 1 ∧ x.2.1 < B + 1 ∧ x.2.2 ∈ T := by
        intro s t hs3 ht2 hx'
        obtain ⟨h1, h2, hy⟩ := mem_msupp_mapDomain hx'
        obtain ⟨g1, g2, g3⟩ := hs _ hy
        dsimp only at g1 g2 g3
        exact ⟨by omega, by omega, (hT' _ _ g3).1⟩
      have hM : ∀ t, t ≤ 2 → x ∈ msupp ((mulMB 1 q).mapDomain (sh 3 t)) →
          x.1 < A + 1 ∧ x.2.1 < B + 1 ∧ x.2.2 ∈ T := by
        intro t ht2 hx'
        obtain ⟨h1, h2, hy⟩ := mem_msupp_mapDomain hx'
        rcases mem_msupp_mulMB hy with hy | ⟨hj, hy⟩
        · obtain ⟨g1, g2, g3⟩ := hs _ hy
          dsimp only at g1 g2 g3
          exact ⟨by omega, by omega, (hT' _ _ g3).1⟩
        · obtain ⟨g1, g2, g3⟩ := hs _ hy
          dsimp only at g1 g2 g3 hj
          have e : x.2.2.2 - 1 + 1 = x.2.2.2 := by omega
          have := (hT' _ _ g3).2
          rw [e] at this
          exact ⟨by omega, by omega, this⟩
      unfold TN at hx
      rcases mem_msupp_sub hx with hx | hx
      · rcases mem_msupp_sub hx with hx | hx
        · rcases mem_msupp_sub hx with hx | hx
          · rcases mem_msupp_sub hx with hx | hx
            · rcases mem_msupp_sub hx with hx | hx
              · obtain ⟨g1, g2, g3⟩ := hs x hx
                exact ⟨by omega, by omega, (hT' _ _ g3).1⟩
              · exact hS 1 0 (by norm_num) (by norm_num) hx
            · exact hS 1 1 (by norm_num) (by norm_num) hx
          · exact hM 0 (by norm_num) hx
        · rcases mem_msupp_add hx with hx | hx
          · exact hM 1 (by norm_num) hx
          · exact hM 1 (by norm_num) hx
      · exact hM 2 (by norm_num) hx
    · have : Q * LN ∈ RelN := by rw [RelN_eq]; exact ⟨Q, hQOU, rfl⟩
      exact this.2

/-- 辅助引理（T3.8）：`N` 的盒子关系空间的维数等于小盒子里单项式的个数。 -/
theorem finrank_relN {A B : ℕ} {T T' : Finset (ℕ × ℕ)}
    (hT' : ∀ i j, (i, j) ∈ T' → (i, j) ∈ T ∧ (i, j + 1) ∈ T)
    (W : (ℕ → ℕ → ℕ) → Prop) (hW : ∀ w, W w → ∀ i j, w i j ≤ w i (j + 1))
    (hWT : ∀ i j, (∀ w, W w → ∃ i0 j0, (i0, j0 + 1) ∈ T ∧ w i j ≤ w i0 j0) → (i, j) ∈ T') :
    Module.finrank ℂ ↥(boxSp A B T ⊓ vanSub Narr) = (A - 2) * (B - 1) * T'.card := by
  have heq : boxSp A B T ⊓ vanSub Narr = LinearMap.range
      ((LinearMap.mulRight ℂ LN).domRestrict (spanBox (range (A - 2) ×ˢ range (B - 1) ×ˢ T'))) := by
    rw [LinearMap.range_domRestrict]
    ext R
    rw [relN_box_iff hT' W hW hWT, Submodule.mem_map]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
  rw [heq, LinearMap.finrank_range_of_inj, finrank_spanBox, card_product, card_product, card_range,
    card_range, mul_assoc]
  rintro ⟨Q1, h1⟩ ⟨Q2, h2⟩ h
  simp only [LinearMap.domRestrict_apply, LinearMap.mulRight_apply] at h
  have h0 : (Q1 - Q2) * LN = 0 := by rw [sub_mul, h, sub_self]
  have := eq_zero_of_mul_LN (sub_mem (spanBox_le_OU _ h1) (spanBox_le_OU _ h2)) h0
  exact Subtype.ext (sub_eq_zero.mp this)

/-- **T3.8**（`N` 的维数公式，总次数版）：支撑在 `[0..A] × [0..B]`（`X` 的次数 `≤ A`、`Y` 的次数 `≤ B`）、
系数（`k`、`q` 的多项式）总次数 `≤ D` 的关系空间（盒子与 `Rel(N)` 之交，见 `mem_relBoxN_iff`）的维数，
在 `A ≥ 3`、`B ≥ 2`、`D ≥ 1` 时为 `(A−2)(B−1)·D(D+1)/2`，否则为 0。 -/
theorem finrank_relN_tot (A B D : ℕ) :
    Module.finrank ℂ ↥(boxSp A B (degLe D) ⊓ vanSub Narr) =
      if 3 ≤ A ∧ 2 ≤ B ∧ 1 ≤ D then (A - 2) * (B - 1) * (D * (D + 1) / 2) else 0 := by
  rw [finrank_relN (degLe_hT' D) _ degLe_hW (degLe_hWT D), card_degLt]
  split_ifs with h
  · rfl
  · rcases (by omega : A < 3 ∨ B < 2 ∨ D = 0) with h1 | h1 | h1
    · rw [show A - 2 = 0 by omega]; simp
    · rw [show B - 1 = 0 by omega]; simp
    · subst h1; simp

/-- **T3.8**（`N` 的维数公式，分次版）：支撑在 `[0..A] × [0..B]`、系数关于 `k` 的次数 `≤ D_k`、关于 `q`
的次数 `≤ D_q` 的关系空间的维数，在 `A ≥ 3`、`B ≥ 2`、`D_q ≥ 1` 时为 `(A−2)(B−1)(D_k+1)·D_q`，
否则为 0。 -/
theorem finrank_relN_gr (A B Dk Dq : ℕ) :
    Module.finrank ℂ ↥(boxSp A B (grT Dk Dq) ⊓ vanSub Narr) =
      if 3 ≤ A ∧ 2 ≤ B ∧ 1 ≤ Dq then (A - 2) * (B - 1) * ((Dk + 1) * Dq) else 0 := by
  rw [finrank_relN (grT_hT' Dk Dq) _ grT_hW (grT_hWT Dk Dq), card_product, card_range, card_range]
  split_ifs with h
  · rfl
  · rcases (by omega : A < 3 ∨ B < 2 ∨ Dq = 0) with h1 | h1 | h1
    · rw [show A - 2 = 0 by omega]; simp
    · rw [show B - 1 = 0 by omega]; simp
    · subst h1; simp

/-- **T3.8**（`U` 的计数，总次数版）：支撑在 `[0..A] × [0..B]`、系数总次数 `≤ D` 的关系恰为 `Q·L1`，
`Q` 的支撑在 `[0..A−3] × [0..B−1]`、系数总次数 `≤ D−1`（`D = 0` 或 `A < 3` 或 `B = 0` 时小盒子为空）。 -/
theorem relU_box_tot_iff (A B D : ℕ) (R : Module.End ℂ Arr) :
    R ∈ boxSp A B (degLe D) ⊓ vanSub Uarr ↔
      ∃ Q ∈ spanBox (range (A - 2) ×ˢ range B ×ˢ degLt D), R = Q * L1 :=
  relU_box_iff (degLe_hT' D) _ degLe_hW (degLe_hWT D) R

/-- **T3.8**（`N` 的计数，总次数版）：支撑在 `[0..A] × [0..B]`、系数总次数 `≤ D` 的关系恰为 `Q·L_N`，
`Q` 的支撑在 `[0..A−3] × [0..B−2]`、系数总次数 `≤ D−1`。 -/
theorem relN_box_tot_iff (A B D : ℕ) (R : Module.End ℂ Arr) :
    R ∈ boxSp A B (degLe D) ⊓ vanSub Narr ↔
      ∃ Q ∈ spanBox (range (A - 2) ×ˢ range (B - 1) ×ˢ degLt D), R = Q * LN :=
  relN_box_iff (degLe_hT' D) _ degLe_hW (degLe_hWT D) R

end A207123
