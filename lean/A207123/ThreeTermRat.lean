import A207123.ThreeTerm

/-!
# 论文推论 5.7：有理函数系数的陈述（取公分母这一步）

论文推论 5.7 的系数 `c_i` 是 `(k, m)` 的有理函数，假设只要求 `T` 在象限中「系数都有定义」的点上零化 `U`。
`ThreeTerm.lean` 把分母乘掉，系数写成 `n_i/Δ`。本文件补上取公分母这一步，按论文原样陈述：

* `RatCoef = FractionRing Coef` 是有理函数域 `ℂ(k, m)`（`Coef = ℂ[k][m]` 是整环）。
* `HasValueAt c x y z`：`c` 有一个表示 `a/b`（`a, b ∈ ℂ[k, m]`），分母 `b(x, y) ≠ 0`，且 `z = a(x, y)/b(x, y)`；
  即 `c` 在 `(x, y)` 有定义、值为 `z`。`HasValueAt.unique`：值与所取的表示无关。
* `not_annihilate_three_terms_rat`：推论 5.7。`not_annihilate_two_terms_rat`：「`U` 没有至多两项的递推」。
  `not_annihilate_kauers_rat`：Kauers 2007 定义 3 的生成元形状 `u + v·S^{(v₁,v₂)} − w·S^{(w₁,w₂)}`。
  与 `ThreeTerm.lean` 一样，`f` 是 `U` 在 `ℤ²` 上的任意延拓，象限取在 `ℤ²` 里。

**证明**（同论文推论 5.7 的证明）：取表示 `c_i = a_i/b_i`（`b_i ≠ 0`），公分母 `Δ = b₀b₁b₂`，
`n_i = a_i·∏_{j≠i} b_j`。在 `Δ(k, m) ≠ 0` 的点上三个 `b_i(k, m)` 都不为 0，`c_i` 有定义、值为
`a_i(k, m)/b_i(k, m)`，关系乘以 `Δ(k, m)` 就是 `ThreeTerm.lean` 的假设；`c_i ≠ 0` 推出 `a_i ≠ 0`，而 `ℂ[k, m]`
是整环，所以 `n_i ≠ 0`。

由 Kauers 定义 3 推出「生成元在系数有定义的点上零化序列」这一步仍是书面的（论文注 5.8）。
-/

open Polynomial

namespace A207123

/-- `(k, m)` 的有理函数域 `ℂ(k, m)`：二元多项式环 `Coef = ℂ[k][m]` 的分式域。 -/
abbrev RatCoef := FractionRing Coef

/-- 有理函数 `c` 在点 `(x, y)` 有定义、值为 `z`：`c` 有一个表示 `a/b`（`a, b ∈ ℂ[k, m]`），分母在该点不为 0，
且 `z = a(x, y)/b(x, y)`。 -/
def HasValueAt (c : RatCoef) (x y z : ℂ) : Prop :=
  ∃ a b : Coef, b.evalEval x y ≠ 0 ∧ algebraMap Coef RatCoef a = c * algebraMap Coef RatCoef b ∧
    z = a.evalEval x y / b.evalEval x y

/-- 辅助引理（推论 5.7）：有理函数在一点的值与所取的表示无关。 -/
theorem HasValueAt.unique {c : RatCoef} {x y z z' : ℂ} (h : HasValueAt c x y z)
    (h' : HasValueAt c x y z') : z = z' := by
  obtain ⟨a, b, hb, e, rfl⟩ := h
  obtain ⟨a', b', hb', e', rfl⟩ := h'
  -- `a·b' = a'·b` 在 `ℂ[k, m]` 中成立
  have key : a * b' = a' * b := by
    apply IsFractionRing.injective Coef RatCoef
    rw [map_mul, map_mul, e, e']
    ring
  have hv := congrArg (fun p : Coef => p.evalEval x y) key
  simp only [evalEval_mul] at hv
  rw [div_eq_div_iff hb hb']
  exact hv

/-- 辅助引理（推论 5.7）：每个有理函数都有表示 `a/b`，`b ≠ 0`。 -/
theorem exists_rep (c : RatCoef) :
    ∃ a b : Coef, b ≠ 0 ∧ algebraMap Coef RatCoef a = c * algebraMap Coef RatCoef b := by
  obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (nonZeroDivisors Coef) c
  exact ⟨a, b, nonZeroDivisors.ne_zero b.2, e.symm⟩

/-- 辅助引理（推论 5.7）：`c = a/b ≠ 0`（`b ≠ 0`）时 `a ≠ 0`。 -/
theorem num_ne_zero {c : RatCoef} {a b : Coef} (hc : c ≠ 0) (hb : b ≠ 0)
    (e : algebraMap Coef RatCoef a = c * algebraMap Coef RatCoef b) : a ≠ 0 := by
  rintro rfl
  rw [map_zero, eq_comm, mul_eq_zero] at e
  rcases e with h | h
  · exact hc h
  · exact hb (IsFractionRing.to_map_eq_zero_iff.mp h)

/-- 辅助引理（推论 5.7）：分母在该点不为 0 时，`a/b` 在该点有定义，值是 `a(x, y)/b(x, y)`。 -/
theorem hasValueAt_of_rep {c : RatCoef} {a b : Coef}
    (e : algebraMap Coef RatCoef a = c * algebraMap Coef RatCoef b) {x y : ℂ} (hb : b.evalEval x y ≠ 0) :
    HasValueAt c x y (a.evalEval x y / b.evalEval x y) :=
  ⟨a, b, hb, e, rfl⟩

/-- **推论 5.7**（论文原样，有理函数系数）：设 `v₀, v₁, v₂ ∈ ℤ²` 两两不同，`|det(v₁ − v₀, v₂ − v₀)| ≤ 2`，有理函数
`c₀, c₁, c₂` 不全为 0。则没有象限 `k ≥ k₀, m ≥ m₀`（`k, m ∈ ℤ`），使得在其中三个系数都有定义的每个点上
`c₀(k, m)·f(k + s₀, m + t₀) + c₁(k, m)·f(k + s₁, m + t₁) + c₂(k, m)·f(k + s₂, m + t₂) = 0`
（`f` 是 `U` 在 `ℤ²` 上的任意延拓，系数的值 `z_i` 由 `HasValueAt` 给出）。 -/
theorem not_annihilate_three_terms_rat (f : ℤ → ℤ → ℂ) (hf : ∀ k m : ℕ, f k m = U k m)
    {v0 v1 v2 : ℤ × ℤ} (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2)
    (hdet : |(v1.1 - v0.1) * (v2.2 - v0.2) - (v1.2 - v0.2) * (v2.1 - v0.1)| ≤ 2)
    {c0 c1 c2 : RatCoef} (hc : c0 ≠ 0 ∨ c1 ≠ 0 ∨ c2 ≠ 0) (k0 m0 : ℤ) :
    ¬ ∀ k m : ℤ, k0 ≤ k → m0 ≤ m → ∀ z0 z1 z2 : ℂ,
      HasValueAt c0 k m z0 → HasValueAt c1 k m z1 → HasValueAt c2 k m z2 →
        z0 * f (k + v0.1) (m + v0.2) + z1 * f (k + v1.1) (m + v1.2) + z2 * f (k + v2.1) (m + v2.2) = 0 := by
  intro h
  obtain ⟨a0, b0, hb0, e0⟩ := exists_rep c0
  obtain ⟨a1, b1, hb1, e1⟩ := exists_rep c1
  obtain ⟨a2, b2, hb2, e2⟩ := exists_rep c2
  refine not_annihilate_three_terms f hf h01 h02 h12 hdet (n0 := a0 * b1 * b2) (n1 := a1 * b0 * b2)
    (n2 := a2 * b0 * b1) (Δ := b0 * b1 * b2) ?_ (mul_ne_zero (mul_ne_zero hb0 hb1) hb2) k0 m0 ?_
  · rcases hc with hc | hc | hc
    · exact Or.inl (mul_ne_zero (mul_ne_zero (num_ne_zero hc hb0 e0) hb1) hb2)
    · exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (num_ne_zero hc hb1 e1) hb0) hb2))
    · exact Or.inr (Or.inr (mul_ne_zero (mul_ne_zero (num_ne_zero hc hb2 e2) hb0) hb1))
  · intro k m hk hm hΔ
    simp only [evalEval_mul] at hΔ ⊢
    have hB2 := right_ne_zero_of_mul hΔ
    have hB0 := left_ne_zero_of_mul (left_ne_zero_of_mul hΔ)
    have hB1 := right_ne_zero_of_mul (left_ne_zero_of_mul hΔ)
    have hrel := h k m hk hm _ _ _ (hasValueAt_of_rep e0 hB0) (hasValueAt_of_rep e1 hB1)
      (hasValueAt_of_rep e2 hB2)
    have hz0 := div_mul_cancel₀ (a0.evalEval (k : ℂ) (m : ℂ)) hB0
    have hz1 := div_mul_cancel₀ (a1.evalEval (k : ℂ) (m : ℂ)) hB1
    have hz2 := div_mul_cancel₀ (a2.evalEval (k : ℂ) (m : ℂ)) hB2
    set B0 := b0.evalEval (k : ℂ) (m : ℂ)
    set B1 := b1.evalEval (k : ℂ) (m : ℂ)
    set B2 := b2.evalEval (k : ℂ) (m : ℂ)
    linear_combination (B0 * B1 * B2) * hrel - (B1 * B2 * f (k + v0.1) (m + v0.2)) * hz0
      - (B0 * B2 * f (k + v1.1) (m + v1.2)) * hz1 - (B0 * B1 * f (k + v2.1) (m + v2.2)) * hz2

/-- **推论 5.7**（「特别地，`U` 没有至多两项的递推」，有理函数系数）：`v₀ ≠ v₁`，有理函数 `c₀, c₁` 不全为 0，
则没有象限使得在其中两个系数都有定义的每个点上 `c₀(k, m)·f(k + s₀, m + t₀) + c₁(k, m)·f(k + s₁, m + t₁) = 0`。 -/
theorem not_annihilate_two_terms_rat (f : ℤ → ℤ → ℂ) (hf : ∀ k m : ℕ, f k m = U k m)
    {v0 v1 : ℤ × ℤ} (h01 : v0 ≠ v1) {c0 c1 : RatCoef} (hc : c0 ≠ 0 ∨ c1 ≠ 0) (k0 m0 : ℤ) :
    ¬ ∀ k m : ℤ, k0 ≤ k → m0 ≤ m → ∀ z0 z1 : ℂ, HasValueAt c0 k m z0 → HasValueAt c1 k m z1 →
      z0 * f (k + v0.1) (m + v0.2) + z1 * f (k + v1.1) (m + v1.2) = 0 := by
  intro h
  obtain ⟨a0, b0, hb0, e0⟩ := exists_rep c0
  obtain ⟨a1, b1, hb1, e1⟩ := exists_rep c1
  refine not_annihilate_two_terms f hf h01 (n0 := a0 * b1) (n1 := a1 * b0) (Δ := b0 * b1) ?_
    (mul_ne_zero hb0 hb1) k0 m0 ?_
  · rcases hc with hc | hc
    · exact Or.inl (mul_ne_zero (num_ne_zero hc hb0 e0) hb1)
    · exact Or.inr (mul_ne_zero (num_ne_zero hc hb1 e1) hb0)
  · intro k m hk hm hΔ
    simp only [evalEval_mul] at hΔ ⊢
    have hB0 := left_ne_zero_of_mul hΔ
    have hB1 := right_ne_zero_of_mul hΔ
    have hrel := h k m hk hm _ _ (hasValueAt_of_rep e0 hB0) (hasValueAt_of_rep e1 hB1)
    have hz0 := div_mul_cancel₀ (a0.evalEval (k : ℂ) (m : ℂ)) hB0
    have hz1 := div_mul_cancel₀ (a1.evalEval (k : ℂ) (m : ℂ)) hB1
    set B0 := b0.evalEval (k : ℂ) (m : ℂ)
    set B1 := b1.evalEval (k : ℂ) (m : ℂ)
    linear_combination (B0 * B1) * hrel - (B1 * f (k + v0.1) (m + v0.2)) * hz0
      - (B0 * f (k + v1.1) (m + v1.2)) * hz1

/-- **推论 5.7**（Kauers 2007 定义 3 的生成元形状，有理函数系数）：`(v₁, v₂)`、`(w₁, w₂)` 是 `ℤ²` 的基
（`|v₁w₂ − v₂w₁| = 1`），有理函数 `u, v, w` 不全为 0，则没有象限使得在其中三个系数都有定义的每个点上
`u(k, m)·f(k, m) + v(k, m)·f(k + v₁, m + v₂) − w(k, m)·f(k + w₁, m + w₂) = 0`。 -/
theorem not_annihilate_kauers_rat (f : ℤ → ℤ → ℂ) (hf : ∀ k m : ℕ, f k m = U k m)
    {v w : ℤ × ℤ} (hvw : |v.1 * w.2 - v.2 * w.1| = 1) {cu cv cw : RatCoef}
    (hc : cu ≠ 0 ∨ cv ≠ 0 ∨ cw ≠ 0) (k0 m0 : ℤ) :
    ¬ ∀ k m : ℤ, k0 ≤ k → m0 ≤ m → ∀ zu zv zw : ℂ,
      HasValueAt cu k m zu → HasValueAt cv k m zv → HasValueAt cw k m zw →
        zu * f k m + zv * f (k + v.1) (m + v.2) - zw * f (k + w.1) (m + w.2) = 0 := by
  intro h
  obtain ⟨au, bu, hbu, eu⟩ := exists_rep cu
  obtain ⟨av, bv, hbv, ev⟩ := exists_rep cv
  obtain ⟨aw, bw, hbw, ew⟩ := exists_rep cw
  refine not_annihilate_kauers f hf hvw (nu := au * bv * bw) (nv := av * bu * bw) (nw := aw * bu * bv)
    (Δ := bu * bv * bw) ?_ (mul_ne_zero (mul_ne_zero hbu hbv) hbw) k0 m0 ?_
  · rcases hc with hc | hc | hc
    · exact Or.inl (mul_ne_zero (mul_ne_zero (num_ne_zero hc hbu eu) hbv) hbw)
    · exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (num_ne_zero hc hbv ev) hbu) hbw))
    · exact Or.inr (Or.inr (mul_ne_zero (mul_ne_zero (num_ne_zero hc hbw ew) hbu) hbv))
  · intro k m hk hm hΔ
    simp only [evalEval_mul] at hΔ ⊢
    have hBw := right_ne_zero_of_mul hΔ
    have hBu := left_ne_zero_of_mul (left_ne_zero_of_mul hΔ)
    have hBv := right_ne_zero_of_mul (left_ne_zero_of_mul hΔ)
    have hrel := h k m hk hm _ _ _ (hasValueAt_of_rep eu hBu) (hasValueAt_of_rep ev hBv)
      (hasValueAt_of_rep ew hBw)
    have hzu := div_mul_cancel₀ (au.evalEval (k : ℂ) (m : ℂ)) hBu
    have hzv := div_mul_cancel₀ (av.evalEval (k : ℂ) (m : ℂ)) hBv
    have hzw := div_mul_cancel₀ (aw.evalEval (k : ℂ) (m : ℂ)) hBw
    set Bu := bu.evalEval (k : ℂ) (m : ℂ)
    set Bv := bv.evalEval (k : ℂ) (m : ℂ)
    set Bw := bw.evalEval (k : ℂ) (m : ℂ)
    linear_combination (Bu * Bv * Bw) * hrel - (Bv * Bw * f k m) * hzu
      - (Bu * Bw * f (k + v.1) (m + v.2)) * hzv + (Bu * Bv * f (k + w.1) (m + w.2)) * hzw

end A207123
