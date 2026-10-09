import A207123.NotStirlingLike

/-!
# 论文推论 5.7 与注 5.8：三项算子不零化 `U`（把分母乘掉的形式）

论文推论 5.7：设 `v_i = (s_i, t_i) ∈ ℤ²`（`i = 0, 1, 2`）两两不同，`|det(v₀, v₁, v₂)| ≤ 2`，`c_i` 是 `(k, m)` 的
有理函数、不全为 0，`T = Σ c_i(k, m)·S^{v_i}`，`(S^{(s,t)} f)(k, m) = f(k + s, m + t)`。则 `T` 不在任何象限中
系数有定义的每个点上零化 `U`。

本文件把分母乘掉：取 `c_i` 的公分母 `Δ ∈ ℂ[k, m]`，`c_i = n_i/Δ`（`n_i` 是多项式）。在 `Δ(k, m) ≠ 0` 的点上
`c_i` 都有定义，`Σ c_i·U = 0` 乘以 `Δ(k, m)` 就是这里的假设 `Σ n_i(k, m)·f(k + s_i, m + t_i) = 0`。`f : ℤ² → ℂ`
是 `U` 的任意一个延拓（在 `ℕ²` 上等于 `U`），象限取在 `ℤ²` 里，所以这同时覆盖注 5.8 的论证：`U` 的某个延拓若是
Stirling-like，它的三项生成元在系数有定义的点上零化这个延拓。

* `not_annihilate_three_terms`：推论 5.7。
* `not_annihilate_two_terms`：推论 5.7 的「特别地，`U` 没有至多两项的递推」（第三个点取在 `v₀`、`v₁` 所在的
  直线上，系数为 0）。
* `not_annihilate_kauers`：Kauers 2007 定义 3 的生成元形状 `u + v·S^{(v₁,v₂)} − w·S^{(w₁,w₂)}`，
  `(v₁, v₂)`、`(w₁, w₂)` 是 `ℤ²` 的基（`|v₁w₂ − v₂w₁| = 1`）。

**证明**（同论文）：取自然数 `c ≥ s_i`、`d ≥ t_i`，在点 `(K − c, M − d)` 处用假设。记
`p'(K, M) = p(K − c, M − d)`（`shiftK^[c] (shiftM^[d] p)`），正规形
`r = Σ_i (Δ·n_i)'·X^{c − s_i}·E^{−(d − t_i)}` 在一个象限上零化 `U`：`Δ' ≠ 0` 的点上由假设，`Δ' = 0` 的点上
因子 `Δ'` 为 0。三个点 `(c − s_i, d − t_i)` 是 `v_i` 经点反射与平移后的像，两两不同，`det` 不变；`r ≠ 0`，因为
平移后为 0 的多项式本身为 0，而 `ℂ[k, m]` 是整环、`Δ ≠ 0`。这与命题 5.6（`not_mem_relU_of_support_subset`）矛盾。

有理函数系数本身（取公分母这一步），以及由 Kauers 定义 3 推出「生成元在系数有定义的点上零化序列」，是书面的。
-/

open Polynomial

namespace A207123

/-- 辅助引理（推论 5.7）：`shiftK` 迭代 `c` 次，`k` 平移 `c`。 -/
theorem evalEval_shiftK_iterate (c : ℕ) (p : Coef) (x y : ℂ) :
    (shiftK^[c] p).evalEval x y = p.evalEval (x - c) y := by
  induction c generalizing p with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply, ih, evalEval_shiftK,
      show x - (c : ℂ) - 1 = x - ((c + 1 : ℕ) : ℂ) by rw [Nat.cast_add, Nat.cast_one]; ring]

/-- 辅助引理（推论 5.7）：`shiftM` 迭代 `d` 次，`m` 平移 `d`。 -/
theorem evalEval_shiftM_iterate (d : ℕ) (p : Coef) (x y : ℂ) :
    (shiftM^[d] p).evalEval x y = p.evalEval x (y - d) := by
  induction d generalizing p with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih, evalEval_shiftM,
      show y - (d : ℂ) - 1 = y - ((d + 1 : ℕ) : ℂ) by rw [Nat.cast_add, Nat.cast_one]; ring]

/-- 辅助引理（推论 5.7）：`p'(x, y) = p(x − c, y − d)`。 -/
theorem evalEval_shift_iterate (c d : ℕ) (p : Coef) (x y : ℂ) :
    (shiftK^[c] (shiftM^[d] p)).evalEval x y = p.evalEval (x - c) (y - d) := by
  rw [evalEval_shiftK_iterate, evalEval_shiftM_iterate]

/-- 辅助引理（推论 5.7）：平移后为 0 的多项式本身为 0。 -/
theorem eq_zero_of_shift_eq_zero (c d : ℕ) {p : Coef} (h : shiftK^[c] (shiftM^[d] p) = 0) :
    p = 0 := by
  refine coef_eq_zero_of_vanish p 0 0 fun k m _ _ => ?_
  have e := evalEval_shift_iterate c d p ((k : ℂ) + c) ((m : ℂ) + d)
  rw [h, Polynomial.evalEval_zero, add_sub_cancel_right, add_sub_cancel_right] at e
  exact e.symm

/-- **推论 5.7**（论文，分母乘掉的形式；`f` 是 `U` 在 `ℤ²` 上的任意延拓，也覆盖注 5.8 的论证）：设
`v₀, v₁, v₂ ∈ ℤ²` 两两不同，`|det(v₁ − v₀, v₂ − v₀)| ≤ 2`，多项式 `n₀, n₁, n₂` 不全为 0，`Δ ≠ 0`。则没有象限
`k ≥ k₀, m ≥ m₀`（`k, m ∈ ℤ`），使得在其中 `Δ(k, m) ≠ 0` 的每个点上
`n₀(k, m)·f(k + s₀, m + t₀) + n₁(k, m)·f(k + s₁, m + t₁) + n₂(k, m)·f(k + s₂, m + t₂) = 0`。 -/
theorem not_annihilate_three_terms (f : ℤ → ℤ → ℂ) (hf : ∀ k m : ℕ, f k m = U k m)
    {v0 v1 v2 : ℤ × ℤ} (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2)
    (hdet : |(v1.1 - v0.1) * (v2.2 - v0.2) - (v1.2 - v0.2) * (v2.1 - v0.1)| ≤ 2)
    {n0 n1 n2 Δ : Coef} (hn : n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0) (hΔ : Δ ≠ 0) (k0 m0 : ℤ) :
    ¬ ∀ k m : ℤ, k0 ≤ k → m0 ≤ m → Δ.evalEval (k : ℂ) (m : ℂ) ≠ 0 →
      n0.evalEval (k : ℂ) (m : ℂ) * f (k + v0.1) (m + v0.2)
        + n1.evalEval (k : ℂ) (m : ℂ) * f (k + v1.1) (m + v1.2)
        + n2.evalEval (k : ℂ) (m : ℂ) * f (k + v2.1) (m + v2.2) = 0 := by
  intro h
  -- 自然数 `c ≥ s_i`、`d ≥ t_i`；三个点反射到 `ℕ²`：`(a_i, b_i) = (c − s_i, d − t_i)`
  obtain ⟨c, hc0, hc1, hc2⟩ : ∃ c : ℕ, v0.1 ≤ c ∧ v1.1 ≤ c ∧ v2.1 ≤ c :=
    ⟨(max (max v0.1 v1.1) v2.1).toNat, by omega, by omega, by omega⟩
  obtain ⟨d, hd0, hd1, hd2⟩ : ∃ d : ℕ, v0.2 ≤ d ∧ v1.2 ≤ d ∧ v2.2 ≤ d :=
    ⟨(max (max v0.2 v1.2) v2.2).toNat, by omega, by omega, by omega⟩
  obtain ⟨a0, ha0⟩ : ∃ a : ℕ, (a : ℤ) = c - v0.1 := ⟨(c - v0.1).toNat, by omega⟩
  obtain ⟨a1, ha1⟩ : ∃ a : ℕ, (a : ℤ) = c - v1.1 := ⟨(c - v1.1).toNat, by omega⟩
  obtain ⟨a2, ha2⟩ : ∃ a : ℕ, (a : ℤ) = c - v2.1 := ⟨(c - v2.1).toNat, by omega⟩
  obtain ⟨b0, hb0⟩ : ∃ b : ℕ, (b : ℤ) = d - v0.2 := ⟨(d - v0.2).toNat, by omega⟩
  obtain ⟨b1, hb1⟩ : ∃ b : ℕ, (b : ℤ) = d - v1.2 := ⟨(d - v1.2).toNat, by omega⟩
  obtain ⟨b2, hb2⟩ : ∃ b : ℕ, (b : ℤ) = d - v2.2 := ⟨(d - v2.2).toNat, by omega⟩
  have hp01 : ((a0, b0) : ℕ × ℕ) ≠ (a1, b1) := fun e => by
    obtain ⟨ea, eb⟩ := Prod.mk.inj e
    exact h01 (Prod.ext (by omega) (by omega))
  have hp02 : ((a0, b0) : ℕ × ℕ) ≠ (a2, b2) := fun e => by
    obtain ⟨ea, eb⟩ := Prod.mk.inj e
    exact h02 (Prod.ext (by omega) (by omega))
  have hp12 : ((a1, b1) : ℕ × ℕ) ≠ (a2, b2) := fun e => by
    obtain ⟨ea, eb⟩ := Prod.mk.inj e
    exact h12 (Prod.ext (by omega) (by omega))
  -- 正规形 `r = Σ_i (Δ·n_i)'·X^{a_i}·E^{−b_i}`
  obtain ⟨r, hr⟩ : ∃ r : ℕ × ℕ →₀ Coef,
      r = Finsupp.single (a0, b0) (shiftK^[c] (shiftM^[d] (Δ * n0)))
        + Finsupp.single (a1, b1) (shiftK^[c] (shiftM^[d] (Δ * n1)))
        + Finsupp.single (a2, b2) (shiftK^[c] (shiftM^[d] (Δ * n2))) := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by
    intro hr0
    have e0 := DFunLike.congr_fun hr0 (a0, b0)
    have e1 := DFunLike.congr_fun hr0 (a1, b1)
    have e2 := DFunLike.congr_fun hr0 (a2, b2)
    simp only [hr, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hp01,
      Finsupp.single_eq_of_ne hp02, Finsupp.single_eq_of_ne hp12, Finsupp.single_eq_of_ne hp01.symm,
      Finsupp.single_eq_of_ne hp02.symm, Finsupp.single_eq_of_ne hp12.symm, add_zero, zero_add,
      Finsupp.coe_zero, Pi.zero_apply] at e0 e1 e2
    have z0 := (mul_eq_zero.mp (eq_zero_of_shift_eq_zero c d e0)).resolve_left hΔ
    have z1 := (mul_eq_zero.mp (eq_zero_of_shift_eq_zero c d e1)).resolve_left hΔ
    have z2 := (mul_eq_zero.mp (eq_zero_of_shift_eq_zero c d e2)).resolve_left hΔ
    rcases hn with hn | hn | hn
    · exact hn z0
    · exact hn z1
    · exact hn z2
  have hsupp : r.support ⊆ {(a0, b0), (a1, b1), (a2, b2)} := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨h0, h1, h2⟩ := hne
    apply hx
    simp only [hr, Finsupp.add_apply, Finsupp.single_eq_of_ne h0, Finsupp.single_eq_of_ne h1,
      Finsupp.single_eq_of_ne h2, add_zero]
  -- 点反射加平移不改变 `det`
  have hdet' : |det2 (a0, b0) (a1, b1) (a2, b2)| ≤ 2 := by
    have e : det2 (a0, b0) (a1, b1) (a2, b2)
        = (v1.1 - v0.1) * (v2.2 - v0.2) - (v1.2 - v0.2) * (v2.1 - v0.1) := by
      simp only [det2, ha0, ha1, ha2, hb0, hb1, hb2]
      ring
    rw [e]
    exact hdet
  -- `normOp r` 在象限上零化 `U`
  have hmem : normOp r ∈ RelU := by
    refine ⟨normOp_mem r, (k0 + c).toNat + a0 + a1 + a2, (m0 + d).toNat + b0 + b1 + b2,
      fun K M hK hM => ?_⟩
    have hKa0 : a0 ≤ K := by omega
    have hKa1 : a1 ≤ K := by omega
    have hKa2 : a2 ≤ K := by omega
    have hMb0 : b0 ≤ M := by omega
    have hMb1 : b1 ≤ M := by omega
    have hMb2 : b2 ≤ M := by omega
    obtain ⟨x, hxd⟩ : ∃ x : ℤ, x = K - c := ⟨_, rfl⟩
    obtain ⟨y, hyd⟩ : ∃ y : ℤ, y = M - d := ⟨_, rfl⟩
    have hxC : ((x : ℤ) : ℂ) = (K : ℂ) - c := by
      rw [hxd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    have hyC : ((y : ℤ) : ℂ) = (M : ℂ) - d := by
      rw [hyd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    have hf0 : f (x + v0.1) (y + v0.2) = Uarr (K - a0) (M - b0) := by
      rw [show x + v0.1 = ((K - a0 : ℕ) : ℤ) by omega, show y + v0.2 = ((M - b0 : ℕ) : ℤ) by omega]
      exact hf _ _
    have hf1 : f (x + v1.1) (y + v1.2) = Uarr (K - a1) (M - b1) := by
      rw [show x + v1.1 = ((K - a1 : ℕ) : ℤ) by omega, show y + v1.2 = ((M - b1 : ℕ) : ℤ) by omega]
      exact hf _ _
    have hf2 : f (x + v2.1) (y + v2.2) = Uarr (K - a2) (M - b2) := by
      rw [show x + v2.1 = ((K - a2 : ℕ) : ℤ) by omega, show y + v2.2 = ((M - b2 : ℕ) : ℤ) by omega]
      exact hf _ _
    simp only [hr, normOp_add, normOp_single, LinearMap.add_apply, Pi.add_apply, Module.End.mul_apply,
      mulOp_apply, opX_pow_apply, opEinv_pow_apply, hKa0, hKa1, hKa2, hMb0, hMb1, hMb2, ↓reduceIte,
      evalEval_shift_iterate, evalEval_mul]
    by_cases hΔ0 : Δ.evalEval ((K : ℂ) - c) ((M : ℂ) - d) = 0
    · rw [hΔ0]
      ring
    · have e := h x y (by omega) (by omega) (by rwa [hxC, hyC])
      rw [hxC, hyC, hf0, hf1, hf2] at e
      linear_combination Δ.evalEval ((K : ℂ) - c) ((M : ℂ) - d) * e
  exact not_mem_relU_of_support_subset hr0 hsupp hdet' hmem

/-- **推论 5.7 的「特别地」**（分母乘掉的形式）：`U` 的任何延拓都没有至多两项的象限递推。`v₀ ≠ v₁`，多项式
`n₀, n₁` 不全为 0（一项的情形取 `n₁ = 0`），`Δ ≠ 0`。 -/
theorem not_annihilate_two_terms (f : ℤ → ℤ → ℂ) (hf : ∀ k m : ℕ, f k m = U k m)
    {v0 v1 : ℤ × ℤ} (h01 : v0 ≠ v1) {n0 n1 Δ : Coef} (hn : n0 ≠ 0 ∨ n1 ≠ 0) (hΔ : Δ ≠ 0)
    (k0 m0 : ℤ) :
    ¬ ∀ k m : ℤ, k0 ≤ k → m0 ≤ m → Δ.evalEval (k : ℂ) (m : ℂ) ≠ 0 →
      n0.evalEval (k : ℂ) (m : ℂ) * f (k + v0.1) (m + v0.2)
        + n1.evalEval (k : ℂ) (m : ℂ) * f (k + v1.1) (m + v1.2) = 0 := by
  intro h
  -- 第三个点 `2v₁ − v₀` 与 `v₀, v₁` 共线，系数取 0
  have h02 : v0 ≠ (2 * v1.1 - v0.1, 2 * v1.2 - v0.2) := by
    intro e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    dsimp only at e1 e2
    exact h01 (Prod.ext (by omega) (by omega))
  have h12 : v1 ≠ (2 * v1.1 - v0.1, 2 * v1.2 - v0.2) := by
    intro e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    dsimp only at e1 e2
    exact h01 (Prod.ext (by omega) (by omega))
  refine not_annihilate_three_terms f hf h01 h02 h12 ?_ (n0 := n0) (n1 := n1) (n2 := 0)
    (hn.elim Or.inl fun h => Or.inr (Or.inl h)) hΔ k0 m0 ?_
  · show |(v1.1 - v0.1) * ((2 * v1.2 - v0.2) - v0.2) - (v1.2 - v0.2) * ((2 * v1.1 - v0.1) - v0.1)| ≤ 2
    rw [show (v1.1 - v0.1) * ((2 * v1.2 - v0.2) - v0.2) - (v1.2 - v0.2) * ((2 * v1.1 - v0.1) - v0.1)
      = 0 by ring, abs_zero]
    norm_num
  · intro k m hk hm hΔk
    rw [Polynomial.evalEval_zero, zero_mul, add_zero]
    exact h k m hk hm hΔk

/-- **推论 5.7 的最后一句**（分母乘掉的形式）：Kauers 2007 定义 3 的生成元形状
`u + v·S^{(v₁,v₂)} − w·S^{(w₁,w₂)}`，其中 `(v₁, v₂)`、`(w₁, w₂)` 是 `ℤ²` 的基（`|v₁w₂ − v₂w₁| = 1`），
`u, v, w` 的分子 `nu, nv, nw` 不全为 0、公分母 `Δ ≠ 0`：它不在任何象限中 `Δ ≠ 0` 的每个点上零化 `U` 的任何延拓。 -/
theorem not_annihilate_kauers (f : ℤ → ℤ → ℂ) (hf : ∀ k m : ℕ, f k m = U k m)
    {v w : ℤ × ℤ} (hvw : |v.1 * w.2 - v.2 * w.1| = 1) {nu nv nw Δ : Coef}
    (hn : nu ≠ 0 ∨ nv ≠ 0 ∨ nw ≠ 0) (hΔ : Δ ≠ 0) (k0 m0 : ℤ) :
    ¬ ∀ k m : ℤ, k0 ≤ k → m0 ≤ m → Δ.evalEval (k : ℂ) (m : ℂ) ≠ 0 →
      nu.evalEval (k : ℂ) (m : ℂ) * f k m + nv.evalEval (k : ℂ) (m : ℂ) * f (k + v.1) (m + v.2)
        - nw.evalEval (k : ℂ) (m : ℂ) * f (k + w.1) (m + w.2) = 0 := by
  intro h
  have hv0 : ((0 : ℤ), (0 : ℤ)) ≠ v := by
    intro e
    rw [← e] at hvw
    norm_num at hvw
  have hw0 : ((0 : ℤ), (0 : ℤ)) ≠ w := by
    intro e
    rw [← e] at hvw
    norm_num at hvw
  have hvw' : v ≠ w := by
    intro e
    rw [e, mul_comm w.2 w.1, sub_self, abs_zero] at hvw
    exact zero_ne_one hvw
  refine not_annihilate_three_terms f hf hv0 hw0 hvw' ?_ (n0 := nu) (n1 := nv) (n2 := -nw) ?_ hΔ k0 m0 ?_
  · show |(v.1 - 0) * (w.2 - 0) - (v.2 - 0) * (w.1 - 0)| ≤ 2
    rw [sub_zero, sub_zero, sub_zero, sub_zero, hvw]
    norm_num
  · rcases hn with hu | hu | hu
    exacts [Or.inl hu, Or.inr (Or.inl hu), Or.inr (Or.inr (neg_ne_zero.mpr hu))]
  · intro k m hk hm hΔk
    have e := h k m hk hm hΔk
    simp only [add_zero, Polynomial.evalEval_neg]
    linear_combination e

end A207123
