import A207123.Interlace

/-!
# 论文引理 8.7(3)：交错关系在求导下保持

论文引理 8.7(3)：`g ≪ f`、`deg g ≥ 1` 推出 `g' ≪ f'`。论文用上半平面的虚部刻画（引理 8.5(1)）与 Gauss–Lucas 定理证明；
这里用下锥（`Interlace.lean` 第 5、9 节）：首项系数为正时 `g = c·f + Σ_a w(a)·f/(X−a)`（`c ≥ 0`，`w ≥ 0`，
`cone_of_interlaces`），求导得 `g' = c·f' + Σ_a w(a)·(f/(X−a))'`。对 `q = f/(X−a)` 有 `f' = q + (X−a)·q'`，由引理 8.7(1)
（`q' ≪ q`、`q' ≪ (X−a)·q'`）与引理 8.6 得 `q' ≪ f'`，即 `q'` 在 `f'` 的下锥中（`inCone_derivative_of_eq_mul`）；下锥对
非负线性组合封闭，所以 `g'` 也在 `f'` 的下锥中，`g' ≪ f'`（`interlaces_derivative_of_interlaces_pos`）。
交错关系（计数定义）与首项系数的符号无关，所以主定理 `interlaces_derivative_of_interlaces` 不要求首项系数为正。
-/

namespace A207123

open Polynomial

noncomputable section

/-- 交错关系与两边的非零常数倍无关（反方向）。 -/
theorem Interlaces.of_C_mul {g f : ℝ[X]} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Interlaces (C a * g) (C b * f)) : Interlaces g f := by
  have := (h.C_mul_left (inv_ne_zero ha)).C_mul_right (inv_ne_zero hb)
  rwa [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, C_1, one_mul,
    one_mul] at this

/-- `f = (X − a)·q`，`q` 实根、首项系数为正：`q'` 在 `f'` 的下锥中（`deg q = 0` 时 `q' = 0`）。 -/
theorem inCone_derivative_of_eq_mul {f q : ℝ[X]} (a : ℝ) (hfq : f = (X - C a) * q) (hq : RealRooted q)
    (hlc : 0 < q.leadingCoeff) : InCone (derivative q) (derivative f) := by
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
  · rw [derivative_of_natDegree_zero h0]
    exact InCone.zero _
  · have h1 : Interlaces (derivative q) q := interlaces_derivative hq hlc hpos
    have hlcq' : 0 < (derivative q).leadingCoeff := leadingCoeff_derivative_pos hlc hpos
    have h2 : Interlaces (derivative q) ((X - C a) * derivative q) := interlaces_X_sub_C_mul h1.2.1 a
    have hlc2 : 0 < ((X - C a) * derivative q).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
      exact hlcq'
    have hf' : derivative f = q + (X - C a) * derivative q := by
      rw [hfq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
    rw [hf']
    exact (Interlaces.add_right h1 h2 hlcq' hlc hlc2).inCone (leadingCoeff_add_pos hlc hlc2) hlcq'

/-- 论文引理 8.7(3)，首项系数为正的情形：`g ≪ f`、`deg g ≥ 1` 推出 `g' ≪ f'`。 -/
theorem interlaces_derivative_of_interlaces_pos {g f : ℝ[X]} (h : Interlaces g f)
    (hlcf : 0 < f.leadingCoeff) (hlcg : 0 < g.leadingCoeff) (hdeg : 1 ≤ g.natDegree) :
    Interlaces (derivative g) (derivative f) := by
  have hdegf : 1 ≤ f.natDegree := le_trans hdeg h.natDegree_le.1
  have hf := h.1
  have hf' : RealRooted (derivative f) := (interlaces_derivative hf hlcf hdegf).2.1
  have hlcf' : 0 < (derivative f).leadingCoeff := leadingCoeff_derivative_pos hlcf hdegf
  have hg' : derivative g ≠ 0 := fun h0 => by
    have := derivative_eq_zero.1 h0
    omega
  obtain ⟨c, hc, w, hw, rfl⟩ := cone_of_interlaces h hlcf hlcg
  have hd : derivative (coneSum f c w) = C c * derivative f +
      ∑ a ∈ f.roots.toFinset, C (w a) * derivative (f /ₘ (X - C a)) := by
    simp only [coneSum, derivative_add, derivative_sum, derivative_C_mul]
  refine InCone.interlaces ?_ hf' hlcf' hg'
  rw [hd]
  refine (InCone.C_mul (InCone.self _) hc).add
    (InCone.sum _ (fun a ha => hw a (Multiset.mem_toFinset.1 ha)) fun a ha => ?_)
  have hroot : f.IsRoot a := (mem_roots hf.1).1 (Multiset.mem_toFinset.1 ha)
  exact inCone_derivative_of_eq_mul a (divByMonic_spec hroot).symm (realRooted_divByMonic hf hroot)
    (by rw [leadingCoeff_divByMonic' hroot]; exact hlcf)

/-- 论文引理 8.7(3)：`g ≪ f`、`deg g ≥ 1` 推出 `g' ≪ f'`（不要求首项系数为正：先把 `f`、`g` 除以各自的首项系数）。 -/
theorem interlaces_derivative_of_interlaces {g f : ℝ[X]} (h : Interlaces g f) (hdeg : 1 ≤ g.natDegree) :
    Interlaces (derivative g) (derivative f) := by
  have hf0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 h.1.1
  have hg0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 h.2.1.1
  have hlc : ∀ p : ℝ[X], p.leadingCoeff ≠ 0 → 0 < (C p.leadingCoeff⁻¹ * p).leadingCoeff := by
    intro p hp
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hp]
    exact one_pos
  have h2 := interlaces_derivative_of_interlaces_pos
    ((h.C_mul_left (inv_ne_zero hg0)).C_mul_right (inv_ne_zero hf0)) (hlc f hf0) (hlc g hg0)
    (by rwa [natDegree_C_mul (inv_ne_zero hg0)])
  rw [derivative_C_mul, derivative_C_mul] at h2
  exact h2.of_C_mul (inv_ne_zero hg0) (inv_ne_zero hf0)

end

end A207123
