import A207123.Interlace

/-!
# 首一 Laguerre 多项式只有实根（报告 T4.3(8) 证明中引用的 Szegő 定理，`α` 为自然数的情形）

报告 T4.3(8)（`gcd(Num_q, P_{q−1}) = 1`）的证明在 `b_i` 可约（`i = r²(r−1)`）时引用了「`α > −1` 时广义 Laguerre 多项式
`L_n^{(α)}` 的零点都是正实数」（Szegő），没有重证（报告 ⑥ 第 3 处）。证明里只用到 `α = i + 1` 为正整数的情形。这里对一切
自然数 `α` 证明需要的结论，不用正交性与积分，只用三项递推与 `Interlace.lean` 的锥表示：

* `lagM α n`：首一的 Laguerre 多项式 `M_n = (−1)^n·n!·L_n^{(α)}`，按三项递推定义（`M_0 = 1`，`M_1 = X − (α+1)`，
  `M_{n+2} = (X − (2n+3+α))·M_{n+1} − (n+1)(n+1+α)·M_n`）；`lagM_monic_natDegree`：首一、`n` 次。
* `lagM_interlaces`：`M_n ≪ M_{n+1}`（对 `n` 归纳：`cone_of_interlaces` 把 `M_n` 写成 `M_{n+1}` 的下锥元素，代入递推后
  `M_{n+2}` 是 `M_{n+1}` 的上锥元素，再用 `interlaces_uconeSum`）；`realRooted_lagM`：`M_n` 只有实根；
  `lagM_aeval_ne_zero`：虚部非零的复数不是 `M_n` 的根。
* `lagS α n = Σ_{t≤n} C(n+α,t)·n^{\underline t}·v^t`（T4.3(8) 证明里的 `S_{q,i}` 看成 `v = x³` 的多项式，`q = n+α`，
  `α = i+1`）：系数 `coeff_lagS`；递推 `lagS_rec`（`s_{n+2} = (1 + (2n+3+α)v)·s_{n+1} − (n+1)(n+1+α)·v²·s_n`，
  系数恒等式 `lagS_key` 借 `descPochhammer` 在 `ℚ` 中证）；`lagS_aeval`：`v ≠ 0` 时 `s_n(v) = (−v)^n·M_n(−1/v)`。
* `lagS_aeval_ne_zero`：虚部非零的复数 `v` 处 `s_n(v) ≠ 0`；`lagS_aeval_ofReal_ne_zero`：非负实数处 `s_n ≥ 1`。
-/

namespace A207123

open Polynomial
open scoped Nat

noncomputable section

/-! ## 1. 首一 Laguerre 多项式只有实根 -/

/-- 首一的 Laguerre 多项式 `M_n = (−1)^n·n!·L_n^{(α)}`，按三项递推定义。 -/
def lagM (α : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C ((α : ℝ) + 1)
  | n + 2 => (X - C (2 * (n : ℝ) + 3 + α)) * lagM α (n + 1)
      - C (((n : ℝ) + 1) * ((n : ℝ) + 1 + α)) * lagM α n

theorem lagM_succ_succ (α n : ℕ) :
    lagM α (n + 2) = (X - C (2 * (n : ℝ) + 3 + α)) * lagM α (n + 1)
      - C (((n : ℝ) + 1) * ((n : ℝ) + 1 + α)) * lagM α n := rfl

/-- `M_n` 首一、`n` 次。 -/
theorem lagM_monic_natDegree (α : ℕ) : ∀ n, (lagM α n).Monic ∧ (lagM α n).natDegree = n
  | 0 => ⟨monic_one, natDegree_one⟩
  | 1 => ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩
  | n + 2 => by
    obtain ⟨h1m, h1d⟩ := lagM_monic_natDegree α (n + 1)
    obtain ⟨_, h0d⟩ := lagM_monic_natDegree α n
    have hp : ((X - C (2 * (n : ℝ) + 3 + α)) * lagM α (n + 1)).Monic := (monic_X_sub_C _).mul h1m
    have hpd : ((X - C (2 * (n : ℝ) + 3 + α)) * lagM α (n + 1)).natDegree = n + 2 := by
      rw [(monic_X_sub_C _).natDegree_mul h1m, natDegree_X_sub_C, h1d]
      ring
    have hqd : (C (((n : ℝ) + 1) * ((n : ℝ) + 1 + α)) * lagM α n).natDegree < n + 2 :=
      lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans h0d.le) (by omega)
    rw [lagM_succ_succ]
    refine ⟨hp.sub_of_left ?_, ?_⟩
    · rw [degree_eq_natDegree hp.ne_zero, hpd]
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast hqd)
    · rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hpd]; exact hqd), hpd]

/-- `M_n ≪ M_{n+1}`（根交错）。 -/
theorem lagM_interlaces (α : ℕ) : ∀ n, Interlaces (lagM α n) (lagM α (n + 1))
  | 0 => by
    refine ⟨realRooted_X_sub_C _, ?_, fun x => ?_⟩
    · show RealRooted (1 : ℝ[X])
      rw [← C_1]
      exact realRooted_C one_ne_zero
    · show nAbove 1 x ≤ nAbove (X - C ((α : ℝ) + 1)) x ∧ nAbove (X - C ((α : ℝ) + 1)) x ≤ nAbove 1 x + 1
      have h1 : nAbove (1 : ℝ[X]) x = 0 := by simp [nAbove]
      rw [h1, nAbove_X_sub_C]
      split_ifs <;> exact ⟨by omega, by omega⟩
  | n + 1 => by
    have ih := lagM_interlaces α n
    obtain ⟨hfm, _⟩ := lagM_monic_natDegree α (n + 1)
    obtain ⟨hgm, _⟩ := lagM_monic_natDegree α n
    obtain ⟨hnm, _⟩ := lagM_monic_natDegree α (n + 2)
    have hlcf : 0 < (lagM α (n + 1)).leadingCoeff := by rw [hfm.leadingCoeff]; exact one_pos
    have hlcg : 0 < (lagM α n).leadingCoeff := by rw [hgm.leadingCoeff]; exact one_pos
    obtain ⟨c, _, w, hw, hg⟩ := cone_of_interlaces ih hlcf hlcg
    have hb0 : (0 : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1 + α) := by positivity
    have key : lagM α (n + 2) = uconeSum (lagM α (n + 1)) 1
        (-(2 * (n : ℝ) + 3 + α) - ((n : ℝ) + 1) * ((n : ℝ) + 1 + α) * c)
        (fun t => ((n : ℝ) + 1) * ((n : ℝ) + 1 + α) * w t) := by
      rw [lagM_succ_succ, hg]
      unfold coneSum uconeSum
      have hsum : C (((n : ℝ) + 1) * ((n : ℝ) + 1 + α))
            * ∑ r ∈ (lagM α (n + 1)).roots.toFinset, C (w r) * (lagM α (n + 1) /ₘ (X - C r))
          = ∑ r ∈ (lagM α (n + 1)).roots.toFinset,
              C (((n : ℝ) + 1) * ((n : ℝ) + 1 + α) * w r) * (lagM α (n + 1) /ₘ (X - C r)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [C_mul (a := ((n : ℝ) + 1) * ((n : ℝ) + 1 + α)), mul_assoc]
      rw [mul_add, hsum]
      simp only [map_sub, map_neg, map_mul, C_1]
      ring
    have hlcn : 0 < (uconeSum (lagM α (n + 1)) 1
        (-(2 * (n : ℝ) + 3 + α) - ((n : ℝ) + 1) * ((n : ℝ) + 1 + α) * c)
        (fun t => ((n : ℝ) + 1) * ((n : ℝ) + 1 + α) * w t)).leadingCoeff := by
      rw [← key, hnm.leadingCoeff]
      exact one_pos
    have h := interlaces_uconeSum ih.realRooted_right hlcf zero_le_one
      (-(2 * (n : ℝ) + 3 + α) - ((n : ℝ) + 1) * ((n : ℝ) + 1 + α) * c)
      (fun t ht => mul_nonneg hb0 (hw t ht)) hlcn
    rw [← key] at h
    exact h

/-- `M_n` 只有实根（Szegő 定理在 `α ∈ ℕ` 时的情形）。 -/
theorem realRooted_lagM (α n : ℕ) : RealRooted (lagM α n) := (lagM_interlaces α n).realRooted_left

/-- 虚部非零的复数不是 `M_n` 的根。 -/
theorem lagM_aeval_ne_zero (α n : ℕ) {z : ℂ} (hz : z.im ≠ 0) : aeval z (lagM α n) ≠ 0 := by
  have hrr := realRooted_lagM α n
  have hmon := (lagM_monic_natDegree α n).1
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C hrr.2
  rw [hmon.leadingCoeff, C_1, one_mul] at hsplit
  rw [← hsplit, map_multiset_prod, Multiset.map_map]
  intro h
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
  obtain ⟨r, _, hr⟩ := h
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C] at hr
  have him := congrArg Complex.im hr
  simp at him
  exact hz him

/-! ## 2. `s_n(v) = Σ_t C(n+α,t)·n^{\underline t}·v^t` 与 `M_n` 的关系 -/

/-- `s_n(v) = Σ_{t≤n} C(n+α,t)·n^{\underline t}·v^t`。 -/
def lagS (α n : ℕ) : ℚ[X] :=
  ∑ t ∈ Finset.range (n + 1), C (((n + α).choose t : ℚ) * (n.descFactorial t : ℚ)) * X ^ t

theorem coeff_lagS (α n m : ℕ) :
    (lagS α n).coeff m = ((n + α).choose m : ℚ) * (n.descFactorial m : ℚ) := by
  rw [lagS, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega), Nat.cast_zero, mul_zero]

/-- 系数恒等式：`c(n+2,t+2) = c(n+1,t+2) + (2n+3+α)·c(n+1,t+1) − (n+1)(n+1+α)·c(n,t)`，`c(N,t) = C(N+α,t)·N^{\underline t}`。 -/
theorem lagS_key (α n t : ℕ) :
    ((n + 2 + α).choose (t + 2) : ℚ) * ((n + 2).descFactorial (t + 2) : ℚ)
      = ((n + 1 + α).choose (t + 2) : ℚ) * ((n + 1).descFactorial (t + 2) : ℚ)
        + (2 * (n : ℚ) + 3 + α) * (((n + 1 + α).choose (t + 1) : ℚ) * ((n + 1).descFactorial (t + 1) : ℚ))
        - ((n : ℚ) + 1) * ((n : ℚ) + 1 + α) * (((n + α).choose t : ℚ) * (n.descFactorial t : ℚ)) := by
  have hF : ∀ M k : ℕ, ((M.descFactorial k : ℕ) : ℚ) = (descPochhammer ℚ k).eval (M : ℚ) := by
    intro M k
    rw [descPochhammer_eval_eq_descFactorial]
  have hC : ∀ M k : ℕ, ((M.choose k : ℕ) : ℚ) = (descPochhammer ℚ k).eval (M : ℚ) / (k ! : ℚ) := by
    intro M k
    rw [← hF, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have : (k ! : ℚ) ≠ 0 := by positivity
    field_simp
  have hL : ∀ (x : ℚ) (k : ℕ),
      (descPochhammer ℚ (k + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℚ k).eval x := by
    intro x k
    rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one,
      add_sub_cancel_right]
  have hR : ∀ (x : ℚ) (k : ℕ),
      (descPochhammer ℚ (k + 1)).eval x = (descPochhammer ℚ k).eval x * (x - k) :=
    fun x k => descPochhammer_succ_eval k x
  have e1 : (descPochhammer ℚ (t + 2)).eval ((n + 2 + α : ℕ) : ℚ)
      = ((n : ℚ) + α + 1 + 1) * (((n : ℚ) + α + 1) * (descPochhammer ℚ t).eval ((n : ℚ) + α)) := by
    rw [show ((n + 2 + α : ℕ) : ℚ) = (n : ℚ) + α + 1 + 1 by push_cast; ring, hL, hL]
  have e2 : (descPochhammer ℚ (t + 2)).eval ((n + 2 : ℕ) : ℚ)
      = ((n : ℚ) + 1 + 1) * (((n : ℚ) + 1) * (descPochhammer ℚ t).eval (n : ℚ)) := by
    rw [show ((n + 2 : ℕ) : ℚ) = (n : ℚ) + 1 + 1 by push_cast; ring, hL, hL]
  have e3 : (descPochhammer ℚ (t + 2)).eval ((n + 1 + α : ℕ) : ℚ)
      = ((n : ℚ) + α + 1) * ((descPochhammer ℚ t).eval ((n : ℚ) + α) * ((n : ℚ) + α - t)) := by
    rw [show ((n + 1 + α : ℕ) : ℚ) = (n : ℚ) + α + 1 by push_cast; ring, hL, hR]
  have e4 : (descPochhammer ℚ (t + 2)).eval ((n + 1 : ℕ) : ℚ)
      = ((n : ℚ) + 1) * ((descPochhammer ℚ t).eval (n : ℚ) * ((n : ℚ) - t)) := by
    rw [show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by push_cast; ring, hL, hR]
  have e5 : (descPochhammer ℚ (t + 1)).eval ((n + 1 + α : ℕ) : ℚ)
      = ((n : ℚ) + α + 1) * (descPochhammer ℚ t).eval ((n : ℚ) + α) := by
    rw [show ((n + 1 + α : ℕ) : ℚ) = (n : ℚ) + α + 1 by push_cast; ring, hL]
  have e6 : (descPochhammer ℚ (t + 1)).eval ((n + 1 : ℕ) : ℚ)
      = ((n : ℚ) + 1) * (descPochhammer ℚ t).eval (n : ℚ) := by
    rw [show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by push_cast; ring, hL]
  have e7 : (descPochhammer ℚ t).eval ((n + α : ℕ) : ℚ) = (descPochhammer ℚ t).eval ((n : ℚ) + α) := by
    rw [Nat.cast_add]
  have f1 : ((t + 1)! : ℚ) = ((t : ℚ) + 1) * (t ! : ℚ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring
  have f2 : ((t + 2)! : ℚ) = ((t : ℚ) + 2) * (((t : ℚ) + 1) * (t ! : ℚ)) := by
    have h : (t + 2)! = (t + 2) * (t + 1)! := Nat.factorial_succ (t + 1)
    rw [h, Nat.cast_mul, f1]
    push_cast
    ring
  simp only [hC, hF]
  rw [e1, e2, e3, e4, e5, e6, e7, f1, f2]
  have ht0 : (t ! : ℚ) ≠ 0 := by positivity
  have ht1 : (t : ℚ) + 1 ≠ 0 := by positivity
  have ht2 : (t : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `s_{n+2} = (1 + (2n+3+α)v)·s_{n+1} − (n+1)(n+1+α)·v²·s_n`。 -/
theorem lagS_rec (α n : ℕ) :
    lagS α (n + 2) = (1 + C (2 * (n : ℚ) + 3 + α) * X) * lagS α (n + 1)
      - C (((n : ℚ) + 1) * ((n : ℚ) + 1 + α)) * X ^ 2 * lagS α n := by
  have e : (1 + C (2 * (n : ℚ) + 3 + α) * X) * lagS α (n + 1)
      - C (((n : ℚ) + 1) * ((n : ℚ) + 1 + α)) * X ^ 2 * lagS α n
      = lagS α (n + 1) + C (2 * (n : ℚ) + 3 + α) * (X ^ 1 * lagS α (n + 1))
        - C (((n : ℚ) + 1) * ((n : ℚ) + 1 + α)) * (X ^ 2 * lagS α n) := by ring
  rw [e]
  ext m
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_lagS]
  match m with
  | 0 => simp
  | 1 =>
    rw [ite_eq_left (le_refl 1), ite_eq_right (by norm_num : ¬ (2 ≤ 1)), Nat.sub_self,
      Nat.choose_zero_right, Nat.descFactorial_zero, Nat.choose_one_right, Nat.choose_one_right,
      Nat.descFactorial_one, Nat.descFactorial_one]
    push_cast
    ring
  | t + 2 =>
    rw [ite_eq_left (show 1 ≤ t + 2 by omega), ite_eq_left (show 2 ≤ t + 2 by omega),
      show t + 2 - 1 = t + 1 by omega, show t + 2 - 2 = t by omega]
    exact lagS_key α n t

theorem lagS_zero (α : ℕ) : lagS α 0 = 1 := by
  simp [lagS]

theorem lagS_aeval_one (α : ℕ) (v : ℂ) : aeval v (lagS α 1) = 1 + ((α : ℂ) + 1) * v := by
  rw [lagS, map_sum, Finset.sum_range_succ, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.descFactorial_zero, Nat.choose_one_right, Nat.descFactorial_one]
  simp only [map_mul, aeval_X, map_natCast, pow_zero, pow_one, Nat.cast_one,
    mul_one, map_one]
  push_cast
  ring

/-- `v ≠ 0` 时 `s_n(v) = (−v)^n·M_n(−1/v)`。 -/
theorem lagS_aeval (α : ℕ) (v : ℂ) (hv : v ≠ 0) :
    ∀ n, aeval v (lagS α n) = (-v) ^ n * aeval (-1 / v) (lagM α n)
  | 0 => by
    rw [lagS_zero]
    simp [lagM]
  | 1 => by
    rw [lagS_aeval_one]
    simp only [lagM, map_sub, aeval_X, aeval_C, pow_one]
    simp
    field_simp
    ring
  | n + 2 => by
    rw [lagS_rec, lagM_succ_succ]
    simp only [map_sub, map_mul, map_add, map_one, aeval_X, aeval_C, map_pow]
    rw [lagS_aeval α v hv (n + 1), lagS_aeval α v hv n]
    simp
    field_simp
    ring

/-- 虚部非零的复数 `v` 处 `s_n(v) ≠ 0`。 -/
theorem lagS_aeval_ne_zero (α n : ℕ) {v : ℂ} (hv : v.im ≠ 0) : aeval v (lagS α n) ≠ 0 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  rw [lagS_aeval α v hv0 n]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hv0)) (lagM_aeval_ne_zero α n ?_)
  have h1 : (-1 / v).im = v.im / Complex.normSq v := by
    simp [Complex.div_im]
    ring
  rw [h1]
  exact div_ne_zero hv (by rw [Ne, Complex.normSq_eq_zero]; exact hv0)

/-- 非负实数 `r` 处 `s_n(r) ≥ 1`，所以不为零。 -/
theorem lagS_aeval_ofReal_ne_zero (α n : ℕ) {r : ℝ} (hr : 0 ≤ r) : aeval (r : ℂ) (lagS α n) ≠ 0 := by
  have hpos : (1 : ℝ) ≤ aeval r (lagS α n) := by
    rw [lagS, map_sum]
    have hnn : ∀ t ∈ Finset.range (n + 1),
        0 ≤ aeval r (C (((n + α).choose t : ℚ) * (n.descFactorial t : ℚ)) * X ^ t) := by
      intro t _
      rw [map_mul, aeval_C, map_pow, aeval_X, eq_ratCast]
      positivity
    have h0 := Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.succ_pos n))
    have e0 : aeval r (C (((n + α).choose 0 : ℚ) * (n.descFactorial 0 : ℚ)) * X ^ 0) = 1 := by simp
    rw [e0] at h0
    exact h0
  have e : aeval (r : ℂ) (lagS α n) = ((aeval r (lagS α n) : ℝ) : ℂ) := by
    rw [← Complex.coe_algebraMap, aeval_algebraMap_apply, Complex.coe_algebraMap]
  rw [e]
  exact_mod_cast (show aeval r (lagS α n) ≠ 0 by linarith)

end

end A207123
