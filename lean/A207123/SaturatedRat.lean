import A207123.ThreeTermRat
import A207123.Saturated

/-!
# 论文推论 5.5：有理函数系数的陈述（用正规形描述 `𝒪(k,m)·L1`）

论文推论 5.5 在有理系数的 Ore 代数 `𝒪(k,m) = ℂ(k,m)⟨X, E⁻¹⟩` 中陈述；`Saturated.lean` 把分母乘掉，只用多项式系数
的算子（`OU`）。本文件补上两者之间的一步。这里不构造 `𝒪(k,m)` 这个环，而用正规形描述它的元素与右乘 `L1`：

* `𝒪(k,m)` 的元素有唯一的正规形 `Σ q_{ab}(k, m)·X^a·E^{−b}`，`q` 有限支撑、系数在 `RatCoef = ℂ(k, m)` 中。
* 右乘 `L1` 的正规形由论文式 (4)给出；系数在 `ℂ(k, m)` 中时交换规则相同，公式不变：
  `TUrat q a b = q_{ab} − q_{a,b−1} − q_{a−1,b} − (m − b)·q_{a−3,b}`（下标为负的项取 0）。系数为多项式时它就是
  `OreDim.lean` 的 `TU`（`TUrat_algebraMap`），而 `normOp_mul_L1` 证明了 `normOp q·L1 = normOp (TU q)`。
* 于是「`T ∈ 𝒪(k,m)·L1`」写成：存在有限支撑的 `q`，使 `T` 的正规形系数 `t_{ab}` 都等于 `TUrat q a b`。

定理：

* `saturated_one_rat`：推论 5.5(1)。`t` 是 `T` 的正规形系数；若在某个象限中所有 `t_{ab}` 都有定义的每个点
  `(k, m)` 上 `Σ t_{ab}(k, m)·U_{k−a}(m−b) = 0`（`HasValueAt` 给出各系数在该点的值；下标为负的项取 0，同 `𝒜` 上
  算子的约定），则 `T ∈ 𝒪(k,m)·L1`。
* `saturated_two_rat`：推论 5.5(2)，`𝒪(k,m)·L1 ∩ 𝒪 = 𝒪·L1`：系数为多项式 `r` 的算子若在 `𝒪(k,m)·L1` 中，则
  `normOp r = Q·L1`，`Q ∈ OU`。

**证明**（同论文）：取公分母（`exists_common_den`，用 Mathlib 的 `IsLocalization.exist_integer_multiples`），
化到 `Saturated.lean` 的 `mul_mem_ideal_of_vanish` 与 `mem_ideal_of_mul_mem_ideal`；再用正规形的唯一性
（`normal_form_unique`）与 `normOp_mul_L1`，把算子等式换成系数等式。

没有形式化的：`𝒪(k,m)` 本身（作为环）的构造，以及它的正规形唯一、右乘 `L1` 由式 (4)给出这两点；本文件把它们当作
`𝒪(k,m)·L1` 的描述来用。
-/

open Polynomial

namespace A207123

/-- 右乘 `L1` 的正规形公式（论文式 (4)），系数在 `ℂ(k, m)` 中：
`(q·L1)_{ab} = q_{ab} − q_{a,b−1} − q_{a−1,b} − (m − b)·q_{a−3,b}`（下标为负的项取 0）。 -/
noncomputable def TUrat (q : ℕ × ℕ → RatCoef) (a b : ℕ) : RatCoef :=
  q (a, b) - (if 1 ≤ b then q (a, b - 1) else 0) - (if 1 ≤ a then q (a - 1, b) else 0)
    - (if 3 ≤ a then (algebraMap Coef RatCoef cM - (b : RatCoef)) * q (a - 3, b) else 0)

/-- 辅助引理（推论 5.5）：`TUrat` 对左乘 `ℂ(k, m)` 中的元素线性。 -/
theorem TUrat_mul (c : RatCoef) (q : ℕ × ℕ → RatCoef) (a b : ℕ) :
    TUrat (fun x => c * q x) a b = c * TUrat q a b := by
  simp only [TUrat]
  split_ifs <;> ring

/-- 辅助引理（推论 5.5）：系数为多项式时 `TUrat` 就是 `TU`（`OreDim.lean`，`Q·L1` 的正规形）。 -/
theorem TUrat_algebraMap (q : ℕ × ℕ →₀ Coef) (a b : ℕ) :
    TUrat (fun x => algebraMap Coef RatCoef (q x)) a b = algebraMap Coef RatCoef (TU q (a, b)) := by
  rw [TU_apply]
  simp only [TUrat]
  split_ifs <;> simp [map_sub, map_mul, map_natCast]

/-- 辅助引理（推论 5.5）：`mulOp p · normOp q = normOp (p·q)`（系数逐项乘 `p`）。 -/
theorem mulOp_mul_normOp (p : Coef) (q : ℕ × ℕ →₀ Coef) :
    mulOp p * normOp q = normOp (q.mapRange (fun c => p * c) (mul_zero p)) := by
  simp only [normOp]
  rw [Finsupp.sum_mapRange_index (fun _ => by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun ab _ => by simp only [map_mul, mul_assoc]

/-- 辅助引理（推论 5.5）：有限支撑的有理函数系数有公分母：`Δ ≠ 0`，且每个 `Δ·t_x` 是多项式 `r_x`。 -/
theorem exists_common_den (t : ℕ × ℕ →₀ RatCoef) :
    ∃ Δ : Coef, Δ ≠ 0 ∧ ∃ r : ℕ × ℕ →₀ Coef,
      ∀ x, algebraMap Coef RatCoef (r x) = algebraMap Coef RatCoef Δ * t x := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors Coef) t.support t
  have hb' : ∀ x ∈ t.support, ∃ y : Coef, algebraMap Coef RatCoef y = (b : Coef) • t x :=
    fun x hx => RingHom.mem_rangeS.mp (hb x hx)
  choose! g hg using hb'
  refine ⟨b, nonZeroDivisors.ne_zero b.2,
    Finsupp.onFinset t.support (fun x => if x ∈ t.support then g x else 0) fun x hx => ?_, fun x => ?_⟩
  · by_contra h
    exact hx (ite_eq_right h)
  · rw [Finsupp.onFinset_apply]
    by_cases hx : x ∈ t.support
    · rw [ite_eq_left hx, hg x hx]
      exact Algebra.smul_def (b : Coef) (t x)
    · rw [ite_eq_right hx, map_zero, show t x = 0 by simpa using hx, mul_zero]

/-- **推论 5.5(1)**（论文原样，有理函数系数；`𝒪(k,m)·L1` 用正规形描述）：`t` 是 `T ∈ 𝒪(k,m)` 的正规形系数
（有限支撑）。若在某个象限 `k ≥ k₀, m ≥ m₀` 中所有 `t_{ab}` 都有定义的每个点上
`Σ_{ab} t_{ab}(k, m)·U_{k−a}(m−b) = 0`（`z_{ab}` 是 `t_{ab}` 在该点的值，下标为负的项取 0），则存在有限支撑的 `q`，
使 `t_{ab} = TUrat q a b`，即 `T = Q·L1`，`Q = Σ q_{ab} X^a E^{−b} ∈ 𝒪(k,m)`。 -/
theorem saturated_one_rat (t : ℕ × ℕ →₀ RatCoef) (k0 m0 : ℕ)
    (h : ∀ k m : ℕ, k0 ≤ k → m0 ≤ m → ∀ z : ℕ × ℕ → ℂ,
      (∀ ab ∈ t.support, HasValueAt (t ab) k m (z ab)) →
      ∑ ab ∈ t.support, z ab *
        (if ab.1 ≤ k then (if ab.2 ≤ m then (U (k - ab.1) (m - ab.2) : ℂ) else 0) else 0) = 0) :
    ∃ q : ℕ × ℕ →₀ RatCoef, ∀ a b, t (a, b) = TUrat q a b := by
  obtain ⟨Δ, hΔ, r, hr⟩ := exists_common_den t
  -- `normOp r` 在象限中 `Δ ≠ 0` 的点上零化 `U`
  have hsub : r.support ⊆ t.support := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx ⊢
    intro htx
    apply hx
    apply IsFractionRing.injective Coef RatCoef
    rw [hr, htx, mul_zero, map_zero]
  have hvan : ∀ k m, k0 ≤ k → m0 ≤ m → Δ.evalEval (k : ℂ) (m : ℂ) ≠ 0 → normOp r Uarr k m = 0 := by
    intro k m hk hm hΔkm
    have hval : ∀ ab, HasValueAt (t ab) k m ((r ab).evalEval (k : ℂ) (m : ℂ) / Δ.evalEval (k : ℂ) (m : ℂ)) :=
      fun ab => ⟨r ab, Δ, hΔkm, by rw [hr, mul_comm], rfl⟩
    have h0 := h k m hk hm _ fun ab _ => hval ab
    rw [normOp_apply, Finset.sum_subset hsub]
    · simp only [Uarr]
      calc ∑ ab ∈ t.support, (r ab).evalEval (k : ℂ) (m : ℂ) *
            (if ab.1 ≤ k then (if ab.2 ≤ m then (U (k - ab.1) (m - ab.2) : ℂ) else 0) else 0)
          = Δ.evalEval (k : ℂ) (m : ℂ) * ∑ ab ∈ t.support,
              (r ab).evalEval (k : ℂ) (m : ℂ) / Δ.evalEval (k : ℂ) (m : ℂ) *
                (if ab.1 ≤ k then (if ab.2 ≤ m then (U (k - ab.1) (m - ab.2) : ℂ) else 0) else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ab _ => ?_
            rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hΔkm]
        _ = 0 := by rw [h0, mul_zero]
    · intro x _ hx
      rw [show r x = 0 by simpa using hx, evalEval_zero, zero_mul]
  obtain ⟨Q, hQ, hQe⟩ := mul_mem_ideal_of_vanish (normOp_mem r) Δ hvan
  obtain ⟨q0, rfl⟩ := exists_normal_form hQ
  rw [normOp_mul_L1, mulOp_mul_normOp] at hQe
  -- 正规形唯一：`Δ·r = TU q0`
  have hcoef : r.mapRange (fun c => Δ * c) (mul_zero Δ) = TU q0 :=
    sub_eq_zero.mp (normal_form_unique _ (by rw [normOp_sub, hQe, sub_self]))
  -- 取 `q = q0/Δ²`
  have hΔ' : algebraMap Coef RatCoef Δ ≠ 0 := fun h0 => hΔ (IsFractionRing.to_map_eq_zero_iff.mp h0)
  have hD : algebraMap Coef RatCoef Δ * algebraMap Coef RatCoef Δ ≠ 0 := mul_ne_zero hΔ' hΔ'
  refine ⟨q0.mapRange (fun c => (algebraMap Coef RatCoef Δ * algebraMap Coef RatCoef Δ)⁻¹ *
    algebraMap Coef RatCoef c) (by simp), fun a b => ?_⟩
  have hfun : (⇑(q0.mapRange (fun c => (algebraMap Coef RatCoef Δ * algebraMap Coef RatCoef Δ)⁻¹ *
      algebraMap Coef RatCoef c) (by simp)) : ℕ × ℕ → RatCoef) = fun x =>
      (algebraMap Coef RatCoef Δ * algebraMap Coef RatCoef Δ)⁻¹ * algebraMap Coef RatCoef (q0 x) :=
    funext fun x => Finsupp.mapRange_apply ..
  rw [hfun, TUrat_mul, TUrat_algebraMap, ← hcoef]
  simp only [Finsupp.mapRange_apply]
  rw [map_mul, hr, ← mul_assoc (algebraMap Coef RatCoef Δ), inv_mul_cancel_left₀ hD]

/-- **推论 5.5(2)**（论文原样，`𝒪(k,m)·L1 ∩ 𝒪 = 𝒪·L1`；`𝒪(k,m)·L1` 用正规形描述）：系数为多项式 `r` 的算子若在
`𝒪(k,m)·L1` 中（存在有限支撑的有理系数 `q`，使 `r_{ab} = TUrat q a b`），则 `normOp r = Q·L1`，`Q ∈ OU`。 -/
theorem saturated_two_rat (r : ℕ × ℕ →₀ Coef) (q : ℕ × ℕ →₀ RatCoef)
    (h : ∀ a b, algebraMap Coef RatCoef (r (a, b)) = TUrat q a b) :
    ∃ Q ∈ OU, normOp r = Q * L1 := by
  obtain ⟨D, hD, q1, hq1⟩ := exists_common_den q
  -- `D·r = TU q1`
  have hcoef : r.mapRange (fun c => D * c) (mul_zero D) = TU q1 := by
    refine Finsupp.ext fun ab => ?_
    obtain ⟨a, b⟩ := ab
    apply IsFractionRing.injective Coef RatCoef
    simp only [Finsupp.mapRange_apply]
    rw [map_mul, h, ← TUrat_mul, ← TUrat_algebraMap,
      show (fun x => algebraMap Coef RatCoef D * q x) = fun x => algebraMap Coef RatCoef (q1 x) from
        funext fun x => (hq1 x).symm]
  have hmul : mulOp D * normOp r = normOp q1 * L1 := by
    rw [mulOp_mul_normOp, hcoef, normOp_mul_L1]
  exact mem_ideal_of_mul_mem_ideal (normOp_mem r) (normOp_mem q1) hD hmul

end A207123
