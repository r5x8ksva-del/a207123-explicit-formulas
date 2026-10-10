import A207123.ShapeCases
import A207123.SingleSumAsc
import A207123.Coeffs

/-!
# 论文第 6.1 节其余的断言

* 定理 6.1 之后：不以上升结尾的那部分 `NA k m` 正是定理 6.1 排除的形状，`A(s) = S(m+s, m)`（`NA_single_sum`、
  `NA_excluded_form`：注记 5.2 的 `P_m·Σ_k NA k m xᵏ = 1` 与 `1/P_m` 的系数公式 `coeff_inv_Ppoly`）；`m = 0` 时
  定理 6.1 的结论不成立（`U_zero_single_sum`：`U_k(0) = 1 = NA k 0`）。
* 定理 6.2 之后：`U^↑_k(1) = Σ_{s≥0} C(k−2−2s, s)`，也是被排除的形状（`NUp_one_single_sum`、
  `NUp_one_excluded_form`；论文写成 `G^↑_1 = x²/b_1 = x^{−1}u/(1−u)`），所以定理 6.2 的条件 `m ≥ 2` 不能放宽。
  一般的 `m`：`U^↑_k(m)` 是定理 4.6 的第二个和（`NUp_explicit`：`U_explicit` 减去 `NA`）。
* 注记 6.4 的第一句：`α < 0`、`α + β = 1` 时（例如 `(α, β) = (−1, 2)`）每个数列都有定理 6.3 那样的表示
  （`shape_neg`；`ShapeRepZ` 是 `ShapeRep` 的整数参数版本，`shapeRepZ_natCast`）。`s = k` 一项是 `C(βk, βk) = 1`，
  `s > k` 的项为 0，所以系数可以逐个解出（`triA`）。`shape_sum_one` 把它与 `ShapeCases.lean` 的 `shape_10`、
  `shape_01` 合起来：`β ≥ 0`、`α + β = 1` 的形状对每个数列都有表示（论文第 6 节开头）。
-/

namespace A207123

open Finset

noncomputable section

/-- `binomZ` 在自然数处就是 `Nat.choose`。 -/
theorem binomZ_natCast (a b : ℕ) : binomZ a b = a.choose b := by
  unfold binomZ
  split_ifs with h
  · simp only [Int.toNat_natCast]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]

/-! ## 1. 不以上升结尾的部分 -/

/-- `NA k m = Σ_{s ≤ k/3} S(m+s, m)·C(k+m−2s, m+s)`（`P_m·Σ NA xᵏ = 1` 与 `coeff_inv_Ppoly`）。 -/
theorem NA_eq_sum (k m : ℕ) :
    (NA k m : ℚ) = ∑ s ∈ range (k / 3 + 1),
      (Nat.stirlingSecond (m + s) m : ℚ) * ((k + m - 2 * s).choose (m + s) : ℚ) := by
  have h : NAser m = (↑(Ppoly ℚ m) : PowerSeries ℚ)⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one (constantCoeff_Ppoly_ne m)).2 (by rw [mul_comm]; exact P_mul_NAser m)
  rw [← coeff_NAser, h, coeff_inv_Ppoly]

/-- 同一公式写成 `U_explicit` 第一个和的样子（`C(k+m−2s, k−3s)`），在 `ℕ` 中。 -/
theorem NA_eq_first (k m : ℕ) :
    NA k m = ∑ s ∈ range (k / 3 + 1), Nat.stirlingSecond (m + s) m * Nat.choose (k + m - 2 * s) (k - 3 * s) := by
  have h := NA_eq_sum k m
  have e : ∑ s ∈ range (k / 3 + 1), (Nat.stirlingSecond (m + s) m : ℚ) * ((k + m - 2 * s).choose (m + s) : ℚ) =
      ∑ s ∈ range (k / 3 + 1), (Nat.stirlingSecond (m + s) m : ℚ) * ((k + m - 2 * s).choose (k - 3 * s) : ℚ) := by
    refine sum_congr rfl fun s hs => ?_
    rw [mem_range] at hs
    rw [Nat.choose_symm_of_eq_add (show k + m - 2 * s = (m + s) + (k - 3 * s) by omega)]
  rw [e] at h
  exact_mod_cast h

/-- 定理 6.1 之后：不以上升结尾的那部分 `NA k m = Σ_{s≥0} S(m+s, m)·C(k+m−2s, m+s)`，正是定理 6.1 排除的形状
（`c = m`、`d = 0`、`A(s) = S(m+s, m)`）。 -/
theorem NA_single_sum (k m : ℕ) :
    (NA k m : ℂ) = ∑ᶠ s : ℤ, (if 0 ≤ s then (Nat.stirlingSecond (m + s.toNat) m : ℂ) else 0) *
      (binomZ (k + m - 2 * s) (m + s) : ℂ) := by
  have hC : (NA k m : ℂ) = ∑ s ∈ range (k / 3 + 1),
      (Nat.stirlingSecond (m + s) m : ℂ) * ((k + m - 2 * s).choose (m + s) : ℂ) := by
    have h := congrArg (fun q : ℚ => (q : ℂ)) (NA_eq_sum k m)
    push_cast at h
    exact h
  rw [hC, finsum_eq_sum_of_support_subset _ (s := (range (k / 3 + 1)).map Nat.castEmbedding) ?_]
  · rw [sum_map]
    refine sum_congr rfl fun t ht => ?_
    have htk : 3 * t ≤ k := by
      rw [mem_range] at ht
      omega
    simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
    rw [ite_eq_left (by omega), show (k : ℤ) + m - 2 * t = ((k + m - 2 * t : ℕ) : ℤ) by omega,
      show (m : ℤ) + t = ((m + t : ℕ) : ℤ) by omega, binomZ_natCast]
  · intro s hs
    simp only [Function.mem_support, ne_eq] at hs
    have hs0 : 0 ≤ s := by
      by_contra h
      exact hs (by rw [ite_eq_right h, zero_mul])
    rw [ite_eq_left hs0] at hs
    have hb : binomZ ((k : ℤ) + m - 2 * s) ((m : ℤ) + s) ≠ 0 := by
      intro h0
      apply hs
      rw [h0, Nat.cast_zero, mul_zero]
    unfold binomZ at hb
    have hsk : 3 * s ≤ (k : ℤ) := by
      by_contra h
      apply hb
      rw [ite_eq_right (by omega)]
    rw [Finset.mem_coe, Finset.mem_map]
    exact ⟨s.toNat, mem_range.2 (by omega), by simp only [Nat.castEmbedding_apply]; omega⟩

/-- 存在形式，与 `thm_S` 的陈述同形。 -/
theorem NA_excluded_form (m : ℕ) : ∃ (c d : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
    (NA k m : ℂ) = ∑ᶠ s : ℤ, A s * (binomZ (k + c - 2 * s) (m + s + d) : ℂ) := by
  refine ⟨m, 0, 0, fun s => if 0 ≤ s then (Nat.stirlingSecond (m + s.toNat) m : ℂ) else 0, fun k _ => ?_⟩
  rw [NA_single_sum]
  refine finsum_congr fun s => ?_
  simp only [add_zero]

/-- 定理 6.1 之后：`m = 0` 时定理 6.1 的结论不成立（`U_k(0) = 1 = NA k 0`）。 -/
theorem U_zero_single_sum : ∃ (c d : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
    (U k 0 : ℂ) = ∑ᶠ s : ℤ, A s * (binomZ (k + c - 2 * s) ((0 : ℕ) + s + d) : ℂ) := by
  obtain ⟨c, d, k₀, A, h⟩ := NA_excluded_form 0
  refine ⟨c, d, k₀, A, fun k hk => ?_⟩
  rw [show (U k 0 : ℂ) = NA k 0 by rw [U_zero_right, NA_zero_right], h k hk]

/-! ## 2. 以上升结尾的部分 -/

/-- `U^↑_k(m)` 是定理 4.6 的第二个和（`U_explicit` 减去 `NA`）。 -/
theorem NUp_explicit (k m : ℕ) :
    NUp k m = if 2 ≤ k then
        ∑ j ∈ Icc 1 m, j * ∑ s ∈ range ((k - 2) / 3 + 1),
          hc s (vars j m) * Nat.choose (k - 2 + m - j - 2 * s) (k - 2 - 3 * s)
      else 0 := by
  have h := NUp_add_NA k m
  rw [U_explicit, ← NA_eq_first] at h
  exact Nat.add_right_cancel (h.trans (Nat.add_comm _ _))

theorem hc_single_one (s : ℕ) : hc s [1] = 1 := by
  induction s with
  | zero => simp
  | succ s ih => simp [hc_succ_cons, ih]

/-- 定理 6.2 之后：`U^↑_k(1) = Σ_{s≥0} C(k−2−2s, s)`（论文：`G^↑_1 = x²/b_1 = x^{−1}u/(1−u)`）。 -/
theorem NUp_one_single_sum (k : ℕ) :
    (NUp k 1 : ℂ) = ∑ᶠ s : ℤ, (if 0 ≤ s then (1 : ℂ) else 0) * (binomZ (k - 2 - 2 * s) s : ℂ) := by
  rw [NUp_explicit]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rw [ite_eq_right (by omega), Nat.cast_zero]
    refine (finsum_eq_zero_of_forall_eq_zero fun s => ?_).symm
    by_cases hs : 0 ≤ s
    · rw [ite_eq_left hs, one_mul]
      unfold binomZ
      rw [ite_eq_right (by omega), Nat.cast_zero]
    · rw [ite_eq_right hs, zero_mul]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    rw [ite_eq_left hk, Nat.add_sub_cancel, Icc_self, sum_singleton, one_mul]
    have hv : vars 1 1 = [1] := by simp [vars]
    simp only [hv, hc_single_one, one_mul, Nat.add_sub_cancel]
    rw [Nat.cast_sum, finsum_eq_sum_of_support_subset _ (s := (range (n / 3 + 1)).map Nat.castEmbedding) ?_]
    · rw [sum_map]
      refine sum_congr rfl fun t ht => ?_
      have htn : 3 * t ≤ n := by
        rw [mem_range] at ht
        omega
      simp only [Nat.castEmbedding_apply]
      rw [ite_eq_left (by omega), one_mul, show ((n + 2 : ℕ) : ℤ) - 2 - 2 * t = ((n - 2 * t : ℕ) : ℤ) by omega,
        binomZ_natCast, Nat.choose_symm_of_eq_add (show n - 2 * t = t + (n - 3 * t) by omega)]
    · intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      have hs0 : 0 ≤ s := by
        by_contra h
        exact hs (by rw [ite_eq_right h, zero_mul])
      rw [ite_eq_left hs0, one_mul] at hs
      unfold binomZ at hs
      have hsn : 3 * s ≤ (n : ℤ) := by
        by_contra h
        apply hs
        rw [ite_eq_right (by omega), Nat.cast_zero]
      rw [Finset.mem_coe, Finset.mem_map]
      exact ⟨s.toNat, mem_range.2 (by omega), by simp only [Nat.castEmbedding_apply]; omega⟩

/-- 存在形式：`m = 1` 时定理 6.2 的结论不成立（`c = −2`、`d = −1`、`A(s) = [s ≥ 0]`）。 -/
theorem NUp_one_excluded_form : ∃ (c d : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
    (NUp k 1 : ℂ) = ∑ᶠ s : ℤ, A s * (binomZ (k + c - 2 * s) ((1 : ℕ) + s + d) : ℂ) := by
  refine ⟨-2, -1, 0, fun s => if 0 ≤ s then 1 else 0, fun k _ => ?_⟩
  rw [NUp_one_single_sum]
  refine finsum_congr fun s => ?_
  rw [show (k : ℤ) + -2 - 2 * s = (k : ℤ) - 2 - 2 * s by omega, show ((1 : ℕ) : ℤ) + s + -1 = s by omega]

/-! ## 3. 注记 6.4：`α < 0`、`α + β = 1` -/

/-- 定理 6.3 的表示，`α, β` 取整数（`ShapeRep` 的整数参数版本）：存在整数 `c, d, s₀`、`k₀ ≥ 0` 与复数 `A(s)`，使
`k ≥ k₀` 时 `f(k) = Σ_{s≥s₀} A(s)·C(k+c−αs, βs+d)`。 -/
def ShapeRepZ (f : ℕ → ℂ) (α β : ℤ) : Prop :=
  ∃ (c d s₀ : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
    f k = ∑ᶠ s : ℤ, if s₀ ≤ s then A s * (binomZ (k + c - α * s) (β * s + d) : ℂ) else 0

/-- `α, β ≥ 0` 时与 `ShapeRep` 相同。 -/
theorem shapeRepZ_natCast (f : ℕ → ℂ) (α β : ℕ) : ShapeRepZ f α β ↔ ShapeRep f α β := Iff.rfl

/-- 解三角方程组的系数：`A(k) = f(k) − Σ_{s<k} A(s)·C(k+ps, (p+1)s)`。 -/
def triA (f : ℕ → ℂ) (p : ℕ) (k : ℕ) : ℂ :=
  f k - ∑ s : Fin k, triA f p s * ((k + p * s).choose ((p + 1) * s) : ℂ)
termination_by k
decreasing_by exact s.isLt

theorem triA_eq (f : ℕ → ℂ) (p k : ℕ) :
    triA f p k = f k - ∑ s ∈ range k, triA f p s * ((k + p * s).choose ((p + 1) * s) : ℂ) := by
  rw [triA, Fin.sum_univ_eq_sum_range (fun s => triA f p s * ((k + p * s).choose ((p + 1) * s) : ℂ)) k]

theorem sum_triA (f : ℕ → ℂ) (p k : ℕ) :
    f k = ∑ s ∈ range (k + 1), triA f p s * ((k + p * s).choose ((p + 1) * s) : ℂ) := by
  rw [sum_range_succ, show k + p * k = (p + 1) * k by ring, Nat.choose_self, Nat.cast_one, mul_one,
    triA_eq f p k]
  ring

/-- 注记 6.4 的第一句：`α < 0`、`α + β = 1` 时每个数列都有表示（`c = d = s₀ = k₀ = 0`）。 -/
theorem shape_neg (f : ℕ → ℂ) {α β : ℤ} (hα : α < 0) (hαβ : α + β = 1) : ShapeRepZ f α β := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, α = -(p : ℤ) := ⟨(-α).toNat, by omega⟩
  obtain rfl : β = (p : ℤ) + 1 := by omega
  refine ⟨0, 0, 0, 0, fun s => triA f p s.toNat, fun k _ => ?_⟩
  rw [sum_triA f p k, finsum_eq_sum_of_support_subset _ (s := (range (k + 1)).map Nat.castEmbedding) ?_]
  · rw [sum_map]
    refine sum_congr rfl fun t ht => ?_
    have htk : t ≤ k := Nat.lt_succ_iff.1 (mem_range.1 ht)
    simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
    have e1 : (k : ℤ) + 0 - -(p : ℤ) * t = ((k + p * t : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_mul]
      ring
    have e2 : ((p : ℤ) + 1) * t + 0 = (((p + 1) * t : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [ite_eq_left (by omega), e1, e2, binomZ_natCast]
  · intro s hs
    simp only [Function.mem_support, ne_eq] at hs
    have hs0 : 0 ≤ s := by
      by_contra h
      exact hs (by rw [ite_eq_right h])
    rw [ite_eq_left hs0] at hs
    have hb : binomZ ((k : ℤ) + 0 - -(p : ℤ) * s) (((p : ℤ) + 1) * s + 0) ≠ 0 := by
      intro h0
      apply hs
      rw [h0, Nat.cast_zero, mul_zero]
    unfold binomZ at hb
    have hsk : s ≤ k := by
      by_contra h
      apply hb
      have e1 : (k : ℤ) + 0 - -(p : ℤ) * s = k + p * s := by ring
      have e2 : ((p : ℤ) + 1) * s + 0 = p * s + s := by ring
      rw [e1, e2, ite_eq_right (by omega)]
    rw [Finset.mem_coe, Finset.mem_map]
    exact ⟨s.toNat, mem_range.2 (by omega), by simp only [Nat.castEmbedding_apply]; omega⟩

/-- `β ≥ 0`、`α + β = 1` 的整数形状对每个数列都有表示：`(1,0)`、`(0,1)` 由 `shape_10`、`shape_01`，`α < 0` 由
`shape_neg`（论文第 6 节开头与注记 6.4）。 -/
theorem shape_sum_one (f : ℕ → ℂ) {α β : ℤ} (hβ : 0 ≤ β) (hαβ : α + β = 1) : ShapeRepZ f α β := by
  rcases lt_or_ge α 0 with hα | hα
  · exact shape_neg f hα hαβ
  · rcases (by omega : (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using (shapeRepZ_natCast f 1 0).2 (shape_10 f)
    · simpa using (shapeRepZ_natCast f 0 1).2 (shape_01 f)

end

end A207123
