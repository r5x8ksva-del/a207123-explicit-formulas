import A207123.EndAscent
import A207123.RStirling

/-!
# 论文命题 4.7：双射的存在（两边计数相等）

论文命题 4.7：「长 `k`、取值在 `{0, …, m}`、恰有 `s` 个上升且不以上升结尾的好序列，与『`{1, …, k+m−2s}` 的
`(k−3s)` 元子集』和『`{1, …, m+s}` 分成 `m` 块的集合划分』组成的对之间有显式双射」。本文件形式化双射的存在：

* `NAs k m s`：`H_k(m)` 中恰有 `s` 个上升且不以上升结尾的序列个数。
* `NAs_eq_g`：`NAs k m s` 是 `1/∏_{v=0}^{m}(1 − x − v·y·x³)` 的 `x^k y^s` 系数（`Formula.lean` 的 `g`）。证明照细化引理 1：
  按最大值首次出现的位置分类（`L_split`）；首位是最大值时上升数与结尾都不变，`a :: M :: M :: t` 恰在第 1 个位置
  上升、结尾由 `t` 决定，截断块 `[a, m]` 以上升结尾、不计入。
* `NAs_explicit`：`NAs k m s = [3s ≤ k]·S(m+s, m)·C(k+m−2s, k−3s)`（与 `Us_explicit` 的第一项相同）。
* `prop_bijection`：`3s ≤ k` 时两边一一对应（两边个数都是 `C(k+m−2s, k−3s)·S(m+s, m)`；集合划分用
  `RStirling.lean` 的 `setParts`，`S(m+s, m)` 是划分个数由 `stirlingSecond_eq_partCount` 给出）。

没有形式化的：论文给出的显式双射（用 `S`、`T` 与竖线组成的词把块编码成子集与划分）。这里的证明只比较个数。
-/

namespace A207123

open Finset

/-- `H_k(m)` 中恰有 `s` 个上升且不以上升结尾的序列个数。 -/
def NAs (k m s : ℕ) : ℕ := ((L k m).filter fun l => asc l = s ∧ endsAsc l = false).card

/-- 辅助引理（命题 4.7）：`NAs 0 m s = [s = 0]`。 -/
theorem NAs_zero_left (m s : ℕ) : NAs 0 m s = if s = 0 then 1 else 0 := by
  unfold NAs
  have h2 : endsAsc [] = false := rfl
  rw [L_zero_left, filter_singleton, asc_nil, h2]
  by_cases hs : s = 0
  · subst hs
    simp
  · rw [ite_eq_right (fun h => hs h.1.symm), ite_eq_right hs, card_empty]

/-- 辅助引理（命题 4.7）：`NAs k 0 s = [s = 0]`（只有全零序列）。 -/
theorem NAs_zero_right (k s : ℕ) : NAs k 0 s = if s = 0 then 1 else 0 := by
  unfold NAs
  rw [L_zero_right, filter_singleton, asc_replicate_zero, endsAsc_replicate_zero]
  by_cases hs : s = 0
  · subst hs
    simp
  · rw [ite_eq_right (fun h => hs h.1.symm), ite_eq_right hs, card_empty]

/-- 辅助引理（命题 4.7）：第二部分 `(m+1) :: w`：上升数与结尾都不变。 -/
theorem NAs_cons_max (k m s : ℕ) :
    (((L k (m + 1)).image (List.cons (m + 1))).filter fun l => asc l = s ∧ endsAsc l = false).card
      = NAs k (m + 1) s := by
  rw [filter_image, card_image_of_injective _ List.cons_injective]
  unfold NAs
  congr 1
  apply filter_congr
  intro w hw
  rw [asc_cons_of_le (mem_L.mp hw).2.1, endsAsc_cons_of_le (mem_L.mp hw).2.1]

/-- 辅助引理（命题 4.7）：第三部分 `a :: (m+1) :: (m+1) :: t`：上升数是 `asc t + 1`，结尾由 `t` 决定。 -/
theorem NAs_third (k m s : ℕ) :
    ((((range (m + 1)) ×ˢ (L k (m + 1))).image
        (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2)).filter
          fun l => asc l = s ∧ endsAsc l = false).card
      = (m + 1) * ((L k (m + 1)).filter fun t => asc t + 1 = s ∧ endsAsc t = false).card := by
  rw [filter_image, card_image_of_injective _ (L_split_inj m)]
  have h : ∀ p ∈ (range (m + 1)) ×ˢ (L k (m + 1)),
      (asc (p.1 :: (m + 1) :: (m + 1) :: p.2) = s ∧ endsAsc (p.1 :: (m + 1) :: (m + 1) :: p.2) = false) ↔
        (asc p.2 + 1 = s ∧ endsAsc p.2 = false) := by
    intro p hp
    rw [mem_product, mem_range, mem_L] at hp
    rw [asc_third hp.1 hp.2.2.1, endsAsc_third p.1 hp.2.2.1]
  rw [filter_congr h, filter_product_right (fun t => asc t + 1 = s ∧ endsAsc t = false), card_product,
    card_range]

/-- 辅助引理（命题 4.7，k ≥ 3）：按最大值首次出现的位置分类。 -/
theorem NAs_split (k m s : ℕ) :
    NAs (k + 3) (m + 1) s = NAs (k + 3) m s + NAs (k + 2) (m + 1) s
      + (m + 1) * ((L k (m + 1)).filter fun t => asc t + 1 = s ∧ endsAsc t = false).card := by
  obtain ⟨hAB, hAC, hBC⟩ := L_split_disjoint k m
  show ((L (k + 3) (m + 1)).filter fun l => asc l = s ∧ endsAsc l = false).card = _
  rw [L_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_union_left.mpr ⟨hAC, hBC⟩)),
    filter_union, card_union_of_disjoint (disjoint_filter_filter hAB), NAs_cons_max, NAs_third]
  rfl

/-- 辅助引理（命题 4.7，k ≥ 3，s ≥ 1）：`NAs (k+3) (m+1) (s+1) = NAs (k+3) m (s+1) + NAs (k+2) (m+1) (s+1)
+ (m+1)·NAs k (m+1) s`。 -/
theorem NAs_rec (k m s : ℕ) :
    NAs (k + 3) (m + 1) (s + 1)
      = NAs (k + 3) m (s + 1) + NAs (k + 2) (m + 1) (s + 1) + (m + 1) * NAs k (m + 1) s := by
  rw [NAs_split]
  have : ((L k (m + 1)).filter fun t => asc t + 1 = s + 1 ∧ endsAsc t = false).card = NAs k (m + 1) s := by
    unfold NAs
    congr 1
    apply filter_congr
    intro t _
    rw [Nat.add_right_cancel_iff]
  rw [this]

/-- 辅助引理（命题 4.7，k ≥ 3，s = 0）：第三部分至少有一个上升，不计入。 -/
theorem NAs_rec_zero (k m : ℕ) :
    NAs (k + 3) (m + 1) 0 = NAs (k + 3) m 0 + NAs (k + 2) (m + 1) 0 := by
  rw [NAs_split]
  have : ((L k (m + 1)).filter fun t => asc t + 1 = 0 ∧ endsAsc t = false).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro t _ h
    exact Nat.add_one_ne_zero _ h.1
  rw [this, mul_zero, add_zero]

/-- 辅助引理（命题 4.7，k = 1）。 -/
theorem NAs_one (m s : ℕ) : NAs 1 (m + 1) s = NAs 1 m s + NAs 0 (m + 1) s := by
  show ((L 1 (m + 1)).filter fun l => asc l = s ∧ endsAsc l = false).card = _
  rw [L_one_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_L_cons 1 0 m)), NAs_cons_max]
  rfl

/-- 辅助引理（命题 4.7，k = 2）：截断块 `[a, m+1]` 以上升结尾，不计入。 -/
theorem NAs_two (m s : ℕ) : NAs 2 (m + 1) s = NAs 2 m s + NAs 1 (m + 1) s := by
  have hAC : Disjoint (L 2 m) ((range (m + 1)).image (fun a => [a, m + 1])) := by
    rw [disjoint_left]
    intro l hlA hlC
    rw [mem_L] at hlA
    rw [mem_image] at hlC
    obtain ⟨a, -, rfl⟩ := hlC
    have := hlA.2.1 (m + 1) (by simp)
    omega
  have hBC : Disjoint ((L 1 (m + 1)).image (List.cons (m + 1)))
      ((range (m + 1)).image (fun a => [a, m + 1])) := by
    rw [disjoint_left]
    intro l hlB hlC
    rw [mem_image] at hlB hlC
    obtain ⟨w, -, rfl⟩ := hlB
    obtain ⟨a, ha, hae⟩ := hlC
    rw [mem_range] at ha
    have := (List.cons.inj hae).1
    omega
  have hC : (((range (m + 1)).image (fun a => [a, m + 1])).filter
      fun l => asc l = s ∧ endsAsc l = false) = ∅ := by
    rw [filter_eq_empty_iff]
    intro l hl
    rw [mem_image] at hl
    obtain ⟨a, ha, rfl⟩ := hl
    rw [mem_range] at ha
    simp [endsAsc, ha]
  show ((L 2 (m + 1)).filter fun l => asc l = s ∧ endsAsc l = false).card = _
  rw [L_two_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_union_left.mpr ⟨hAC, hBC⟩)),
    filter_union, card_union_of_disjoint (disjoint_filter_filter (disjoint_L_cons 2 1 m)),
    NAs_cons_max, hC, card_empty, add_zero]
  rfl

/-- 辅助引理（命题 4.7）：`NAs k m s` 是 `1/∏_{v=0}^{m}(1 − x − v·y·x³)` 的 `x^k y^s` 系数 `g [m, …, 0] k s`。 -/
theorem NAs_eq_g (k m s : ℕ) : NAs k m s = g (vars 0 m) k s := by
  induction m generalizing k s with
  | zero => rw [NAs_zero_right, vars_zero_zero, g_single_zero]
  | succ m ihm =>
    induction k using Nat.strong_induction_on generalizing s with
    | _ k ihk =>
      have hv : vars 0 (m + 1) = (m + 1) :: vars 0 m := vars_succ (Nat.zero_le _)
      match k, s with
      | 0, s => rw [NAs_zero_left, g_zero]
      | 1, s =>
        have hg := g_cons (m + 1) (vars 0 m) 1 s
        rw [← hv, ite_eq_right (show ¬ (3 ≤ 1 ∧ 1 ≤ s) by omega), ite_eq_left (show 1 ≤ 1 by omega), add_zero,
          show 1 - 1 = 0 from rfl] at hg
        rw [NAs_one, ihm 1 s, ihk 0 (by omega) s, hg]
      | 2, s =>
        have hg := g_cons (m + 1) (vars 0 m) 2 s
        rw [← hv, ite_eq_right (show ¬ (3 ≤ 2 ∧ 1 ≤ s) by omega), ite_eq_left (show 1 ≤ 2 by omega), add_zero,
          show 2 - 1 = 1 from rfl] at hg
        rw [NAs_two, ihm 2 s, ihk 1 (by omega) s, hg]
      | k + 3, 0 =>
        have hg := g_rec (m + 1) (vars 0 m) k 0
        rw [← hv, ite_eq_left rfl, add_zero] at hg
        rw [NAs_rec_zero, ihm (k + 3) 0, ihk (k + 2) (by omega) 0, hg]
      | k + 3, s + 1 =>
        have hg := g_rec (m + 1) (vars 0 m) k (s + 1)
        rw [← hv, ite_eq_right (Nat.add_one_ne_zero s), Nat.add_sub_cancel] at hg
        rw [NAs_rec, ihm (k + 3) (s + 1), ihk (k + 2) (by omega) (s + 1), ihk k (by omega) s, hg]
        ring

/-- **命题 4.7**（计数）：`H_k(m)` 中恰有 `s` 个上升且不以上升结尾的序列有 `C(k+m−2s, k−3s)·S(m+s, m)` 个
（`3s > k` 时没有）。 -/
theorem NAs_explicit (k m s : ℕ) :
    NAs k m s = if 3 * s ≤ k then Nat.stirlingSecond (m + s) m * Nat.choose (k + m - 2 * s) (k - 3 * s) else 0 := by
  rw [NAs_eq_g]
  unfold g
  by_cases h : 3 * s ≤ k
  · rw [ite_eq_left h, ite_eq_left h, length_vars (Nat.zero_le _), hc_vars_zero, Nat.multichoose_eq]
    congr 2
    omega
  · rw [ite_eq_right h, ite_eq_right h]

/-- **命题 4.7**（双射的存在）：`3s ≤ k` 时，长 `k`、取值在 `{0, …, m}`、恰有 `s` 个上升且不以上升结尾的好序列，
与「`{1, …, k+m−2s}` 的 `(k−3s)` 元子集」和「`{1, …, m+s}` 分成 `m` 块的集合划分」组成的对之间存在双射（两边个数
都是 `C(k+m−2s, k−3s)·S(m+s, m)`）。论文给出的显式双射没有形式化。 -/
theorem prop_bijection {k m s : ℕ} (h : 3 * s ≤ k) :
    Nonempty (((L k m).filter fun l => asc l = s ∧ endsAsc l = false) ≃
      ((Icc 1 (k + m - 2 * s)).powersetCard (k - 3 * s) ×ˢ setParts 0 (m + s) m)) := by
  refine ⟨Fintype.equivOfCardEq ?_⟩
  have hN := NAs_explicit k m s
  rw [ite_eq_left h] at hN
  unfold NAs at hN
  rw [Fintype.card_coe, Fintype.card_coe, card_product, card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel,
    ← partCount, ← stirlingSecond_eq_partCount, hN, mul_comm]

end A207123
