import A207123.Formula

/-!
# 按上升数细化（报告 T2.2 的细化引理 1、T2.4 第二式）

上升数 `asc l`：满足 `l[i] < l[i+1]` 的下标 `i` 的个数。`Us k m s`：长 `k`、取值 ≤ `m`、
恰有 `s` 个上升的合法序列个数（报告的 `U_k(m,s)`）。

本文件证明：
* `asc_eq_card`：`asc` 的逐下标刻画（递归定义与「数下标」一致）；
* `sum_Us`：按 `s` 求和回到 `U k m`（长 `k` 的序列上升数 ≤ `k − 1`）；
* T2.2 按上升数细化的引理 1（每条单独成定理，避免 ℕ 减法截断）：
  `lemma1_asc`（k ≥ 3，s ≥ 1）、`lemma1_asc_s0`（k ≥ 3，s = 0）、`lemma1_asc_one`（k = 1）、
  `lemma1_asc_two`（k = 2，截断块项 `(m+1)·[s=1]` 单列），以及边界
  `Us_zero_left`（`U_0(m,s) = [s=0]`）、`Us_zero_right`（`U_k(0,s) = [s=0]`，
  即约定 `U_k(−1,s) = 0` 下 m = 0 的情形）；
* T2.4 第二式 `Us_explicit`：
    U_k(m,s) = S(m+s,m)·C(k+m−2s, k−3s) + Σ_{j=1}^{m} j·H(m,s−1,j)·C(k+m−j−2s, k+1−3s)，
  其中 `H(m,s,j) = hc s (vars j m) = h_s(j,…,m)`，s = 0 时第二项为空。

证明路线：
* 细化引理 1：k ≥ 3 复用 `Basic.lean` 的分类 `L_split`（按最大值首次出现的位置），k = 1, 2 另证
  小分解 `L_one_split`、`L_two_split`。首位是最大值时首个位置不是上升（`asc_cons_of_le`）；
  `a :: M :: M :: t`（a < M）恰在第 1 个位置上升，其余上升来自 `t`（`asc_third`）。
* 显式公式：沿用 `Formula.lean` 的路线，但把 `E l n = Σ_s g l n s` 换成单项 `g l n s`
  （它是 ∏_{v∈l}(1−x−v·y·x³)^{-1} 的 xⁿyˢ 系数）。`g_cons` 是「加入最大变量」的递推（对一切 n）；
  闭式 `Fs m k s = g [m..0] k s + [k ≥ 2][s ≥ 1]·Σ_j j·g [m..j] (k−2) (s−1)`
  （即 G_m(x,y) = 1/P_m + y·x²·Σ_{j=1}^{m} j/∏_{v=j}^{m}(1−x−v·y·x³) 的 x^k y^s 系数）满足与
  细化引理 1 相同的递推与边界（`Fs_rec` 等），归纳得 `Us_eq_Fs`，再换成 Stirling 数与二项式。
-/

namespace A207123

open Finset

/-! ### 上升数 -/

/-- 上升数：满足 `l[i] < l[i+1]` 的下标 `i` 的个数。 -/
def asc : List ℕ → ℕ
  | a :: b :: t => (if a < b then 1 else 0) + asc (b :: t)
  | _ => 0

/-- 空列表没有上升。 -/
@[simp] theorem asc_nil : asc [] = 0 := rfl

/-- 单元素列表没有上升。 -/
@[simp] theorem asc_single (a : ℕ) : asc [a] = 0 := rfl

/-- `asc` 的定义式：`asc (a :: b :: t) = [a < b] + asc (b :: t)`。 -/
theorem asc_cons_cons (a b : ℕ) (t : List ℕ) :
    asc (a :: b :: t) = (if a < b then 1 else 0) + asc (b :: t) := rfl

/-- `asc` 的逐下标刻画：上升数等于满足 `l[i] < l[i+1]` 的下标 `i < |l| − 1` 的个数
（报告 T2.2 中上升数的定义）。 -/
theorem asc_eq_card (l : List ℕ) :
    asc l = ((range (l.length - 1)).filter fun i => l.getD i 0 < l.getD (i + 1) 0).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      rw [asc_cons_cons, ih, card_filter, card_filter]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [sum_range_succ', add_comm]
      simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- 上升数不超过 `|l| − 1`。 -/
theorem asc_le (l : List ℕ) : asc l ≤ l.length - 1 := by
  rw [asc_eq_card]
  exact (card_filter_le _ _).trans (card_range _).le

/-- 首项是上界时，第一个位置不是上升：`asc (M :: t) = asc t`（报告 T2.2 的证明要点）。 -/
theorem asc_cons_of_le {M : ℕ} {t : List ℕ} (ht : ∀ x ∈ t, x ≤ M) : asc (M :: t) = asc t := by
  match t, ht with
  | [], _ => rfl
  | b :: t, ht =>
    have hb : b ≤ M := ht b (by simp)
    rw [asc_cons_cons, ite_eq_right (show ¬ M < b by omega), zero_add]

/-- `a :: M :: M :: t`（`a < M`，`t` 的项都 ≤ `M`）恰在第 1 个位置上升，其余上升来自 `t`
（报告 T2.2 的证明要点）。 -/
theorem asc_third {a M : ℕ} {t : List ℕ} (ha : a < M) (ht : ∀ x ∈ t, x ≤ M) :
    asc (a :: M :: M :: t) = asc t + 1 := by
  rw [asc_cons_cons, asc_cons_cons, asc_cons_of_le ht, ite_eq_left ha,
    ite_eq_right (lt_irrefl M)]
  omega

/-- 全零序列没有上升。 -/
theorem asc_replicate_zero (k : ℕ) : asc (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, asc_cons_of_le (fun x hx => (List.eq_of_mem_replicate hx).le), ih]

/-! ### `Us` 与按 `s` 求和 -/

/-- `Us k m s`：长 k、取值 ≤ m、恰有 s 个上升的合法序列个数（报告 T2.2 的 U_k(m,s)）。 -/
def Us (k m s : ℕ) : ℕ := ((L k m).filter fun l => asc l = s).card

/-- 按 `s` 求和回到 `U k m`（报告 T2.2 的健全性：长 `k` 的序列上升数 < k + 1）。 -/
theorem sum_Us (k m : ℕ) : ∑ s ∈ range (k + 1), Us k m s = U k m := by
  unfold Us U
  symm
  apply card_eq_sum_card_fiberwise
  intro l hl
  obtain ⟨hlen, -, -⟩ := mem_L.mp (mem_coe.mp hl)
  have := asc_le l
  rw [mem_coe, mem_range]
  omega

/-! ### 边界 -/

/-- `L 0 m = {[]}`：长 0 的序列只有空列表。 -/
theorem L_zero_left (m : ℕ) : L 0 m = {[]} := by
  ext l
  rw [mem_L, mem_singleton]
  constructor
  · rintro ⟨h, -, -⟩
    exact List.eq_nil_of_length_eq_zero h
  · rintro rfl
    simp

/-- `L k 0 = {[0,…,0]}`：取值 ≤ 0 的序列只有全零序列。 -/
theorem L_zero_right (k : ℕ) : L k 0 = {List.replicate k 0} := by
  ext l
  rw [mem_L, mem_singleton]
  constructor
  · rintro ⟨hlen, hle, -⟩
    rw [List.eq_replicate_iff]
    exact ⟨hlen, fun x hx => Nat.le_zero.mp (hle x hx)⟩
  · rintro rfl
    exact ⟨by simp, by simp, legal_replicate k⟩

/-- 边界（报告 T2.2）：`U_0(m,s) = [s = 0]`。 -/
theorem Us_zero_left (m s : ℕ) : Us 0 m s = if s = 0 then 1 else 0 := by
  unfold Us
  rw [L_zero_left, filter_singleton, asc_nil]
  by_cases hs : s = 0
  · subst hs; simp
  · rw [ite_eq_right (Ne.symm hs), ite_eq_right hs, card_empty]

/-- 边界（报告 T2.2，约定 `U_k(−1,s) = 0` 下 m = 0 的情形）：`U_k(0,s) = [s = 0]`，
值域 `{0}` 时只有全零序列，它没有上升。 -/
theorem Us_zero_right (k s : ℕ) : Us k 0 s = if s = 0 then 1 else 0 := by
  unfold Us
  rw [L_zero_right, filter_singleton, asc_replicate_zero]
  by_cases hs : s = 0
  · subst hs; simp
  · rw [ite_eq_right (Ne.symm hs), ite_eq_right hs, card_empty]

/-! ### 细化引理 1（k ≥ 3） -/

/-- 第二部分 `(m+1) :: w`：首位是最大值，首个位置不是上升，上升数不变（报告 T2.2）。 -/
theorem card_filter_cons_max (k m s : ℕ) :
    (((L k (m + 1)).image (List.cons (m + 1))).filter fun l => asc l = s).card
      = Us k (m + 1) s := by
  rw [filter_image, card_image_of_injective _ List.cons_injective]
  unfold Us
  congr 1
  apply filter_congr
  intro w hw
  rw [asc_cons_of_le (mem_L.mp hw).2.1]

/-- 第三部分 `a :: (m+1) :: (m+1) :: t`（`a ≤ m`）：上升数是 `asc t + 1`（报告 T2.2）。 -/
theorem card_filter_third (k m s : ℕ) :
    ((((range (m + 1)) ×ˢ (L k (m + 1))).image
        (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2)).filter fun l => asc l = s).card
      = (m + 1) * ((L k (m + 1)).filter fun t => asc t + 1 = s).card := by
  rw [filter_image, card_image_of_injective _ (L_split_inj m)]
  have h : ∀ p ∈ (range (m + 1)) ×ˢ (L k (m + 1)),
      asc (p.1 :: (m + 1) :: (m + 1) :: p.2) = s ↔ asc p.2 + 1 = s := by
    intro p hp
    rw [mem_product, mem_range, mem_L] at hp
    rw [asc_third hp.1 hp.2.2.1]
  rw [filter_congr h, filter_product_right (fun t => asc t + 1 = s), card_product, card_range]

/-- 细化引理 1 的统一形式（报告 T2.2，k ≥ 3）：第三部分贡献
`(m+1)·#{t ∈ L k (m+1) | asc t + 1 = s}`。 -/
theorem Us_split (k m s : ℕ) :
    Us (k + 3) (m + 1) s = Us (k + 3) m s + Us (k + 2) (m + 1) s
      + (m + 1) * ((L k (m + 1)).filter fun t => asc t + 1 = s).card := by
  obtain ⟨hAB, hAC, hBC⟩ := L_split_disjoint k m
  show ((L (k + 3) (m + 1)).filter fun l => asc l = s).card = _
  rw [L_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_union_left.mpr ⟨hAC, hBC⟩)),
    filter_union, card_union_of_disjoint (disjoint_filter_filter hAB),
    card_filter_cons_max, card_filter_third]
  rfl

/-- 第三部分在 s ≥ 1 时的计数：`#{t | asc t + 1 = s + 1} = U_k(m,s)`。 -/
theorem card_filter_asc_succ (k m s : ℕ) :
    ((L k m).filter fun t => asc t + 1 = s + 1).card = Us k m s := by
  unfold Us
  congr 1
  apply filter_congr
  intro t _
  exact Nat.add_right_cancel_iff

/-- 第三部分不进入 s = 0：`asc t + 1 = 0` 不可能。 -/
theorem card_filter_asc_zero (k m : ℕ) :
    ((L k m).filter fun t => asc t + 1 = 0).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro t _
  exact Nat.add_one_ne_zero _

/-- **报告 T2.2 细化引理 1**（k ≥ 3，s ≥ 1；这里写成 k+3、m+1、s+1）：
`U_k(m,s) = U_k(m−1,s) + U_{k−1}(m,s) + m·U_{k−3}(m,s−1)`。 -/
theorem lemma1_asc (k m s : ℕ) :
    Us (k + 3) (m + 1) (s + 1)
      = Us (k + 3) m (s + 1) + Us (k + 2) (m + 1) (s + 1) + (m + 1) * Us k (m + 1) s := by
  rw [Us_split, card_filter_asc_succ]

/-- **报告 T2.2 细化引理 1**（k ≥ 3，s = 0）：`U_k(m,0) = U_k(m−1,0) + U_{k−1}(m,0)`
（第三部分 `a :: M :: M :: t` 至少有一个上升，不进入 s = 0）。 -/
theorem lemma1_asc_s0 (k m : ℕ) :
    Us (k + 3) (m + 1) 0 = Us (k + 3) m 0 + Us (k + 2) (m + 1) 0 := by
  rw [Us_split, card_filter_asc_zero, mul_zero, add_zero]

/-! ### 细化引理 1（k = 1, 2） -/

/-- `(m+1) :: w` 不在 `L k m` 中（它含有 `m+1`）。 -/
theorem disjoint_L_cons (k k' m : ℕ) :
    Disjoint (L k m) ((L k' (m + 1)).image (List.cons (m + 1))) := by
  rw [disjoint_left]
  intro l hlA hlB
  rw [mem_L] at hlA
  rw [mem_image] at hlB
  obtain ⟨w, -, rfl⟩ := hlB
  have := hlA.2.1 (m + 1) (by simp)
  omega

/-- `k = 1` 的分类（报告 T2.2）：最大值 `m+1` 不出现，或出现在首位。 -/
theorem L_one_split (m : ℕ) :
    L 1 (m + 1) = L 1 m ∪ (L 0 (m + 1)).image (List.cons (m + 1)) := by
  ext l
  simp only [mem_union, mem_image, mem_L]
  constructor
  · rintro ⟨hlen, hle, -⟩
    match l, hlen, hle with
    | [x], _, hle =>
      have hx : x ≤ m + 1 := hle x (by simp)
      by_cases hxM : x = m + 1
      · right
        exact ⟨[], ⟨rfl, by simp, trivial⟩, by rw [hxM]⟩
      · left
        refine ⟨rfl, fun w hw => ?_, trivial⟩
        rw [List.mem_singleton] at hw
        omega
  · rintro (⟨hlen, hle, hleg⟩ | ⟨w, ⟨hwlen, -, -⟩, rfl⟩)
    · exact ⟨hlen, fun x hx => by have := hle x hx; omega, hleg⟩
    · rw [List.length_eq_zero_iff] at hwlen
      subst hwlen
      exact ⟨rfl, by simp, trivial⟩

/-- `k = 2` 的分类（报告 T2.2）：最大值 `m+1` 不出现；出现在首位；只出现在第 2 位
（截断块 `[a, m+1]`，`a ≤ m`）。 -/
theorem L_two_split (m : ℕ) :
    L 2 (m + 1) = L 2 m ∪ (L 1 (m + 1)).image (List.cons (m + 1)) ∪
      (range (m + 1)).image (fun a => [a, m + 1]) := by
  ext l
  simp only [mem_union, mem_image, mem_range, mem_L]
  constructor
  · rintro ⟨hlen, hle, -⟩
    match l, hlen, hle with
    | [x, y], _, hle =>
      have hx : x ≤ m + 1 := hle x (by simp)
      have hy : y ≤ m + 1 := hle y (by simp)
      by_cases hxM : x = m + 1
      · left; right
        exact ⟨[y], ⟨rfl, by simpa using hy, trivial⟩, by rw [hxM]⟩
      · by_cases hyM : y = m + 1
        · right
          exact ⟨x, by omega, by rw [hyM]⟩
        · left; left
          refine ⟨rfl, fun w hw => ?_, trivial⟩
          simp at hw
          omega
  · rintro ((⟨hlen, hle, hleg⟩ | ⟨w, ⟨hwlen, hwle, -⟩, rfl⟩) | ⟨a, ha, rfl⟩)
    · exact ⟨hlen, fun x hx => by have := hle x hx; omega, hleg⟩
    · refine ⟨by simp [hwlen], ?_, legal_of_length_le_two (by simp [hwlen])⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_refl _
      · exact hwle x hx
    · refine ⟨rfl, fun x hx => ?_, trivial⟩
      simp at hx
      omega

/-- `k = 2` 的第三部分 `[a, m+1]`（`a ≤ m`）：恰有一个上升（报告 T2.2 的 `m·[k=2][s=1]`）。 -/
theorem card_filter_two_third (m s : ℕ) :
    (((range (m + 1)).image (fun a => [a, m + 1])).filter fun l => asc l = s).card
      = (m + 1) * (if s = 1 then 1 else 0) := by
  rw [filter_image, card_image_of_injective _ (fun a b h => (List.cons.inj h).1)]
  have hasc : ∀ a ∈ range (m + 1), asc [a, m + 1] = 1 := by
    intro a ha
    rw [mem_range] at ha
    rw [asc_cons_cons, ite_eq_left ha, asc_single]
  by_cases hs : s = 1
  · rw [filter_true_of_mem, card_range, ite_eq_left hs, mul_one]
    intro a ha
    show asc [a, m + 1] = s
    rw [hasc a ha, hs]
  · rw [filter_false_of_mem, card_empty, ite_eq_right hs, mul_zero]
    intro a ha
    show ¬ asc [a, m + 1] = s
    rw [hasc a ha]
    exact Ne.symm hs

/-- **报告 T2.2 细化引理 1**（k = 1，约定 `U_{−2} = 0`）：`U_1(m,s) = U_1(m−1,s) + U_0(m,s)`。 -/
theorem lemma1_asc_one (m s : ℕ) : Us 1 (m + 1) s = Us 1 m s + Us 0 (m + 1) s := by
  show ((L 1 (m + 1)).filter fun l => asc l = s).card = _
  rw [L_one_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_L_cons 1 0 m)), card_filter_cons_max]
  rfl

/-- **报告 T2.2 细化引理 1**（k = 2，约定 `U_{−1} = 0`）：
`U_2(m,s) = U_2(m−1,s) + U_1(m,s) + m·[s=1]`（截断块 `[a, m]` 由 `m·[k=2][s=1]` 单列）。 -/
theorem lemma1_asc_two (m s : ℕ) :
    Us 2 (m + 1) s = Us 2 m s + Us 1 (m + 1) s + (m + 1) * (if s = 1 then 1 else 0) := by
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
  show ((L 2 (m + 1)).filter fun l => asc l = s).card = _
  rw [L_two_split, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_union_left.mpr ⟨hAC, hBC⟩)),
    filter_union, card_union_of_disjoint (disjoint_filter_filter (disjoint_L_cons 2 1 m)),
    card_filter_cons_max, card_filter_two_third]
  rfl

/-! ### 单项系数 `g` 的「加入最大变量」递推 -/

/-- `g l 0 s = [s = 0]`（T2.4 证明用）。 -/
theorem g_zero (l : List ℕ) (s : ℕ) : g l 0 s = if s = 0 then 1 else 0 := by
  unfold g
  by_cases hs : s = 0
  · subst hs; simp [Nat.multichoose_zero_right]
  · rw [ite_eq_right (show ¬ 3 * s ≤ 0 by omega), ite_eq_right hs]

/-- `g l 1 s = [s = 0]·|l|`（T2.4 证明用）。 -/
theorem g_one (l : List ℕ) (s : ℕ) : g l 1 s = if s = 0 then l.length else 0 := by
  unfold g
  by_cases hs : s = 0
  · subst hs; simp [Nat.multichoose_one_right]
  · rw [ite_eq_right (show ¬ 3 * s ≤ 1 by omega), ite_eq_right hs]

/-- `g l 2 s = [s = 0]·multichoose |l| 2`（T2.4 证明用）。 -/
theorem g_two (l : List ℕ) (s : ℕ) :
    g l 2 s = if s = 0 then Nat.multichoose l.length 2 else 0 := by
  unfold g
  by_cases hs : s = 0
  · subst hs; simp
  · rw [ite_eq_right (show ¬ 3 * s ≤ 2 by omega), ite_eq_right hs]

/-- `g [] (n+1) s = 0`：空乘积没有 x 的正幂（T2.4 证明用）。 -/
theorem g_nil_succ (n s : ℕ) : g [] (n + 1) s = 0 := by
  unfold g
  cases s with
  | zero => simp [Nat.multichoose_zero_succ]
  | succ s => simp

/-- `g [0] k s = [s = 0]`：`(1 − x)^{-1}` 的系数（T2.4 证明用）。 -/
theorem g_single_zero (k s : ℕ) : g [0] k s = if s = 0 then 1 else 0 := by
  unfold g
  cases s with
  | zero => simp [Nat.multichoose_one]
  | succ s => rw [hc_succ_single_zero]; simp

/-- `multichoose (n+1) 2 = multichoose n 2 + (n+1)`（Pascal 递推的特例）。 -/
theorem multichoose_succ_two (n : ℕ) :
    Nat.multichoose (n + 1) 2 = Nat.multichoose n 2 + (n + 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.multichoose_succ_succ, Nat.multichoose_one_right]

/-- 「加入最大变量」的逐项递推（T2.4 证明用，对一切 n）：
`g (v::l) n s = g l n s + [n ≥ 3][s ≥ 1]·v·g (v::l) (n−3) (s−1) + [n ≥ 1]·g (v::l) (n−1) s`，
即 `Q′ = (1 − x − v·y·x³)·Q` 的系数形式（`Q′ = ∏_{u∈l}`，`Q = ∏_{u∈v::l}`）。 -/
theorem g_cons (v : ℕ) (l : List ℕ) (n s : ℕ) :
    g (v :: l) n s = g l n s + (if 3 ≤ n ∧ 1 ≤ s then v * g (v :: l) (n - 3) (s - 1) else 0)
      + (if 1 ≤ n then g (v :: l) (n - 1) s else 0) := by
  match n with
  | 0 => simp [g_zero]
  | 1 => by_cases hs : s = 0 <;> simp [g_one, g_zero, hs]
  | 2 => by_cases hs : s = 0 <;> simp [g_two, g_one, hs, multichoose_succ_two]
  | n + 3 =>
    rw [g_rec, ite_eq_left (show 1 ≤ n + 3 by omega), show n + 3 - 3 = n by omega,
      show n + 3 - 1 = n + 2 by omega]
    by_cases hs : s = 0
    · rw [ite_eq_left hs, ite_eq_right (show ¬ (3 ≤ n + 3 ∧ 1 ≤ s) by omega)]
    · rw [ite_eq_right hs, ite_eq_left (show 3 ≤ n + 3 ∧ 1 ≤ s by omega)]

/-! ### 闭式 `Fs m k s` 满足细化引理 1 的递推 -/

/-- 闭式（报告 T2.4）：`Fs m k s = g [m..0] k s + [k ≥ 2][s ≥ 1]·Σ_{j=1}^{m} j·g [m..j] (k−2) (s−1)`，
即 `G_m(x,y) = 1/P_m + y·x²·Σ_{j=1}^{m} j/∏_{v=j}^{m}(1−x−v·y·x³)` 的 `x^k y^s` 系数。 -/
def Fs (m k s : ℕ) : ℕ :=
  g (vars 0 m) k s + if 2 ≤ k ∧ 1 ≤ s then ∑ j ∈ Icc 1 m, j * g (vars j m) (k - 2) (s - 1) else 0

/-- `Fs m 0 s = [s = 0]`，对应 `Us_zero_left`（T2.4 证明用）。 -/
theorem Fs_zero_right (m s : ℕ) : Fs m 0 s = if s = 0 then 1 else 0 := by
  simp [Fs, g_zero]

/-- `Fs 0 k s = [s = 0]`，对应 `Us_zero_right`（T2.4 证明用）。 -/
theorem Fs_zero_left (k s : ℕ) : Fs 0 k s = if s = 0 then 1 else 0 := by
  simp [Fs, vars_zero_zero, g_single_zero]

/-- `Fs` 满足 `lemma1_asc_one` 的递推（T2.4 证明用）。 -/
theorem Fs_one (m s : ℕ) : Fs (m + 1) 1 s = Fs m 1 s + Fs (m + 1) 0 s := by
  simp only [Fs, show ¬ (2 ≤ 1) by omega, show ¬ (2 ≤ 0) by omega, false_and, ite_false, add_zero]
  rw [vars_succ (Nat.zero_le _), g_cons]
  simp

/-- `Fs` 满足 `lemma1_asc_two` 的递推（T2.4 证明用）。 -/
theorem Fs_two (m s : ℕ) :
    Fs (m + 1) 2 s = Fs m 2 s + Fs (m + 1) 1 s + (m + 1) * (if s = 1 then 1 else 0) := by
  have hg : g (vars 0 (m + 1)) 2 s = g (vars 0 m) 2 s + g (vars 0 (m + 1)) 1 s := by
    rw [vars_succ (Nat.zero_le _), g_cons]
    simp
  simp only [Fs, show (2 : ℕ) ≤ 2 by omega, true_and, show ¬ (2 ≤ 1) by omega, false_and,
    ite_false, add_zero, Nat.sub_self, g_zero, hg]
  by_cases hs : s = 0
  · simp [hs]
  · have h1 : 1 ≤ s := by omega
    have hif : (if s - 1 = 0 then 1 else 0) = (if s = 1 then 1 else 0) := by
      split_ifs <;> omega
    rw [ite_eq_left h1, ite_eq_left h1, sum_Icc_succ_top (show 1 ≤ m + 1 by omega), hif]
    ring

/-- 第二部分的和对最大变量 `m+1` 的递推（T2.4 证明用；对每个 `j` 用 `g_cons`，
`j = m+1` 的项在 `g [m..j] (n+1) t` 中为 0）。 -/
theorem sum_g_vars_succ (m n t : ℕ) :
    ∑ j ∈ Icc 1 (m + 1), j * g (vars j (m + 1)) (n + 1) t
      = ∑ j ∈ Icc 1 m, j * g (vars j m) (n + 1) t
        + (if 2 ≤ n ∧ 1 ≤ t then
            (m + 1) * ∑ j ∈ Icc 1 (m + 1), j * g (vars j (m + 1)) (n - 2) (t - 1) else 0)
        + ∑ j ∈ Icc 1 (m + 1), j * g (vars j (m + 1)) n t := by
  have hv : ∀ j ∈ Icc 1 (m + 1), vars j (m + 1) = (m + 1) :: vars j m := by
    intro j hj
    exact vars_succ (mem_Icc.mp hj).2
  have hlast : ∑ j ∈ Icc 1 (m + 1), j * g (vars j m) (n + 1) t
      = ∑ j ∈ Icc 1 m, j * g (vars j m) (n + 1) t := by
    rw [sum_Icc_succ_top (show 1 ≤ m + 1 by omega), vars_self_succ, g_nil_succ, mul_zero,
      add_zero]
  by_cases hc : 2 ≤ n ∧ 1 ≤ t
  · have hE : ∀ j ∈ Icc 1 (m + 1), j * g (vars j (m + 1)) (n + 1) t
        = j * g (vars j m) (n + 1) t + (m + 1) * (j * g (vars j (m + 1)) (n - 2) (t - 1))
          + j * g (vars j (m + 1)) n t := by
      intro j hj
      rw [hv j hj, g_cons, ite_eq_left (show 3 ≤ n + 1 ∧ 1 ≤ t by omega),
        ite_eq_left (show 1 ≤ n + 1 by omega), show n + 1 - 3 = n - 2 by omega,
        Nat.add_sub_cancel]
      ring
    rw [sum_congr rfl hE, sum_add_distrib, sum_add_distrib, ← mul_sum, hlast, ite_eq_left hc]
  · have hE : ∀ j ∈ Icc 1 (m + 1), j * g (vars j (m + 1)) (n + 1) t
        = j * g (vars j m) (n + 1) t + j * g (vars j (m + 1)) n t := by
      intro j hj
      rw [hv j hj, g_cons, ite_eq_right (show ¬ (3 ≤ n + 1 ∧ 1 ≤ t) by omega),
        ite_eq_left (show 1 ≤ n + 1 by omega), Nat.add_sub_cancel]
      ring
    rw [sum_congr rfl hE, sum_add_distrib, hlast, ite_eq_right hc, add_zero]

/-- `Fs` 满足细化引理 1（k ≥ 3）的递推，s = 0 与 s ≥ 1 合写（T2.4 证明用）。 -/
theorem Fs_rec (k m s : ℕ) :
    Fs (m + 1) (k + 3) s = Fs m (k + 3) s + Fs (m + 1) (k + 2) s
      + (if s = 0 then 0 else (m + 1) * Fs (m + 1) k (s - 1)) := by
  have hg := g_rec (m + 1) (vars 0 m) k s
  rw [← vars_succ (Nat.zero_le _)] at hg
  cases s with
  | zero => simp [Fs, hg]
  | succ t =>
    simp only [Fs, hg, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      show 2 ≤ k + 3 by omega, show 2 ≤ k + 2 by omega, show 1 ≤ t + 1 by omega, and_self,
      ite_true, show k + 3 - 2 = k + 1 by omega, show k + 2 - 2 = k by omega,
      sum_g_vars_succ m k t]
    split_ifs <;> ring

/-- `Fs` 满足 `lemma1_asc` 的递推（T2.4 证明用）。 -/
theorem Fs_rec_succ (k m s : ℕ) :
    Fs (m + 1) (k + 3) (s + 1)
      = Fs m (k + 3) (s + 1) + Fs (m + 1) (k + 2) (s + 1) + (m + 1) * Fs (m + 1) k s := by
  rw [Fs_rec, ite_eq_right (Nat.add_one_ne_zero s), Nat.add_sub_cancel]

/-- `Fs` 满足 `lemma1_asc_s0` 的递推（T2.4 证明用）。 -/
theorem Fs_rec_zero (k m : ℕ) :
    Fs (m + 1) (k + 3) 0 = Fs m (k + 3) 0 + Fs (m + 1) (k + 2) 0 := by
  rw [Fs_rec, ite_eq_left (show (0 : ℕ) = 0 from rfl), add_zero]

/-! ### 主定理 -/

/-- `Us k m s` 等于闭式 `Fs m k s`（报告 T2.4：由 T2.2 细化引理 1 与边界归纳）。 -/
theorem Us_eq_Fs (k m s : ℕ) : Us k m s = Fs m k s := by
  induction m generalizing k s with
  | zero => rw [Us_zero_right, Fs_zero_left]
  | succ m ihm =>
    induction k using Nat.strong_induction_on generalizing s with
    | _ k ihk =>
      match k, s with
      | 0, s => rw [Us_zero_left, Fs_zero_right]
      | 1, s => rw [lemma1_asc_one, ihm 1 s, ihk 0 (by omega) s, Fs_one]
      | 2, s => rw [lemma1_asc_two, ihm 2 s, ihk 1 (by omega) s, Fs_two]
      | k + 3, 0 => rw [lemma1_asc_s0, ihm (k + 3) 0, ihk (k + 2) (by omega) 0, Fs_rec_zero]
      | k + 3, s + 1 =>
        rw [lemma1_asc, ihm (k + 3) (s + 1), ihk (k + 2) (by omega) (s + 1), ihk k (by omega) s,
          Fs_rec_succ]

/-- **报告 T2.4 第二式**（按上升数 s 细化的显式公式）：
  U_k(m,s) = S(m+s,m)·C(k+m−2s, k−3s) + Σ_{j=1}^{m} j·H(m,s−1,j)·C(k+m−j−2s, k+1−3s)，
其中 `S` 是第二类 Stirling 数，`H(m,s,j) = hc s (vars j m) = h_s(j,…,m)`，s = 0 时第二项为空。
二项式约定 C(a,b) = 0（除非 0 ≤ b ≤ a）由守卫条件实现：第一项守卫 `3s ≤ k` 成立时
`k+m−2s ≥ k−3s ≥ 0`；第二项守卫 `1 ≤ s ∧ 3s ≤ k+1` 成立时（j ≤ m）`k+m−j−2s ≥ k+1−3s ≥ 0`，
所以式中的 ℕ 减法都不截断；守卫不成立时对应的下指标为负，按约定该项为 0。 -/
theorem Us_explicit (k m s : ℕ) :
    Us k m s = (if 3 * s ≤ k then
        Nat.stirlingSecond (m + s) m * Nat.choose (k + m - 2 * s) (k - 3 * s) else 0)
      + if 1 ≤ s ∧ 3 * s ≤ k + 1 then
          ∑ j ∈ Icc 1 m, j * hc (s - 1) (vars j m) * Nat.choose (k + m - j - 2 * s) (k + 1 - 3 * s)
        else 0 := by
  rw [Us_eq_Fs, Fs]
  congr 1
  · unfold g
    by_cases h : 3 * s ≤ k
    · rw [ite_eq_left h, ite_eq_left h, length_vars (Nat.zero_le _), hc_vars_zero,
        Nat.multichoose_eq]
      congr 2
      omega
    · rw [ite_eq_right h, ite_eq_right h]
  · by_cases h : 1 ≤ s ∧ 3 * s ≤ k + 1
    · rw [ite_eq_left h, ite_eq_left (show 2 ≤ k ∧ 1 ≤ s by omega)]
      apply sum_congr rfl
      intro j hj
      rw [mem_Icc] at hj
      unfold g
      rw [ite_eq_left (show 3 * (s - 1) ≤ k - 2 by omega), length_vars (show j ≤ m + 1 by omega),
        Nat.multichoose_eq, ← mul_assoc]
      congr 2 <;> omega
    · rw [ite_eq_right h]
      by_cases h2 : 2 ≤ k ∧ 1 ≤ s
      · rw [ite_eq_left h2]
        apply sum_eq_zero
        intro j _
        unfold g
        rw [ite_eq_right (show ¬ (3 * (s - 1) ≤ k - 2) by omega), mul_zero]
      · rw [ite_eq_right h2]

/-! ### 小例子核对（报告 T2.4；按定义穷举计算，不依赖上面的证明） -/

-- `U_3(1,1) = 2`：`(0,1,1)` 与 `(1,0,1)`（公式给 1 + 1）。
example : Us 3 1 1 = 2 := by decide

-- `U_2(1,1) = 1`：只有 `(0,1)`（公式给 0 + 1）。
example : Us 2 1 1 = 1 := by decide

end A207123
