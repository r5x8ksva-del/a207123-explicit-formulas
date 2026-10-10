import A207123.Barker

/-!
# OEIS A326247 与 Colin Barker 的三条猜想（报告 T5.4(2)(4)）

A326247 的 %N 是「n 个带标号顶点上既不交叉也不嵌套的 2 边多重图个数」，%C 规定边 `{a,b}`、`{c,d}` 交叉指
`a < c < b < d` 或 `c < a < d < b`，嵌套指 `a < c < d < b` 或 `c < a < b < d`；按 %t 的程序与数据，数的是边的有序对
（两条边可以相同）。这里按这个定义形式化（顶点取 `0, …, n−1`，边写成 `x < y` 的有序对）：

* `A326247 n`：`edgePairs n` 中既不交叉（`EdgeCross`）也不嵌套（`EdgeNest`）的有序对个数；`A326247_small`：
  前 7 项 `0, 0, 1, 9, 32, 80, 165` 与条目的 %S 相同（在内核里按定义直接数）。
* `A326247_add`：`a(n) + 4·C(n,4) = C(n,2)²`（有序对共 `C(n,2)²` 个；坏的分成四类，每类经坐标置换对应到
  `a < b < c < d < n`，个数 `C(n,4)`，见 `inc4_eq`）；`A326247_eq_U_four`：`U_4(m) = A326247(m+2)`
  （论文第 2 节与报告 T5.4(4)，由 `U_four_choose`）。
* Barker 的三条猜想：`barker_A326247_formula`（`a(n) = n(12 − 19n + 6n² + n³)/12`）、`barker_A326247_rec`
  （`n > 4` 时 `a(n) = 5a(n−1) − 10a(n−2) + 10a(n−3) − 5a(n−4) + a(n−5)`）、`barker_A326247_gf`
  （g.f. `x²(1 + 4x − 3x²)/(1 − x)⁵`，写成 `(1 − x)⁵·Σ_n a(n)xⁿ = x²(1 + 4x − 3x²)`）。
-/

namespace A207123

open Polynomial Finset

/-! ## 1. 定义（按条目的 %N、%C） -/

/-- 顶点 `0, …, n−1` 上两条边（各写成 `x < y` 的有序对 `(x, y)`）组成的有序对 `((x, y), (z, t))`，两条边可以相同。 -/
def edgePairs (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {p ∈ (range n ×ˢ range n) ×ˢ (range n ×ˢ range n) | p.1.1 < p.1.2 ∧ p.2.1 < p.2.2}

/-- A326247 的 %C：边 `{x, y}`、`{z, t}` 交叉，即 `x < z < y < t` 或 `z < x < t < y`。 -/
def EdgeCross (p : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  (p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2) ∨ (p.2.1 < p.1.1 ∧ p.1.1 < p.2.2 ∧ p.2.2 < p.1.2)

/-- A326247 的 %C：边 `{x, y}`、`{z, t}` 嵌套，即 `x < z < t < y` 或 `z < x < y < t`。 -/
def EdgeNest (p : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  (p.1.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.2 < p.1.2) ∨ (p.2.1 < p.1.1 ∧ p.1.1 < p.1.2 ∧ p.1.2 < p.2.2)

instance : DecidablePred EdgeCross := fun p => by unfold EdgeCross; infer_instance

instance : DecidablePred EdgeNest := fun p => by unfold EdgeNest; infer_instance

/-- **OEIS A326247**：`n` 个带标号顶点上既不交叉也不嵌套的边的有序对（可以相同）的个数。 -/
def A326247 (n : ℕ) : ℕ := #{p ∈ edgePairs n | ¬ EdgeCross p ∧ ¬ EdgeNest p}

/-- A326247 的 %S 的前 7 项（按定义在内核里直接数）。 -/
theorem A326247_small : (List.range 7).map A326247 = [0, 0, 1, 9, 32, 80, 165] := by
  decide +kernel

/-! ## 2. 递增元组的个数 -/

/-- `#{(a, b) : a < b < n}`。 -/
def inc2 (n : ℕ) : ℕ := #{p ∈ range n ×ˢ range n | p.1 < p.2}

/-- `#{((a, b), c) : a < b < c < n}`。 -/
def inc3 (n : ℕ) : ℕ := #{p ∈ (range n ×ˢ range n) ×ˢ range n | p.1.1 < p.1.2 ∧ p.1.2 < p.2}

/-- `#{(((a, b), c), d) : a < b < c < d < n}`。 -/
def inc4 (n : ℕ) : ℕ :=
  #{p ∈ ((range n ×ˢ range n) ×ˢ range n) ×ˢ range n | p.1.1.1 < p.1.1.2 ∧ p.1.1.2 < p.1.2 ∧ p.1.2 < p.2}

/-- 辅助引理：按第二个坐标分类计数。 -/
theorem card_filter_prod {α β : Type*} (s : Finset α) (t : Finset β) (P : α × β → Prop) [DecidablePred P] :
    #{p ∈ s ×ˢ t | P p} = ∑ b ∈ t, #{a ∈ s | P (a, b)} := by
  rw [card_filter, sum_product_right]
  exact sum_congr rfl fun b _ => (card_filter _ _).symm

/-- 曲棍球恒等式：`Σ_{j<m} C(j,k) = C(m,k+1)`。 -/
theorem sum_range_choose_eq (k : ℕ) : ∀ m, ∑ j ∈ range m, j.choose k = m.choose (k + 1)
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, sum_range_choose_eq k m, Nat.choose_succ_succ' m k]
    ring

theorem inc2_eq (n : ℕ) : inc2 n = n.choose 2 := by
  rw [inc2, card_filter_prod, ← sum_range_choose_eq 1 n]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.1 hb
  rw [Nat.choose_one_right]
  convert card_range b using 2
  ext a
  simp only [mem_filter, mem_range]
  omega

theorem inc3_eq (n : ℕ) : inc3 n = n.choose 3 := by
  rw [inc3, card_filter_prod, ← sum_range_choose_eq 2 n]
  refine sum_congr rfl fun c hc => ?_
  have hc' := mem_range.1 hc
  rw [← inc2_eq, inc2]
  congr 1
  ext p
  simp only [mem_filter, mem_product, mem_range]
  omega

theorem inc4_eq (n : ℕ) : inc4 n = n.choose 4 := by
  rw [inc4, card_filter_prod, ← sum_range_choose_eq 3 n]
  refine sum_congr rfl fun d hd => ?_
  have hd' := mem_range.1 hd
  rw [← inc3_eq, inc3]
  congr 1
  ext p
  simp only [mem_filter, mem_product, mem_range]
  omega

/-! ## 3. 计数：`a(n) + 4·C(n,4) = C(n,2)²` -/

theorem card_edgePairs (n : ℕ) : #(edgePairs n) = n.choose 2 ^ 2 := by
  have h : edgePairs n =
      {q ∈ range n ×ˢ range n | q.1 < q.2} ×ˢ {q ∈ range n ×ˢ range n | q.1 < q.2} := by
    ext p
    simp only [edgePairs, mem_filter, mem_product, mem_range]
    tauto
  rw [h, card_product, ← inc2, inc2_eq, sq]

/-- 交叉的第一类 `x < z < y < t`，对应 `a < b < c < d`（`(a, b, c, d) = (x, z, y, t)`）。 -/
theorem card_cross_one (n : ℕ) :
    #{p ∈ edgePairs n | p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2} = n.choose 4 := by
  rw [← inc4_eq, inc4]
  refine card_nbij' (fun p => (((p.1.1, p.2.1), p.1.2), p.2.2)) (fun q => ((q.1.1.1, q.1.2), (q.1.1.2, q.2)))
    ?_ ?_ (fun p _ => rfl) (fun q _ => rfl)
  · intro p hp
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hp ⊢
    omega
  · intro q hq
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hq ⊢
    omega

/-- 交叉的第二类 `z < x < t < y`（`(a, b, c, d) = (z, x, t, y)`）。 -/
theorem card_cross_two (n : ℕ) :
    #{p ∈ edgePairs n | p.2.1 < p.1.1 ∧ p.1.1 < p.2.2 ∧ p.2.2 < p.1.2} = n.choose 4 := by
  rw [← inc4_eq, inc4]
  refine card_nbij' (fun p => (((p.2.1, p.1.1), p.2.2), p.1.2)) (fun q => ((q.1.1.2, q.2), (q.1.1.1, q.1.2)))
    ?_ ?_ (fun p _ => rfl) (fun q _ => rfl)
  · intro p hp
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hp ⊢
    omega
  · intro q hq
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hq ⊢
    omega

/-- 嵌套的第一类 `x < z < t < y`（`(a, b, c, d) = (x, z, t, y)`）。 -/
theorem card_nest_one (n : ℕ) :
    #{p ∈ edgePairs n | p.1.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.2 < p.1.2} = n.choose 4 := by
  rw [← inc4_eq, inc4]
  refine card_nbij' (fun p => (((p.1.1, p.2.1), p.2.2), p.1.2)) (fun q => ((q.1.1.1, q.2), (q.1.1.2, q.1.2)))
    ?_ ?_ (fun p _ => rfl) (fun q _ => rfl)
  · intro p hp
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hp ⊢
    omega
  · intro q hq
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hq ⊢
    omega

/-- 嵌套的第二类 `z < x < y < t`（`(a, b, c, d) = (z, x, y, t)`）。 -/
theorem card_nest_two (n : ℕ) :
    #{p ∈ edgePairs n | p.2.1 < p.1.1 ∧ p.1.1 < p.1.2 ∧ p.1.2 < p.2.2} = n.choose 4 := by
  rw [← inc4_eq, inc4]
  refine card_nbij' (fun p => (((p.2.1, p.1.1), p.1.2), p.2.2)) (fun q => ((q.1.1.2, q.1.2), (q.1.1.1, q.2)))
    ?_ ?_ (fun p _ => rfl) (fun q _ => rfl)
  · intro p hp
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hp ⊢
    omega
  · intro q hq
    simp only [mem_coe, edgePairs, mem_filter, mem_product, mem_range] at hq ⊢
    omega

/-- 辅助引理：边的有序对恰好落在「好的」与四类坏的之一（逐类分情形）。 -/
theorem edge_split (p : (ℕ × ℕ) × (ℕ × ℕ)) (h2 : p.2.1 < p.2.2) :
    ((if ¬ EdgeCross p ∧ ¬ EdgeNest p then 1 else 0) +
        (if p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2 then 1 else 0) +
        (if p.2.1 < p.1.1 ∧ p.1.1 < p.2.2 ∧ p.2.2 < p.1.2 then 1 else 0) +
        (if p.1.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.2 < p.1.2 then 1 else 0) +
        (if p.2.1 < p.1.1 ∧ p.1.1 < p.1.2 ∧ p.1.2 < p.2.2 then 1 else 0) : ℕ) = 1 := by
  by_cases c1 : p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2
  · rw [ite_eq_right (by unfold EdgeCross; tauto), ite_eq_left c1, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases c2 : p.2.1 < p.1.1 ∧ p.1.1 < p.2.2 ∧ p.2.2 < p.1.2
  · rw [ite_eq_right (by unfold EdgeCross; tauto), ite_eq_right c1, ite_eq_left c2, ite_eq_right (by omega),
      ite_eq_right (by omega)]
  by_cases c3 : p.1.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.2 < p.1.2
  · rw [ite_eq_right (by unfold EdgeNest; tauto), ite_eq_right c1, ite_eq_right c2, ite_eq_left c3,
      ite_eq_right (by omega)]
  by_cases c4 : p.2.1 < p.1.1 ∧ p.1.1 < p.1.2 ∧ p.1.2 < p.2.2
  · rw [ite_eq_right (by unfold EdgeNest; tauto), ite_eq_right c1, ite_eq_right c2, ite_eq_right c3,
      ite_eq_left c4]
  · rw [ite_eq_left (by unfold EdgeCross EdgeNest; tauto), ite_eq_right c1, ite_eq_right c2, ite_eq_right c3,
      ite_eq_right c4]

/-- 每个有序对恰好落在「好的」与四类坏的之一。 -/
theorem A326247_partition (n : ℕ) :
    #(edgePairs n) = A326247 n + #{p ∈ edgePairs n | p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2}
      + #{p ∈ edgePairs n | p.2.1 < p.1.1 ∧ p.1.1 < p.2.2 ∧ p.2.2 < p.1.2}
      + #{p ∈ edgePairs n | p.1.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.2 < p.1.2}
      + #{p ∈ edgePairs n | p.2.1 < p.1.1 ∧ p.1.1 < p.1.2 ∧ p.1.2 < p.2.2} := by
  rw [A326247, card_eq_sum_ones, card_filter, card_filter, card_filter, card_filter, card_filter,
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  simp only [edgePairs, mem_filter, mem_product, mem_range] at hp
  exact (edge_split p hp.2.2).symm

/-- **T5.4(4)**：`a(n) + 4·C(n,4) = C(n,2)²`，即 `a(n) = C(n,2)² − 4·C(n,4)`。 -/
theorem A326247_add (n : ℕ) : A326247 n + 4 * n.choose 4 = n.choose 2 ^ 2 := by
  have h := A326247_partition n
  rw [card_cross_one, card_cross_two, card_nest_one, card_nest_two, card_edgePairs] at h
  generalize n.choose 2 ^ 2 = S at h ⊢
  omega

/-- **论文第 2 节、报告 T5.4(4)**：`U_4(m) = A326247(m + 2)`（A326247 按条目的定义）。 -/
theorem A326247_eq_U_four (m : ℕ) : A326247 (m + 2) = U 4 m := by
  have h1 : ((A326247 (m + 2) + 4 * (m + 2).choose 4 : ℕ) : ℤ) = (((m + 2).choose 2 ^ 2 : ℕ) : ℤ) := by
    rw [A326247_add]
  have h2 := U_four_choose m
  push_cast at h1
  have h3 : (A326247 (m + 2) : ℤ) = (U 4 m : ℤ) := by linarith
  exact_mod_cast h3

/-! ## 4. Barker 的三条猜想 -/

theorem choose_two_rat (n : ℕ) : 2 * (n.choose 2 : ℚ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem choose_three_rat (n : ℕ) : 6 * (n.choose 3 : ℚ) = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ']
    push_cast
    linear_combination 3 * choose_two_rat n + ih

theorem choose_four_rat (n : ℕ) : 24 * (n.choose 4 : ℚ) = n * (n - 1) * (n - 2) * (n - 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ']
    push_cast
    linear_combination 4 * choose_three_rat n + ih

/-- **T5.4(2)**（Barker 在 A326247 的猜想）：`a(n) = n(12 − 19n + 6n² + n³)/12`。 -/
theorem barker_A326247_formula (n : ℕ) :
    (A326247 n : ℚ) = n * (12 - 19 * n + 6 * n ^ 2 + n ^ 3) / 12 := by
  have h : (A326247 n : ℚ) + 4 * (n.choose 4 : ℚ) = (n.choose 2 : ℚ) ^ 2 := by exact_mod_cast A326247_add n
  linear_combination h + ((n.choose 2 : ℚ) / 2 + (n : ℚ) * (n - 1) / 4) * choose_two_rat n
    - (1 / 6 : ℚ) * choose_four_rat n

/-- **T5.4(2)**（Barker 在 A326247 的猜想）：`n > 4` 时
`a(n) = 5a(n−1) − 10a(n−2) + 10a(n−3) − 5a(n−4) + a(n−5)`。 -/
theorem barker_A326247_rec (n : ℕ) (hn : 4 < n) :
    (A326247 n : ℤ) = 5 * A326247 (n - 1) - 10 * A326247 (n - 2) + 10 * A326247 (n - 3) - 5 * A326247 (n - 4)
      + A326247 (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  qify
  simp only [barker_A326247_formula]
  push_cast
  ring

/-- **T5.4(2)**（Barker 在 A326247 的猜想）：g.f. 是 `x²(1 + 4x − 3x²)/(1 − x)⁵`，即
`(1 − x)⁵·Σ_n a(n)xⁿ = x²(1 + 4x − 3x²)`（条目从 `n = 0` 编号）。 -/
theorem barker_A326247_gf :
    (↑((1 - X) ^ 5 : ℚ[X]) : PowerSeries ℚ) * PowerSeries.mk (fun n => (A326247 n : ℚ)) =
      ↑(X ^ 2 * (1 + 4 * X - 3 * X ^ 2) : ℚ[X]) := by
  have hD : ((1 - X) ^ 5 : ℚ[X]) = ofList [1, -5, 10, -10, 5, -1] := by
    simp [ofList, Finset.sum_range_succ]
    ring
  have hN : (X ^ 2 * (1 + 4 * X - 3 * X ^ 2) : ℚ[X]) = ofList [-1, 5, -9, 14, -8, 1] + ofList [1, -5, 10, -10, 5, -1] := by
    simp [ofList, Finset.sum_range_succ]
    ring
  have key := gf_of_rec [1, -5, 10, -10, 5, -1] [-1, 5, -9, 14, -8, 1] [0, 0, 1, 9, 32] 5 rfl (by simp)
    (fun n => (A326247 n : ℚ)) ?_ ?_ (by decide +kernel) (by decide +kernel)
  · rw [hD, hN, Polynomial.coe_add, ← key]
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [show k + 5 - 0 = k + 5 by omega, show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
    simp only [barker_A326247_formula]
    norm_num
    ring
  · intro k hk
    rw [barker_A326247_formula]
    interval_cases k <;> norm_num

end A207123
