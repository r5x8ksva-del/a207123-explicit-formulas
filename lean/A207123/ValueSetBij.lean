import A207123.A326247

/-!
# `U_3`、`U_4` 的显式保值集双射（报告 T5.4(4)(5)，猜想总表 A16；notes/c5b.md 的 T9、T13）

* `U_three_bijOn`：长 3 的合法序列（`L 3 m`）到单调三元组（非增或非减，`monoSet m`）的双射 `bij3`（notes/c5b T9）：
  非增三元组不动；`(a < b = c) ↦ (a, a, b)`；`(b < c ≤ a) ↦ (b, c, a)`；逆映射 `bij3inv`：非增不动；
  `x = y < z ↦ (x, z, z)`；`x < y ≤ z ↦ (z, x, y)`。`bij3_values`：保持取值集合。单调三元组的个数是
  `2C(m+3,3) − (m+1)`，即 A084990 的条目注释。
* `U_four_bijOn`：长 4 的合法序列（`L 4 m`）到 `{0..m+1}` 上既不交叉也不嵌套的有序边对（A326247 的对象，
  `edgePairs (m+2)` 中满足 `¬EdgeCross ∧ ¬EdgeNest` 者）的分段双射 `bij4`（notes/c5b T13）：区间 `[x, y]` 记成边
  `(x, y+1)`，按合法 4 元组的四种块型 SSSS / ST / TS / SSE 各分两段，共 8 段；逆映射 `bij4inv` 按可接受区间对的
  类型 L≤ / L> / R′ / D1 / D2 分段。`bij4_values`：`{x₁, y₁, x₂, y₂} = {h₁, h₂, h₃, h₄}`。
报告指出：两边计数是同一多项式、又都对取值的保序重标号不变时，这类双射必然存在，所以双射本身不算「结构」的证据。
-/

namespace A207123

open Finset

/-! ## 列表成员 -/

theorem mem_L_three {m : ℕ} {l : List ℕ} :
    l ∈ L 3 m ↔ ∃ a b c, l = [a, b, c] ∧ a ≤ m ∧ b ≤ m ∧ c ≤ m ∧ Good a b c := by
  rw [mem_L]
  constructor
  · rintro ⟨hlen, hle, hleg⟩
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 hlen
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hle
    exact ⟨a, b, c, rfl, hle.1, hle.2.1, hle.2.2, hleg.1⟩
  · rintro ⟨a, b, c, rfl, ha, hb, hc, hg⟩
    refine ⟨rfl, ?_, ⟨hg, trivial⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ha, hb, hc⟩

theorem mem_L_four {m : ℕ} {l : List ℕ} :
    l ∈ L 4 m ↔ ∃ a b c d, l = [a, b, c, d] ∧ a ≤ m ∧ b ≤ m ∧ c ≤ m ∧ d ≤ m ∧
      Good a b c ∧ Good b c d := by
  rw [mem_L]
  constructor
  · rintro ⟨hlen, hle, hleg⟩
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩ <;> simp at hlen
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hle
    exact ⟨a, b, c, d, rfl, hle.1, hle.2.1, hle.2.2.1, hle.2.2.2, hleg.1, hleg.2.1⟩
  · rintro ⟨a, b, c, d, rfl, ha, hb, hc, hd, hg1, hg2⟩
    refine ⟨rfl, ?_, ⟨hg1, hg2, trivial⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ha, hb, hc, hd⟩

/-! ## `U_3`：合法三元组 ↔ 单调三元组 -/

/-- 取值 ≤ `m` 的单调三元组（非增或非减）。 -/
def monoSet (m : ℕ) : Finset (List ℕ) :=
  (seqs m 3).filter fun l => l.Pairwise (· ≥ ·) ∨ l.Pairwise (· ≤ ·)

theorem mem_monoSet {m : ℕ} {l : List ℕ} :
    l ∈ monoSet m ↔ ∃ x y z, l = [x, y, z] ∧ x ≤ m ∧ y ≤ m ∧ z ≤ m ∧
      ((z ≤ y ∧ y ≤ x) ∨ (x ≤ y ∧ y ≤ z)) := by
  rw [monoSet, Finset.mem_filter, mem_seqs]
  constructor
  · rintro ⟨⟨hlen, hle⟩, hp⟩
    obtain ⟨x, y, z, rfl⟩ := List.length_eq_three.1 hlen
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hle
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true, IsEmpty.forall_iff, forall_const, ge_iff_le] at hp
    exact ⟨x, y, z, rfl, hle.1, hle.2.1, hle.2.2, by omega⟩
  · rintro ⟨x, y, z, rfl, hx, hy, hz, h⟩
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hx, hy, hz⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, forall_const, ge_iff_le]
      omega

/-- notes/c5b T9 的映射 `f3`。 -/
def bij3 : List ℕ → List ℕ
  | [a, b, c] => if c ≤ b ∧ b ≤ a then [a, b, c] else if b = c then [a, a, b] else [b, c, a]
  | l => l

/-- `f3` 的逆映射 `g3`。 -/
def bij3inv : List ℕ → List ℕ
  | [x, y, z] => if z ≤ y ∧ y ≤ x then [x, y, z] else if x = y then [x, z, z] else [z, x, y]
  | l => l

theorem bij3_mapsTo (m : ℕ) : Set.MapsTo bij3 (L 3 m) (monoSet m) := by
  intro l hl
  rw [Finset.mem_coe] at hl ⊢
  obtain ⟨a, b, c, rfl, ha, hb, hc, hg⟩ := mem_L_three.1 hl
  unfold Good at hg
  rw [mem_monoSet, bij3]
  split_ifs with h1 h2
  · exact ⟨a, b, c, rfl, ha, hb, hc, by omega⟩
  · exact ⟨a, a, b, rfl, ha, ha, hb, by omega⟩
  · exact ⟨b, c, a, rfl, hb, hc, ha, by omega⟩

theorem bij3inv_mapsTo (m : ℕ) : Set.MapsTo bij3inv (monoSet m) (L 3 m) := by
  intro l hl
  rw [Finset.mem_coe] at hl ⊢
  obtain ⟨x, y, z, rfl, hx, hy, hz, h⟩ := mem_monoSet.1 hl
  rw [mem_L_three, bij3inv]
  unfold Good
  split_ifs with h1 h2
  · exact ⟨x, y, z, rfl, hx, hy, hz, by omega⟩
  · exact ⟨x, z, z, rfl, hx, hz, hz, by omega⟩
  · exact ⟨z, x, y, rfl, hz, hx, hy, by omega⟩

theorem bij3_invOn (m : ℕ) : Set.InvOn bij3inv bij3 (L 3 m) (monoSet m) := by
  constructor
  · intro l hl
    rw [Finset.mem_coe] at hl
    obtain ⟨a, b, c, rfl, -, -, -, hg⟩ := mem_L_three.1 hl
    unfold Good at hg
    simp only [bij3]
    split_ifs <;> simp only [bij3inv] <;> split_ifs <;> simp only [List.cons.injEq, and_true, true_and] <;> omega
  · intro l hl
    rw [Finset.mem_coe] at hl
    obtain ⟨x, y, z, rfl, -, -, -, h⟩ := mem_monoSet.1 hl
    simp only [bij3inv]
    split_ifs <;> simp only [bij3] <;> split_ifs <;> simp only [List.cons.injEq, and_true, true_and] <;> omega

/-- **报告 T5.4(4)（notes/c5b T9）**：`f3` 是合法三元组到单调三元组的双射。 -/
theorem U_three_bijOn (m : ℕ) : Set.BijOn bij3 (L 3 m) (monoSet m) :=
  (bij3_invOn m).bijOn (bij3_mapsTo m) (bij3inv_mapsTo m)

/-- `f3` 保持取值集合。 -/
theorem bij3_values {m : ℕ} {l : List ℕ} (hl : l ∈ L 3 m) (v : ℕ) : v ∈ bij3 l ↔ v ∈ l := by
  obtain ⟨a, b, c, rfl, -, -, -, hg⟩ := mem_L_three.1 hl
  unfold Good at hg
  simp only [bij3]
  split_ifs <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> omega

/-! ## `U_4`：合法 4 元组 ↔ 不交叉也不嵌套的有序边对 -/

/-- notes/c5b T13 的分段双射 `Φ`（区间 `[x, y]` 记成边 `(x, y+1)`）：
SSSS（`h₁ ≥ h₂ ≥ h₃ ≥ h₄`）、ST（`h₁ ≥ h₃ = h₄ > h₂`）、TS（`h₂ = h₃ > h₁`、`h₄ ≤ h₃`）、SSE（`h₁ ≥ h₂ ≥ h₄ > h₃`）各两段。 -/
def bij4 : List ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | [h1, h2, h3, h4] =>
    if h2 ≤ h1 ∧ h3 ≤ h2 ∧ h4 ≤ h3 then
      if h2 = h3 then ((h4, h3 + 1), (h4, h1 + 1)) else ((h2, h1 + 1), (h4, h3 + 1))
    else if h2 < h3 then
      if h3 < h1 then ((h2, h1 + 1), (h2, h3 + 1)) else ((h2, h3 + 1), (h2, h2 + 1))
    else if h2 = h3 then
      if h4 ≠ h1 then ((h1, h2 + 1), (h4, h2 + 1)) else ((h2, h2 + 1), (h1, h2 + 1))
    else
      if h4 < h2 then ((h3, h4 + 1), (h2, h1 + 1)) else ((h3, h3 + 1), (h4, h1 + 1))
  | _ => ((0, 0), (0, 0))

/-- `Φ` 的逆映射：按区间对 `([x₁, y₁], [x₂, y₂])` 的类型 L≤ / L> / R′ / D1 / D2 分段。 -/
def bij4inv (p : (ℕ × ℕ) × (ℕ × ℕ)) : List ℕ :=
  if p.1.1 = p.2.1 then
    if p.1.2 ≤ p.2.2 then [p.2.2 - 1, p.1.2 - 1, p.1.2 - 1, p.1.1]
    else if p.1.1 + 1 < p.2.2 then [p.1.2 - 1, p.1.1, p.2.2 - 1, p.2.2 - 1]
    else [p.1.2 - 1, p.1.1, p.1.2 - 1, p.1.2 - 1]
  else if p.1.2 = p.2.2 then
    if p.1.1 + 1 < p.1.2 then [p.1.1, p.1.2 - 1, p.1.2 - 1, p.2.1]
    else [p.2.1, p.1.2 - 1, p.1.2 - 1, p.2.1]
  else if p.1.2 ≤ p.2.1 then
    if p.1.1 + 1 < p.1.2 then [p.2.2 - 1, p.2.1, p.1.1, p.1.2 - 1]
    else [p.2.2 - 1, p.2.1, p.1.1, p.2.1]
  else [p.1.2 - 1, p.1.1, p.2.2 - 1, p.2.1]

/-- A326247 的对象：`{0..n−1}` 上既不交叉也不嵌套的有序边对（`A326247 n` 就是它的元素个数）。 -/
def goodPairs (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := {p ∈ edgePairs n | ¬ EdgeCross p ∧ ¬ EdgeNest p}

theorem card_goodPairs (n : ℕ) : #(goodPairs n) = A326247 n := rfl

theorem mem_goodPairs {n : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} :
    p ∈ goodPairs n ↔
      p.1.1 < n ∧ p.1.2 < n ∧ p.2.1 < n ∧ p.2.2 < n ∧ p.1.1 < p.1.2 ∧ p.2.1 < p.2.2 ∧
        ¬ EdgeCross p ∧ ¬ EdgeNest p := by
  simp only [goodPairs, edgePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  tauto

theorem bij4_mapsTo (m : ℕ) :
    Set.MapsTo bij4 (L 4 m) (goodPairs (m + 2)) := by
  intro l hl
  rw [Finset.mem_coe] at hl ⊢
  obtain ⟨a, b, c, d, rfl, ha, hb, hc, hd, hg1, hg2⟩ := mem_L_four.1 hl
  unfold Good at hg1 hg2
  rw [mem_goodPairs, bij4]
  unfold EdgeCross EdgeNest
  split_ifs <;> simp only <;> omega

theorem bij4inv_mapsTo (m : ℕ) :
    Set.MapsTo bij4inv (goodPairs (m + 2)) (L 4 m) := by
  intro p hp
  rw [Finset.mem_coe] at hp ⊢
  obtain ⟨⟨x1, e1⟩, ⟨x2, e2⟩⟩ := p
  rw [mem_goodPairs] at hp
  unfold EdgeCross EdgeNest at hp
  simp only at hp
  rw [mem_L_four, bij4inv]
  unfold Good
  simp only
  split_ifs
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem bij4_invOn (m : ℕ) :
    Set.InvOn bij4inv bij4 (L 4 m) (goodPairs (m + 2)) := by
  constructor
  · intro l hl
    rw [Finset.mem_coe] at hl
    obtain ⟨a, b, c, d, rfl, -, -, -, -, hg1, hg2⟩ := mem_L_four.1 hl
    unfold Good at hg1 hg2
    simp only [bij4]
    split_ifs <;> simp only [bij4inv] <;> split_ifs <;> simp only [List.cons.injEq, and_true, true_and] <;> omega
  · intro p hp
    rw [Finset.mem_coe] at hp
    obtain ⟨⟨x1, e1⟩, ⟨x2, e2⟩⟩ := p
    rw [mem_goodPairs] at hp
    unfold EdgeCross EdgeNest at hp
    simp only at hp
    simp only [bij4inv]
    split_ifs <;> simp only [bij4] <;> split_ifs <;> simp only [Prod.mk.injEq, true_and] <;> omega

/-- **报告 T5.4(5)（notes/c5b T13）**：`Φ` 是 `{0..m}⁴` 中的合法 4 元组到 `{0..m+1}` 上既不交叉也不嵌套的有序边对
（A326247 的对象）的双射。 -/
theorem U_four_bijOn (m : ℕ) :
    Set.BijOn bij4 (L 4 m) (goodPairs (m + 2)) :=
  (bij4_invOn m).bijOn (bij4_mapsTo m) (bij4inv_mapsTo m)

/-- `Φ` 保持取值集合：`{x₁, y₁, x₂, y₂} = {h₁, h₂, h₃, h₄}`（边 `(x, y+1)` 对应区间 `[x, y]`）。 -/
theorem bij4_values {m : ℕ} {l : List ℕ} (hl : l ∈ L 4 m) (v : ℕ) :
    v ∈ l ↔ (v = (bij4 l).1.1 ∨ v + 1 = (bij4 l).1.2 ∨ v = (bij4 l).2.1 ∨ v + 1 = (bij4 l).2.2) := by
  obtain ⟨a, b, c, d, rfl, -, -, -, -, hg1, hg2⟩ := mem_L_four.1 hl
  unfold Good at hg1 hg2
  simp only [bij4]
  split_ifs <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> omega

end A207123
