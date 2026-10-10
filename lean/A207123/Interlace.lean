import Mathlib

/-!
# 实系数多项式的根的交错（论文 §8.1 的工具）

论文 §8.1 对实根多项式 `f`、`g` 定义 `g ≪ f`（根交错、`f` 的最大根在最上面），并给出等价刻画：对每个实数 `x`，
`f` 在 `(x, ∞)` 中的根（计重数）比 `g` 多 0 个或 1 个。本文件用这个刻画作为定义（`Interlaces g f`），只用实分析
（介值定理）与多项式插值证明 §8.1 用到的性质，不用论文证明里的上半平面虚部刻画：

* `nAbove p x`：`p` 在 `(x, ∞)` 中的根数（计重数）；`RealRooted p`：`p ≠ 0` 且根数（计重数）等于次数。
* `sign_eval`：首项系数为正的实根多项式在非根 `x` 处的符号是 `(−1)^{nAbove p x}`。
* `alt_points`：若 `g` 在有限点集 `P` 上交替变号且 `deg g + 1 ≤ |P|`，则 `g` 实根，且 `(x, ∞)` 中 `g` 的根数与
  `P` 的点数至多差 1（介值定理加 Mathlib 的 `Finset.card_le_of_interleaved`）。
* 下锥 `coneSum f c w = c·f + Σ_a w(a)·f/(X−a)`（`a` 取 `f` 的不同根）与上锥
  `uconeSum f a b e = (aX+b)·f − Σ_t e(t)·f/(X−t)`：`interlaces_coneSum`（系数非负时 `coneSum ≪ f`）、
  `interlaces_uconeSum`（`f ≪ uconeSum`）；反过来 `cone_of_interlaces`、`ucone_of_interlaces`（插值）。
  这两组等价代替论文引理 8.5 的虚部刻画。
* 由此得到论文引理 8.4（`interlaces_mul_iff`）、引理 8.6（`Interlaces.add_left`、`Interlaces.add_right`）与
  引理 8.7(1)(2)（`interlaces_X_sub_C_mul`、`interlaces_derivative`、`Interlaces.X_mul`）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 定义与基本性质 -/

/-- `p` 在 `(x, ∞)` 中的根数（计重数）。 -/
def nAbove (p : ℝ[X]) (x : ℝ) : ℕ := Multiset.card (p.roots.filter (x < ·))

/-- `p` 是实根多项式：`p ≠ 0`，且实根（计重数）的个数等于次数。 -/
def RealRooted (p : ℝ[X]) : Prop := p ≠ 0 ∧ Multiset.card p.roots = p.natDegree

/-- 交错 `g ≪ f`（论文 §8.1）：`f`、`g` 都是实根多项式，且对每个实数 `x`，`f` 在 `(x, ∞)` 中的根数比 `g` 多
0 或 1（论文给出的等价刻画）。 -/
def Interlaces (g f : ℝ[X]) : Prop :=
  RealRooted f ∧ RealRooted g ∧ ∀ x, nAbove g x ≤ nAbove f x ∧ nAbove f x ≤ nAbove g x + 1

theorem nAbove_le_card (p : ℝ[X]) (x : ℝ) : nAbove p x ≤ Multiset.card p.roots :=
  Multiset.card_le_card (Multiset.filter_le _ _)

theorem nAbove_anti (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y) : nAbove p y ≤ nAbove p x :=
  Multiset.card_le_card (Multiset.monotone_filter_right _ fun _ h => lt_of_le_of_lt hxy h)

theorem nAbove_mul {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) (x : ℝ) :
    nAbove (p * q) x = nAbove p x + nAbove q x := by
  unfold nAbove
  rw [roots_mul (mul_ne_zero hp hq), Multiset.filter_add, Multiset.card_add]

theorem nAbove_C_mul (p : ℝ[X]) {a : ℝ} (ha : a ≠ 0) (x : ℝ) : nAbove (C a * p) x = nAbove p x := by
  unfold nAbove
  rw [roots_C_mul _ ha]

theorem nAbove_X_sub_C (r x : ℝ) : nAbove (X - C r) x = if x < r then 1 else 0 := by
  unfold nAbove
  rw [roots_X_sub_C]
  split_ifs with h
  · rw [Multiset.filter_singleton, ite_eq_left h]; rfl
  · rw [Multiset.filter_singleton, ite_eq_right h]; rfl

/-- `(x, ∞)` 与 `(−∞, x]` 中的根数之和是根的总数。 -/
theorem nAbove_add_card_le (p : ℝ[X]) (x : ℝ) :
    nAbove p x + Multiset.card (p.roots.filter (· ≤ x)) = Multiset.card p.roots := by
  unfold nAbove
  rw [← Multiset.card_add]
  congr 1
  conv_rhs => rw [← Multiset.filter_add_not (x < ·) p.roots]
  congr 1
  exact Multiset.filter_congr fun r _ => not_lt.symm

theorem RealRooted.ne_zero {p : ℝ[X]} (h : RealRooted p) : p ≠ 0 := h.1

theorem realRooted_mul {p q : ℝ[X]} (hp : RealRooted p) (hq : RealRooted q) : RealRooted (p * q) := by
  refine ⟨mul_ne_zero hp.1 hq.1, ?_⟩
  rw [roots_mul (mul_ne_zero hp.1 hq.1), Multiset.card_add, hp.2, hq.2, natDegree_mul hp.1 hq.1]

theorem RealRooted.of_mul_right {p q : ℝ[X]} (h : RealRooted (p * q)) : RealRooted q := by
  have hp : p ≠ 0 := left_ne_zero_of_mul h.1
  have hq : q ≠ 0 := right_ne_zero_of_mul h.1
  refine ⟨hq, ?_⟩
  have h2 := h.2
  rw [roots_mul h.1, Multiset.card_add, natDegree_mul hp hq] at h2
  have := card_roots' p
  have := card_roots' q
  omega

theorem RealRooted.of_mul_left {p q : ℝ[X]} (h : RealRooted (p * q)) : RealRooted p := by
  rw [mul_comm] at h
  exact h.of_mul_right

theorem realRooted_X_sub_C (r : ℝ) : RealRooted (X - C r) :=
  ⟨X_sub_C_ne_zero r, by rw [roots_X_sub_C, natDegree_X_sub_C]; rfl⟩

theorem realRooted_C {a : ℝ} (ha : a ≠ 0) : RealRooted (C a) :=
  ⟨C_ne_zero.2 ha, by rw [roots_C, natDegree_C]; rfl⟩

theorem RealRooted.C_mul {p : ℝ[X]} (hp : RealRooted p) {a : ℝ} (ha : a ≠ 0) : RealRooted (C a * p) :=
  realRooted_mul (realRooted_C ha) hp

theorem Interlaces.realRooted_left {g f : ℝ[X]} (h : Interlaces g f) : RealRooted g := h.2.1

theorem Interlaces.realRooted_right {g f : ℝ[X]} (h : Interlaces g f) : RealRooted f := h.1

theorem Interlaces.self {f : ℝ[X]} (hf : RealRooted f) : Interlaces f f :=
  ⟨hf, hf, fun _ => ⟨le_rfl, Nat.le_succ _⟩⟩

/-- 论文引理 8.4：乘以实根多项式不改变交错关系。 -/
theorem interlaces_mul_iff {p g f : ℝ[X]} (hp : RealRooted p) :
    Interlaces (p * g) (p * f) ↔ Interlaces g f := by
  constructor
  · rintro ⟨hf, hg, h⟩
    have hf' := hf.of_mul_right
    have hg' := hg.of_mul_right
    refine ⟨hf', hg', fun x => ?_⟩
    have := h x
    rw [nAbove_mul hp.1 hf'.1, nAbove_mul hp.1 hg'.1] at this
    omega
  · rintro ⟨hf, hg, h⟩
    refine ⟨realRooted_mul hp hf, realRooted_mul hp hg, fun x => ?_⟩
    have := h x
    rw [nAbove_mul hp.1 hf.1, nAbove_mul hp.1 hg.1]
    omega

theorem Interlaces.C_mul_left {g f : ℝ[X]} (h : Interlaces g f) {a : ℝ} (ha : a ≠ 0) :
    Interlaces (C a * g) f := by
  refine ⟨h.1, h.2.1.C_mul ha, fun x => ?_⟩
  rw [nAbove_C_mul _ ha]
  exact h.2.2 x

theorem Interlaces.C_mul_right {g f : ℝ[X]} (h : Interlaces g f) {a : ℝ} (ha : a ≠ 0) :
    Interlaces g (C a * f) := by
  refine ⟨h.1.C_mul ha, h.2.1, fun x => ?_⟩
  rw [nAbove_C_mul _ ha]
  exact h.2.2 x

/-- 交错时次数相差 0 或 1。 -/
theorem Interlaces.natDegree_le {g f : ℝ[X]} (h : Interlaces g f) :
    g.natDegree ≤ f.natDegree ∧ f.natDegree ≤ g.natDegree + 1 := by
  obtain ⟨b, hb⟩ := (Multiset.toFinset (f.roots + g.roots)).bddBelow
  have hall : ∀ p : ℝ[X], (∀ r ∈ p.roots, b - 1 < r) → nAbove p (b - 1) = Multiset.card p.roots := by
    intro p hp
    unfold nAbove
    rw [Multiset.filter_eq_self.2 hp]
  have hf := hall f fun r hr => by
    have := hb (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inl hr)))
    linarith
  have hg := hall g fun r hr => by
    have := hb (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inr hr)))
    linarith
  have := h.2.2 (b - 1)
  rw [hf, hg, h.1.2, h.2.1.2] at this
  exact this

/-! ## 2. 符号引理 -/

/-- 首项系数为正的实根多项式 `p` 在非根 `x` 处的符号是 `(−1)^{nAbove p x}`。 -/
theorem sign_eval {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff) {x : ℝ}
    (hx : p.eval x ≠ 0) : 0 < (-1) ^ nAbove p x * p.eval x := by
  have key : ∀ s : Multiset ℝ, x ∉ s →
      0 < (-1) ^ Multiset.card (s.filter (x < ·)) * (s.map fun a => x - a).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hxs
      have hxa : x ≠ a := fun h => hxs (h ▸ Multiset.mem_cons_self _ _)
      have ih := ih fun h => hxs (Multiset.mem_cons_of_mem h)
      rw [Multiset.map_cons, Multiset.prod_cons]
      by_cases hlt : x < a
      · rw [Multiset.filter_cons_of_pos _ hlt, Multiset.card_cons, pow_succ]
        have h1 : 0 < a - x := sub_pos.2 hlt
        have e : (-1 : ℝ) ^ Multiset.card (s.filter (x < ·)) * -1 *
            ((x - a) * (s.map fun a => x - a).prod) =
            (a - x) * ((-1) ^ Multiset.card (s.filter (x < ·)) * (s.map fun a => x - a).prod) := by
          ring
        rw [e]
        exact mul_pos h1 ih
      · rw [Multiset.filter_cons_of_neg _ hlt]
        have h1 : 0 < x - a := sub_pos.2 (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hxa))
        have e : (-1 : ℝ) ^ Multiset.card (s.filter (x < ·)) *
            ((x - a) * (s.map fun a => x - a).prod) =
            (x - a) * ((-1) ^ Multiset.card (s.filter (x < ·)) * (s.map fun a => x - a).prod) := by
          ring
        rw [e]
        exact mul_pos h1 ih
  have hroots : x ∉ p.roots := fun h => hx ((mem_roots hp.1).1 h)
  have hpx : p.eval x = p.leadingCoeff * (p.roots.map fun a => x - a).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hp.2]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 2
    exact Multiset.map_congr rfl fun a _ => by simp
  rw [hpx, nAbove]
  have := mul_pos hlc (key _ hroots)
  calc (0 : ℝ) < _ := this
    _ = _ := by ring

/-- 首项系数为正时 `p` 在充分大处为正。 -/
theorem exists_pos_right {p : ℝ[X]} (hlc : 0 < p.leadingCoeff) (y : ℝ) :
    ∃ R, y < R ∧ 0 < p.eval R := by
  by_cases hd : 0 < p.degree
  · have ht := p.tendsto_atTop_of_leadingCoeff_nonneg hd hlc.le
    obtain ⟨R, hR⟩ :=
      ((ht.eventually (Filter.eventually_gt_atTop 0)).and (Filter.eventually_gt_atTop y)).exists
    exact ⟨R, hR.2, hR.1⟩
  · refine ⟨y + 1, by linarith, ?_⟩
    have hdeg : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 (not_lt.1 hd)
    rw [eq_C_of_degree_le_zero (not_lt.1 hd), eval_C]
    have : p.leadingCoeff = p.coeff 0 := by rw [leadingCoeff, hdeg]
    rw [← this]
    exact hlc

/-- 首项系数为正时 `p` 在充分小处的符号是 `(−1)^{deg p}`。 -/
theorem exists_sign_left {p : ℝ[X]} (hlc : 0 < p.leadingCoeff) (y : ℝ) :
    ∃ L, L < y ∧ 0 < (-1) ^ p.natDegree * p.eval L := by
  set q := C ((-1 : ℝ) ^ p.natDegree) * p.comp (-X) with hqdef
  have hq : 0 < q.leadingCoeff := by
    rw [hqdef, leadingCoeff_mul, leadingCoeff_C, comp_neg_X_leadingCoeff_eq, ← mul_assoc, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, one_mul]
    exact hlc
  obtain ⟨R, hR, hpos⟩ := exists_pos_right hq (-y)
  refine ⟨-R, by linarith, ?_⟩
  rw [hqdef, eval_mul, eval_C, eval_comp, eval_neg, eval_X] at hpos
  exact hpos

/-- 介值定理：`g(p)` 与 `g(q)` 异号时 `(p, q)` 中有根。 -/
theorem exists_root_Ioo {g : ℝ[X]} {p q : ℝ} (hpq : p < q) (h : g.eval p * g.eval q < 0) :
    ∃ z, p < z ∧ z < q ∧ g.eval z = 0 := by
  have hc : ContinuousOn (fun x => g.eval x) (Set.Icc p q) := g.continuous.continuousOn
  have hp0 : g.eval p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl _ h
  rcases lt_or_gt_of_ne hp0 with h1 | h1
  · have h2 : 0 < g.eval q := by
      by_contra h2
      nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hpq.le hc ⟨h1, h2⟩
    exact ⟨z, hz.1, hz.2, hz0⟩
  · have h2 : g.eval q < 0 := by
      by_contra h2
      nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hpq.le hc ⟨h2, h1⟩
    exact ⟨z, hz.1, hz.2, hz0⟩

/-! ## 3. 交替变号的点集 -/

/-- 点集 `P` 中相邻的两点 `p < q`：`P` 中大于 `p` 的点比大于 `q` 的点多一个（就是 `q`）。 -/
theorem card_filter_lt_of_consec {P : Finset ℝ} {p q : ℝ} (hq : q ∈ P) (hpq : p < q)
    (hcons : ∀ r ∈ P, r ∉ Set.Ioo p q) :
    (P.filter (p < ·)).card = (P.filter (q < ·)).card + 1 := by
  have : P.filter (p < ·) = insert q (P.filter (q < ·)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hr, hpr⟩
      rcases lt_trichotomy r q with h | h | h
      · exact absurd ⟨hpr, h⟩ (hcons r hr)
      · exact Or.inl h
      · exact Or.inr ⟨hr, h⟩
    · rintro (rfl | ⟨hr, hqr⟩)
      · exact ⟨hq, hpq⟩
      · exact ⟨hr, hpq.trans hqr⟩
  rw [this, Finset.card_insert_of_notMem]
  simp

/-- 交替变号：相邻两点处 `g` 异号。 -/
theorem alt_mul_neg {g : ℝ[X]} {P : Finset ℝ}
    (hP : ∀ p ∈ P, 0 < (-1) ^ (P.filter (p < ·)).card * g.eval p) {p q : ℝ} (hp : p ∈ P)
    (hq : q ∈ P) (hpq : p < q) (hcons : ∀ r ∈ P, r ∉ Set.Ioo p q) : g.eval p * g.eval q < 0 := by
  have h1 := hP p hp
  have h2 := hP q hq
  rw [card_filter_lt_of_consec hq hpq hcons, pow_succ] at h1
  set m := (P.filter (q < ·)).card
  have hsq : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have e : ((-1 : ℝ) ^ m * -1 * g.eval p) * ((-1) ^ m * g.eval q) = -(g.eval p * g.eval q) := by
    linear_combination (-(g.eval p * g.eval q)) * hsq
  have := mul_pos h1 h2
  rw [e] at this
  linarith

/-- 交替变号的点集给出 `(x, ∞)` 中根数的下界。 -/
theorem card_filter_le_nAbove {g : ℝ[X]} (hg : g ≠ 0) {P : Finset ℝ}
    (hP : ∀ p ∈ P, 0 < (-1) ^ (P.filter (p < ·)).card * g.eval p) (x : ℝ) :
    (P.filter (x < ·)).card ≤ nAbove g x + 1 := by
  have h := Finset.card_le_of_interleaved (s := P.filter (x < ·))
    (t := g.roots.toFinset.filter (x < ·)) ?_
  · calc _ ≤ _ := h
      _ ≤ nAbove g x + 1 := by
        gcongr
        unfold nAbove
        rw [← Multiset.toFinset_filter]
        exact Multiset.toFinset_card_le _
  · intro p hp q hq hpq hcons
    rw [Finset.mem_filter] at hp hq
    have hcons' : ∀ r ∈ P, r ∉ Set.Ioo p q := fun r hr hrI =>
      hcons r (Finset.mem_filter.2 ⟨hr, hp.2.trans hrI.1⟩) hrI
    obtain ⟨z, hpz, hzq, hz⟩ := exists_root_Ioo hpq (alt_mul_neg hP hp.1 hq.1 hpq hcons')
    exact ⟨z, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_roots hg).2 hz), hp.2.trans hpz⟩,
      hpz, hzq⟩

/-- 交替变号的点集给出 `(−∞, x]` 中根数的下界。 -/
theorem card_filter_le_card_roots_le {g : ℝ[X]} (hg : g ≠ 0) {P : Finset ℝ}
    (hP : ∀ p ∈ P, 0 < (-1) ^ (P.filter (p < ·)).card * g.eval p) (x : ℝ) :
    (P.filter (· ≤ x)).card ≤ Multiset.card (g.roots.filter (· ≤ x)) + 1 := by
  have h := Finset.card_le_of_interleaved (s := P.filter (· ≤ x))
    (t := g.roots.toFinset.filter (· ≤ x)) ?_
  · calc _ ≤ _ := h
      _ ≤ Multiset.card (g.roots.filter (· ≤ x)) + 1 := by
        gcongr
        rw [← Multiset.toFinset_filter]
        exact Multiset.toFinset_card_le _
  · intro p hp q hq hpq hcons
    rw [Finset.mem_filter] at hp hq
    have hcons' : ∀ r ∈ P, r ∉ Set.Ioo p q := fun r hr hrI =>
      hcons r (Finset.mem_filter.2 ⟨hr, (hrI.2.trans_le hq.2).le⟩) hrI
    obtain ⟨z, hpz, hzq, hz⟩ := exists_root_Ioo hpq (alt_mul_neg hP hp.1 hq.1 hpq hcons')
    exact ⟨z, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_roots hg).2 hz),
      (hzq.trans_le hq.2).le⟩, hpz, hzq⟩

/-- 若 `g` 在有限点集 `P` 上交替变号（`(−1)^{P 中更大的点数}·g(p) > 0`）且 `deg g + 1 ≤ |P|`，则 `g` 实根，
且对每个 `x`，`|P ∩ (x, ∞)| ≤ nAbove g x + 1`、`nAbove g x ≤ |P ∩ (x, ∞)|`。 -/
theorem alt_points {g : ℝ[X]} (hg : g ≠ 0) {P : Finset ℝ}
    (hP : ∀ p ∈ P, 0 < (-1) ^ (P.filter (p < ·)).card * g.eval p)
    (hdeg : g.natDegree + 1 ≤ P.card) :
    RealRooted g ∧ ∀ x, (P.filter (x < ·)).card ≤ nAbove g x + 1 ∧
      nAbove g x ≤ (P.filter (x < ·)).card := by
  have hsplit : ∀ x, (P.filter (x < ·)).card + (P.filter (· ≤ x)).card = P.card := by
    intro x
    rw [← Finset.card_filter_add_card_filter_not (s := P) (fun r => x < r)]
    congr 2
    exact Finset.filter_congr fun r _ => not_lt.symm
  obtain ⟨b, hb⟩ := P.bddBelow
  have hrr : RealRooted g := by
    refine ⟨hg, le_antisymm (card_roots' g) ?_⟩
    have h1 := card_filter_le_nAbove hg hP (b - 1)
    have h2 : P.filter ((b - 1) < ·) = P :=
      Finset.filter_true_of_mem fun r hr => by have := hb hr; linarith
    rw [h2] at h1
    have h3 := nAbove_le_card g (b - 1)
    omega
  refine ⟨hrr, fun x => ⟨card_filter_le_nAbove hg hP x, ?_⟩⟩
  have h1 := card_filter_le_card_roots_le hg hP x
  have h2 := nAbove_add_card_le g x
  have h3 := hsplit x
  have h4 := card_roots' g
  omega

/-! ## 4. 除以 `X − a` -/

theorem divByMonic_spec {f : ℝ[X]} {a : ℝ} (ha : f.IsRoot a) : (X - C a) * (f /ₘ (X - C a)) = f :=
  mul_divByMonic_eq_iff_isRoot.2 ha

theorem divByMonic_ne_zero {f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (ha : f.IsRoot a) :
    f /ₘ (X - C a) ≠ 0 := by
  intro h0
  have := divByMonic_spec ha
  rw [h0, mul_zero] at this
  exact hf this.symm

theorem roots_divByMonic {f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (ha : f.IsRoot a) :
    f.roots = a ::ₘ (f /ₘ (X - C a)).roots := by
  conv_lhs => rw [← divByMonic_spec ha]
  rw [roots_mul (by rw [divByMonic_spec ha]; exact hf), roots_X_sub_C, Multiset.singleton_add]

theorem realRooted_divByMonic {f : ℝ[X]} (hf : RealRooted f) {a : ℝ} (ha : f.IsRoot a) :
    RealRooted (f /ₘ (X - C a)) := by
  have h := divByMonic_spec ha
  rw [← h] at hf
  exact hf.of_mul_right

theorem leadingCoeff_divByMonic' {f : ℝ[X]} {a : ℝ} (ha : f.IsRoot a) :
    (f /ₘ (X - C a)).leadingCoeff = f.leadingCoeff := by
  conv_rhs => rw [← divByMonic_spec ha]
  rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]

theorem natDegree_divByMonic' {f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (ha : f.IsRoot a) :
    (f /ₘ (X - C a)).natDegree + 1 = f.natDegree := by
  conv_rhs => rw [← divByMonic_spec ha]
  rw [natDegree_mul (X_sub_C_ne_zero a) (divByMonic_ne_zero hf ha), natDegree_X_sub_C, add_comm]

theorem nAbove_divByMonic {f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (ha : f.IsRoot a) :
    nAbove (f /ₘ (X - C a)) a = nAbove f a := by
  unfold nAbove
  rw [roots_divByMonic hf ha, Multiset.filter_cons_of_neg _ (lt_irrefl a)]

/-- 在单根 `a` 处，`f/(X−a)` 在 `a` 的值（即 `f'(a)`）的符号是 `(−1)^{nAbove f a}`。 -/
theorem sign_divByMonic_eval {f : ℝ[X]} (hf : RealRooted f) (hlc : 0 < f.leadingCoeff) {a : ℝ}
    (ha : f.IsRoot a) (hsimple : f.roots.count a = 1) :
    0 < (-1) ^ nAbove f a * (f /ₘ (X - C a)).eval a := by
  have hq := realRooted_divByMonic hf ha
  have hne : (f /ₘ (X - C a)).eval a ≠ 0 := by
    intro h0
    have hmem : a ∈ (f /ₘ (X - C a)).roots := (mem_roots hq.1).2 h0
    rw [roots_divByMonic hf.1 ha, Multiset.count_cons_self] at hsimple
    have : 0 < (f /ₘ (X - C a)).roots.count a := Multiset.count_pos.2 hmem
    omega
  rw [← nAbove_divByMonic hf.1 ha]
  exact sign_eval hq (by rw [leadingCoeff_divByMonic' ha]; exact hlc) hne

theorem divByMonic_eval_of_ne {f : ℝ[X]} {a b : ℝ} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hab : a ≠ b) : (f /ₘ (X - C b)).eval a = 0 := by
  have := congrArg (eval a) (divByMonic_spec hb)
  rw [eval_mul, eval_sub, eval_X, eval_C, ha.eq_zero] at this
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab)

/-- `b` 是 `p` 的根时 `(q·p)/(X−b) = q·(p/(X−b))`。 -/
theorem mul_divByMonic_of_root {p : ℝ[X]} (q : ℝ[X]) {b : ℝ} (hb : p.IsRoot b) :
    (q * p) /ₘ (X - C b) = q * (p /ₘ (X - C b)) := by
  have h := divByMonic_spec hb
  conv_lhs => rw [← h]
  rw [show q * ((X - C b) * (p /ₘ (X - C b))) = (X - C b) * (q * (p /ₘ (X - C b))) by ring,
    mul_divByMonic_cancel_left _ (monic_X_sub_C b)]

/-! ## 5. 下锥与上锥 -/

/-- 下锥中的元素 `c·f + Σ_{a ∈ f 的不同根} w(a)·f/(X−a)`。 -/
def coneSum (f : ℝ[X]) (c : ℝ) (w : ℝ → ℝ) : ℝ[X] :=
  C c * f + ∑ a ∈ f.roots.toFinset, C (w a) * (f /ₘ (X - C a))

/-- 上锥中的元素 `(aX+b)·f − Σ_{t ∈ f 的不同根} e(t)·f/(X−t)`。 -/
def uconeSum (f : ℝ[X]) (a b : ℝ) (e : ℝ → ℝ) : ℝ[X] :=
  (C a * X + C b) * f - ∑ t ∈ f.roots.toFinset, C (e t) * (f /ₘ (X - C t))

theorem sum_divByMonic_eval_root {f : ℝ[X]} (hf : f ≠ 0) (w : ℝ → ℝ) {a : ℝ} (ha : f.IsRoot a) :
    (∑ t ∈ f.roots.toFinset, C (w t) * (f /ₘ (X - C t))).eval a =
      w a * (f /ₘ (X - C a)).eval a := by
  rw [eval_finsetSum, Finset.sum_eq_single a]
  · rw [eval_mul, eval_C]
  · intro b hb hba
    rw [eval_mul, divByMonic_eval_of_ne ha (isRoot_of_mem_roots (Multiset.mem_toFinset.1 hb))
      (Ne.symm hba), mul_zero]
  · intro hna
    exact absurd (Multiset.mem_toFinset.2 ((mem_roots hf).2 ha)) hna

theorem coneSum_eval_root {f : ℝ[X]} (hf : f ≠ 0) (c : ℝ) (w : ℝ → ℝ) {a : ℝ}
    (ha : f.IsRoot a) : (coneSum f c w).eval a = w a * (f /ₘ (X - C a)).eval a := by
  rw [coneSum, eval_add, eval_mul, eval_C, ha.eq_zero, mul_zero, zero_add,
    sum_divByMonic_eval_root hf w ha]

theorem uconeSum_eval_root {f : ℝ[X]} (hf : f ≠ 0) (a b : ℝ) (e : ℝ → ℝ) {t : ℝ}
    (ht : f.IsRoot t) : (uconeSum f a b e).eval t = -(e t * (f /ₘ (X - C t)).eval t) := by
  rw [uconeSum, eval_sub, eval_mul, ht.eq_zero, mul_zero, zero_sub,
    sum_divByMonic_eval_root hf e ht]

theorem coeff_sum_divByMonic {f : ℝ[X]} (hf : f ≠ 0) (w : ℝ → ℝ) {m : ℕ} (hm : f.natDegree ≤ m) :
    (∑ t ∈ f.roots.toFinset, C (w t) * (f /ₘ (X - C t))).coeff m = 0 := by
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hr := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ht)
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by have := natDegree_divByMonic' hf hr; omega),
    mul_zero]

theorem natDegree_coneSum_le {f : ℝ[X]} (hf : f ≠ 0) (c : ℝ) (w : ℝ → ℝ) :
    (coneSum f c w).natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coneSum, coeff_add, coeff_C_mul, coeff_eq_zero_of_natDegree_lt hm, mul_zero, zero_add,
    coeff_sum_divByMonic hf w hm.le]

theorem coneSum_coeff {f : ℝ[X]} (hf : f ≠ 0) (c : ℝ) (w : ℝ → ℝ) :
    (coneSum f c w).coeff f.natDegree = c * f.leadingCoeff := by
  rw [coneSum, coeff_add, coeff_C_mul, coeff_sum_divByMonic hf w le_rfl, add_zero]
  rfl

theorem natDegree_uconeSum_le {f : ℝ[X]} (hf : f ≠ 0) (a b : ℝ) (e : ℝ → ℝ) :
    (uconeSum f a b e).natDegree ≤ f.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [uconeSum, coeff_sub, coeff_sum_divByMonic hf e (by omega), sub_zero]
  apply coeff_eq_zero_of_natDegree_lt
  calc ((C a * X + C b) * f).natDegree ≤ (C a * X + C b).natDegree + f.natDegree := natDegree_mul_le
    _ ≤ 1 + f.natDegree := by gcongr; exact natDegree_linear_le
    _ < m := by omega

theorem uconeSum_coeff_succ {f : ℝ[X]} (hf : f ≠ 0) (a b : ℝ) (e : ℝ → ℝ) :
    (uconeSum f a b e).coeff (f.natDegree + 1) = a * f.leadingCoeff := by
  rw [uconeSum, coeff_sub, coeff_sum_divByMonic hf e (by omega), sub_zero, add_mul, coeff_add,
    mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), mul_zero, add_zero]
  rfl

/-- 去掉公共因子 `X − a`：若 `a` 是重根，或 `w(a) = 0`，则锥和里的求和可以提出 `X − a`。 -/
theorem sum_divByMonic_factor {f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (ha : f.IsRoot a) (w : ℝ → ℝ)
    (hw : f.roots.count a = 1 → w a = 0) :
    ∑ t ∈ f.roots.toFinset, C (w t) * (f /ₘ (X - C t)) =
      (X - C a) * ∑ t ∈ (f /ₘ (X - C a)).roots.toFinset,
        C (w t) * ((f /ₘ (X - C a)) /ₘ (X - C t)) := by
  have hS : f.roots = a ::ₘ (f /ₘ (X - C a)).roots := roots_divByMonic hf ha
  have hsub : (f /ₘ (X - C a)).roots.toFinset ⊆ f.roots.toFinset := by
    intro t ht
    rw [hS]
    exact Multiset.mem_toFinset.2 (Multiset.mem_cons_of_mem (Multiset.mem_toFinset.1 ht))
  rw [Finset.mul_sum]
  have h1 : ∑ t ∈ (f /ₘ (X - C a)).roots.toFinset,
      (X - C a) * (C (w t) * ((f /ₘ (X - C a)) /ₘ (X - C t))) =
      ∑ t ∈ (f /ₘ (X - C a)).roots.toFinset, C (w t) * (f /ₘ (X - C t)) :=
    Finset.sum_congr rfl fun t ht => by
      have hr := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ht)
      rw [mul_left_comm, ← mul_divByMonic_of_root _ hr, divByMonic_spec ha]
  rw [h1]
  symm
  refine Finset.sum_subset hsub fun t ht ht1 => ?_
  have htm := Multiset.mem_toFinset.1 ht
  rw [hS] at htm
  rcases Multiset.mem_cons.1 htm with rfl | h
  · have hc1 : f.roots.count t = 1 := by
      rw [hS, Multiset.count_cons_self,
        Multiset.count_eq_zero.2 fun h => ht1 (Multiset.mem_toFinset.2 h)]
    rw [hw hc1, C_0, zero_mul]
  · exact absurd (Multiset.mem_toFinset.2 h) ht1

theorem coneSum_factor {f : ℝ[X]} (hf : f ≠ 0) {a : ℝ} (ha : f.IsRoot a) (c : ℝ) (w : ℝ → ℝ)
    (hw : f.roots.count a = 1 → w a = 0) :
    coneSum f c w = (X - C a) * coneSum (f /ₘ (X - C a)) c w := by
  have h1 : C c * f = (X - C a) * (C c * (f /ₘ (X - C a))) := by
    calc C c * f = C c * ((X - C a) * (f /ₘ (X - C a))) := by rw [divByMonic_spec ha]
      _ = _ := by ring
  rw [coneSum, coneSum, h1, sum_divByMonic_factor hf ha w hw, mul_add]

theorem uconeSum_factor {f : ℝ[X]} (hf : f ≠ 0) {t : ℝ} (ht : f.IsRoot t) (a b : ℝ) (e : ℝ → ℝ)
    (he : f.roots.count t = 1 → e t = 0) :
    uconeSum f a b e = (X - C t) * uconeSum (f /ₘ (X - C t)) a b e := by
  have h1 : (C a * X + C b) * f = (X - C t) * ((C a * X + C b) * (f /ₘ (X - C t))) := by
    calc (C a * X + C b) * f = (C a * X + C b) * ((X - C t) * (f /ₘ (X - C t))) := by
          rw [divByMonic_spec ht]
      _ = _ := by ring
  rw [uconeSum, uconeSum, h1, sum_divByMonic_factor hf ht e he, mul_sub]

/-! ## 6. 锥中的元素交错 -/

/-- 单根情形：权重全正时 `coneSum f c w ≪ f`（交替变号的点是 `f` 的根，`c > 0` 时再加左边一点）。 -/
theorem interlaces_coneSum_nodup {f : ℝ[X]} (hf : RealRooted f) (hlc : 0 < f.leadingCoeff)
    (hnd : f.roots.Nodup) {c : ℝ} (hc : 0 ≤ c) {w : ℝ → ℝ} (hw : ∀ a ∈ f.roots, 0 < w a)
    (hg : coneSum f c w ≠ 0) : Interlaces (coneSum f c w) f := by
  set g := coneSum f c w with hgdef
  set S := f.roots.toFinset with hS
  have hSn : S.card = f.natDegree := by rw [hS, Multiset.toFinset_card_of_nodup hnd, hf.2]
  have hnf : ∀ x, nAbove f x = (S.filter (x < ·)).card := by
    intro x
    unfold nAbove
    rw [hS, ← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hnd.filter _)]
  have hsgn : ∀ a ∈ S, 0 < (-1) ^ nAbove f a * g.eval a := by
    intro a ha
    have hm := Multiset.mem_toFinset.1 ha
    have hr := isRoot_of_mem_roots hm
    rw [hgdef, coneSum_eval_root hf.1 c w hr]
    have := sign_divByMonic_eval hf hlc hr (Multiset.count_eq_one_of_mem hnd hm)
    calc (0 : ℝ) < w a * ((-1) ^ nAbove f a * (f /ₘ (X - C a)).eval a) := mul_pos (hw a hm) this
      _ = _ := by ring
  have hdegle : g.natDegree ≤ f.natDegree := natDegree_coneSum_le hf.1 c w
  have hcoeff : g.coeff f.natDegree = c * f.leadingCoeff := coneSum_coeff hf.1 c w
  rcases hc.lt_or_eq with hc | hc
  · have hdeg : g.natDegree = f.natDegree := by
      apply le_antisymm hdegle
      apply le_natDegree_of_ne_zero
      rw [hcoeff]
      exact mul_ne_zero hc.ne' hlc.ne'
    have hlcg : 0 < g.leadingCoeff := by
      rw [leadingCoeff, hdeg, hcoeff]
      exact mul_pos hc hlc
    obtain ⟨b, hb⟩ := S.bddBelow
    obtain ⟨L, hL, hLs⟩ := exists_sign_left hlcg b
    have hLS : L ∉ S := fun h => by have := hb h; linarith
    have hPf : ∀ p ∈ S, (insert L S).filter (p < ·) = S.filter (p < ·) := by
      intro p hp
      rw [Finset.filter_insert, ite_eq_right (by have := hb hp; linarith)]
    have hPL : (insert L S).filter (L < ·) = S := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl L)]
      exact Finset.filter_true_of_mem fun r hr => by have := hb hr; linarith
    have halt : ∀ p ∈ insert L S, 0 < (-1) ^ ((insert L S).filter (p < ·)).card * g.eval p := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · rw [hPL, hSn, ← hdeg]
        exact hLs
      · rw [hPf p hp, ← hnf]
        exact hsgn p hp
    have hcard : (insert L S).card = f.natDegree + 1 := by
      rw [Finset.card_insert_of_notMem hLS, hSn]
    obtain ⟨hrr, hbd⟩ := alt_points hg halt (by rw [hdeg, hcard])
    refine ⟨hf, hrr, fun x => ?_⟩
    obtain ⟨h1, h2⟩ := hbd x
    by_cases hxL : x < L
    · have hPx : (insert L S).filter (x < ·) = insert L S :=
        Finset.filter_true_of_mem fun r hr => by
          rcases Finset.mem_insert.1 hr with rfl | hr
          · exact hxL
          · have := hb hr; linarith
      have hfx : nAbove f x = f.natDegree := by
        rw [hnf, Finset.filter_true_of_mem fun r hr => by have := hb hr; linarith, hSn]
      rw [hPx, hcard] at h1
      have h3 := nAbove_le_card g x
      rw [hrr.2, hdeg] at h3
      omega
    · have hPx : (insert L S).filter (x < ·) = S.filter (x < ·) := by
        rw [Finset.filter_insert, ite_eq_right hxL]
      rw [hPx, ← hnf] at h1 h2
      omega
  · subst hc
    have hne : g.natDegree ≠ f.natDegree := by
      intro h
      have := leadingCoeff_ne_zero.2 hg
      rw [leadingCoeff, h, hcoeff, zero_mul] at this
      exact this rfl
    have halt : ∀ p ∈ S, 0 < (-1) ^ (S.filter (p < ·)).card * g.eval p := by
      intro p hp
      rw [← hnf]
      exact hsgn p hp
    obtain ⟨hrr, hbd⟩ := alt_points hg halt (by rw [hSn]; omega)
    refine ⟨hf, hrr, fun x => ?_⟩
    obtain ⟨h1, h2⟩ := hbd x
    rw [← hnf] at h1 h2
    omega

/-- 论文引理 8.5(1) 的「⇐」方向（锥的形式）：`f` 实根、首项系数为正，`c ≥ 0`、`w ≥ 0`（在根上），
`coneSum f c w ≠ 0`，则 `coneSum f c w ≪ f`。 -/
theorem interlaces_coneSum {f : ℝ[X]} (hf : RealRooted f) (hlc : 0 < f.leadingCoeff)
    {c : ℝ} (hc : 0 ≤ c) {w : ℝ → ℝ} (hw : ∀ a ∈ f.roots, 0 ≤ w a) (hg : coneSum f c w ≠ 0) :
    Interlaces (coneSum f c w) f := by
  have key : ∀ n, ∀ f : ℝ[X], f.natDegree = n → RealRooted f → 0 < f.leadingCoeff →
      (∀ a ∈ f.roots, 0 ≤ w a) → coneSum f c w ≠ 0 → Interlaces (coneSum f c w) f := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hn hf hlc hw hg
      by_cases hbad : ∃ a ∈ f.roots, w a = 0 ∨ 2 ≤ f.roots.count a
      · obtain ⟨a, ham, hwa⟩ := hbad
        have hr := isRoot_of_mem_roots ham
        have hfac := coneSum_factor hf.1 hr c w fun h1 => by
          rcases hwa with h | h
          · exact h
          · omega
        have hspec := divByMonic_spec hr
        have hf₁ : RealRooted (f /ₘ (X - C a)) := realRooted_divByMonic hf hr
        have hlc₁ : 0 < (f /ₘ (X - C a)).leadingCoeff := by
          rw [leadingCoeff_divByMonic' hr]
          exact hlc
        have hdeg₁ : (f /ₘ (X - C a)).natDegree < n := by
          have := natDegree_divByMonic' hf.1 hr
          omega
        have hw₁ : ∀ b ∈ (f /ₘ (X - C a)).roots, 0 ≤ w b := fun b hb =>
          hw b (by rw [roots_divByMonic hf.1 hr]; exact Multiset.mem_cons_of_mem hb)
        have hg₁ : coneSum (f /ₘ (X - C a)) c w ≠ 0 := by
          intro h0
          rw [hfac, h0, mul_zero] at hg
          exact hg rfl
        have := ih _ hdeg₁ _ rfl hf₁ hlc₁ hw₁ hg₁
        rw [hfac]
        conv => arg 2; rw [← hspec]
        exact (interlaces_mul_iff (realRooted_X_sub_C a)).2 this
      · have hpos : ∀ a ∈ f.roots, 0 < w a := fun a ha =>
          lt_of_le_of_ne (hw a ha) fun h => hbad ⟨a, ha, Or.inl h.symm⟩
        have hnd : f.roots.Nodup := Multiset.nodup_iff_count_le_one.2 fun a => by
          by_contra h
          have ha : a ∈ f.roots := Multiset.count_pos.1 (by omega)
          exact hbad ⟨a, ha, Or.inr (by omega)⟩
        exact interlaces_coneSum_nodup hf hlc hnd hc hpos hg
  exact key _ f rfl hf hlc hw hg

/-- 单根情形：`e` 全正时 `f ≪ uconeSum f a b e`（交替变号的点是 `f` 的根与右边一点，`a > 0` 时再加左边一点）。 -/
theorem interlaces_uconeSum_nodup {f : ℝ[X]} (hf : RealRooted f) (hlc : 0 < f.leadingCoeff)
    (hnd : f.roots.Nodup) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) {e : ℝ → ℝ} (he : ∀ t ∈ f.roots, 0 < e t)
    (hlcg : 0 < (uconeSum f a b e).leadingCoeff) : Interlaces f (uconeSum f a b e) := by
  set g := uconeSum f a b e with hgdef
  have hg : g ≠ 0 := leadingCoeff_ne_zero.1 hlcg.ne'
  set S := f.roots.toFinset with hS
  have hSn : S.card = f.natDegree := by rw [hS, Multiset.toFinset_card_of_nodup hnd, hf.2]
  have hnf : ∀ x, nAbove f x = (S.filter (x < ·)).card := by
    intro x
    unfold nAbove
    rw [hS, ← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hnd.filter _)]
  have hsgn : ∀ t ∈ S, 0 < (-1) ^ (nAbove f t + 1) * g.eval t := by
    intro t ht
    have hm := Multiset.mem_toFinset.1 ht
    have hr := isRoot_of_mem_roots hm
    rw [hgdef, uconeSum_eval_root hf.1 a b e hr]
    have := sign_divByMonic_eval hf hlc hr (Multiset.count_eq_one_of_mem hnd hm)
    calc (0 : ℝ) < e t * ((-1) ^ nAbove f t * (f /ₘ (X - C t)).eval t) := mul_pos (he t hm) this
      _ = _ := by ring
  have hdegle : g.natDegree ≤ f.natDegree + 1 := natDegree_uconeSum_le hf.1 a b e
  have hcoeff : g.coeff (f.natDegree + 1) = a * f.leadingCoeff := uconeSum_coeff_succ hf.1 a b e
  obtain ⟨b0, hb0⟩ := S.bddBelow
  obtain ⟨B0, hB0⟩ := S.bddAbove
  obtain ⟨R, hR, hRs⟩ := exists_pos_right hlcg B0
  have hRS : R ∉ S := fun h => by have := hB0 h; linarith
  -- 加上右边一点 `R` 后的点集
  have hQf : ∀ p ∈ S, (insert R S).filter (p < ·) = insert R (S.filter (p < ·)) := by
    intro p hp
    rw [Finset.filter_insert, ite_eq_left (by have := hB0 hp; linarith)]
  have hQR : (insert R S).filter (R < ·) = ∅ := by
    rw [Finset.filter_insert, ite_eq_right (lt_irrefl R)]
    exact Finset.filter_false_of_mem fun r hr => by have := hB0 hr; linarith
  have hQcard : (insert R S).card = f.natDegree + 1 := by
    rw [Finset.card_insert_of_notMem hRS, hSn]
  have hQx : ∀ x, x < R → ((insert R S).filter (x < ·)).card = nAbove f x + 1 := by
    intro x hx
    rw [Finset.filter_insert, ite_eq_left hx, Finset.card_insert_of_notMem
      (fun h => hRS (Finset.mem_filter.1 h).1), hnf]
  have hfR : ∀ x, R ≤ x → nAbove f x = 0 := by
    intro x hx
    rw [hnf, Finset.filter_false_of_mem fun r hr => by have := hB0 hr; linarith]
    rfl
  have haltQ : ∀ p ∈ insert R S, 0 < (-1) ^ ((insert R S).filter (p < ·)).card * g.eval p := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · rw [hQR, Finset.card_empty, pow_zero, one_mul]
      exact hRs
    · rw [hQf p hp, Finset.card_insert_of_notMem (fun h => hRS (Finset.mem_filter.1 h).1),
        ← hnf]
      exact hsgn p hp
  rcases ha.lt_or_eq with ha | ha
  · have hdeg : g.natDegree = f.natDegree + 1 := by
      apply le_antisymm hdegle
      apply le_natDegree_of_ne_zero
      rw [hcoeff]
      exact mul_ne_zero ha.ne' hlc.ne'
    obtain ⟨L, hL, hLs⟩ := exists_sign_left hlcg (min b0 R)
    have hLb : L < b0 := lt_of_lt_of_le hL (min_le_left _ _)
    have hLR : L < R := lt_of_lt_of_le hL (min_le_right _ _)
    have hLQ : L ∉ insert R S := by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · linarith
      · have := hb0 h
        linarith
    have hPf : ∀ p ∈ insert R S,
        (insert L (insert R S)).filter (p < ·) = (insert R S).filter (p < ·) := by
      intro p hp
      rw [Finset.filter_insert, ite_eq_right]
      rcases Finset.mem_insert.1 hp with rfl | hp
      · linarith
      · have := hb0 hp
        linarith
    have hPL : (insert L (insert R S)).filter (L < ·) = insert R S := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl L)]
      refine Finset.filter_true_of_mem fun r hr => ?_
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact hLR
      · have := hb0 hr
        linarith
    have halt : ∀ p ∈ insert L (insert R S),
        0 < (-1) ^ ((insert L (insert R S)).filter (p < ·)).card * g.eval p := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · rw [hPL, hQcard, ← hdeg]
        exact hLs
      · rw [hPf p hp]
        exact haltQ p hp
    have hcard : (insert L (insert R S)).card = f.natDegree + 2 := by
      rw [Finset.card_insert_of_notMem hLQ, hQcard]
    obtain ⟨hrr, hbd⟩ := alt_points hg halt (by rw [hdeg, hcard])
    refine ⟨hrr, hf, fun x => ?_⟩
    obtain ⟨h1, h2⟩ := hbd x
    by_cases hxL : x < L
    · have hPx : (insert L (insert R S)).filter (x < ·) = insert L (insert R S) :=
        Finset.filter_true_of_mem fun r hr => by
          rcases Finset.mem_insert.1 hr with rfl | hr
          · exact hxL
          · rcases Finset.mem_insert.1 hr with rfl | hr
            · linarith
            · have := hb0 hr
              linarith
      have hfx : nAbove f x = f.natDegree := by
        rw [hnf, Finset.filter_true_of_mem fun r hr => by have := hb0 hr; linarith, hSn]
      rw [hPx, hcard] at h1
      have h3 := nAbove_le_card g x
      rw [hrr.2, hdeg] at h3
      omega
    · have hPx : (insert L (insert R S)).filter (x < ·) = (insert R S).filter (x < ·) := by
        rw [Finset.filter_insert, ite_eq_right hxL]
      rw [hPx] at h1 h2
      by_cases hxR : x < R
      · rw [hQx x hxR] at h1 h2
        omega
      · have hfx := hfR x (not_lt.1 hxR)
        have h0 : (insert R S).filter (x < ·) = ∅ :=
          Finset.filter_false_of_mem fun r hr => by
            rcases Finset.mem_insert.1 hr with rfl | hr
            · exact hxR
            · have := hB0 hr
              linarith
        rw [h0, Finset.card_empty] at h2
        omega
  · subst ha
    have hne : g.natDegree ≠ f.natDegree + 1 := by
      intro h
      have := leadingCoeff_ne_zero.2 hg
      rw [leadingCoeff, h, hcoeff, zero_mul] at this
      exact this rfl
    obtain ⟨hrr, hbd⟩ := alt_points hg haltQ (by rw [hQcard]; omega)
    refine ⟨hrr, hf, fun x => ?_⟩
    obtain ⟨h1, h2⟩ := hbd x
    by_cases hxR : x < R
    · rw [hQx x hxR] at h1 h2
      omega
    · have hfx := hfR x (not_lt.1 hxR)
      have h0 : (insert R S).filter (x < ·) = ∅ :=
        Finset.filter_false_of_mem fun r hr => by
          rcases Finset.mem_insert.1 hr with rfl | hr
          · exact hxR
          · have := hB0 hr
            linarith
      rw [h0, Finset.card_empty] at h2
      omega

/-- 论文引理 8.5(2) 的「⇐」方向（上锥的形式）：`f` 实根、首项系数为正，`a ≥ 0`、`e ≥ 0`（在根上），
`uconeSum f a b e` 的首项系数为正，则 `f ≪ uconeSum f a b e`。 -/
theorem interlaces_uconeSum {f : ℝ[X]} (hf : RealRooted f) (hlc : 0 < f.leadingCoeff)
    {a : ℝ} (ha : 0 ≤ a) (b : ℝ) {e : ℝ → ℝ} (he : ∀ t ∈ f.roots, 0 ≤ e t)
    (hlcg : 0 < (uconeSum f a b e).leadingCoeff) : Interlaces f (uconeSum f a b e) := by
  have key : ∀ n, ∀ f : ℝ[X], f.natDegree = n → RealRooted f → 0 < f.leadingCoeff →
      (∀ t ∈ f.roots, 0 ≤ e t) → 0 < (uconeSum f a b e).leadingCoeff →
      Interlaces f (uconeSum f a b e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hn hf hlc he hlcg
      by_cases hbad : ∃ t ∈ f.roots, e t = 0 ∨ 2 ≤ f.roots.count t
      · obtain ⟨t, htm, het⟩ := hbad
        have hr := isRoot_of_mem_roots htm
        have hfac := uconeSum_factor hf.1 hr a b e fun h1 => by
          rcases het with h | h
          · exact h
          · omega
        have hspec := divByMonic_spec hr
        have hf₁ : RealRooted (f /ₘ (X - C t)) := realRooted_divByMonic hf hr
        have hlc₁ : 0 < (f /ₘ (X - C t)).leadingCoeff := by
          rw [leadingCoeff_divByMonic' hr]
          exact hlc
        have hdeg₁ : (f /ₘ (X - C t)).natDegree < n := by
          have := natDegree_divByMonic' hf.1 hr
          omega
        have he₁ : ∀ s ∈ (f /ₘ (X - C t)).roots, 0 ≤ e s := fun s hs =>
          he s (by rw [roots_divByMonic hf.1 hr]; exact Multiset.mem_cons_of_mem hs)
        have hlcg₁ : 0 < (uconeSum (f /ₘ (X - C t)) a b e).leadingCoeff := by
          rw [hfac, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul] at hlcg
          exact hlcg
        have := ih _ hdeg₁ _ rfl hf₁ hlc₁ he₁ hlcg₁
        rw [hfac]
        conv => arg 1; rw [← hspec]
        exact (interlaces_mul_iff (realRooted_X_sub_C t)).2 this
      · have hpos : ∀ t ∈ f.roots, 0 < e t := fun t ht =>
          lt_of_le_of_ne (he t ht) fun h => hbad ⟨t, ht, Or.inl h.symm⟩
        have hnd : f.roots.Nodup := Multiset.nodup_iff_count_le_one.2 fun t => by
          by_contra h
          have ht : t ∈ f.roots := Multiset.count_pos.1 (by omega)
          exact hbad ⟨t, ht, Or.inr (by omega)⟩
        exact interlaces_uconeSum_nodup hf hlc hnd ha b hpos hlcg
  exact key _ f rfl hf hlc he hlcg

/-! ## 7. 交错的元素在锥中（插值） -/

/-- 在 `a` 的左边取一点 `x`，使 `p`、`q` 小于 `a` 的根都小于 `x`。 -/
theorem exists_just_below (p q : ℝ[X]) (a : ℝ) :
    ∃ x < a, ∀ r ∈ p.roots + q.roots, r < a → r < x := by
  set T := insert (a - 1) (((p.roots + q.roots).filter (· < a)).toFinset)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hlt : T.max' hT < a := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith
    · exact (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hy)).2
  refine ⟨(T.max' hT + a) / 2, by linarith, fun r hr hra => ?_⟩
  have : r ≤ T.max' hT := Finset.le_max' _ _
    (Finset.mem_insert_of_mem (Multiset.mem_toFinset.2 (Multiset.mem_filter.2 ⟨hr, hra⟩)))
  linarith

/-- 若 `p` 小于 `a` 的根都小于 `x < a`，则 `(x, ∞)` 中的根数等于 `(a, ∞)` 中的根数加上 `a` 的重数。 -/
theorem nAbove_just_below {p : ℝ[X]} {a x : ℝ} (hx : x < a) (h : ∀ r ∈ p.roots, r < a → r < x) :
    nAbove p x = nAbove p a + p.roots.count a := by
  have key : ∀ s : Multiset ℝ, (∀ r ∈ s, r < a → r < x) →
      Multiset.card (s.filter (x < ·)) = Multiset.card (s.filter (a < ·)) + s.count a := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons b s ih =>
      intro hs
      have ih := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
      rcases lt_trichotomy b a with hb | rfl | hb
      · have hbx : b < x := hs b (Multiset.mem_cons_self _ _) hb
        rw [Multiset.filter_cons_of_neg _ (not_lt.2 hbx.le),
          Multiset.filter_cons_of_neg _ (not_lt.2 hb.le), Multiset.count_cons_of_ne (ne_of_gt hb)]
        exact ih
      · rw [Multiset.filter_cons_of_pos _ hx, Multiset.filter_cons_of_neg _ (lt_irrefl _),
          Multiset.card_cons, Multiset.count_cons_self, ih]
        ring
      · rw [Multiset.filter_cons_of_pos _ (hx.trans hb), Multiset.filter_cons_of_pos _ hb,
          Multiset.card_cons, Multiset.card_cons, Multiset.count_cons_of_ne (ne_of_lt hb), ih]
        ring
  exact key _ h

/-- `g ≪ f` 时 `f` 在每点的重数至多比 `g` 多 1。 -/
theorem Interlaces.count_le {g f : ℝ[X]} (h : Interlaces g f) (a : ℝ) :
    f.roots.count a ≤ g.roots.count a + 1 := by
  obtain ⟨x, hx, hxr⟩ := exists_just_below f g a
  have hf := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inl hr))
  have hg := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inr hr))
  have h1 := h.2.2 x
  have h2 := h.2.2 a
  omega

/-- `f ≪ g` 时 `f` 在每点的重数至多比 `g` 多 1。 -/
theorem Interlaces.count_le' {f g : ℝ[X]} (h : Interlaces f g) (a : ℝ) :
    f.roots.count a ≤ g.roots.count a + 1 := by
  obtain ⟨x, hx, hxr⟩ := exists_just_below f g a
  have hf := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inl hr))
  have hg := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inr hr))
  have h1 := h.2.2 x
  have h2 := h.2.2 a
  omega

/-- `g ≪ f`、`a` 是 `f` 的单根且不是 `g` 的根时，`(a, ∞)` 中两者根数相同。 -/
theorem Interlaces.nAbove_eq_of_simple {g f : ℝ[X]} (h : Interlaces g f) {a : ℝ}
    (hfa : f.roots.count a = 1) (hga : g.roots.count a = 0) : nAbove g a = nAbove f a := by
  obtain ⟨x, hx, hxr⟩ := exists_just_below f g a
  have hf := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inl hr))
  have hg := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inr hr))
  have h1 := h.2.2 x
  have h2 := h.2.2 a
  omega

/-- `f ≪ g`、`a` 是 `f` 的单根且不是 `g` 的根时，`g` 在 `(a, ∞)` 中多一个根。 -/
theorem Interlaces.nAbove_eq_of_simple' {f g : ℝ[X]} (h : Interlaces f g) {a : ℝ}
    (hfa : f.roots.count a = 1) (hga : g.roots.count a = 0) : nAbove g a = nAbove f a + 1 := by
  obtain ⟨x, hx, hxr⟩ := exists_just_below f g a
  have hf := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inl hr))
  have hg := nAbove_just_below hx fun r hr => hxr r (Multiset.mem_add.2 (Or.inr hr))
  have h1 := h.2.2 x
  have h2 := h.2.2 a
  omega

theorem coneSum_congr {f : ℝ[X]} (c : ℝ) {w w' : ℝ → ℝ} (h : ∀ a ∈ f.roots, w a = w' a) :
    coneSum f c w = coneSum f c w' := by
  unfold coneSum
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [h a (Multiset.mem_toFinset.1 ha)]

theorem uconeSum_congr {f : ℝ[X]} (a b : ℝ) {e e' : ℝ → ℝ} (h : ∀ t ∈ f.roots, e t = e' t) :
    uconeSum f a b e = uconeSum f a b e' := by
  unfold uconeSum
  congr 1
  exact Finset.sum_congr rfl fun t ht => by rw [h t (Multiset.mem_toFinset.1 ht)]

/-- 首项系数为正的多项式的系数 `coeff n`（`deg ≤ n`）非负。 -/
theorem coeff_nonneg_of_natDegree_le {g : ℝ[X]} (hlc : 0 < g.leadingCoeff) {n : ℕ}
    (hn : g.natDegree ≤ n) : 0 ≤ g.coeff n := by
  rcases hn.lt_or_eq with hn | hn
  · rw [coeff_eq_zero_of_natDegree_lt hn]
  · rw [← hn]
    exact hlc.le

/-- 论文引理 8.5(1) 的「⇒」方向（锥的形式）：`g ≪ f`，首项系数都为正，则 `g = coneSum f c w`，
`c ≥ 0`，`w ≥ 0`（在 `f` 的根上）。 -/
theorem cone_of_interlaces {g f : ℝ[X]} (h : Interlaces g f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) :
    ∃ c, 0 ≤ c ∧ ∃ w : ℝ → ℝ, (∀ a ∈ f.roots, 0 ≤ w a) ∧ g = coneSum f c w := by
  have key : ∀ n, ∀ f g : ℝ[X], f.natDegree = n → Interlaces g f → 0 < f.leadingCoeff →
      0 < g.leadingCoeff →
      ∃ c, 0 ≤ c ∧ ∃ w : ℝ → ℝ, (∀ a ∈ f.roots, 0 ≤ w a) ∧ g = coneSum f c w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f g hn h hlcf hlcg
      have hf := h.1
      have hg := h.2.1
      by_cases hbad : ∃ a ∈ f.roots, 2 ≤ f.roots.count a ∨ g.IsRoot a
      · obtain ⟨a, ham, hcase⟩ := hbad
        have hfa := isRoot_of_mem_roots ham
        have hga : g.IsRoot a := by
          rcases hcase with hc | hc
          · have := h.count_le a
            exact isRoot_of_mem_roots (Multiset.count_pos.1 (by omega))
          · exact hc
        have hsf := divByMonic_spec hfa
        have hsg := divByMonic_spec hga
        have h₁ : Interlaces (g /ₘ (X - C a)) (f /ₘ (X - C a)) := by
          rw [← interlaces_mul_iff (realRooted_X_sub_C a), hsf, hsg]
          exact h
        have hdeg₁ : (f /ₘ (X - C a)).natDegree < n := by
          have := natDegree_divByMonic' hf.1 hfa
          omega
        obtain ⟨c, hc, w, hw, hgw⟩ := ih _ hdeg₁ _ _ rfl h₁
          (by rw [leadingCoeff_divByMonic' hfa]; exact hlcf)
          (by rw [leadingCoeff_divByMonic' hga]; exact hlcg)
        set w' : ℝ → ℝ := fun t => if t ∈ (f /ₘ (X - C a)).roots then w t else 0 with hw'
        refine ⟨c, hc, w', fun t ht => ?_, ?_⟩
        · simp only [hw']
          split_ifs with h'
          · exact hw t h'
          · exact le_rfl
        · have hfac := coneSum_factor hf.1 hfa c w' fun h1 => by
            simp only [hw']
            rw [ite_eq_right]
            intro hmem
            rw [roots_divByMonic hf.1 hfa, Multiset.count_cons_self] at h1
            have := Multiset.count_pos.2 hmem
            omega
          have hcongr : coneSum (f /ₘ (X - C a)) c w' = coneSum (f /ₘ (X - C a)) c w :=
            coneSum_congr c fun t ht => by
              simp only [hw']
              rw [ite_eq_left ht]
          rw [hfac, hcongr, ← hgw, hsg]
      · have hsimple : ∀ a ∈ f.roots, f.roots.count a = 1 := fun a ha => by
          have h1 := Multiset.count_pos.2 ha
          have h2 : ¬ 2 ≤ f.roots.count a := fun h2 => hbad ⟨a, ha, Or.inl h2⟩
          omega
        have hgne : ∀ a ∈ f.roots, g.eval a ≠ 0 := fun a ha h0 => hbad ⟨a, ha, Or.inr h0⟩
        have hnd : f.roots.Nodup := Multiset.nodup_iff_count_le_one.2 fun a => by
          by_cases ha : a ∈ f.roots
          · rw [hsimple a ha]
          · rw [Multiset.count_eq_zero.2 ha]
            exact zero_le_one
        set S := f.roots.toFinset with hS
        have hSn : S.card = f.natDegree := by
          rw [hS, Multiset.toFinset_card_of_nodup hnd, hf.2]
        have hdeg := h.natDegree_le
        set c := g.coeff f.natDegree / f.leadingCoeff with hc
        set w : ℝ → ℝ := fun a => g.eval a / (f /ₘ (X - C a)).eval a with hw
        have hq : ∀ a ∈ f.roots, (f /ₘ (X - C a)).eval a ≠ 0 := fun a ha h0 => by
          have := sign_divByMonic_eval hf hlcf (isRoot_of_mem_roots ha) (hsimple a ha)
          rw [h0, mul_zero] at this
          exact lt_irrefl _ this
        refine ⟨c, div_nonneg (coeff_nonneg_of_natDegree_le hlcg hdeg.1) hlcf.le, w,
          fun a ha => ?_, ?_⟩
        · have hfa := isRoot_of_mem_roots ha
          have hga0 : g.roots.count a = 0 :=
            Multiset.count_eq_zero.2 fun hm => hgne a ha ((mem_roots hg.1).1 hm)
          have hN := h.nAbove_eq_of_simple (hsimple a ha) hga0
          have h1 := sign_eval hg hlcg (hgne a ha)
          have h2 := sign_divByMonic_eval hf hlcf hfa (hsimple a ha)
          rw [hN] at h1
          have e : w a = ((-1) ^ nAbove f a * g.eval a) /
              ((-1) ^ nAbove f a * (f /ₘ (X - C a)).eval a) := by
            rw [hw, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]
          rw [e]
          exact (div_pos h1 h2).le
        · refine eq_of_degree_sub_lt_of_eval_finset_eq S ?_ ?_
          · rw [hSn, degree_lt_iff_coeff_zero]
            intro m hm
            rw [coeff_sub]
            rcases hm.lt_or_eq with hm | hm
            · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg.1 hm),
                coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_coneSum_le hf.1 c w) hm),
                sub_zero]
            · rw [← hm, coneSum_coeff hf.1 c w, hc, div_mul_cancel₀ _ hlcf.ne', sub_self]
          · intro a ha
            have ha' := Multiset.mem_toFinset.1 ha
            rw [coneSum_eval_root hf.1 c w (isRoot_of_mem_roots ha'), hw,
              div_mul_cancel₀ _ (hq a ha')]
  exact key _ f g rfl h hlcf hlcg

/-- 论文引理 8.5(2) 的「⇒」方向（上锥的形式）：`f ≪ g`，首项系数都为正，则 `g = uconeSum f a b e`，
`a ≥ 0`，`e ≥ 0`（在 `f` 的根上）。 -/
theorem ucone_of_interlaces {f g : ℝ[X]} (h : Interlaces f g) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) :
    ∃ a, 0 ≤ a ∧ ∃ b, ∃ e : ℝ → ℝ, (∀ t ∈ f.roots, 0 ≤ e t) ∧ g = uconeSum f a b e := by
  have key : ∀ n, ∀ f g : ℝ[X], f.natDegree = n → Interlaces f g → 0 < f.leadingCoeff →
      0 < g.leadingCoeff →
      ∃ a, 0 ≤ a ∧ ∃ b, ∃ e : ℝ → ℝ, (∀ t ∈ f.roots, 0 ≤ e t) ∧ g = uconeSum f a b e := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f g hn h hlcf hlcg
      have hf := h.2.1
      have hg := h.1
      by_cases hbad : ∃ t ∈ f.roots, 2 ≤ f.roots.count t ∨ g.IsRoot t
      · obtain ⟨t, htm, hcase⟩ := hbad
        have hft := isRoot_of_mem_roots htm
        have hgt : g.IsRoot t := by
          rcases hcase with hc | hc
          · have := h.count_le' t
            exact isRoot_of_mem_roots (Multiset.count_pos.1 (by omega))
          · exact hc
        have hsf := divByMonic_spec hft
        have hsg := divByMonic_spec hgt
        have h₁ : Interlaces (f /ₘ (X - C t)) (g /ₘ (X - C t)) := by
          rw [← interlaces_mul_iff (realRooted_X_sub_C t), hsf, hsg]
          exact h
        have hdeg₁ : (f /ₘ (X - C t)).natDegree < n := by
          have := natDegree_divByMonic' hf.1 hft
          omega
        obtain ⟨a, ha, b, e, he, hge⟩ := ih _ hdeg₁ _ _ rfl h₁
          (by rw [leadingCoeff_divByMonic' hft]; exact hlcf)
          (by rw [leadingCoeff_divByMonic' hgt]; exact hlcg)
        set e' : ℝ → ℝ := fun s => if s ∈ (f /ₘ (X - C t)).roots then e s else 0 with he'
        refine ⟨a, ha, b, e', fun s hs => ?_, ?_⟩
        · simp only [he']
          split_ifs with h'
          · exact he s h'
          · exact le_rfl
        · have hfac := uconeSum_factor hf.1 hft a b e' fun h1 => by
            simp only [he']
            rw [ite_eq_right]
            intro hmem
            rw [roots_divByMonic hf.1 hft, Multiset.count_cons_self] at h1
            have := Multiset.count_pos.2 hmem
            omega
          have hcongr : uconeSum (f /ₘ (X - C t)) a b e' = uconeSum (f /ₘ (X - C t)) a b e :=
            uconeSum_congr a b fun s hs => by
              simp only [he']
              rw [ite_eq_left hs]
          rw [hfac, hcongr, ← hge, hsg]
      · have hsimple : ∀ t ∈ f.roots, f.roots.count t = 1 := fun t ht => by
          have h1 := Multiset.count_pos.2 ht
          have h2 : ¬ 2 ≤ f.roots.count t := fun h2 => hbad ⟨t, ht, Or.inl h2⟩
          omega
        have hgne : ∀ t ∈ f.roots, g.eval t ≠ 0 := fun t ht h0 => hbad ⟨t, ht, Or.inr h0⟩
        have hnd : f.roots.Nodup := Multiset.nodup_iff_count_le_one.2 fun t => by
          by_cases ht : t ∈ f.roots
          · rw [hsimple t ht]
          · rw [Multiset.count_eq_zero.2 ht]
            exact zero_le_one
        set S := f.roots.toFinset with hS
        have hSn : S.card = f.natDegree := by
          rw [hS, Multiset.toFinset_card_of_nodup hnd, hf.2]
        have hdeg := h.natDegree_le
        set a := g.coeff (f.natDegree + 1) / f.leadingCoeff with ha
        set b := (g.coeff f.natDegree - (C a * X * f).coeff f.natDegree) / f.leadingCoeff with hb
        set e : ℝ → ℝ := fun t => -(g.eval t / (f /ₘ (X - C t)).eval t) with he
        have hq : ∀ t ∈ f.roots, (f /ₘ (X - C t)).eval t ≠ 0 := fun t ht h0 => by
          have := sign_divByMonic_eval hf hlcf (isRoot_of_mem_roots ht) (hsimple t ht)
          rw [h0, mul_zero] at this
          exact lt_irrefl _ this
        refine ⟨a, div_nonneg (coeff_nonneg_of_natDegree_le hlcg hdeg.2) hlcf.le, b, e,
          fun t ht => ?_, ?_⟩
        · have hft := isRoot_of_mem_roots ht
          have hgt0 : g.roots.count t = 0 :=
            Multiset.count_eq_zero.2 fun hm => hgne t ht ((mem_roots hg.1).1 hm)
          have hN := h.nAbove_eq_of_simple' (hsimple t ht) hgt0
          have h1 := sign_eval hg hlcg (hgne t ht)
          have h2 := sign_divByMonic_eval hf hlcf hft (hsimple t ht)
          rw [hN, pow_succ] at h1
          have e1 : e t = ((-1) ^ nAbove f t * -1 * g.eval t) /
              ((-1) ^ nAbove f t * (f /ₘ (X - C t)).eval t) := by
            rw [he, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]
            beta_reduce
            ring
          rw [e1]
          exact (div_pos h1 h2).le
        · refine eq_of_degree_sub_lt_of_eval_finset_eq S ?_ ?_
          · rw [hSn, degree_lt_iff_coeff_zero]
            intro m hm
            rw [coeff_sub]
            rcases hm.lt_or_eq with hm | hm
            · rcases (Nat.lt_iff_add_one_le.1 hm).lt_or_eq with hm2 | hm2
              · rw [coeff_eq_zero_of_natDegree_lt (by omega),
                  coeff_eq_zero_of_natDegree_lt
                    (lt_of_le_of_lt (natDegree_uconeSum_le hf.1 a b e) (by omega)), sub_zero]
              · rw [← hm2, uconeSum_coeff_succ hf.1 a b e, ha, div_mul_cancel₀ _ hlcf.ne', sub_self]
            · rw [← hm, uconeSum, coeff_sub, coeff_sum_divByMonic hf.1 e le_rfl, sub_zero, add_mul,
                coeff_add, coeff_C_mul, hb]
              have hl : f.coeff f.natDegree = f.leadingCoeff := rfl
              rw [hl, div_mul_cancel₀ _ hlcf.ne']
              ring
          · intro t ht
            have ht' := Multiset.mem_toFinset.1 ht
            rw [uconeSum_eval_root hf.1 a b e (isRoot_of_mem_roots ht'), he, neg_mul,
              div_mul_cancel₀ _ (hq t ht'), neg_neg]
  exact key _ f g rfl h hlcf hlcg

/-! ## 8. 交错的加法（论文引理 8.6） -/

theorem coneSum_add (f : ℝ[X]) (c₁ c₂ : ℝ) (w₁ w₂ : ℝ → ℝ) :
    coneSum f c₁ w₁ + coneSum f c₂ w₂ = coneSum f (c₁ + c₂) (fun a => w₁ a + w₂ a) := by
  simp only [coneSum, C_add, add_mul, Finset.sum_add_distrib]
  ring

theorem uconeSum_add (f : ℝ[X]) (a₁ a₂ b₁ b₂ : ℝ) (e₁ e₂ : ℝ → ℝ) :
    uconeSum f a₁ b₁ e₁ + uconeSum f a₂ b₂ e₂ =
      uconeSum f (a₁ + a₂) (b₁ + b₂) (fun t => e₁ t + e₂ t) := by
  simp only [uconeSum, C_add, add_mul, Finset.sum_add_distrib]
  ring

theorem leadingCoeff_add_pos {p q : ℝ[X]} (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff) :
    0 < (p + q).leadingCoeff := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · rw [leadingCoeff_add_of_degree_lt h]
    exact hq
  · rw [leadingCoeff_add_of_degree_eq h (by linarith)]
    linarith
  · rw [leadingCoeff_add_of_degree_lt' h]
    exact hp

/-- 论文引理 8.6 的第一句：`g ≪ f`、`h ≪ f`（首项系数都为正）推出 `g + h ≪ f`。 -/
theorem Interlaces.add_left {g h f : ℝ[X]} (hg : Interlaces g f) (hh : Interlaces h f)
    (hlcf : 0 < f.leadingCoeff) (hlcg : 0 < g.leadingCoeff) (hlch : 0 < h.leadingCoeff) :
    Interlaces (g + h) f := by
  obtain ⟨c₁, hc₁, w₁, hw₁, e₁⟩ := cone_of_interlaces hg hlcf hlcg
  obtain ⟨c₂, hc₂, w₂, hw₂, e₂⟩ := cone_of_interlaces hh hlcf hlch
  have hne : g + h ≠ 0 := leadingCoeff_ne_zero.1 (leadingCoeff_add_pos hlcg hlch).ne'
  have hsum : g + h = coneSum f (c₁ + c₂) (fun a => w₁ a + w₂ a) := by
    rw [e₁, e₂, coneSum_add]
  rw [hsum] at hne ⊢
  exact interlaces_coneSum hg.1 hlcf (by linarith)
    (fun a ha => add_nonneg (hw₁ a ha) (hw₂ a ha)) hne

/-- 论文引理 8.6 的第二句：`f ≪ g`、`f ≪ h`（首项系数都为正）推出 `f ≪ g + h`。 -/
theorem Interlaces.add_right {f g h : ℝ[X]} (hg : Interlaces f g) (hh : Interlaces f h)
    (hlcf : 0 < f.leadingCoeff) (hlcg : 0 < g.leadingCoeff) (hlch : 0 < h.leadingCoeff) :
    Interlaces f (g + h) := by
  obtain ⟨a₁, ha₁, b₁, e₁, he₁, E₁⟩ := ucone_of_interlaces hg hlcf hlcg
  obtain ⟨a₂, ha₂, b₂, e₂, he₂, E₂⟩ := ucone_of_interlaces hh hlcf hlch
  have hlc := leadingCoeff_add_pos hlcg hlch
  have hsum : g + h = uconeSum f (a₁ + a₂) (b₁ + b₂) (fun t => e₁ t + e₂ t) := by
    rw [E₁, E₂, uconeSum_add]
  rw [hsum] at hlc ⊢
  exact interlaces_uconeSum hg.2.1 hlcf (by linarith) _
    (fun t ht => add_nonneg (he₁ t ht) (he₂ t ht)) hlc

/-! ## 9. 下锥的封闭性 -/

/-- `g` 在 `f` 的下锥中。 -/
def InCone (g f : ℝ[X]) : Prop :=
  ∃ c, 0 ≤ c ∧ ∃ w : ℝ → ℝ, (∀ a ∈ f.roots, 0 ≤ w a) ∧ g = coneSum f c w

theorem InCone.zero (f : ℝ[X]) : InCone 0 f :=
  ⟨0, le_rfl, fun _ => 0, fun _ _ => le_rfl, by simp [coneSum]⟩

theorem InCone.self (f : ℝ[X]) : InCone f f :=
  ⟨1, zero_le_one, fun _ => 0, fun _ _ => le_rfl, by simp [coneSum]⟩

theorem InCone.add {g h f : ℝ[X]} (hg : InCone g f) (hh : InCone h f) : InCone (g + h) f := by
  obtain ⟨c₁, hc₁, w₁, hw₁, rfl⟩ := hg
  obtain ⟨c₂, hc₂, w₂, hw₂, rfl⟩ := hh
  exact ⟨c₁ + c₂, add_nonneg hc₁ hc₂, _, fun a ha => add_nonneg (hw₁ a ha) (hw₂ a ha),
    coneSum_add f c₁ c₂ w₁ w₂⟩

theorem InCone.C_mul {g f : ℝ[X]} (hg : InCone g f) {r : ℝ} (hr : 0 ≤ r) : InCone (C r * g) f := by
  obtain ⟨c, hc, w, hw, rfl⟩ := hg
  refine ⟨r * c, mul_nonneg hr hc, fun a => r * w a, fun a ha => mul_nonneg hr (hw a ha), ?_⟩
  rw [coneSum, coneSum, mul_add, Finset.mul_sum]
  congr 1
  · rw [Polynomial.C_mul]
    ring
  · exact Finset.sum_congr rfl fun a _ => by rw [Polynomial.C_mul]; ring

theorem InCone.sum {ι : Type*} (s : Finset ι) {r : ι → ℝ} {h : ι → ℝ[X]} {f : ℝ[X]}
    (hr : ∀ i ∈ s, 0 ≤ r i) (hh : ∀ i ∈ s, InCone (h i) f) :
    InCone (∑ i ∈ s, C (r i) * h i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InCone.zero f
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (InCone.C_mul (hh i (Finset.mem_insert_self _ _)) (hr i (Finset.mem_insert_self _ _))).add
      (ih (fun j hj => hr j (Finset.mem_insert_of_mem hj)) fun j hj =>
        hh j (Finset.mem_insert_of_mem hj))

theorem Interlaces.inCone {g f : ℝ[X]} (h : Interlaces g f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) : InCone g f :=
  cone_of_interlaces h hlcf hlcg

theorem InCone.interlaces {g f : ℝ[X]} (h : InCone g f) (hf : RealRooted f)
    (hlcf : 0 < f.leadingCoeff) (hg : g ≠ 0) : Interlaces g f := by
  obtain ⟨c, hc, w, hw, rfl⟩ := h
  exact interlaces_coneSum hf hlcf hc hw hg

/-! ## 10. 导数（论文引理 8.7(1)）与乘 `X`（引理 8.7(2)） -/

theorem derivative_prod_X_sub_C (s : Multiset ℝ) :
    derivative (s.map fun a => X - C a).prod =
      (s.map fun b => ((s.erase b).map fun a => X - C a).prod).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, ih,
      ← Multiset.sum_map_mul_left]
    congr 1
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro b hb
    by_cases hba : b = a
    · rw [hba, Multiset.erase_cons_head]
      rw [hba] at hb
      exact Multiset.prod_map_erase (f := fun a => X - C a) hb
    · rw [Multiset.erase_cons_tail _ (Ne.symm hba), Multiset.map_cons, Multiset.prod_cons]

/-- 实根多项式的导数：`f' = Σ_{a ∈ f 的不同根} (a 的重数)·f/(X−a)`。 -/
theorem derivative_eq_coneSum {f : ℝ[X]} (hf : RealRooted f) :
    derivative f = coneSum f 0 fun a => (f.roots.count a : ℝ) := by
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hf.2
  have h1 : derivative f = (f.roots.map fun b => f /ₘ (X - C b)).sum := by
    conv_lhs => rw [← hprod]
    rw [derivative_C_mul, derivative_prod_X_sub_C, ← Multiset.sum_map_mul_left]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro b hb
    have e : f = (X - C b) * (C f.leadingCoeff * ((f.roots.erase b).map fun a => X - C a).prod) := by
      rw [mul_left_comm, Multiset.prod_map_erase (f := fun a => X - C a) hb, hprod]
    conv_rhs => rw [e]
    rw [mul_divByMonic_cancel_left _ (monic_X_sub_C b)]
  rw [h1, Finset.sum_multiset_map_count, coneSum, C_0, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [nsmul_eq_mul, ← C_eq_natCast]

theorem leadingCoeff_derivative_pos {f : ℝ[X]} (hlc : 0 < f.leadingCoeff) (hdeg : 1 ≤ f.natDegree) :
    0 < (derivative f).leadingCoeff := by
  have hne : derivative f ≠ 0 := fun h0 => by
    have := derivative_eq_zero.1 h0
    omega
  have hle := natDegree_derivative_le f
  have hcoeff : (derivative f).coeff (f.natDegree - 1) = f.leadingCoeff * f.natDegree := by
    rw [coeff_derivative, Nat.sub_add_cancel hdeg, leadingCoeff]
    congr 1
    rw [Nat.cast_sub hdeg]
    push_cast
    ring
  have hdeg' : (derivative f).natDegree = f.natDegree - 1 := by
    apply le_antisymm hle
    apply le_natDegree_of_ne_zero
    rw [hcoeff]
    exact mul_ne_zero hlc.ne' (Nat.cast_ne_zero.2 (by omega))
  rw [leadingCoeff, hdeg', hcoeff]
  exact mul_pos hlc (by exact_mod_cast hdeg)

/-- 论文引理 8.7(1) 的第二句：`f' ≪ f`（`f` 实根、首项系数为正、`deg f ≥ 1`）。 -/
theorem interlaces_derivative {f : ℝ[X]} (hf : RealRooted f) (hlc : 0 < f.leadingCoeff)
    (hdeg : 1 ≤ f.natDegree) : Interlaces (derivative f) f := by
  have hne : derivative f ≠ 0 := fun h0 => by
    have := derivative_eq_zero.1 h0
    omega
  rw [derivative_eq_coneSum hf] at hne ⊢
  exact interlaces_coneSum hf hlc le_rfl (fun a _ => Nat.cast_nonneg _) hne

/-- 论文引理 8.7(1) 的第一句：`f ≪ (X − r)·f`（论文取 `r = −1`，即 `(1+z)·f`）。 -/
theorem interlaces_X_sub_C_mul {f : ℝ[X]} (hf : RealRooted f) (r : ℝ) :
    Interlaces f ((X - C r) * f) := by
  refine ⟨realRooted_mul (realRooted_X_sub_C r) hf, hf, fun x => ?_⟩
  rw [nAbove_mul (X_sub_C_ne_zero r) hf.1, nAbove_X_sub_C]
  split_ifs <;> omega

theorem realRooted_X : RealRooted (X : ℝ[X]) := by
  have := realRooted_X_sub_C 0
  rwa [C_0, sub_zero] at this

theorem nAbove_X (x : ℝ) : nAbove X x = if x < 0 then 1 else 0 := by
  have := nAbove_X_sub_C 0 x
  rwa [C_0, sub_zero] at this

/-- 论文引理 8.7(2)：`f` 的根都 `≤ 0` 时，`g ≪ f` 推出 `f ≪ X·g`。 -/
theorem Interlaces.X_mul {g f : ℝ[X]} (h : Interlaces g f) (hf0 : nAbove f 0 = 0) :
    Interlaces f (X * g) := by
  refine ⟨realRooted_mul realRooted_X h.2.1, h.1, fun x => ?_⟩
  rw [nAbove_mul realRooted_X.1 h.2.1.1, nAbove_X]
  obtain ⟨h1, h2⟩ := h.2.2 x
  split_ifs with hx
  · omega
  · have := nAbove_anti f (not_lt.1 hx)
    omega

/-- 系数都非负的非零多项式没有正根。 -/
theorem nAbove_zero_of_coeff_nonneg {p : ℝ[X]} (hp : p ≠ 0) (hc : ∀ i, 0 ≤ p.coeff i) :
    nAbove p 0 = 0 := by
  unfold nAbove
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr hr0
  have hroot := (mem_roots hp).1 hr
  have hpos : 0 < p.eval r := by
    rw [eval_eq_sum_range]
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hc i) (pow_nonneg hr0.le _))
      ⟨p.natDegree, Finset.self_mem_range_succ _, mul_pos ?_ (pow_pos hr0 _)⟩
    exact lt_of_le_of_ne (hc _) (Ne.symm (leadingCoeff_ne_zero.2 hp))
  rw [hroot.eq_zero] at hpos
  exact lt_irrefl _ hpos

end

end A207123
