import A207123.HStruct

/-!
# `R_k = A038718(k+2)`（猜想总表 A16；报告 T5.4(3)；notes/c5b.md 的 T6）

OEIS A038718（offset 1）按条目 %N 定义：`{1,…,n}` 的置换 `P` 中满足 `P(1) = 1`、且对 `i = 1, …, n−1` 有
`|P⁻¹(i+1) − P⁻¹(i)|` 等于 1 或 2 的个数。`A038718` 照此定义（下标从 0 起）。

令 `p_i = P⁻¹(i)`，则 `(p_0, …, p_{n−1})` 是图 `P_n²`（`|u − v| ≤ 2` 时相邻）中从 0 出发的 Hamilton 路
（`IsHam`，用列表表示；`A038718_eq_card_hamSet`）。`n ≥ 4` 时按开头分三类（`ham_cases`）：
* 0 → 1，此后是 `{1, …, n−1}` 上从 1 出发的路（`hamA`）；
* 0 → 2 → 1 → 3，此后是 `{3, …, n−1}` 上从 3 出发的路（`hamB`）；
* 其余情形 1 只能是终点，这样的路唯一，是之字形 `0, 2, 4, …, 5, 3, 1`（`zz`，`ham_end_one`）。
所以 `a(n) = a(n−1) + a(n−3) + 1`（`A038718_add_four`），与 `R_k = U_k(1)` 的递推 `U_one_rec` 相同，
初值也相同：`U_one_eq_A038718`。
-/

namespace A207123

open Finset

/-- 图 `P²` 的相邻关系：`|a − b|` 为 1 或 2。 -/
def hadj (a b : ℕ) : Prop := a + 1 = b ∨ a + 2 = b ∨ b + 1 = a ∨ b + 2 = a

instance : DecidableRel hadj := fun a b => by unfold hadj; infer_instance

/-- **A038718**（照 OEIS 条目 %N）：`{1,…,n}` 的置换 `P` 中满足 `P(1) = 1`、且对 `i = 1, …, n−1` 有
`|P⁻¹(i+1) − P⁻¹(i)|` 等于 1 或 2 的个数。下标从 0 起：`P(1) = 1` 写成「下标 0 处 `σ` 取 0」，
`P⁻¹(i+1)`、`P⁻¹(i)` 写成 `σ⁻¹ j`、`σ⁻¹ i`（`j = i + 1`）。 -/
def A038718 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, (i : ℕ) = 0 → (σ i : ℕ) = 0) ∧
    ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ((((σ⁻¹ j : Fin n) : ℕ) : ℤ) - (((σ⁻¹ i : Fin n) : ℕ) : ℤ)).natAbs = 1 ∨
      ((((σ⁻¹ j : Fin n) : ℕ) : ℤ) - (((σ⁻¹ i : Fin n) : ℕ) : ℤ)).natAbs = 2).card

/-- 从 0 出发的 Hamilton 路（列表表示）：`l` 无重复、长 `n`、各项 `< n`（即 `l` 是 `0, …, n−1` 的排列），
以 0 开头，相邻两项在 `P²` 中相邻。 -/
abbrev IsHam (n : ℕ) (l : List ℕ) : Prop :=
  l.Nodup ∧ l.length = n ∧ (∀ x ∈ l, x < n) ∧ l.head? = some 0 ∧ l.IsChain hadj

/-- `IsHam n` 的全体，作为有限集。 -/
def hamSet (n : ℕ) : Finset (List ℕ) :=
  (List.range n).permutations.toFinset.filter fun l => l.head? = some 0 ∧ l.IsChain hadj

theorem hadj_add_iff {a b c : ℕ} : hadj (a + c) (b + c) ↔ hadj a b := by
  unfold hadj
  constructor <;> intro h <;> omega

theorem hadj_sub_iff {a b c : ℕ} (ha : c ≤ a) (hb : c ≤ b) : hadj (a - c) (b - c) ↔ hadj a b := by
  unfold hadj
  constructor <;> intro h <;> omega

/-- 无重复、长 `n`、各项 `< n` 的列表含有每个 `x < n`。 -/
theorem IsHam.mem {n : ℕ} {l : List ℕ} (h : IsHam n l) {x : ℕ} (hx : x < n) : x ∈ l := by
  obtain ⟨hnd, hlen, hlt, -, -⟩ := h
  have hsub : l.toFinset ⊆ range n := fun y hy => mem_range.2 (hlt y (List.mem_toFinset.1 hy))
  have hcard : (range n).card ≤ l.toFinset.card := by
    rw [card_range, List.toFinset_card_of_nodup hnd, hlen]
  rw [← List.mem_toFinset, eq_of_subset_of_card_le hsub hcard]
  exact mem_range.2 hx

theorem mem_hamSet {n : ℕ} {l : List ℕ} : l ∈ hamSet n ↔ IsHam n l := by
  unfold hamSet
  rw [mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hp, hh, hc⟩
    exact ⟨hp.nodup_iff.2 List.nodup_range, by rw [hp.length_eq, List.length_range],
      fun x hx => List.mem_range.1 (hp.mem_iff.1 hx), hh, hc⟩
  · rintro ⟨hnd, hlen, hlt, hh, hc⟩
    refine ⟨(List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun a => ?_, hh, hc⟩
    rw [List.mem_range]
    exact ⟨hlt a, fun ha => IsHam.mem ⟨hnd, hlen, hlt, hh, hc⟩ ha⟩

/-- 各项 `≥ c` 的列表先减 `c` 再加 `c` 不变。 -/
theorem ham_map_sub_add : ∀ {l : List ℕ} {c : ℕ}, (∀ x ∈ l, c ≤ x) → (l.map (· - c)).map (· + c) = l
  | [], _, _ => rfl
  | a :: t, c, h => by
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ham_map_sub_add fun x hx => h x (List.mem_cons_of_mem a hx)⟩
    have := h a List.mem_cons_self
    omega

theorem ham_chain_map_add {c : ℕ} {l : List ℕ} (h : l.IsChain hadj) : (l.map (· + c)).IsChain hadj :=
  List.isChain_map_of_isChain _ (fun _ _ hab => hadj_add_iff.2 hab) h

/-- 各项 `< c` 的无重复列表接在各项 `≥ c` 的无重复列表前面，仍无重复。 -/
theorem ham_nodup_append {p l : List ℕ} {c : ℕ} (hp : p.Nodup) (hpc : ∀ x ∈ p, x < c)
    (hl : l.Nodup) (hlc : ∀ x ∈ l, c ≤ x) : (p ++ l).Nodup :=
  List.nodup_append.2 ⟨hp, hl, fun a ha b hb hab => by
    have := hpc a ha
    have := hlc b hb
    omega⟩

/-- 平移：`l` 无重复、长 `n`、各项在 `[c, n + c)` 中、以 `c` 开头、相邻项在 `P²` 中相邻，
则 `l` 各项减 `c` 是从 0 出发的 Hamilton 路。 -/
theorem isHam_map_sub {n c : ℕ} {l : List ℕ} (hnd : l.Nodup) (hlen : l.length = n)
    (hge : ∀ x ∈ l, c ≤ x) (hlt : ∀ x ∈ l, x < n + c) (hh : l.head? = some c)
    (hc : l.IsChain hadj) : IsHam n (l.map (· - c)) := by
  refine ⟨hnd.map_on fun x hx y hy hxy => ?_, by rw [List.length_map, hlen], fun x hx => ?_, ?_, ?_⟩
  · have h1 : x - c = y - c := hxy
    have := hge x hx
    have := hge y hy
    omega
  · simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hge y hy
    have := hlt y hy
    omega
  · rw [List.head?_map, hh]
    simp
  · rw [List.isChain_map]
    exact hc.imp_of_mem_imp fun a b ha hb hab => (hadj_sub_iff (hge a ha) (hge b hb)).2 hab

/-- 第一类：0 → 1，此后是平移 1 的路。 -/
def hamA (m : List ℕ) : List ℕ := 0 :: m.map (· + 1)

/-- 第二类：0 → 2 → 1 → 3，此后是平移 3 的路。 -/
def hamB (m : List ℕ) : List ℕ := 0 :: 2 :: 1 :: m.map (· + 3)

theorem isHam_hamA {n : ℕ} {m : List ℕ} (h : IsHam n m) : IsHam (n + 1) (hamA m) := by
  obtain ⟨hnd, hlen, hlt, hh, hc⟩ := h
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
  have heq : hamA (0 :: t) = [0] ++ (0 :: t).map (· + 1) := rfl
  have hge : ∀ x ∈ (0 :: t).map (· + 1), 1 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    omega
  rw [heq]
  refine ⟨ham_nodup_append (by decide) (by decide) (hnd.map (add_left_injective 1)) hge, ?_,
    fun x hx => ?_, rfl, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen ⊢
    omega
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · simp at hx
      omega
    · simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hlt y hy
      omega
  · refine List.isChain_append.2 ⟨by decide, ham_chain_map_add hc, fun x hx y hy => ?_⟩
    simp at hx hy
    subst hx
    subst hy
    unfold hadj
    omega

theorem isHam_hamB {n : ℕ} {m : List ℕ} (h : IsHam n m) : IsHam (n + 3) (hamB m) := by
  obtain ⟨hnd, hlen, hlt, hh, hc⟩ := h
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
  have heq : hamB (0 :: t) = [0, 2, 1] ++ (0 :: t).map (· + 3) := rfl
  have hge : ∀ x ∈ (0 :: t).map (· + 3), 3 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    omega
  rw [heq]
  refine ⟨ham_nodup_append (by decide) (by decide) (hnd.map (add_left_injective 3)) hge, ?_,
    fun x hx => ?_, rfl, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen ⊢
    omega
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · simp at hx
      omega
    · simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hlt y hy
      omega
  · refine List.isChain_append.2 ⟨by decide, ham_chain_map_add hc, fun x hx y hy => ?_⟩
    simp at hx hy
    subst hx
    subst hy
    unfold hadj
    omega

theorem hamA_injective : Function.Injective hamA := fun _ _ h =>
  List.map_injective_iff.2 (add_left_injective 1) (List.cons.inj h).2

theorem hamB_injective : Function.Injective hamB := fun _ _ h =>
  List.map_injective_iff.2 (add_left_injective 3)
    (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2

/-- 之字形路 `0, 2, 4, …, 5, 3, 1`（长 `n`）。 -/
def zz : ℕ → List ℕ
  | 0 => []
  | 1 => [0]
  | n + 2 => 0 :: ((zz n).map (· + 2) ++ [1])

theorem zz_add_two (n : ℕ) : zz (n + 2) = 0 :: ((zz n).map (· + 2) ++ [1]) := rfl

theorem zz_getLast (n : ℕ) : (zz (n + 2)).getLast? = some 1 := by
  rw [zz_add_two, ← List.cons_append, List.getLast?_concat]

theorem zz_getLast_le (n : ℕ) : ∀ x ∈ (zz (n + 1)).getLast?, x ≤ 1 := by
  rcases n with _ | n
  · intro x hx
    simp [zz] at hx
    omega
  · show ∀ x ∈ (zz (n + 2)).getLast?, x ≤ 1
    rw [zz_getLast]
    intro x hx
    simp at hx
    omega

theorem isHam_zz : ∀ n, IsHam (n + 1) (zz (n + 1))
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    obtain ⟨hnd, hlen, hlt, hh, hc⟩ := isHam_zz k
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 hh
    show IsHam (k + 3) (zz (k + 1 + 2))
    rw [zz_add_two]
    have hge : ∀ x ∈ (zz (k + 1)).map (· + 2), 2 ≤ x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      omega
    have hnd' : ((zz (k + 1)).map (· + 2) ++ [1]).Nodup :=
      List.nodup_append.2 ⟨hnd.map (add_left_injective 2), List.nodup_singleton 1,
        fun a ha b hb hab => by
          have := hge a ha
          simp at hb
          omega⟩
    refine ⟨List.nodup_cons.2 ⟨fun h0 => ?_, hnd'⟩, ?_, fun x hx => ?_, rfl, ?_⟩
    · rw [List.mem_append] at h0
      rcases h0 with h0 | h0
      · have := hge 0 h0
        omega
      · simp at h0
    · simp only [List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
    · simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩ | rfl
      · omega
      · have := hlt y hy
        omega
      · omega
    · refine List.isChain_cons.2 ⟨fun y hy => ?_, List.isChain_append.2 ⟨ham_chain_map_add hc,
        List.isChain_singleton 1, fun x hx y hy => ?_⟩⟩
      · rw [ht] at hy
        simp at hy
        subst hy
        unfold hadj
        omega
      · rw [List.getLast?_map] at hx
        simp only [Option.mem_def, Option.map_eq_some_iff] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        have := zz_getLast_le k z hz
        simp at hy
        subst hy
        unfold hadj
        omega

/-- 以 1 结尾、从 0 出发的 Hamilton 路唯一，就是之字形 `zz`（notes/c5b.md T6 (γ) 用到的子引理）。 -/
theorem ham_end_one : ∀ (n : ℕ) (p : List ℕ), IsHam (n + 2) (p ++ [1]) → p ++ [1] = zz (n + 2)
  | 0, p, h => by
    obtain ⟨-, hlen, -, hh, -⟩ := h
    have hp : p.length = 1 := by simpa using hlen
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hp
    have ha : a = 0 := by simpa using hh
    subst ha
    rfl
  | 1, p, h => by
    obtain ⟨hnd, hlen, hlt, hh, -⟩ := h
    have hp : p.length = 2 := by simpa using hlen
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hp
    have ha : a = 0 := by simpa using hh
    subst ha
    have hb : b < 3 := hlt b (by simp)
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hnd
    have hb1 : b ≠ 1 := by
      rintro rfl
      simp at hnd
    obtain rfl : b = 2 := by omega
    rfl
  | k + 2, p, h => by
    obtain ⟨hnd, hlen, hlt, hh, hc⟩ := h
    have hplen : p.length = k + 3 := by simpa using hlen
    obtain ⟨q, rfl⟩ : ∃ q, p = 0 :: q := by
      cases p with
      | nil => simp at hplen
      | cons a q =>
        have ha : a = 0 := by simpa using hh
        exact ⟨q, by rw [ha]⟩
    have hqlen : q.length = k + 2 := by simpa using hplen
    rw [List.cons_append] at hnd hlt hc ⊢
    have hq0 : ∀ x ∈ q, x ≠ 0 := fun x hx h0 =>
      (List.nodup_cons.1 hnd).1 (List.mem_append_left _ (h0 ▸ hx))
    have hq1 : ∀ x ∈ q, x ≠ 1 := fun x hx h1 =>
      (List.nodup_append.1 (List.nodup_cons.1 hnd).2).2.2 x hx 1 (by simp) h1
    have hq2 : ∀ x ∈ q, 2 ≤ x := fun x hx => by
      have := hq0 x hx
      have := hq1 x hx
      omega
    -- `q` 的末项 `x` 与 1 相邻
    obtain ⟨q₂, x, rfl⟩ : ∃ q₂ x, q = q₂ ++ [x] := by
      rcases List.eq_nil_or_concat' q with h | h
      · subst h
        simp at hqlen
      · exact h
    have hx1 : hadj x 1 :=
      (List.isChain_append.1 (List.isChain_cons.1 hc).2).2.2 x (by simp) 1 (by simp)
    -- `q` 的首项是 2
    obtain ⟨y, q₃, rfl⟩ : ∃ y q₃, q₂ = y :: q₃ := by
      cases q₂ with
      | nil => simp at hqlen
      | cons y q₃ => exact ⟨y, q₃, rfl⟩
    have hc' : (0 :: y :: (q₃ ++ [x] ++ [1])).IsChain hadj := by
      simpa only [List.cons_append] using hc
    have hy : hadj 0 y := (List.isChain_cons_cons.1 hc').1
    have hy2 : y = 2 := by
      have := hq2 y (by simp)
      unfold hadj at hy
      omega
    subst hy2
    -- 于是 `q` 的末项是 3
    have hx3 : x = 3 := by
      have hx2 := hq2 x (by simp)
      have hx2' : x ≠ 2 := by
        rintro rfl
        simp at hnd
      unfold hadj at hx1
      omega
    subst hx3
    -- 中间一段 `2, …, 3` 减 2 后是以 1 结尾的路，按归纳假设是 `zz (k + 2)`
    have hL : IsHam (k + 2) (((2 :: q₃) ++ [3]).map (· - 2)) := by
      refine isHam_map_sub (List.nodup_append.1 (List.nodup_cons.1 hnd).2).1 hqlen hq2
        (fun z hz => ?_) rfl (List.isChain_cons.1 hc).2.left_of_append
      have := hlt z (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
      omega
    rw [List.map_append] at hL
    have key := ham_end_one k ((2 :: q₃).map (· - 2)) hL
    have hq_eq : (2 :: q₃) ++ [3] = ((2 :: q₃).map (· - 2) ++ [1]).map (· + 2) := by
      rw [List.map_append, ham_map_sub_add fun z hz => hq2 z (List.mem_append_left _ hz)]
      rfl
    rw [hq_eq, key]
    rfl

/-- `zz (n + 4)` 的第三项 ≥ 3（用来区分 `zz` 与第二类）。 -/
theorem zz_add_four (n : ℕ) : ∃ x t, zz (n + 4) = 0 :: 2 :: x :: t ∧ 3 ≤ x := by
  rw [show n + 4 = n + 2 + 2 from rfl, zz_add_two, zz_add_two]
  rcases h : (zz n).map (· + 2) with _ | ⟨y, t⟩
  · exact ⟨3, [1], rfl, le_rfl⟩
  · have hy : 2 ≤ y := by
      have hy' : y ∈ (zz n).map (· + 2) := by
        rw [h]
        simp
      simp only [List.mem_map] at hy'
      obtain ⟨a, -, rfl⟩ := hy'
      omega
    exact ⟨y + 2, (t ++ [1]).map (· + 2) ++ [1], rfl, by omega⟩

/-- `n ≥ 4` 时从 0 出发的 Hamilton 路分三类（notes/c5b.md T6 的 (α)(β)(γ)）。 -/
theorem ham_cases {n : ℕ} {l : List ℕ} (h : IsHam (n + 4) l) :
    (∃ m, IsHam (n + 3) m ∧ l = hamA m) ∨ (∃ m, IsHam (n + 1) m ∧ l = hamB m) ∨
      l = zz (n + 4) := by
  have hmem : ∀ x, x < n + 4 → x ∈ l := fun x hx => h.mem hx
  obtain ⟨hnd, hlen, hlt, hh, hc⟩ := h
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
  have ht0 : ∀ x ∈ t, x ≠ 0 := fun x hx h0 => (List.nodup_cons.1 hnd).1 (h0 ▸ hx)
  have htlen : t.length = n + 3 := by simpa using hlen
  obtain ⟨b, t1, rfl⟩ : ∃ b t1, t = b :: t1 := by
    cases t with
    | nil => simp at htlen
    | cons b t1 => exact ⟨b, t1, rfl⟩
  have hb : hadj 0 b := (List.isChain_cons_cons.1 hc).1
  have hb12 : b = 1 ∨ b = 2 := by
    unfold hadj at hb
    omega
  rcases hb12 with rfl | rfl
  · -- (α) 0 → 1
    left
    have hge : ∀ x ∈ 1 :: t1, 1 ≤ x := fun x hx => Nat.one_le_iff_ne_zero.2 (ht0 x hx)
    refine ⟨(1 :: t1).map (· - 1), isHam_map_sub (List.nodup_cons.1 hnd).2 htlen hge
      (fun x hx => ?_) rfl (List.isChain_cons_cons.1 hc).2, ?_⟩
    · have := hlt x (List.mem_cons_of_mem _ hx)
      omega
    · unfold hamA
      rw [ham_map_sub_add hge]
  · -- 0 → 2
    right
    have ht1len : t1.length = n + 2 := by simpa using htlen
    obtain ⟨c, t2, rfl⟩ : ∃ c t2, t1 = c :: t2 := by
      cases t1 with
      | nil => simp at ht1len
      | cons c t2 => exact ⟨c, t2, rfl⟩
    have hc2 : hadj 2 c := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hc).2).1
    have hc0 : c ≠ 0 := ht0 c (by simp)
    have hc' : c = 1 ∨ c = 3 ∨ c = 4 := by
      unfold hadj at hc2
      omega
    rcases hc' with rfl | hc34
    · -- (β) 0 → 2 → 1 → 3
      left
      have ht2len : t2.length = n + 1 := by simpa using ht1len
      obtain ⟨d, t3, rfl⟩ : ∃ d t3, t2 = d :: t3 := by
        cases t2 with
        | nil => simp at ht2len
        | cons d t3 => exact ⟨d, t3, rfl⟩
      have hd : hadj 1 d :=
        (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hc).2).2).1
      have hd0 : d ≠ 0 := ht0 d (by simp)
      have hnd2 := List.nodup_cons.1 (List.nodup_cons.1 hnd).2
      have hnd1 := List.nodup_cons.1 hnd2.2
      have hd2 : d ≠ 2 := by
        rintro rfl
        exact hnd2.1 (by simp)
      obtain rfl : d = 3 := by
        unfold hadj at hd
        omega
      have hge : ∀ x ∈ 3 :: t3, 3 ≤ x := by
        intro x hx
        have h0 : x ≠ 0 := ht0 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
        have h1 : x ≠ 1 := fun h => hnd1.1 (h ▸ hx)
        have h2 : x ≠ 2 := fun h => hnd2.1 (List.mem_cons_of_mem _ (h ▸ hx))
        omega
      refine ⟨(3 :: t3).map (· - 3), isHam_map_sub hnd1.2 ht2len hge (fun x hx => ?_) rfl
        (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hc).2).2).2, ?_⟩
      · have := hlt x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
        omega
      · unfold hamB
        rw [ham_map_sub_add hge]
    · -- (γ) 0 → 2 → c（c = 3 或 4）：1 只能是终点
      right
      have h1 : 1 ∈ t2 := by
        have := hmem 1 (by omega)
        simp only [List.mem_cons] at this
        rcases this with h | h | h | h
        · omega
        · omega
        · omega
        · exact h
      obtain ⟨u, w, rfl⟩ := List.append_of_mem h1
      have hc3 : (u ++ 1 :: w).IsChain hadj :=
        (List.isChain_cons.1 (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hc).2).2).2
      have hnd3 : (u ++ 1 :: w).Nodup :=
        (List.nodup_cons.1 (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).2).2
      have h2u : 2 ∉ c :: (u ++ 1 :: w) := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
      have hw : w = [] := by
        rcases w with _ | ⟨y, w'⟩
        · rfl
        · exfalso
          have h1y : hadj 1 y := (List.isChain_cons_cons.1 (List.isChain_append.1 hc3).2.1).1
          have hy0 : y ≠ 0 := ht0 y (by simp)
          have hy2 : y ≠ 2 := by
            rintro rfl
            exact h2u (by simp)
          obtain rfl : y = 3 := by
            unfold hadj at h1y
            omega
          rcases List.eq_nil_or_concat' u with rfl | ⟨u', x, rfl⟩
          · -- 1 的前一项是 c：c = 3，与 y = 3 重复
            have hc1 : hadj c 1 := by
              simp only [List.nil_append] at hc
              exact (List.isChain_cons_cons.1 (List.isChain_cons_cons.1
                (List.isChain_cons_cons.1 hc).2).2).1
            obtain rfl : c = 3 := by
              unfold hadj at hc1
              omega
            simp at hnd
          · -- 1 的前一项 x：x = 3，与 y = 3 重复
            have hx1 : hadj x 1 := (List.isChain_append.1 hc3).2.2 x (by simp) 1 (by simp)
            have hx0 : x ≠ 0 := ht0 x (by simp)
            have hx2 : x ≠ 2 := by
              rintro rfl
              exact h2u (by simp)
            obtain rfl : x = 3 := by
              unfold hadj at hx1
              omega
            exact (List.nodup_append.1 hnd3).2.2 3 (by simp) 3 (by simp) rfl
      subst hw
      exact ham_end_one (n + 2) (0 :: 2 :: c :: u) ⟨hnd, hlen, hlt, rfl, hc⟩

theorem hamSet_add_four (n : ℕ) :
    hamSet (n + 4) =
      ((hamSet (n + 3)).image hamA ∪ (hamSet (n + 1)).image hamB) ∪ {zz (n + 4)} := by
  ext l
  simp only [mem_union, mem_image, mem_singleton, mem_hamSet]
  constructor
  · intro h
    rcases ham_cases h with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | rfl
    · exact Or.inl (Or.inl ⟨m, hm, rfl⟩)
    · exact Or.inl (Or.inr ⟨m, hm, rfl⟩)
    · exact Or.inr rfl
  · rintro ((⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩) | rfl)
    · exact isHam_hamA hm
    · exact isHam_hamB hm
    · exact isHam_zz (n + 3)

theorem card_hamSet_add_four (n : ℕ) :
    (hamSet (n + 4)).card = (hamSet (n + 3)).card + (hamSet (n + 1)).card + 1 := by
  have hAB : Disjoint ((hamSet (n + 3)).image hamA) ((hamSet (n + 1)).image hamB) := by
    rw [disjoint_left]
    intro l hA hB
    rw [mem_image] at hA hB
    obtain ⟨m₁, hm₁, rfl⟩ := hA
    obtain ⟨m₂, -, h⟩ := hB
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 (mem_hamSet.1 hm₁).2.2.2.1
    have : (0 : ℕ) + 1 = 2 := (List.cons.inj (List.cons.inj h).2).1.symm
    omega
  have hZ : Disjoint ((hamSet (n + 3)).image hamA ∪ (hamSet (n + 1)).image hamB) {zz (n + 4)} := by
    rw [disjoint_singleton_right, mem_union, not_or, mem_image, mem_image]
    obtain ⟨x, t, hz, hx⟩ := zz_add_four n
    refine ⟨fun ⟨m, hm, h⟩ => ?_, fun ⟨m, _, h⟩ => ?_⟩
    · obtain ⟨t', rfl⟩ := List.head?_eq_some_iff.1 (mem_hamSet.1 hm).2.2.2.1
      rw [hz] at h
      have : (0 : ℕ) + 1 = 2 := (List.cons.inj (List.cons.inj h).2).1
      omega
    · rw [hz] at h
      have : 1 = x := (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).1
      omega
  rw [hamSet_add_four, card_union_of_disjoint hZ, card_union_of_disjoint hAB,
    card_image_of_injective _ hamA_injective, card_image_of_injective _ hamB_injective, card_singleton]

/-- 按 OEIS 的置换定义数出的 A038718(n) 等于从 0 出发的 Hamilton 路数（`p_i = σ⁻¹(i)`）。 -/
theorem A038718_eq_card_hamSet {n : ℕ} (hn : 1 ≤ n) : A038718 n = (hamSet n).card := by
  unfold A038718
  refine card_bij (fun σ _ => (List.finRange n).map fun i => ((σ⁻¹ i : Fin n) : ℕ)) ?_ ?_ ?_
  · intro σ hσ
    rw [mem_filter] at hσ
    obtain ⟨-, h0, h1⟩ := hσ
    show (List.finRange n).map (fun i => ((σ⁻¹ i : Fin n) : ℕ)) ∈ hamSet n
    rw [mem_hamSet]
    refine ⟨(List.nodup_finRange n).map (Fin.val_injective.comp (σ⁻¹).injective), by simp,
      fun x hx => ?_, ?_, ?_⟩
    · simp only [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact (σ⁻¹ i).isLt
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [List.finRange_succ, List.map_cons, List.head?_cons]
      have hs : (σ 0 : ℕ) = 0 := h0 0 (by simp)
      have hs' : σ 0 = 0 := Fin.ext (by rw [hs]; simp)
      have h00 : σ⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, hs']
      rw [h00]
      simp
    · rw [List.isChain_iff_getElem]
      intro i hi
      simp only [List.length_map, List.length_finRange] at hi
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      have := h1 ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
      unfold hadj
      rcases this with h | h <;> rw [Int.natAbs_eq_iff] at h <;> omega
  · intro σ₁ _ σ₂ _ h
    have h2 : (List.finRange n).map (fun i => ((σ₁⁻¹ i : Fin n) : ℕ)) =
        (List.finRange n).map (fun i => ((σ₂⁻¹ i : Fin n) : ℕ)) := h
    have h' : σ₁⁻¹ = σ₂⁻¹ :=
      Equiv.ext fun i => Fin.ext (List.map_inj_left.1 h2 i (List.mem_finRange i))
    exact inv_injective h'
  · intro l hl
    obtain ⟨hnd, hlen, hlt, hh, hc⟩ := mem_hamSet.1 hl
    have hinj : Function.Injective fun i : Fin n =>
        (⟨l[i.val]'(by rw [hlen]; exact i.isLt), hlt _ (List.getElem_mem _)⟩ : Fin n) := by
      intro i j hij
      exact Fin.ext ((hnd.getElem_inj_iff).1 (congrArg Fin.val hij))
    obtain ⟨e, he⟩ : ∃ e : Equiv.Perm (Fin n),
        ∀ (i : ℕ) (hi : i < n), (e ⟨i, hi⟩ : ℕ) = l[i]'(by rw [hlen]; exact hi) :=
      ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj), fun i hi => rfl⟩
    have hl0 : l[0]'(by rw [hlen]; omega) = 0 := by
      obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
      rfl
    refine ⟨e⁻¹, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_univ _, fun i hi => ?_, fun i j hij => ?_⟩
      · have hei : e (e⁻¹ i) = i := by
          rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
        generalize e⁻¹ i = j at hei ⊢
        obtain ⟨jv, hjv⟩ := j
        have h1 := congrArg Fin.val hei
        rw [he, hi] at h1
        show jv = 0
        exact (hnd.getElem_inj_iff).1 (h1.trans hl0.symm)
      · obtain ⟨jv, hjv⟩ := j
        obtain ⟨iv, hiv⟩ := i
        have hij' : jv = iv + 1 := hij
        subst hij'
        rw [inv_inv, he, he]
        have hc' := List.isChain_iff_getElem.1 hc iv (by rw [hlen]; exact hjv)
        unfold hadj at hc'
        rcases hc' with h | h | h | h <;> simp only [Int.natAbs_eq_iff] <;> omega
    · show (List.finRange n).map (fun i => (((e⁻¹)⁻¹ i : Fin n) : ℕ)) = l
      rw [inv_inv]
      apply List.ext_getElem
      · simp [hlen]
      · intro k h1 h2
        simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
        exact he k (by simpa using h1)

theorem A038718_add_four (n : ℕ) :
    A038718 (n + 4) = A038718 (n + 3) + A038718 (n + 1) + 1 := by
  rw [A038718_eq_card_hamSet (by omega), A038718_eq_card_hamSet (by omega),
    A038718_eq_card_hamSet (by omega), card_hamSet_add_four]

/-- OEIS 条目 %F 的递推 `a(n) = a(n−1) + a(n−3) + 1`（`n ≥ 4`）。 -/
theorem A038718_rec {n : ℕ} (hn : 4 ≤ n) :
    A038718 n = A038718 (n - 1) + A038718 (n - 3) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega]
  exact A038718_add_four m

theorem isHam_one_eq {p : List ℕ} (h : IsHam 1 p) : p = [0] := by
  obtain ⟨-, hlen, -, hh, -⟩ := h
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
  have ht : t = [] := by simpa using hlen
  rw [ht]

theorem isHam_two_eq {p : List ℕ} (h : IsHam 2 p) : p = [0, 1] := by
  obtain ⟨hnd, hlen, hlt, hh, -⟩ := h
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
  have ht : t.length = 1 := by simpa using hlen
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 ht
  have hb : b < 2 := hlt b (by simp)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hnd
  obtain rfl : b = 1 := by omega
  rfl

theorem isHam_three_eq {p : List ℕ} (h : IsHam 3 p) : p = [0, 1, 2] ∨ p = [0, 2, 1] := by
  obtain ⟨hnd, hlen, hlt, hh, -⟩ := h
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 hh
  have ht : t.length = 2 := by simpa using hlen
  obtain ⟨b, c, rfl⟩ := List.length_eq_two.1 ht
  have hb : b < 3 := hlt b (by simp)
  have hc : c < 3 := hlt c (by simp)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hnd
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hnd
  have hbc : b ≠ c := by
    rintro rfl
    simp at hnd
  have : (b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem A038718_one : A038718 1 = 1 := by
  rw [A038718_eq_card_hamSet le_rfl, card_eq_one]
  refine ⟨[0], ?_⟩
  ext l
  rw [mem_hamSet, mem_singleton]
  refine ⟨isHam_one_eq, ?_⟩
  rintro rfl
  decide

theorem A038718_two : A038718 2 = 1 := by
  rw [A038718_eq_card_hamSet (by norm_num), card_eq_one]
  refine ⟨[0, 1], ?_⟩
  ext l
  rw [mem_hamSet, mem_singleton]
  refine ⟨isHam_two_eq, ?_⟩
  rintro rfl
  decide

theorem A038718_three : A038718 3 = 2 := by
  rw [A038718_eq_card_hamSet (by norm_num)]
  have h3 : hamSet 3 = {[0, 1, 2], [0, 2, 1]} := by
    ext l
    rw [mem_hamSet, mem_insert, mem_singleton]
    refine ⟨isHam_three_eq, ?_⟩
    rintro (rfl | rfl) <;> decide
  rw [h3, card_pair_eq_two_iff]
  decide

theorem A038718_four : A038718 4 = 4 := by
  have h : A038718 4 = A038718 3 + A038718 1 + 1 := A038718_add_four 0
  rw [A038718_three, A038718_one] at h
  omega

/-- **T5.4(3)（猜想总表 A16）**：`R_k = U_k(1) = A038718(k + 2)`，对一切 `k ≥ 0`
（A038718 按 OEIS 条目的置换定义）。 -/
theorem U_one_eq_A038718 (k : ℕ) : U k 1 = A038718 (k + 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.lt_or_ge k 3 with hk | hk
  · have h0 : U 0 1 = 1 := U_of_le_two (by norm_num) 1
    have h1 : U 1 1 = 2 := U_of_le_two (by norm_num) 1
    have h2 : U 2 1 = 4 := U_of_le_two (by norm_num) 1
    interval_cases k
    · show U 0 1 = A038718 2
      rw [h0, A038718_two]
    · show U 1 1 = A038718 3
      rw [h1, A038718_three]
    · show U 2 1 = A038718 4
      rw [h2, A038718_four]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have h : A038718 (j + 3 + 2) = A038718 (j + 2 + 2) + A038718 (j + 2) + 1 :=
      A038718_add_four (j + 1)
    rw [U_one_rec, ih (j + 2) (by omega), ih j (by omega), h]

/-! ### 显式双射（notes/c5b.md T6 的「自然双射」）

长 `k` 的允许行（`m = 1`：0/1 串，不含 001、010）按前缀分三类：`0^k`、`1w`、`011w`（`k = 2` 时还有 `01`），
与 Hamilton 路的三类逐项对应。 -/

/-- 允许行到 `P_{k+2}²` 中从 0 出发的 Hamilton 路的递归映射：`1w ↦ hamA (rowPath w)`，
`011w ↦ hamB (rowPath w)`，`01 ↦ hamB [0]`，其余 `↦ zz (长度 + 2)`（对允许行而言「其余」就是全 0 行）。 -/
def rowPath : List ℕ → List ℕ
  | 1 :: w => hamA (rowPath w)
  | 0 :: 1 :: 1 :: w => hamB (rowPath w)
  | [0, 1] => hamB [0]
  | w => zz (w.length + 2)

/-- `rowPath` 把任何列表都映到一条 Hamilton 路（长度 + 2 个顶点）。 -/
theorem isHam_rowPath : ∀ w : List ℕ, IsHam (w.length + 2) (rowPath w)
  | [] => isHam_zz 1
  | 1 :: w => isHam_hamA (isHam_rowPath w)
  | 0 :: 1 :: 1 :: w => isHam_hamB (isHam_rowPath w)
  | [0, 1] => isHam_hamB (n := 1) (m := [0]) (by decide)
  | [0] => isHam_zz 2
  | 0 :: 0 :: w => isHam_zz (w.length + 3)
  | 0 :: 1 :: 0 :: w => isHam_zz (w.length + 4)
  | 0 :: 1 :: (_ + 2) :: w => isHam_zz (w.length + 4)
  | 0 :: (_ + 2) :: w => isHam_zz (w.length + 3)
  | (_ + 2) :: w => isHam_zz (w.length + 2)

theorem legal_one_cons : ∀ {w : List ℕ}, (∀ x ∈ w, x ≤ 1) → Legal w → Legal (1 :: w)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: t, hw, hl => by
    refine (legal_cons3 1 a b t).2 ⟨?_, hl⟩
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    unfold Good
    omega

theorem legal_zero_one_one {w : List ℕ} (hw : ∀ x ∈ w, x ≤ 1) (hl : Legal w) :
    Legal (0 :: 1 :: 1 :: w) := by
  have h1 : ∀ x ∈ 1 :: w, x ≤ 1 := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact hw x hx
  exact (legal_cons3 0 1 1 w).2 ⟨Or.inl rfl, legal_one_cons h1 (legal_one_cons hw hl)⟩

theorem legal_replicate_zero : ∀ k, Legal (List.replicate k 0)
  | 0 => trivial
  | 1 => trivial
  | 2 => trivial
  | k + 3 => (legal_cons3 0 0 0 _).2 ⟨Or.inl rfl, legal_replicate_zero (k + 2)⟩

/-- 满射：每条 Hamilton 路都是某个允许行的像。 -/
theorem rowPath_surj (k : ℕ) : ∀ p : List ℕ, IsHam (k + 2) p → ∃ w ∈ L k 1, rowPath w = p := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro p hp
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · refine ⟨[], mem_L.2 ⟨rfl, by simp, trivial⟩, ?_⟩
      rw [isHam_two_eq hp]
      rfl
    · rcases isHam_three_eq hp with rfl | rfl
      · exact ⟨[1], mem_L.2 ⟨rfl, by decide, trivial⟩, rfl⟩
      · exact ⟨[0], mem_L.2 ⟨rfl, by decide, trivial⟩, rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rcases ham_cases (n := j) hp with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | rfl
    · obtain ⟨w, hw, rfl⟩ := ih (j + 1) (by omega) m hm
      obtain ⟨hwl, hwm, hwleg⟩ := mem_L.1 hw
      have hwm1 : ∀ x ∈ 1 :: w, x ≤ 1 := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_rfl
        · exact hwm x hx
      refine ⟨1 :: w, mem_L.2 ⟨?_, hwm1, legal_one_cons hwm hwleg⟩, rfl⟩
      simp only [List.length_cons]
      omega
    · rcases j with _ | i
      · rw [isHam_one_eq hm]
        exact ⟨[0, 1], mem_L.2 ⟨rfl, by decide, trivial⟩, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := ih i (by omega) m hm
        obtain ⟨hwl, hwm, hwleg⟩ := mem_L.1 hw
        have hwm1 : ∀ x ∈ 0 :: 1 :: 1 :: w, x ≤ 1 := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · omega
          · omega
          · omega
          · exact hwm x hx
        refine ⟨0 :: 1 :: 1 :: w, mem_L.2 ⟨?_, hwm1, legal_zero_one_one hwm hwleg⟩, rfl⟩
        simp only [List.length_cons]
        omega
    · refine ⟨List.replicate (j + 2) 0, mem_L.2 ⟨List.length_replicate, fun x hx => ?_,
        legal_replicate_zero _⟩, ?_⟩
      · have := (List.mem_replicate.1 hx).2
        omega
      · show zz ((List.replicate (j + 2) 0).length + 2) = zz (j + 2 + 2)
        rw [List.length_replicate]

/-- **T5.4(3) 的显式双射**：`rowPath` 把长 `k` 的允许行（`L k 1`）一一对应到 `P_{k+2}²` 中从 0 出发的
Hamilton 路（单射由满射与两边个数相同 `U_one_eq_A038718` 得到）。 -/
theorem rowPath_bijOn (k : ℕ) :
    Set.BijOn rowPath (L k 1 : Set (List ℕ)) (hamSet (k + 2) : Set (List ℕ)) := by
  have hmaps : Set.MapsTo rowPath (L k 1 : Set (List ℕ)) (hamSet (k + 2) : Set (List ℕ)) := by
    intro w hw
    rw [Finset.mem_coe] at hw
    rw [Finset.mem_coe, mem_hamSet]
    have := isHam_rowPath w
    rwa [(mem_L.1 hw).1] at this
  have hsurj : Set.SurjOn rowPath (L k 1 : Set (List ℕ)) (hamSet (k + 2) : Set (List ℕ)) := by
    intro p hp
    rw [Finset.mem_coe, mem_hamSet] at hp
    obtain ⟨w, hw, rfl⟩ := rowPath_surj k p hp
    exact Set.mem_image_of_mem rowPath (Finset.mem_coe.2 hw)
  have hcard : (L k 1).card ≤ (hamSet (k + 2)).card := by
    rw [← A038718_eq_card_hamSet (n := k + 2) (by omega), ← U_one_eq_A038718]
    exact le_rfl
  exact ⟨hmaps, Finset.injOn_of_surjOn_of_card_le rowPath hmaps hsurj hcard, hsurj⟩

end A207123
