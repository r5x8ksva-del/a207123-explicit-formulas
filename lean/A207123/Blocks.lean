import A207123.Ascent

/-!
# 论文定理 4.2（唯一分解）：好序列是块序列的串接

论文定义 4.1：对 `0 ≤ a < v`，块 `S_v = [v]`、`T_{v,a} = [a, v, v]`、`E_{v,a} = [a, v]`，另有 `S_0 = [0]`；
`v` 是块的层级（level），`a` 是谷（valley）。

定理 4.2：串接是一个双射，从「层级弱递减、都在 `{0,…,m}` 中、只有最后一块可以是 E 块」的有限块序列全体，
到 `⋃_k H_k(m)`（`H_k(m)` 即 `L k m`）。

* `Blk`、`Blk.toList`、`Blk.level`、`Blk.Valid`（T、E 块要求 `a < v`）、`Blk.IsE`；`concatBlk` 是串接。
* `BlkSeq m bs`：块序列满足定理 4.2 的条件（每块满足定义 4.1 且层级 ≤ `m`；层级弱递减；除最后一块外都不是 E 块）。
* `blocks_bijOn`：定理 4.2，`Set.BijOn concatBlk {bs | BlkSeq m bs} {h | ∃ k, h ∈ L k m}`。
* `asc_concatBlk`：例 4.3 之后一段的前半句：好序列的上升数等于它的 T 块与 E 块的个数。

证明同论文：串接都是好序列（块内与块间的三元组逐一检查，`legal_concatBlk`）；首块由序列决定
（`first_block_eq`：首项是后面各项的上界则为 S 块，否则为 T 或 E 块，E 块只能在最后，长度把两者分开）；存在性按长度
归纳（`exists_blocks_aux`：首项是后面各项的上界时切下 S 块，否则第二项比首项大，长为 2 时是 E 块，否则好三元组迫使
第三项等于第二项，切下 T 块）。
-/

namespace A207123

/-- 块（论文定义 4.1）：`S v = [v]`，`T v a = [a, v, v]`，`E v a = [a, v]`。 -/
inductive Blk
  | S (v : ℕ)
  | T (v a : ℕ)
  | E (v a : ℕ)

namespace Blk

/-- 块作为列表。 -/
def toList : Blk → List ℕ
  | S v => [v]
  | T v a => [a, v, v]
  | E v a => [a, v]

/-- 块的层级 `v`。 -/
def level : Blk → ℕ
  | S v => v
  | T v _ => v
  | E v _ => v

/-- 定义 4.1 的条件：T、E 块的谷小于层级（`a < v`）。 -/
def Valid : Blk → Prop
  | S _ => True
  | T v a => a < v
  | E v a => a < v

/-- E 块。 -/
def IsE : Blk → Prop
  | E _ _ => True
  | _ => False

/-- T 块或 E 块（计数用）。 -/
def isTE : Blk → Bool
  | S _ => false
  | _ => true

end Blk

/-- 串接。 -/
def concatBlk : List Blk → List ℕ
  | [] => []
  | b :: bs => b.toList ++ concatBlk bs

/-- 定理 4.2 的块序列：每块满足定义 4.1、层级 ≤ `m`；层级弱递减；除最后一块外都不是 E 块。 -/
def BlkSeq (m : ℕ) (bs : List Blk) : Prop :=
  (∀ b ∈ bs, b.Valid ∧ b.level ≤ m) ∧ bs.Pairwise (fun b c => c.level ≤ b.level) ∧
    ∀ b ∈ bs.dropLast, ¬ b.IsE

/-- 辅助引理（定理 4.2）：空块序列串接为空。 -/
theorem concatBlk_nil : concatBlk [] = [] := rfl

/-- 辅助引理（定理 4.2）：块中每一项都不超过它的层级。 -/
theorem Blk.le_level {b : Blk} (hb : b.Valid) {x : ℕ} (hx : x ∈ b.toList) : x ≤ b.level := by
  cases b with
  | S v =>
    simp only [Blk.toList, List.mem_singleton] at hx
    simp only [Blk.level]
    omega
  | T v a =>
    simp only [Blk.Valid] at hb
    simp only [Blk.toList, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Blk.level]
    omega
  | E v a =>
    simp only [Blk.Valid] at hb
    simp only [Blk.toList, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Blk.level]
    omega

/-- 辅助引理（定理 4.2）：各块层级都 ≤ `L` 时，串接的每一项都 ≤ `L`。 -/
theorem concatBlk_le {L : ℕ} {bs : List Blk} (h : ∀ b ∈ bs, b.Valid ∧ b.level ≤ L) :
    ∀ x ∈ concatBlk bs, x ≤ L := by
  induction bs with
  | nil => simp [concatBlk]
  | cons b bs ih =>
    intro x hx
    simp only [concatBlk, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (Blk.le_level (h b (by simp)).1 hx).trans (h b (by simp)).2
    · exact ih (fun c hc => h c (by simp [hc])) x hx

/-- 辅助引理（定理 4.2）：空块序列满足条件。 -/
theorem blkSeq_nil (L : ℕ) : BlkSeq L [] := ⟨by simp, List.Pairwise.nil, by simp⟩

/-- 辅助引理（定理 4.2）：`b :: bs` 满足条件，当且仅当 `b` 满足定义 4.1、层级 ≤ `L`、后面还有块时 `b` 不是 E 块，
且 `bs` 在层级上界 `b.level` 下满足条件。 -/
theorem BlkSeq.cons_iff {L : ℕ} {b : Blk} {bs : List Blk} :
    BlkSeq L (b :: bs) ↔ b.Valid ∧ b.level ≤ L ∧ (bs ≠ [] → ¬ b.IsE) ∧ BlkSeq b.level bs := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [List.pairwise_cons] at h2
    refine ⟨(h1 b (by simp)).1, (h1 b (by simp)).2, fun hne => h3 b ?_,
      ⟨fun c hc => ⟨(h1 c (by simp [hc])).1, h2.1 c hc⟩, h2.2, fun c hc => h3 c ?_⟩⟩
    · rw [List.dropLast_cons_of_ne_nil hne]
      simp
    · have hne : bs ≠ [] := by
        rintro rfl
        simp at hc
      rw [List.dropLast_cons_of_ne_nil hne]
      simp [hc]
  · rintro ⟨hb, hbL, hE, h1, h2, h3⟩
    refine ⟨fun c hc => ?_, List.pairwise_cons.mpr ⟨fun c hc => (h1 c hc).2, h2⟩, fun c hc => ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hb, hbL⟩
      · exact ⟨(h1 c hc).1, (h1 c hc).2.trans hbL⟩
    · by_cases hne : bs = []
      · subst hne
        simp at hc
      · rw [List.dropLast_cons_of_ne_nil hne] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hE hne
        · exact h3 c hc

/-- 辅助引理（定理 4.2）：满足条件的块序列，串接是好序列。 -/
theorem legal_concatBlk {L : ℕ} {bs : List Blk} (h : BlkSeq L bs) : Legal (concatBlk bs) := by
  induction bs generalizing L with
  | nil => simp [concatBlk]
  | cons b bs ih =>
    obtain ⟨hb, -, hE, hbs⟩ := BlkSeq.cons_iff.mp h
    have hR := concatBlk_le hbs.1
    have ihR := @ih _ hbs
    cases b with
    | S v =>
      simp only [Blk.level] at hR
      simp only [concatBlk, Blk.toList, List.singleton_append]
      exact (legal_cons_of_le hR).mpr ihR
    | T v a =>
      simp only [Blk.level] at hR
      simp only [concatBlk, Blk.toList, List.cons_append, List.nil_append]
      rw [legal_cons3]
      refine ⟨Or.inl rfl, ?_⟩
      have hR' : ∀ x ∈ v :: concatBlk bs, x ≤ v := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hR x hx
      exact (legal_cons_of_le hR').mpr ((legal_cons_of_le hR).mpr ihR)
    | E v a =>
      have hnil : bs = [] := by
        by_contra hne
        exact hE hne trivial
      subst hnil
      simp [concatBlk, Blk.toList]

/-- 辅助引理（定理 4.2，唯一性）：首块由串接决定。 -/
theorem first_block_eq {b b' : Blk} {R R' : List ℕ} (hb : b.Valid) (hb' : b'.Valid)
    (hR : ∀ x ∈ R, x ≤ b.level) (hR' : ∀ x ∈ R', x ≤ b'.level)
    (hE : b.IsE → R = []) (hE' : b'.IsE → R' = []) (h : b.toList ++ R = b'.toList ++ R') :
    b = b' := by
  cases b with
  | S v =>
    cases b' with
    | S v' =>
      simp only [Blk.toList, List.singleton_append] at h
      rw [(List.cons.inj h).1]
    | T v' a' =>
      simp only [Blk.Valid] at hb'
      simp only [Blk.toList, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hR v' (by simp)
      simp only [Blk.level] at this
      omega
    | E v' a' =>
      simp only [Blk.Valid] at hb'
      rw [hE' trivial] at h
      simp only [Blk.toList, List.cons_append, List.nil_append,
        List.append_nil, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hR v' (by simp)
      simp only [Blk.level] at this
      omega
  | T v a =>
    simp only [Blk.Valid] at hb
    cases b' with
    | S v' =>
      simp only [Blk.toList, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hR' v (by simp)
      simp only [Blk.level] at this
      omega
    | T v' a' =>
      simp only [Blk.toList, List.cons_append, List.nil_append] at h
      have h1 := List.cons.inj h
      have h2 := List.cons.inj h1.2
      rw [h1.1, h2.1]
    | E v' a' =>
      rw [hE' trivial] at h
      have := congrArg List.length h
      simp only [Blk.toList, List.length_append, List.length_cons, List.length_nil] at this
      omega
  | E v a =>
    simp only [Blk.Valid] at hb
    rw [hE trivial] at h
    cases b' with
    | S v' =>
      simp only [Blk.toList, List.cons_append, List.nil_append,
        List.append_nil, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hR' v (by simp)
      simp only [Blk.level] at this
      omega
    | T v' a' =>
      have := congrArg List.length h
      simp only [Blk.toList, List.length_append, List.length_cons, List.length_nil] at this
      omega
    | E v' a' =>
      rw [hE' trivial] at h
      simp only [Blk.toList, List.append_nil] at h
      have h1 := List.cons.inj h
      have h2 := List.cons.inj h1.2
      rw [h1.1, h2.1]

/-- 辅助引理（定理 4.2，唯一性）：满足条件的两个块序列串接相同，则它们相同。 -/
theorem concatBlk_inj {L L' : ℕ} {bs bs' : List Blk} (h : BlkSeq L bs) (h' : BlkSeq L' bs')
    (he : concatBlk bs = concatBlk bs') : bs = bs' := by
  induction bs generalizing L L' bs' with
  | nil =>
    cases bs' with
    | nil => rfl
    | cons b' bs' =>
      exfalso
      have := congrArg List.length he
      cases b' <;>
        simp only [concatBlk, Blk.toList, List.length_append, List.length_cons, List.length_nil] at this <;>
        omega
  | cons b bs ih =>
    cases bs' with
    | nil =>
      exfalso
      have := congrArg List.length he
      cases b <;>
        simp only [concatBlk, Blk.toList, List.length_append, List.length_cons, List.length_nil] at this <;>
        omega
    | cons b' bs' =>
      obtain ⟨hb, -, hE, hbs⟩ := BlkSeq.cons_iff.mp h
      obtain ⟨hb', -, hE', hbs'⟩ := BlkSeq.cons_iff.mp h'
      have hR0 : b.IsE → concatBlk bs = [] := fun hb0 => by
        have hnil : bs = [] := by
          by_contra hne
          exact hE hne hb0
        rw [hnil, concatBlk_nil]
      have hR0' : b'.IsE → concatBlk bs' = [] := fun hb0 => by
        have hnil : bs' = [] := by
          by_contra hne
          exact hE' hne hb0
        rw [hnil, concatBlk_nil]
      simp only [concatBlk] at he
      have hbb : b = b' :=
        first_block_eq hb hb' (concatBlk_le hbs.1) (concatBlk_le hbs'.1) hR0 hR0' he
      subst hbb
      rw [@ih _ _ _ hbs hbs' (List.append_cancel_left he)]

/-- 辅助引理（定理 4.2，存在性）：长度 ≤ `n`、各项 ≤ `L` 的好序列是满足条件（层级上界 `L`）的块序列的串接。 -/
theorem exists_blocks_aux (n : ℕ) : ∀ (h : List ℕ) (L : ℕ), h.length ≤ n → Legal h →
    (∀ x ∈ h, x ≤ L) → ∃ bs, BlkSeq L bs ∧ concatBlk bs = h := by
  induction n with
  | zero =>
    intro h L hlen _ _
    rcases h with _ | ⟨a, t⟩
    · exact ⟨[], blkSeq_nil L, rfl⟩
    · exact absurd hlen (Nat.not_succ_le_zero _)
  | succ n ih =>
    intro h L hlen hl hb
    rcases h with _ | ⟨h1, t⟩
    · exact ⟨[], blkSeq_nil L, rfl⟩
    · have hh1 : h1 ≤ L := hb h1 (by simp)
      by_cases hA : ∀ x ∈ t, x ≤ h1
      · -- 首项是后面各项的上界：切下 `S h1`
        obtain ⟨bs, hbs, hc⟩ :=
          ih t h1 (by simp only [List.length_cons] at hlen; omega) (legal_tail hl) hA
        refine ⟨Blk.S h1 :: bs, BlkSeq.cons_iff.mpr ⟨trivial, hh1, fun _ => id, hbs⟩, ?_⟩
        simp only [concatBlk, Blk.toList, List.singleton_append, hc]
      · rcases t with _ | ⟨h2, t'⟩
        · exact (hA fun x hx => by simp at hx).elim
        · -- 第二项比首项大
          have h12 : h1 < h2 := by
            by_contra h21
            apply hA
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have := legal_bound hl x hx
              omega
          have hh2 : h2 ≤ L := hb h2 (by simp)
          rcases t' with _ | ⟨h3, t''⟩
          · -- `[h1, h2]`：一个 E 块
            refine ⟨[Blk.E h2 h1], BlkSeq.cons_iff.mpr ⟨h12, hh2, fun hne => absurd rfl hne,
              blkSeq_nil _⟩, ?_⟩
            simp [concatBlk, Blk.toList]
          · -- `h1 :: h2 :: h3 :: t''`：好三元组迫使 `h3 = h2`，切下 `T h2 h1`
            have hg := ((legal_cons3 h1 h2 h3 t'').mp hl).1
            have h23 : h2 = h3 := by
              rcases hg with hg | ⟨hg, -⟩
              · exact hg
              · omega
            subst h23
            have hl2 : Legal (h2 :: h2 :: t'') := legal_tail hl
            have hbd : ∀ x ∈ t'', x ≤ h2 := fun x hx => by
              have := legal_bound hl2 x hx
              omega
            obtain ⟨bs, hbs, hc⟩ := ih t'' h2
              (by simp only [List.length_cons] at hlen; omega) (legal_tail (legal_tail hl2)) hbd
            refine ⟨Blk.T h2 h1 :: bs, BlkSeq.cons_iff.mpr ⟨h12, hh2, fun _ => id, hbs⟩, ?_⟩
            simp only [concatBlk, Blk.toList, List.cons_append, List.nil_append, hc]

/-- **定理 4.2（唯一分解）**：串接是一个双射，从「层级弱递减、都在 `{0,…,m}` 中、只有最后一块可以是 E 块」的
有限块序列全体，到 `⋃_k H_k(m)`。 -/
theorem blocks_bijOn (m : ℕ) :
    Set.BijOn concatBlk {bs | BlkSeq m bs} {h | ∃ k, h ∈ L k m} := by
  refine ⟨fun bs (hbs : BlkSeq m bs) => ⟨_, mem_L.mpr ⟨rfl, concatBlk_le hbs.1, legal_concatBlk hbs⟩⟩,
    fun bs (hbs : BlkSeq m bs) bs' (hbs' : BlkSeq m bs') he => concatBlk_inj hbs hbs' he,
    fun h hh => ?_⟩
  obtain ⟨k, hk⟩ := hh
  obtain ⟨-, hb, hl⟩ := mem_L.mp hk
  obtain ⟨bs, hbs, hc⟩ := exists_blocks_aux h.length h m le_rfl hl hb
  exact ⟨bs, hbs, hc⟩

/-- **例 4.3 之后一段**：好序列的上升数等于它的 T 块与 E 块的个数（上升恰好发生在谷之后）。 -/
theorem asc_concatBlk {L : ℕ} {bs : List Blk} (h : BlkSeq L bs) :
    asc (concatBlk bs) = bs.countP Blk.isTE := by
  induction bs generalizing L with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨hb, -, hE, hbs⟩ := BlkSeq.cons_iff.mp h
    have hR := concatBlk_le hbs.1
    have ih' := @ih _ hbs
    cases b with
    | S v =>
      simp only [Blk.level] at hR
      simp [concatBlk, Blk.toList, Blk.isTE, asc_cons_of_le hR, ih']
    | T v a =>
      simp only [Blk.level] at hR
      simp only [Blk.Valid] at hb
      simp [concatBlk, Blk.toList, Blk.isTE, List.countP_cons, asc_third hb hR, ih']
    | E v a =>
      have hnil : bs = [] := by
        by_contra hne
        exact hE hne trivial
      subst hnil
      simp only [Blk.Valid] at hb
      simp [concatBlk, Blk.toList, Blk.isTE, List.countP_cons, asc_cons_cons, hb]

end A207123
