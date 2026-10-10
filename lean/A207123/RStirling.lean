import A207123.Formula

/-!
# 论文引理 4.5 的最后一句：`H(m,s,j)` 是集合划分个数（r-Stirling 数）

论文引理 4.5：「`H(m,s,0) = H(m,s,1) = {m+s \brace m}`，且 `1 ≤ j ≤ m` 时 `H(m,s,j) = {m+s \brace m}_j` 是
`{1, …, m+s}` 分成 `m` 块、使 `1, …, j` 两两不同块的划分个数」。这里 `H(m,s,j) = h_s(j, …, m) = hc s (vars j m)`
（`Formula.lean`）。`H(m,s,0) = S(m+s, m)` 已由 `Formula.lean` 的 `hc_vars_zero` 形式化，其中 `S` 是 Mathlib 的
`Nat.stirlingSecond`（按递推定义）；本文件补上「划分个数」这一层意思：

* `IsSetPartition S Q`：`Q` 是有限集 `S` 的集合划分（各块非空、两两不交、并为 `S`）；`Separates j Q`：`1, …, j`
  两两不在同一块；`setParts j N m`：`{1, …, N}` 分成 `m` 块且分开 `1, …, j` 的划分全体，`partCount j N m` 是其个数。
* `hc_vars_eq_partCount`：`j ≤ m` 时 `H(m,s,j) = partCount j (m+s) m`；`j ≥ 1` 时这就是论文的 r-Stirling 数。
* `stirlingSecond_eq_partCount`：`S(N, m) = partCount 0 N m`，即 Mathlib 按递推定义的 `Nat.stirlingSecond` 确实是
  `{1, …, N}` 分成 `m` 块的划分个数；`partCount_one`：分开一个元素没有约束。
* `lemma_coef_partitions`：论文这一句的合并陈述。

证明：去掉最大元 `N + 1`。它或者单独成块（去掉这一块，`card_setParts_single`），或者在一个更大的块里（从块里
去掉它；反过来把它加进某一块，`card_setParts_join`）。`N + 1 > j` 时加进哪一块都可以，`N + 1 ≤ j` 时它只能进不含
`1, …, j` 的块，而这样的块不存在。于是 `N ≥ j` 时 `partCount j (N+1) (m+1) = partCount j N m + (m+1)·partCount j N (m+1)`，
与 `h_{s+1}(j, …, m+1) = h_{s+1}(j, …, m) + (m+1)·h_s(j, …, m+1)` 一致；`N ≤ j` 时只有全单点划分。
-/

namespace A207123

open Finset

/-- `Q` 是有限集 `S` 的集合划分：各块非空、两两不交、并为 `S`。 -/
def IsSetPartition (S : Finset ℕ) (Q : Finset (Finset ℕ)) : Prop :=
  (∀ B ∈ Q, B.Nonempty) ∧ (∀ B ∈ Q, ∀ C ∈ Q, B ≠ C → Disjoint B C) ∧ Q.biUnion id = S

/-- `1, …, j` 两两不在同一块。 -/
def Separates (j : ℕ) (Q : Finset (Finset ℕ)) : Prop :=
  ∀ B ∈ Q, ∀ a ∈ B, ∀ b ∈ B, a ≤ j → b ≤ j → a = b

open Classical in
/-- `{1, …, N}` 分成 `m` 块、`1, …, j` 两两不同块的集合划分全体。 -/
noncomputable def setParts (j N m : ℕ) : Finset (Finset (Finset ℕ)) :=
  (Icc 1 N).powerset.powerset.filter fun Q => IsSetPartition (Icc 1 N) Q ∧ #Q = m ∧ Separates j Q

/-- 上面这样的划分的个数：`j ≤ 1` 时是第二类 Stirling 数 `S(N, m)`，一般是 r-Stirling 数 `{N \brace m}_j`。 -/
noncomputable def partCount (j N m : ℕ) : ℕ := #(setParts j N m)

/-- 把新元素 `n` 加进块 `B` 不破坏「`1, …, j` 两两不同块」：`n ≤ j` 时 `B` 里不能有 `≤ j` 的元素。 -/
def Allowed (j n : ℕ) (B : Finset ℕ) : Prop := n ≤ j → ∀ b ∈ B, j < b

instance (j n : ℕ) : DecidablePred (Allowed j n) := fun B => by
  unfold Allowed
  infer_instance

/-- 辅助引理（引理 4.5）：`setParts` 的成员。 -/
theorem mem_setParts {j N m : ℕ} {Q : Finset (Finset ℕ)} :
    Q ∈ setParts j N m ↔ IsSetPartition (Icc 1 N) Q ∧ #Q = m ∧ Separates j Q := by
  classical
  unfold setParts
  rw [mem_filter, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨fun B hB => ?_, h⟩⟩
  rw [mem_powerset, ← h.1.2.2]
  exact subset_biUnion_of_mem id hB

/-- 辅助引理（引理 4.5）：每一块都含于 `S`。 -/
theorem IsSetPartition.subset {S : Finset ℕ} {Q : Finset (Finset ℕ)} (h : IsSetPartition S Q)
    {B : Finset ℕ} (hB : B ∈ Q) : B ⊆ S := by
  rw [← h.2.2]
  exact subset_biUnion_of_mem id hB

/-- 辅助引理（引理 4.5）：`S` 的每个元素都在某一块里。 -/
theorem IsSetPartition.exists_mem {S : Finset ℕ} {Q : Finset (Finset ℕ)} (h : IsSetPartition S Q)
    {x : ℕ} (hx : x ∈ S) : ∃ B ∈ Q, x ∈ B := by
  rw [← h.2.2, mem_biUnion] at hx
  exact hx

/-- 辅助引理（引理 4.5）：含同一元素的两块相同。 -/
theorem IsSetPartition.eq_of_mem {S : Finset ℕ} {Q : Finset (Finset ℕ)} (h : IsSetPartition S Q)
    {B C : Finset ℕ} (hB : B ∈ Q) (hC : C ∈ Q) {x : ℕ} (hxB : x ∈ B) (hxC : x ∈ C) : B = C := by
  by_contra hne
  exact Finset.disjoint_left.mp (h.2.1 B hB C hC hne) hxB hxC

/-- 辅助引理（引理 4.5）：`{1, …, N+1} = {N+1} ∪ {1, …, N}`。 -/
theorem Icc_succ_eq (N : ℕ) : Icc 1 (N + 1) = insert (N + 1) (Icc 1 N) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

/-- 辅助引理（引理 4.5）：`{1, …, N}` 的划分的块都不含 `N + 1`。 -/
theorem not_mem_block {N : ℕ} {Q : Finset (Finset ℕ)} (h : IsSetPartition (Icc 1 N) Q) :
    ∀ B ∈ Q, N + 1 ∉ B := fun B hB hn => by
  have := h.subset hB hn
  simp at this

/-- 辅助引理（引理 4.5）：空集只有空划分。 -/
theorem partCount_zero_left (j m : ℕ) : partCount j 0 m = if m = 0 then 1 else 0 := by
  have key : ∀ Q, Q ∈ setParts j 0 m ↔ Q = ∅ ∧ m = 0 := by
    intro Q
    rw [mem_setParts]
    constructor
    · rintro ⟨⟨hne, -, hU⟩, hc, -⟩
      have hQ : Q = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro B hB
        obtain ⟨x, hx⟩ := hne B hB
        have : x ∈ Q.biUnion id := mem_biUnion.mpr ⟨B, hB, hx⟩
        rw [hU] at this
        simp at this
      exact ⟨hQ, by rw [← hc, hQ, card_empty]⟩
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨by simp, by simp, ?_⟩, by simp, by simp [Separates]⟩
      rw [biUnion_empty]
      exact (Icc_eq_empty_of_lt (by norm_num)).symm
  split_ifs with hm
  · subst hm
    rw [partCount, card_eq_one]
    exact ⟨∅, Finset.ext fun Q => by rw [key, mem_singleton]; simp⟩
  · rw [partCount, card_eq_zero, eq_empty_iff_forall_notMem]
    intro Q hQ
    exact hm ((key Q).mp hQ).2

/-- 辅助引理（引理 4.5）：非空集不能分成 0 块。 -/
theorem partCount_succ_zero (j N : ℕ) : partCount j (N + 1) 0 = 0 := by
  rw [partCount, card_eq_zero, eq_empty_iff_forall_notMem]
  intro Q hQ
  rw [mem_setParts] at hQ
  obtain ⟨⟨-, -, hU⟩, hc, -⟩ := hQ
  rw [card_eq_zero] at hc
  subst hc
  have : N + 1 ∈ Icc 1 (N + 1) := by simp
  rw [← hU] at this
  simp at this

/-- 辅助引理（引理 4.5）：`N + 1` 单独成块的划分，去掉这一块后一一对应 `{1, …, N}` 分成 `m` 块的划分。 -/
theorem card_setParts_single (j N m : ℕ) :
    #((setParts j (N + 1) (m + 1)).filter fun Q => {N + 1} ∈ Q) = partCount j N m := by
  classical
  rw [partCount]
  symm
  refine card_bij' (fun R _ => insert {N + 1} R) (fun Q _ => Q.erase {N + 1}) ?_ ?_ ?_ ?_
  · intro R hR
    try dsimp only
    rw [mem_setParts] at hR
    obtain ⟨⟨hne, hdis, hU⟩, hc, hsep⟩ := hR
    have hnot := not_mem_block (⟨hne, hdis, hU⟩ : IsSetPartition (Icc 1 N) R)
    have hsing : ({N + 1} : Finset ℕ) ∉ R := fun h => hnot _ h (mem_singleton_self _)
    rw [mem_filter, mem_setParts]
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, mem_insert_self _ _⟩
    · intro B hB
      rw [mem_insert] at hB
      rcases hB with rfl | hB
      · exact singleton_nonempty _
      · exact hne B hB
    · intro B hB C hC hBC
      rw [mem_insert] at hB hC
      rcases hB with rfl | hB <;> rcases hC with rfl | hC
      · exact absurd rfl hBC
      · exact disjoint_singleton_left.mpr (hnot C hC)
      · exact disjoint_singleton_right.mpr (hnot B hB)
      · exact hdis B hB C hC hBC
    · calc (insert {N + 1} R).biUnion id = {N + 1} ∪ R.biUnion id := biUnion_insert
        _ = Icc 1 (N + 1) := by rw [hU, Icc_succ_eq, insert_eq]
    · rw [card_insert_of_notMem hsing, hc]
    · intro B hB a ha b hb haj hbj
      rw [mem_insert] at hB
      rcases hB with rfl | hB
      · rw [mem_singleton] at ha hb
        rw [ha, hb]
      · exact hsep B hB a ha b hb haj hbj
  · intro Q hQ
    try dsimp only
    rw [mem_filter, mem_setParts] at hQ
    obtain ⟨⟨⟨hne, hdis, hU⟩, hc, hsep⟩, hs⟩ := hQ
    have hP : IsSetPartition (Icc 1 (N + 1)) Q := ⟨hne, hdis, hU⟩
    rw [mem_setParts]
    refine ⟨⟨fun B hB => hne B (mem_of_mem_erase hB),
      fun B hB C hC hBC => hdis B (mem_of_mem_erase hB) C (mem_of_mem_erase hC) hBC, ?_⟩, ?_,
      fun B hB => hsep B (mem_of_mem_erase hB)⟩
    · ext x
      rw [mem_biUnion]
      constructor
      · rintro ⟨B, hB, hx⟩
        have hB' := mem_of_mem_erase hB
        have hxN : x ∈ Icc 1 (N + 1) := by
          rw [← hU]
          exact mem_biUnion.mpr ⟨B, hB', hx⟩
        have hne' : x ≠ N + 1 := by
          rintro rfl
          exact ne_of_mem_erase hB (hP.eq_of_mem hB' hs hx (mem_singleton_self _))
        rw [Icc_succ_eq, mem_insert] at hxN
        exact hxN.resolve_left hne'
      · intro hx
        have hx' : x ∈ Icc 1 (N + 1) := by
          rw [Icc_succ_eq]
          exact mem_insert_of_mem hx
        obtain ⟨B, hB, hxB⟩ := hP.exists_mem hx'
        refine ⟨B, mem_erase.mpr ⟨?_, hB⟩, hxB⟩
        rintro rfl
        rw [mem_singleton] at hxB
        subst hxB
        simp at hx
    · simp [card_erase_of_mem hs, hc]
  · intro R hR
    rw [mem_setParts] at hR
    have hnot := not_mem_block hR.1
    exact erase_insert fun h => hnot _ h (mem_singleton_self _)
  · intro Q hQ
    rw [mem_filter] at hQ
    exact insert_erase hQ.2

/-- 辅助引理（引理 4.5）：`N + 1` 不单独成块的划分，一一对应「`{1, …, N}` 分成 `m + 1` 块的划分 `R` 与 `R` 中可以
加入 `N + 1` 的一块 `B`」。 -/
theorem card_setParts_join (j N m : ℕ) :
    #((setParts j (N + 1) (m + 1)).filter fun Q => {N + 1} ∉ Q) =
      ∑ R ∈ setParts j N (m + 1), #(R.filter (Allowed j (N + 1))) := by
  classical
  rw [← card_sigma]
  symm
  refine card_bij (fun p _ => insert (insert (N + 1) p.2) (p.1.erase p.2)) ?_ ?_ ?_
  · rintro ⟨R, B⟩ hp
    simp only [mem_sigma, mem_filter, mem_setParts] at hp
    obtain ⟨⟨⟨hne, hdis, hU⟩, hc, hsep⟩, hB, hall⟩ := hp
    have hP : IsSetPartition (Icc 1 N) R := ⟨hne, hdis, hU⟩
    have hnot := not_mem_block hP
    have hnew : insert (N + 1) B ∉ R.erase B := fun h =>
      hnot _ (mem_of_mem_erase h) (mem_insert_self _ _)
    try dsimp only
    rw [mem_filter, mem_setParts]
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro C hC
      rw [mem_insert] at hC
      rcases hC with rfl | hC
      · exact insert_nonempty _ _
      · exact hne C (mem_of_mem_erase hC)
    · intro C hC D hD hCD
      rw [mem_insert] at hC hD
      have key : ∀ E ∈ R.erase B, Disjoint (insert (N + 1) B) E := fun E hE => by
        rw [disjoint_insert_left]
        exact ⟨hnot E (mem_of_mem_erase hE),
          hdis B hB E (mem_of_mem_erase hE) (ne_of_mem_erase hE).symm⟩
      rcases hC with rfl | hC <;> rcases hD with rfl | hD
      · exact absurd rfl hCD
      · exact key D hD
      · exact (key C hC).symm
      · exact hdis C (mem_of_mem_erase hC) D (mem_of_mem_erase hD) hCD
    · have hR' : R.biUnion id = B ∪ (R.erase B).biUnion id := by
        conv_lhs => rw [← insert_erase hB]
        simp only [biUnion_insert, id_eq]
      rw [biUnion_insert, Icc_succ_eq, ← hU, hR']
      exact insert_union _ _ _
    · simp [card_insert_of_notMem hnew, card_erase_of_mem hB, hc]
    · intro C hC a ha b hb haj hbj
      rw [mem_insert] at hC
      rcases hC with rfl | hC
      · rw [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · rfl
        · exact absurd hbj (not_le.mpr (hall haj b hb))
        · exact absurd haj (not_le.mpr (hall hbj a ha))
        · exact hsep B hB a ha b hb haj hbj
      · exact hsep C (mem_of_mem_erase hC) a ha b hb haj hbj
    · rw [mem_insert, not_or]
      refine ⟨fun h => ?_, fun h => hnot _ (mem_of_mem_erase h) (mem_singleton_self _)⟩
      obtain ⟨b, hb⟩ := hne B hB
      have hb' : b ∈ ({N + 1} : Finset ℕ) := by
        rw [h]
        exact mem_insert_of_mem hb
      rw [mem_singleton] at hb'
      subst hb'
      exact hnot B hB hb
  · rintro ⟨R, B⟩ hp ⟨R', B'⟩ hp' heq
    try dsimp only at heq
    simp only [mem_sigma, mem_filter, mem_setParts] at hp hp'
    obtain ⟨⟨hP, -, -⟩, hB, -⟩ := hp
    obtain ⟨⟨hP', -, -⟩, hB', -⟩ := hp'
    have hnot := not_mem_block hP
    have hnot' := not_mem_block hP'
    have h1 : insert (N + 1) B ∈ insert (insert (N + 1) B') (R'.erase B') := by
      rw [← heq]
      exact mem_insert_self _ _
    rw [mem_insert] at h1
    have hBB : B = B' := by
      rcases h1 with h1 | h1
      · have := congrArg (fun s => Finset.erase s (N + 1)) h1
        simp only [erase_insert (hnot B hB), erase_insert (hnot' B' hB')] at this
        exact this
      · exact absurd (mem_insert_self (N + 1) B) (hnot' _ (mem_of_mem_erase h1))
    subst hBB
    have hRR : R.erase B = R'.erase B := by
      have := congrArg (fun s => Finset.erase s (insert (N + 1) B)) heq
      simp only [erase_insert (fun h => hnot _ (mem_of_mem_erase h) (mem_insert_self _ _)),
        erase_insert (fun h => hnot' _ (mem_of_mem_erase h) (mem_insert_self _ _))] at this
      exact this
    have hR : R = R' := by rw [← insert_erase hB, hRR, insert_erase hB']
    subst hR
    rfl
  · intro Q hQ
    rw [mem_filter, mem_setParts] at hQ
    obtain ⟨⟨⟨hne, hdis, hU⟩, hc, hsep⟩, hs⟩ := hQ
    have hP : IsSetPartition (Icc 1 (N + 1)) Q := ⟨hne, hdis, hU⟩
    obtain ⟨B0, hB0, hn⟩ := hP.exists_mem (by simp : N + 1 ∈ Icc 1 (N + 1))
    have hB0ne : B0 ≠ {N + 1} := fun h => hs (h ▸ hB0)
    obtain ⟨B, hBdef⟩ : ∃ B, B = B0.erase (N + 1) := ⟨_, rfl⟩
    have hBsub : B ⊆ B0 := by
      rw [hBdef]
      exact erase_subset _ _
    have hnB : N + 1 ∉ B := by
      rw [hBdef]
      exact notMem_erase _ _
    have hBne : B.Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro h
      apply hB0ne
      rw [← insert_erase hn, ← hBdef, h]
      rfl
    have hBQ : B ∉ Q.erase B0 := by
      intro h
      obtain ⟨b, hb⟩ := hBne
      exact ne_of_mem_erase h (hP.eq_of_mem (mem_of_mem_erase h) hB0 hb (hBsub hb))
    refine ⟨⟨insert B (Q.erase B0), B⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_filter, mem_setParts]
      refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, mem_insert_self _ _, ?_⟩
      · intro C hC
        rw [mem_insert] at hC
        rcases hC with rfl | hC
        · exact hBne
        · exact hne C (mem_of_mem_erase hC)
      · intro C hC D hD hCD
        rw [mem_insert] at hC hD
        have key : ∀ E ∈ Q.erase B0, Disjoint B E := fun E hE =>
          (hdis B0 hB0 E (mem_of_mem_erase hE) (ne_of_mem_erase hE).symm).mono_left hBsub
        rcases hC with rfl | hC <;> rcases hD with rfl | hD
        · exact absurd rfl hCD
        · exact key D hD
        · exact (key C hC).symm
        · exact hdis C (mem_of_mem_erase hC) D (mem_of_mem_erase hD) hCD
      · ext x
        rw [mem_biUnion]
        constructor
        · rintro ⟨C, hC, hx⟩
          rw [mem_insert] at hC
          have hxQ : x ∈ Icc 1 (N + 1) := by
            rw [← hU, mem_biUnion]
            rcases hC with rfl | hC
            · exact ⟨B0, hB0, hBsub hx⟩
            · exact ⟨C, mem_of_mem_erase hC, hx⟩
          have hxn : x ≠ N + 1 := by
            rintro rfl
            rcases hC with rfl | hC
            · exact hnB hx
            · exact ne_of_mem_erase hC (hP.eq_of_mem (mem_of_mem_erase hC) hB0 hx hn)
          rw [Icc_succ_eq, mem_insert] at hxQ
          exact hxQ.resolve_left hxn
        · intro hx
          have hx' : x ∈ Icc 1 (N + 1) := by
            rw [Icc_succ_eq]
            exact mem_insert_of_mem hx
          obtain ⟨C, hC, hxC⟩ := hP.exists_mem hx'
          have hxn : x ≠ N + 1 := by
            rintro rfl
            simp at hx
          by_cases hCB : C = B0
          · subst hCB
            refine ⟨B, mem_insert_self _ _, ?_⟩
            rw [hBdef]
            exact mem_erase.mpr ⟨hxn, hxC⟩
          · exact ⟨C, mem_insert_of_mem (mem_erase.mpr ⟨hCB, hC⟩), hxC⟩
      · simp [card_insert_of_notMem hBQ, card_erase_of_mem hB0, hc]
      · intro C hC a ha b hb haj hbj
        rw [mem_insert] at hC
        rcases hC with rfl | hC
        · exact hsep B0 hB0 a (hBsub ha) b (hBsub hb) haj hbj
        · exact hsep C (mem_of_mem_erase hC) a ha b hb haj hbj
      · intro hnj b hb
        by_contra hbj
        obtain rfl := hsep B0 hB0 (N + 1) hn b (hBsub hb) hnj (by omega)
        exact hnB hb
    · try dsimp only
      rw [erase_insert hBQ, hBdef, insert_erase hn, insert_erase hB0]

/-- 辅助引理（引理 4.5）：按 `N + 1` 是否单独成块分开计数。 -/
theorem partCount_succ_succ_eq (j N m : ℕ) :
    partCount j (N + 1) (m + 1) =
      partCount j N m + ∑ R ∈ setParts j N (m + 1), #(R.filter (Allowed j (N + 1))) := by
  rw [partCount, ← card_filter_add_card_filter_not (s := setParts j (N + 1) (m + 1)) (fun Q => {N + 1} ∈ Q),
    card_setParts_single, card_setParts_join]

/-- 辅助引理（引理 4.5）：`N + 1 ≤ j` 时 `N + 1` 不能加进任何一块（块里都有 `≤ N` 的元素）。 -/
theorem sum_allowed_of_le {j N m : ℕ} (h : N + 1 ≤ j) :
    ∑ R ∈ setParts j N (m + 1), #(R.filter (Allowed j (N + 1))) = 0 := by
  refine Finset.sum_eq_zero fun R hR => ?_
  rw [card_eq_zero, filter_eq_empty_iff]
  intro B hB hall
  rw [mem_setParts] at hR
  obtain ⟨b, hb⟩ := hR.1.1 B hB
  have hbN := hR.1.subset hB hb
  rw [mem_Icc] at hbN
  have := hall h b hb
  omega

/-- 辅助引理（引理 4.5）：`N ≥ j` 时 `N + 1` 可以加进任何一块。 -/
theorem sum_allowed_of_ge {j N m : ℕ} (h : j ≤ N) :
    ∑ R ∈ setParts j N (m + 1), #(R.filter (Allowed j (N + 1))) = (m + 1) * partCount j N (m + 1) := by
  have key : ∀ R ∈ setParts j N (m + 1), #(R.filter (Allowed j (N + 1))) = m + 1 := fun R hR => by
    rw [filter_true_of_mem fun B _ hnj => absurd hnj (by omega), (mem_setParts.mp hR).2.1]
  rw [sum_const_nat key, partCount, mul_comm]

/-- 辅助引理（引理 4.5）：`N + 1 ≤ j` 时 `N + 1` 只能单独成块。 -/
theorem partCount_succ_succ_of_le {j N m : ℕ} (h : N + 1 ≤ j) :
    partCount j (N + 1) (m + 1) = partCount j N m := by
  rw [partCount_succ_succ_eq, sum_allowed_of_le h, add_zero]

/-- 辅助引理（引理 4.5）：`N ≥ j` 时 `partCount j (N+1) (m+1) = partCount j N m + (m+1)·partCount j N (m+1)`。 -/
theorem partCount_succ_succ {j N m : ℕ} (h : j ≤ N) :
    partCount j (N + 1) (m + 1) = partCount j N m + (m + 1) * partCount j N (m + 1) := by
  rw [partCount_succ_succ_eq, sum_allowed_of_ge h]

/-- 辅助引理（引理 4.5）：`N ≤ j` 时只有全单点划分（恰 `N` 块）。 -/
theorem partCount_of_le {j : ℕ} : ∀ N, N ≤ j → ∀ m, partCount j N m = if m = N then 1 else 0
  | 0, _, m => partCount_zero_left j m
  | N + 1, _, 0 => by rw [partCount_succ_zero, ite_eq_right (by omega)]
  | N + 1, hN, m + 1 => by
    rw [partCount_succ_succ_of_le hN, partCount_of_le N (by omega) m]
    simp

/-- 辅助引理（引理 4.5）：块数多于元素数时为 0。 -/
theorem partCount_of_lt {j : ℕ} : ∀ N m, N < m → partCount j N m = 0
  | 0, m, h => by rw [partCount_zero_left, ite_eq_right (by omega)]
  | N + 1, 0, h => absurd h (by omega)
  | N + 1, m + 1, h => by
    rcases le_or_gt j N with hjN | hNj
    · rw [partCount_succ_succ hjN, partCount_of_lt N m (by omega), partCount_of_lt N (m + 1) (by omega),
        mul_zero, add_zero]
    · rw [partCount_succ_succ_of_le (by omega), partCount_of_lt N m (by omega)]

/-- 辅助引理（引理 4.5）：`N ≥ j` 时块数少于 `j` 为 0（`1, …, j` 要在不同块）。 -/
theorem partCount_of_lt_j {j : ℕ} : ∀ t m, m < j → partCount j (j + t) m = 0
  | 0, m, h => by rw [add_zero, partCount_of_le j le_rfl, ite_eq_right (by omega)]
  | t + 1, 0, _ => by rw [← add_assoc, partCount_succ_zero]
  | t + 1, m + 1, h => by
    rw [← add_assoc, partCount_succ_succ (by omega), partCount_of_lt_j t m (by omega),
      partCount_of_lt_j t (m + 1) h, mul_zero, add_zero]

/-- 辅助引理（引理 4.5）：`N ≥ j` 时分成 `N` 块只有全单点划分。 -/
theorem partCount_self {j : ℕ} : ∀ t, partCount j (j + t) (j + t) = 1
  | 0 => by rw [add_zero, partCount_of_le j le_rfl, ite_eq_left rfl]
  | t + 1 => by
    rw [← add_assoc, partCount_succ_succ (by omega), partCount_self t,
      partCount_of_lt (j + t) (j + t + 1) (by omega), mul_zero, add_zero]

/-- 辅助引理（引理 4.5）：`{1, …, j+s}` 分成 `j` 块、`1, …, j` 各在一块的划分有 `j^s` 个。 -/
theorem partCount_j (j : ℕ) : ∀ s, partCount j (j + s) j = j ^ s
  | 0 => by rw [add_zero, pow_zero, partCount_of_le j le_rfl, ite_eq_left rfl]
  | s + 1 => by
    have ih := partCount_j j s
    rcases j with _ | j
    · rw [zero_add, partCount_succ_zero, zero_pow (Nat.succ_ne_zero s)]
    · rw [← add_assoc, partCount_succ_succ (by omega), partCount_of_lt_j s j (by omega), ih, zero_add,
        pow_succ, mul_comm]

/-- 辅助引理（引理 4.5）：`hc s [v] = v^s`。 -/
theorem hc_single (v : ℕ) : ∀ s, hc s [v] = v ^ s
  | 0 => by simp
  | s + 1 => by
    rw [hc_succ_cons, hc_single v s, pow_succ, hc_succ_nil, zero_add, mul_comm]

/-- 辅助引理（引理 4.5）：`vars j j = [j]`。 -/
theorem vars_self (j : ℕ) : vars j j = [j] := by
  rcases j with _ | j
  · exact vars_zero_zero
  · rw [vars_succ le_rfl, vars_self_succ]

/-- **引理 4.5**（最后一句）：`j ≤ m` 时 `H(m,s,j) = h_s(j, …, m)` 等于 `{1, …, m+s}` 分成 `m` 块、`1, …, j` 两两
不同块的集合划分个数；`1 ≤ j ≤ m` 时这就是 r-Stirling 数 `{m+s \brace m}_j`。 -/
theorem hc_vars_eq_partCount {j m : ℕ} (hjm : j ≤ m) (s : ℕ) : hc s (vars j m) = partCount j (m + s) m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjm
  clear hjm
  induction t generalizing s with
  | zero => rw [add_zero, vars_self, hc_single, partCount_j]
  | succ t iht =>
    induction s with
    | zero =>
      rw [add_zero, partCount_self (t + 1), hc_zero]
    | succ s ihs =>
      have e1 : j + (t + 1) = j + t + 1 := by omega
      rw [e1] at ihs ⊢
      rw [vars_succ (j := j) (m := j + t) (by omega), hc_succ_cons,
        ← vars_succ (j := j) (m := j + t) (by omega), ihs, iht (s + 1),
        show j + t + 1 + (s + 1) = j + t + 1 + s + 1 by omega, partCount_succ_succ (by omega),
        show j + t + (s + 1) = j + t + 1 + s by omega]

/-- **引理 4.5**（`j = 0, 1` 的情形）：Mathlib 按递推定义的第二类 Stirling 数 `S(N, m)` 等于 `{1, …, N}` 分成 `m`
块的集合划分个数。 -/
theorem stirlingSecond_eq_partCount : ∀ N m, Nat.stirlingSecond N m = partCount 0 N m
  | 0, m => by
    rw [partCount_zero_left]
    rcases m with _ | m
    · simp
    · simp [Nat.stirlingSecond_zero_succ]
  | N + 1, 0 => by rw [partCount_succ_zero, Nat.stirlingSecond_succ_zero]
  | N + 1, m + 1 => by
    rw [Nat.stirlingSecond_succ_succ, partCount_succ_succ (Nat.zero_le N), stirlingSecond_eq_partCount N m,
      stirlingSecond_eq_partCount N (m + 1), add_comm]

/-- 辅助引理（引理 4.5）：只「分开」一个元素没有约束。 -/
theorem partCount_one (N m : ℕ) : partCount 1 N m = partCount 0 N m := by
  unfold partCount setParts
  congr 1
  ext Q
  simp only [mem_filter]
  refine and_congr_right fun _ => and_congr_right fun hP => and_congr_right fun _ => ?_
  constructor
  · intro h B hB a ha b hb ha0 hb0
    exact h B hB a ha b hb (by omega) (by omega)
  · intro _ B hB a ha b hb ha1 hb1
    have h1 := hP.subset hB ha
    have h2 := hP.subset hB hb
    rw [mem_Icc] at h1 h2
    omega

/-- **引理 4.5**（最后一句，合并陈述）：`1 ≤ j ≤ m` 时 `H(m,s,j)` 是 r-Stirling 数 `{m+s \brace m}_j`（`{1, …, m+s}`
分成 `m` 块、`1, …, j` 两两不同块的划分个数），`H(m,s,0)` 与 `H(m,s,1)` 都是分成 `m` 块的划分个数 `{m+s \brace m}`
（与 Mathlib 的 `Nat.stirlingSecond` 一致：`stirlingSecond_eq_partCount`）。 -/
theorem lemma_coef_partitions {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) (s : ℕ) :
    hc s (vars j m) = partCount j (m + s) m ∧ hc s (vars 0 m) = partCount 0 (m + s) m ∧
      hc s (vars 1 m) = partCount 0 (m + s) m :=
  ⟨hc_vars_eq_partCount hjm s, hc_vars_eq_partCount (Nat.zero_le m) s,
    (hc_vars_eq_partCount (by omega : 1 ≤ m) s).trans (partCount_one _ _)⟩

end A207123
