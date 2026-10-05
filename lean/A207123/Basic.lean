import Mathlib

/-!
# A207123 任务 C：`U k m` 的定义与引理 1

按任务说明第 1 节 (b) 的高度表述定义 `U k m`：长度为 `k`、各项取值在 `{0,…,m}` 中、
每个相邻三元组 `(a,b,c)` 都满足「`b = c` 或 `a ≥ max(b,c)`」的序列个数。

本文件证明：
* `mem_L`：`L k m` 恰是满足上述条件的列表（定义是透明的）；
* `legal_iff_getElem`：`Legal` 与「对每个下标 i，第 i,i+1,i+2 项构成好三元组」等价；
* `lemma1`：引理 1（三项递推）`U (k+3) (m+1) = U (k+3) m + U (k+2) (m+1) + (m+1) * U k (m+1)`，
  以及 `k = 1, 2` 与 `m = 0` 的边界情形。
-/

namespace A207123

/-- 好三元组：`b = c`，或 `a ≥ max(b, c)`。 -/
def Good (a b c : ℕ) : Prop := b = c ∨ (b ≤ a ∧ c ≤ a)

instance (a b c : ℕ) : Decidable (Good a b c) := by unfold Good; infer_instance

/-- 高度序列合法：每个相邻三元组都是好三元组。 -/
def Legal : List ℕ → Prop
  | a :: b :: c :: t => Good a b c ∧ Legal (b :: c :: t)
  | _ => True

@[simp] theorem legal_nil : Legal [] := trivial
@[simp] theorem legal_one (a : ℕ) : Legal [a] := trivial
@[simp] theorem legal_two (a b : ℕ) : Legal [a, b] := trivial
@[simp] theorem legal_cons3 (a b c : ℕ) (t : List ℕ) :
    Legal (a :: b :: c :: t) ↔ Good a b c ∧ Legal (b :: c :: t) := Iff.rfl

instance decLegal : DecidablePred Legal
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | [_, _] => isTrue trivial
  | a :: b :: c :: t =>
      haveI := decLegal (b :: c :: t)
      decidable_of_iff _ (legal_cons3 a b c t).symm

/-- 所有长度为 `k`、各项取值在 `{0,…,m}` 中的列表。 -/
def seqs (m : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k + 1 => (Finset.range (m + 1)).biUnion fun a => (seqs m k).image (List.cons a)

theorem mem_seqs {m k : ℕ} {l : List ℕ} :
    l ∈ seqs m k ↔ l.length = k ∧ ∀ x ∈ l, x ≤ m := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp [seqs]
    | cons a t => simp [seqs]
  | succ k ih =>
    cases l with
    | nil => simp [seqs]
    | cons a t =>
      simp only [seqs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.cons.injEq,
        List.length_cons, List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨b, hb, s, hs, rfl, rfl⟩
        obtain ⟨h1, h2⟩ := ih.mp hs
        exact ⟨h1, by omega, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨a, by omega, t, ih.mpr ⟨h1, h3⟩, rfl, rfl⟩

/-- `L k m`：长度 `k`、取值 ≤ `m` 的合法高度序列全体。 -/
def L (k m : ℕ) : Finset (List ℕ) := (seqs m k).filter Legal

/-- `U k m = |L k m|`（任务说明中的 `U_k(m)`）。 -/
def U (k m : ℕ) : ℕ := (L k m).card

theorem mem_L {k m : ℕ} {l : List ℕ} :
    l ∈ L k m ↔ l.length = k ∧ (∀ x ∈ l, x ≤ m) ∧ Legal l := by
  simp [L, mem_seqs, and_assoc]

/-! ### `Legal` 的透明刻画 -/

theorem legal_iff_getElem (l : List ℕ) :
    Legal l ↔ ∀ (i : ℕ) (h : i + 2 < l.length), Good l[i] l[i + 1] l[i + 2] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    match t, ih with
    | [], _ => simp
    | [b], _ => simp
    | b :: c :: s, ih =>
      rw [legal_cons3, ih]
      constructor
      · rintro ⟨hg, hrest⟩ i hi
        cases i with
        | zero => simpa using hg
        | succ i =>
          have := hrest i (by simp at hi ⊢; omega)
          simpa using this
      · intro h
        refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
        have := h (i + 1) (by simp at hi ⊢; omega)
        simpa using this

/-! ### 引理 1 需要的三条性质 -/

theorem legal_tail {a : ℕ} {t : List ℕ} (h : Legal (a :: t)) : Legal t := by
  match t, h with
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => exact h.2

/-- 首项是上界时可以去掉：`Legal (M :: t) ↔ Legal t`。 -/
theorem legal_cons_of_le {M : ℕ} {t : List ℕ} (ht : ∀ x ∈ t, x ≤ M) :
    Legal (M :: t) ↔ Legal t := by
  match t, ht with
  | [], _ => simp
  | [_], _ => simp
  | b :: c :: s, ht =>
    have hb : b ≤ M := ht b (by simp)
    have hc : c ≤ M := ht c (by simp)
    rw [legal_cons3]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr ⟨hb, hc⟩, h⟩⟩

/-- 合法序列 `x :: y :: t` 中，`t` 的每一项都不超过 `max x y`。 -/
theorem legal_bound {x y : ℕ} {t : List ℕ} (h : Legal (x :: y :: t)) :
    ∀ z ∈ t, z ≤ max x y := by
  induction t generalizing x y with
  | nil => simp
  | cons z t ih =>
    rw [legal_cons3] at h
    obtain ⟨hg, hl⟩ := h
    have hz : z ≤ max x y := by
      rcases hg with h1 | ⟨_, h2⟩ <;> omega
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hz
    · have := ih hl w hw
      omega

/-! ### 引理 1 -/

/-- 引理 1 的分类（按最大值 `m+1` 第一次出现的位置）：不出现（`L (k+3) m`）；出现在首位
（`(m+1) :: w`，`w ∈ L (k+2) (m+1)`）；首次出现在第 2 位（`a :: (m+1) :: (m+1) :: t`，`a ≤ m`）。 -/
theorem L_split (k m : ℕ) :
    L (k + 3) (m + 1) = L (k + 3) m ∪ (L (k + 2) (m + 1)).image (List.cons (m + 1)) ∪
      ((Finset.range (m + 1)) ×ˢ (L k (m + 1))).image
        (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2) := by
    classical
    ext l
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product,
      Finset.mem_range, mem_L, Prod.exists]
    constructor
    · rintro ⟨hlen, hle, hleg⟩
      match l, hlen, hle, hleg with
      | x :: y :: z :: t, hlen, hle, hleg =>
        have hx : x ≤ m + 1 := hle x (by simp)
        have hy : y ≤ m + 1 := hle y (by simp)
        have ht : ∀ w ∈ t, w ≤ m + 1 := fun w hw => hle w (by simp [hw])
        have htlen : t.length = k := by simpa using hlen
        by_cases hmem : (m + 1) ∈ x :: y :: z :: t
        · by_cases hxM : x = m + 1
          · -- 首项就是最大值：属于 B
            left; right
            refine ⟨y :: z :: t, ⟨by simpa using hlen, fun w hw => hle w (by simp_all), ?_⟩, ?_⟩
            · exact legal_tail hleg
            · rw [hxM]
          · -- 首项小于最大值、但最大值出现：属于 C
            right
            have hxlt : x < m + 1 := lt_of_le_of_ne hx hxM
            have hyM : y = m + 1 := by
              by_contra hyM
              have hylt : y < m + 1 := lt_of_le_of_ne hy hyM
              have hb := legal_bound hleg
              simp only [List.mem_cons] at hmem
              rcases hmem with h | h | h
              · omega
              · omega
              · have := hb (m + 1) (by simpa using h)
                omega
            have hzM : z = m + 1 := by
              rcases hleg.1 with h | ⟨h1, _⟩ <;> omega
            refine ⟨x, t, ⟨hxlt, htlen, ht, ?_⟩, ?_⟩
            · have h2 : Legal (y :: z :: t) := hleg.2
              rw [hyM, hzM] at h2
              have h3 : Legal ((m + 1) :: t) :=
                (legal_cons_of_le (by
                  intro w hw
                  rcases List.mem_cons.mp hw with rfl | hw
                  · exact le_refl _
                  · exact ht w hw)).mp h2
              exact (legal_cons_of_le ht).mp h3
            · simp [hyM, hzM]
        · -- 最大值不出现：属于 A
          left; left
          refine ⟨hlen, fun w hw => ?_, hleg⟩
          have h1 := hle w hw
          have h2 : w ≠ m + 1 := fun h => hmem (h ▸ hw)
          omega
    · rintro ((⟨hlen, hle, hleg⟩ | ⟨w, ⟨hwlen, hwle, hwleg⟩, rfl⟩) |
          ⟨x, t, ⟨hx, htlen, htle, htleg⟩, rfl⟩)
      · exact ⟨hlen, fun x hx => (hle x hx).trans (Nat.le_succ m), hleg⟩
      · refine ⟨by simp [hwlen], ?_, (legal_cons_of_le hwle).mpr hwleg⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_refl _
        · exact hwle x hx
      · refine ⟨by simp [htlen], ?_, ?_⟩
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | rfl | rfl | hw
          · omega
          · exact le_refl _
          · exact le_refl _
          · exact htle w hw
        · rw [legal_cons3]
          refine ⟨Or.inl rfl, ?_⟩
          have h1 : Legal ((m + 1) :: t) := (legal_cons_of_le htle).mpr htleg
          exact (legal_cons_of_le (by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact le_refl _
            · exact htle w hw)).mpr h1

/-- `L_split` 的三个部分两两不交。 -/
theorem L_split_disjoint (k m : ℕ) :
    Disjoint (L (k + 3) m) ((L (k + 2) (m + 1)).image (List.cons (m + 1))) ∧
    Disjoint (L (k + 3) m) (((Finset.range (m + 1)) ×ˢ (L k (m + 1))).image
        (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2)) ∧
    Disjoint ((L (k + 2) (m + 1)).image (List.cons (m + 1)))
      (((Finset.range (m + 1)) ×ˢ (L k (m + 1))).image
        (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro l hlA hlB
    rw [mem_L] at hlA
    rw [Finset.mem_image] at hlB
    obtain ⟨w, -, rfl⟩ := hlB
    have := hlA.2.1 (m + 1) (by simp)
    omega
  · rw [Finset.disjoint_left]
    intro l hlA hlC
    rw [mem_L] at hlA
    rw [Finset.mem_image] at hlC
    obtain ⟨p, -, rfl⟩ := hlC
    have := hlA.2.1 (m + 1) (by simp)
    omega
  · rw [Finset.disjoint_left]
    intro l hlB hlC
    rw [Finset.mem_image] at hlB
    rw [Finset.mem_image] at hlC
    obtain ⟨w, -, rfl⟩ := hlB
    obtain ⟨p, hp, hpe⟩ := hlC
    rw [Finset.mem_product, Finset.mem_range] at hp
    have := (List.cons.inj hpe).1
    omega

/-- 第三部分 `a :: (m+1) :: (m+1) :: t` 的构造映射是单射。 -/
theorem L_split_inj (m : ℕ) :
    Function.Injective (fun p : ℕ × List ℕ => p.1 :: (m + 1) :: (m + 1) :: p.2) := by
  rintro ⟨x, t⟩ ⟨x', t'⟩ h
  simp only [List.cons.injEq] at h
  obtain ⟨rfl, -, -, rfl⟩ := h
  rfl

/-- **引理 1**（k ≥ 3 的情形）：按最大值 `m+1` 第一次出现的位置分类。 -/
theorem lemma1 (k m : ℕ) :
    U (k + 3) (m + 1) = U (k + 3) m + U (k + 2) (m + 1) + (m + 1) * U k (m + 1) := by
  classical
  obtain ⟨hAB, hAC, hBC⟩ := L_split_disjoint k m
  unfold U
  rw [L_split, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
    Finset.card_union_of_disjoint hAB, Finset.card_image_of_injective _ (List.cons_injective),
    Finset.card_image_of_injective _ (L_split_inj m), Finset.card_product, Finset.card_range]

/-! ### 边界情形 -/

theorem card_seqs (m k : ℕ) : (seqs m k).card = (m + 1) ^ k := by
  induction k with
  | zero => simp [seqs]
  | succ k ih =>
    rw [seqs, Finset.card_biUnion]
    · simp only [Finset.card_image_of_injective _ (List.cons_injective), ih, Finset.sum_const,
        Finset.card_range, smul_eq_mul, pow_succ]
      ring
    · intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      intro l hla hlb
      rw [Finset.mem_image] at hla hlb
      obtain ⟨s, -, rfl⟩ := hla
      obtain ⟨s', -, hs'⟩ := hlb
      exact hab (List.cons.inj hs').1.symm

theorem legal_of_length_le_two {l : List ℕ} (h : l.length ≤ 2) : Legal l := by
  match l, h with
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], _ => trivial

theorem U_of_le_two {k : ℕ} (hk : k ≤ 2) (m : ℕ) : U k m = (m + 1) ^ k := by
  unfold U L
  rw [Finset.filter_true_of_mem, card_seqs]
  intro l hl
  exact legal_of_length_le_two ((mem_seqs.mp hl).1 ▸ hk)

theorem U_zero_left (m : ℕ) : U 0 m = 1 := by
  rw [U_of_le_two (by norm_num)]
  simp

theorem legal_replicate (k : ℕ) : Legal (List.replicate k 0) := by
  rw [legal_iff_getElem]
  intro i hi
  simp [Good]

theorem U_zero_right (k : ℕ) : U k 0 = 1 := by
  unfold U
  rw [Finset.card_eq_one]
  refine ⟨List.replicate k 0, ?_⟩
  ext l
  rw [mem_L, Finset.mem_singleton]
  constructor
  · rintro ⟨hlen, hle, -⟩
    rw [List.eq_replicate_iff]
    exact ⟨hlen, fun x hx => Nat.le_zero.mp (hle x hx)⟩
  · rintro rfl
    exact ⟨by simp, by simp, legal_replicate k⟩

/-- 引理 1 的 `k = 1` 情形（约定 `U_{-2} = 0`）。 -/
theorem lemma1_one (m : ℕ) : U 1 (m + 1) = U 1 m + U 0 (m + 1) := by
  rw [U_of_le_two (by norm_num), U_of_le_two (by norm_num), U_zero_left]
  ring

/-- 引理 1 的 `k = 2` 情形（约定 `U_{-1} = 1`）。 -/
theorem lemma1_two (m : ℕ) : U 2 (m + 1) = U 2 m + U 1 (m + 1) + (m + 1) * 1 := by
  rw [U_of_le_two (by norm_num), U_of_le_two (by norm_num), U_of_le_two (by norm_num)]
  ring

end A207123
