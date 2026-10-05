import A207123.Basic

/-!
# 原题的归约：`a_k(n) = U_k(⌈n/2⌉) · U_k(⌊n/2⌋)`

从任务说明第 1 节的原始定义出发：`a k n` 是满足行规则与列规则的 n×k 0/1 矩阵个数。
本文件证明 `a k n = U k ((n + 1) / 2) * U k (n / 2)`，其中 `U` 是 `Basic.lean` 中按高度序列
定义的计数（`(n+1)/2 = ⌈n/2⌉`，`n/2 = ⌊n/2⌋`）。

证明的结构（对应报告 T1.0）：
* 列规则 ⇔ 每列第 `i` 行为 0 时第 `i+2` 行也为 0，所以偶数行、奇数行各自逐列单调不增；
* 单调不增的 0/1 列由「1 的个数」（高度）唯一决定；
* 行规则 ⇔ 两组高度向量的每个相邻三元组都是好三元组（`rowPattern_iff_good`）。
-/

namespace A207123

open Finset

/-- 原题中的 n×k 0/1 矩阵：`M i j` 是第 `i` 行第 `j` 列（从 0 开始编号），`true` 表示 1。 -/
abbrev Mat (n k : ℕ) := Fin n → Fin k → Bool

/-- 行规则：每一行从左到右读，任意连续三个位置都不是 001，也不是 010。 -/
def RowRule {n k : ℕ} (M : Mat n k) : Prop :=
  ∀ (i : Fin n) (j : ℕ) (h : j + 2 < k),
    ¬ (M i ⟨j, by omega⟩ = false ∧ M i ⟨j + 1, by omega⟩ = false ∧ M i ⟨j + 2, h⟩ = true) ∧
    ¬ (M i ⟨j, by omega⟩ = false ∧ M i ⟨j + 1, by omega⟩ = true ∧ M i ⟨j + 2, h⟩ = false)

/-- 列规则：每一列从上到下读，任意连续三个位置都不是 001，也不是 011。 -/
def ColRule {n k : ℕ} (M : Mat n k) : Prop :=
  ∀ (j : Fin k) (i : ℕ) (h : i + 2 < n),
    ¬ (M ⟨i, by omega⟩ j = false ∧ M ⟨i + 1, by omega⟩ j = false ∧ M ⟨i + 2, h⟩ j = true) ∧
    ¬ (M ⟨i, by omega⟩ j = false ∧ M ⟨i + 1, by omega⟩ j = true ∧ M ⟨i + 2, h⟩ j = true)

open Classical in
/-- `a k n`：满足行规则与列规则的 n×k 0/1 矩阵个数（OEIS A207123 的二维表）。 -/
noncomputable def a (k n : ℕ) : ℕ := Fintype.card {M : Mat n k // RowRule M ∧ ColRule M}

/-! ### 高度向量（函数形式）与 `U` -/

/-- 函数形式的合法高度向量。 -/
def LegalF {k m : ℕ} (h : Fin k → Fin (m + 1)) : Prop :=
  ∀ (j : ℕ) (hj : j + 2 < k), Good (h ⟨j, by omega⟩) (h ⟨j + 1, by omega⟩) (h ⟨j + 2, hj⟩)

theorem legal_ofFn_iff {k m : ℕ} (h : Fin k → Fin (m + 1)) :
    Legal (List.ofFn fun j => (h j : ℕ)) ↔ LegalF h := by
  rw [legal_iff_getElem]
  simp only [List.length_ofFn, List.getElem_ofFn, LegalF]

open Classical in
theorem card_legalF (k m : ℕ) : Fintype.card {h : Fin k → Fin (m + 1) // LegalF h} = U k m := by
  unfold U
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun h => ⟨List.ofFn fun j => (h.1 j : ℕ), ?_⟩
      invFun := fun l => ⟨fun j => ⟨l.1[j.val]'?_, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mem_L]
    refine ⟨by simp, ?_, (legal_ofFn_iff h.1).mpr h.2⟩
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact Nat.lt_succ_iff.mp (h.1 j).2
  · have := (mem_L.mp l.2).1
    omega
  · have := (mem_L.mp l.2).2.1 (l.1[j.val]'(by have := (mem_L.mp l.2).1; omega))
      (List.getElem_mem _)
    omega
  · have hl := mem_L.mp l.2
    rw [← legal_ofFn_iff]
    have : (List.ofFn fun j : Fin k => l.1[j.val]'(by omega)) = l.1 := by
      apply List.ext_getElem <;> simp [hl.1]
    simpa [this] using hl.2.2
  · intro h
    apply Subtype.ext
    funext j
    apply Fin.ext
    simp
  · intro l
    apply Subtype.ext
    have hl := mem_L.mp l.2
    apply List.ext_getElem <;> simp [hl.1]

/-! ### 行规则与好三元组 -/

/-- 在高度表述下，第 `r` 行在三列上的取值是 `(r<a, r<b, r<c)`。对所有行 `r < M`，
这三列上既不出现 001 也不出现 010，当且仅当 `(a,b,c)` 是好三元组（`a,b,c ≤ M`）。 -/
theorem rowPattern_iff_good {a b c M : ℕ} (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M) :
    (∀ r < M,
      ¬ (decide (r < a) = false ∧ decide (r < b) = false ∧ decide (r < c) = true) ∧
      ¬ (decide (r < a) = false ∧ decide (r < b) = true ∧ decide (r < c) = false)) ↔
    Good a b c := by
  constructor
  · intro h
    by_contra hg
    unfold Good at hg
    push Not at hg
    obtain ⟨hbc, hg⟩ := hg
    rcases Nat.lt_or_gt_of_ne hbc with hlt | hlt
    · -- b < c，于是 c > a；取 r = max a b 得到 001
      have hca : a < c := by
        by_contra hca
        exact absurd (hg (by omega)) (by omega)
      have := (h (max a b) (by omega)).1
      apply this
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_lt]
      omega
    · -- c < b，于是 b > a；取 r = max a c 得到 010
      have hba : a < b := by
        by_contra hba
        exact absurd (hg (by omega)) (by omega)
      have := (h (max a c) (by omega)).2
      apply this
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_lt]
      omega
  · intro hg r _
    simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_lt]
    unfold Good at hg
    omega

/-! ### 单调 0/1 序列由 1 的个数决定 -/

/-- 若 `S ⊆ {0,…,m−1}` 向下封闭，则 `r ∈ S ↔ r < |S|`。 -/
theorem mem_iff_lt_card_of_downClosed {m : ℕ} (S : Finset (Fin m))
    (hS : ∀ r s : Fin m, s.val ≤ r.val → r ∈ S → s ∈ S) (r : Fin m) :
    r ∈ S ↔ r.val < S.card := by
  have hr := r.isLt
  constructor
  · intro hrS
    have hsub : (univ.filter fun s : Fin m => (s : ℕ) < r.val + 1) ⊆ S := by
      intro s hs
      rw [mem_filter] at hs
      exact hS r s (by omega) hrS
    have hcard : (univ.filter fun s : Fin m => (s : ℕ) < r.val + 1).card = r.val + 1 := by
      rw [Fin.card_filter_val_lt]
      omega
    have := card_le_card hsub
    omega
  · intro hlt
    by_contra hrS
    have hsub : S ⊆ univ.filter fun s : Fin m => (s : ℕ) < r.val := by
      intro s hs
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      by_contra hsr
      exact hrS (hS s r (by omega) hs)
    have hcard : (univ.filter fun s : Fin m => (s : ℕ) < r.val).card = r.val := by
      rw [Fin.card_filter_val_lt]
      omega
    have := card_le_card hsub
    omega

/-! ### 两组高度向量 ↔ 合法矩阵 -/

/-- 由偶数行高度 `he` 与奇数行高度 `ho` 拼出的矩阵：第 `i` 行属于第 `i % 2` 组，是该组的第 `i / 2` 行。 -/
def build {n k : ℕ} (he : Fin k → Fin ((n + 1) / 2 + 1)) (ho : Fin k → Fin (n / 2 + 1)) : Mat n k :=
  fun i j => if i.val % 2 = 0 then decide (i.val / 2 < (he j : ℕ)) else decide (i.val / 2 < (ho j : ℕ))

/-- 偶数号行（第 0,2,4,… 行）在第 `j` 列中 1 的个数。 -/
def heightE {n k : ℕ} (M : Mat n k) (j : Fin k) : Fin ((n + 1) / 2 + 1) :=
  ⟨(univ.filter fun r : Fin ((n + 1) / 2) => M ⟨2 * r.val, by have := r.isLt; omega⟩ j = true).card,
    Nat.lt_succ_of_le ((card_le_univ _).trans (by simp))⟩

/-- 奇数号行（第 1,3,5,… 行）在第 `j` 列中 1 的个数。 -/
def heightO {n k : ℕ} (M : Mat n k) (j : Fin k) : Fin (n / 2 + 1) :=
  ⟨(univ.filter fun r : Fin (n / 2) => M ⟨2 * r.val + 1, by have := r.isLt; omega⟩ j = true).card,
    Nat.lt_succ_of_le ((card_le_univ _).trans (by simp))⟩

theorem colRule_build {n k : ℕ} (he : Fin k → Fin ((n + 1) / 2 + 1)) (ho : Fin k → Fin (n / 2 + 1)) :
    ColRule (build he ho) := by
  intro j i h
  simp only [build]
  have h1 : (i + 2) % 2 = i % 2 := by omega
  have h2 : (i + 2) / 2 = i / 2 + 1 := by omega
  rw [h1, h2]
  split_ifs <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_lt] <;> omega

/-- 列规则推出：同奇偶的两行中，下面一行为 1 则上面一行也为 1。 -/
theorem colRule_mono {n k : ℕ} {M : Mat n k} (hM : ColRule M) (j : Fin k) :
    ∀ (d i : ℕ) (h : i + 2 * d < n), M ⟨i + 2 * d, h⟩ j = true → M ⟨i, by omega⟩ j = true := by
  intro d
  induction d with
  | zero => intro i h hM'; simpa using hM'
  | succ d ih =>
    intro i h hM'
    apply ih i (by omega)
    have hc := hM j (i + 2 * d) (by omega)
    have e : (⟨i + 2 * d + 2, by omega⟩ : Fin n) = ⟨i + 2 * (d + 1), h⟩ := by
      apply Fin.ext; simp; ring
    rw [e] at hc
    cases hmid : M ⟨i + 2 * d + 1, by omega⟩ j <;> cases htop : M ⟨i + 2 * d, by omega⟩ j <;>
      simp_all

theorem height_build {n k : ℕ} (he : Fin k → Fin ((n + 1) / 2 + 1)) (ho : Fin k → Fin (n / 2 + 1)) :
    heightE (build he ho) = he ∧ heightO (build he ho) = ho := by
  constructor
  · funext j
    apply Fin.ext
    simp only [heightE, build]
    have : ∀ r : Fin ((n + 1) / 2), (2 * r.val) % 2 = 0 ∧ 2 * r.val / 2 = r.val := fun r => by omega
    simp only [this, ite_true, decide_eq_true_eq]
    rw [Fin.card_filter_val_lt]
    have := (he j).isLt
    omega
  · funext j
    apply Fin.ext
    simp only [heightO, build]
    have : ∀ r : Fin (n / 2), ¬ ((2 * r.val + 1) % 2 = 0) ∧ (2 * r.val + 1) / 2 = r.val :=
      fun r => by omega
    simp only [this, ite_false, decide_eq_true_eq]
    rw [Fin.card_filter_val_lt]
    have := (ho j).isLt
    omega

theorem build_height {n k : ℕ} {M : Mat n k} (hM : ColRule M) :
    build (heightE M) (heightO M) = M := by
  funext i j
  have hi := i.isLt
  simp only [build]
  split_ifs with hpar
  · -- 偶数行 i = 2r
    set r : Fin ((n + 1) / 2) := ⟨i.val / 2, by omega⟩ with hr
    have hiE : i = ⟨2 * r.val, by omega⟩ := by apply Fin.ext; simp [hr]; omega
    have key := mem_iff_lt_card_of_downClosed
      (univ.filter fun s : Fin ((n + 1) / 2) => M ⟨2 * s.val, by have := s.isLt; omega⟩ j = true)
      (by
        intro a b hba ha
        rw [mem_filter] at ha ⊢
        refine ⟨mem_univ _, ?_⟩
        have hab := colRule_mono hM j (a.val - b.val) (2 * b.val) (by have := a.isLt; omega)
        have e : (⟨2 * b.val + 2 * (a.val - b.val), by have := a.isLt; omega⟩ : Fin n) =
            ⟨2 * a.val, by have := a.isLt; omega⟩ := by apply Fin.ext; simp; omega
        rw [e] at hab
        exact hab ha.2) r
    simp only [mem_filter, mem_univ, true_and] at key
    rw [hiE]
    by_cases hv : M ⟨2 * r.val, by omega⟩ j = true
    · have := key.mp hv
      simp only [heightE, hr] at this ⊢
      rw [hv]; simp; omega
    · have hlt : ¬ r.val < _ := fun h => hv (key.mpr h)
      simp only [heightE, hr] at hlt ⊢
      simp only [Bool.not_eq_true] at hv
      rw [hv]; simp; omega
  · -- 奇数行 i = 2r + 1
    set r : Fin (n / 2) := ⟨i.val / 2, by omega⟩ with hr
    have hiO : i = ⟨2 * r.val + 1, by omega⟩ := by apply Fin.ext; simp [hr]; omega
    have key := mem_iff_lt_card_of_downClosed
      (univ.filter fun s : Fin (n / 2) => M ⟨2 * s.val + 1, by have := s.isLt; omega⟩ j = true)
      (by
        intro a b hba ha
        rw [mem_filter] at ha ⊢
        refine ⟨mem_univ _, ?_⟩
        have hab := colRule_mono hM j (a.val - b.val) (2 * b.val + 1) (by have := a.isLt; omega)
        have e : (⟨2 * b.val + 1 + 2 * (a.val - b.val), by have := a.isLt; omega⟩ : Fin n) =
            ⟨2 * a.val + 1, by have := a.isLt; omega⟩ := by apply Fin.ext; simp; omega
        rw [e] at hab
        exact hab ha.2) r
    simp only [mem_filter, mem_univ, true_and] at key
    rw [hiO]
    by_cases hv : M ⟨2 * r.val + 1, by omega⟩ j = true
    · have := key.mp hv
      simp only [heightO, hr] at this ⊢
      rw [hv]; simp; omega
    · have hlt : ¬ r.val < _ := fun h => hv (key.mpr h)
      simp only [heightO, hr] at hlt ⊢
      simp only [Bool.not_eq_true] at hv
      rw [hv]; simp; omega

theorem rowRule_build_iff {n k : ℕ} (he : Fin k → Fin ((n + 1) / 2 + 1)) (ho : Fin k → Fin (n / 2 + 1)) :
    RowRule (build he ho) ↔ LegalF he ∧ LegalF ho := by
  constructor
  · intro hR
    constructor
    · intro j hj
      refine (rowPattern_iff_good (M := (n + 1) / 2) (Nat.lt_succ_iff.mp (he _).isLt)
        (Nat.lt_succ_iff.mp (he _).isLt) (Nat.lt_succ_iff.mp (he _).isLt)).mp ?_
      intro r hr
      have := hR ⟨2 * r, by omega⟩ j hj
      have h1 : (2 * r) % 2 = 0 := by omega
      have h2 : 2 * r / 2 = r := by omega
      simpa only [build, h1, h2, ite_true] using this
    · intro j hj
      refine (rowPattern_iff_good (M := n / 2) (Nat.lt_succ_iff.mp (ho _).isLt)
        (Nat.lt_succ_iff.mp (ho _).isLt) (Nat.lt_succ_iff.mp (ho _).isLt)).mp ?_
      intro r hr
      have := hR ⟨2 * r + 1, by omega⟩ j hj
      have h1 : ¬ ((2 * r + 1) % 2 = 0) := by omega
      have h2 : (2 * r + 1) / 2 = r := by omega
      simpa only [build, h1, h2, ite_false] using this
  · rintro ⟨hE, hO⟩ i j hj
    have hi := i.isLt
    simp only [build]
    split_ifs with hpar
    · exact (rowPattern_iff_good (M := (n + 1) / 2) (Nat.lt_succ_iff.mp (he _).isLt)
        (Nat.lt_succ_iff.mp (he _).isLt) (Nat.lt_succ_iff.mp (he _).isLt)).mpr (hE j hj)
        (i.val / 2) (by omega)
    · exact (rowPattern_iff_good (M := n / 2) (Nat.lt_succ_iff.mp (ho _).isLt)
        (Nat.lt_succ_iff.mp (ho _).isLt) (Nat.lt_succ_iff.mp (ho _).isLt)).mpr (hO j hj)
        (i.val / 2) (by omega)

/-! ### 主定理 -/

open Classical in
/-- **原题的归约**：`a_k(n) = U_k(⌈n/2⌉) · U_k(⌊n/2⌋)`。 -/
theorem a_eq (k n : ℕ) : a k n = U k ((n + 1) / 2) * U k (n / 2) := by
  rw [← card_legalF, ← card_legalF, ← Fintype.card_prod, a]
  refine Fintype.card_congr
    { toFun := fun M => (⟨heightE M.1, ?_⟩, ⟨heightO M.1, ?_⟩)
      invFun := fun p => ⟨build p.1.1 p.2.1, (rowRule_build_iff _ _).mpr ⟨p.1.2, p.2.2⟩,
        colRule_build _ _⟩
      left_inv := fun M => Subtype.ext (build_height M.2.2)
      right_inv := fun p => ?_ }
  · have h := M.2.1
    rw [← build_height M.2.2] at h
    exact ((rowRule_build_iff _ _).mp h).1
  · have h := M.2.1
    rw [← build_height M.2.2] at h
    exact ((rowRule_build_iff _ _).mp h).2
  · obtain ⟨⟨he, hhe⟩, ⟨ho, hho⟩⟩ := p
    have hb := height_build (n := n) he ho
    simp only [hb.1, hb.2]

end A207123
