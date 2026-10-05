import A207123.Reduction

/-!
# 多重链表述（报告 T1.0(c)）

允许行：长 `k`、任意连续三位既不是 001 也不是 010 的 0/1 串。允许行偏序集 `Λ_k`（`Lam k`）取逐分量序
（`false < true`，即 `Fin k → Bool` 上的积序限制到允许行）。本文件证明

* `U_eq_multichains`：`U_k(m)` = `Λ_k` 中 m 元多重链 `x_1 ≤ x_2 ≤ ⋯ ≤ x_m` 的个数
  （Stanley 约定下即 zeta 多项式的取值 `Z(Λ_k, m+1)`；m = 0 时只有空链，计 1 个）；
* `card_Lam`：允许行的个数 `R_k = |Λ_k| = U_k(1)`。

证明复用 `Reduction.lean` 的工具：列单调的 0/1 矩阵由各列 1 的个数（高度）决定
（`mem_iff_lt_card_of_downClosed`），行规则 ⇔ 高度的每个相邻三元组都好（`rowPattern_iff_good`），
再用 `card_legalF` 换回 `U`。多重链 `x_1 ≤ ⋯ ≤ x_m` 倒序排列就是从上到下列单调不增的矩阵（`Fin.rev`）。
-/

namespace A207123

open Finset

/-- 允许行：长 `k` 的 0/1 串（`true` 表示 1），任意连续三位既不是 001 也不是 010。 -/
def AllowedRow {k : ℕ} (r : Fin k → Bool) : Prop :=
  ∀ (j : ℕ) (h : j + 2 < k),
    ¬ (r ⟨j, by omega⟩ = false ∧ r ⟨j + 1, by omega⟩ = false ∧ r ⟨j + 2, h⟩ = true) ∧
    ¬ (r ⟨j, by omega⟩ = false ∧ r ⟨j + 1, by omega⟩ = true ∧ r ⟨j + 2, h⟩ = false)

/-- 原题的行规则就是「每一行都是允许行」。 -/
theorem rowRule_iff_allowed {n k : ℕ} (M : Mat n k) : RowRule M ↔ ∀ i, AllowedRow (M i) :=
  Iff.rfl

/-- 允许行偏序集 `Λ_k`：允许行全体，序为逐分量序（`Fin k → Bool` 上的积序，`false < true`）。 -/
abbrev Lam (k : ℕ) := {r : Fin k → Bool // AllowedRow r}

/-! ### 列单调矩阵 ↔ 高度向量 -/

/-- 由高度 `h` 拼出的 m×k 矩阵：第 `i` 行第 `j` 列为 1 ⇔ `i < h j`（每列上面 `h j` 个 1）。 -/
def colMat {k m : ℕ} (h : Fin k → Fin (m + 1)) : Fin m → Fin k → Bool :=
  fun i j => decide (i.val < (h j : ℕ))

/-- 第 `j` 列中 1 的个数。 -/
def colHeight {k m : ℕ} (M : Fin m → Fin k → Bool) (j : Fin k) : Fin (m + 1) :=
  ⟨(univ.filter fun i : Fin m => M i j = true).card,
    Nat.lt_succ_of_le ((card_le_univ _).trans (by simp))⟩

/-- 辅助引理（T1.0(c)）：由高度拼出的矩阵逐行单调不增。 -/
theorem antitone_colMat {k m : ℕ} (h : Fin k → Fin (m + 1)) : Antitone (colMat h) := by
  intro i i' hii' j
  simp only [colMat]
  have hle : (i : ℕ) ≤ i' := hii'
  by_cases h1 : (i' : ℕ) < (h j : ℕ)
  · have h2 : (i : ℕ) < (h j : ℕ) := lt_of_le_of_lt hle h1
    simp [h1, h2]
  · simp [h1]

/-- 辅助引理（T1.0(b)(c)）：由高度拼出的矩阵每行都是允许行 ⇔ 高度的每个相邻三元组都好。 -/
theorem allowed_colMat_iff {k m : ℕ} (h : Fin k → Fin (m + 1)) :
    (∀ i, AllowedRow (colMat h i)) ↔ LegalF h := by
  have hb : ∀ j : Fin k, (h j : ℕ) ≤ m := fun j => Nat.lt_succ_iff.mp (h j).isLt
  constructor
  · intro hA j hj
    refine (rowPattern_iff_good (M := m) (hb _) (hb _) (hb _)).mp ?_
    intro r hr
    exact hA ⟨r, hr⟩ j hj
  · intro hL i j hj
    exact (rowPattern_iff_good (M := m) (hb _) (hb _) (hb _)).mpr (hL j hj) i.val i.isLt

/-- 辅助引理（T1.0(c)）：先拼矩阵再数各列 1 的个数，回到原来的高度。 -/
theorem colHeight_colMat {k m : ℕ} (h : Fin k → Fin (m + 1)) : colHeight (colMat h) = h := by
  funext j
  apply Fin.ext
  simp only [colHeight, colMat, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt]
  have := (h j).isLt
  omega

/-- 辅助引理（T1.0(c)）：逐行单调不增的 0/1 矩阵由各列 1 的个数唯一决定。 -/
theorem colMat_colHeight {k m : ℕ} {M : Fin m → Fin k → Bool} (hM : Antitone M) :
    colMat (colHeight M) = M := by
  funext i j
  have key := mem_iff_lt_card_of_downClosed (univ.filter fun i' : Fin m => M i' j = true)
    (by
      intro a b hba ha
      rw [mem_filter] at ha ⊢
      refine ⟨mem_univ _, ?_⟩
      have hle : M a j ≤ M b j := hM (show b ≤ a from hba) j
      rw [ha.2] at hle
      cases hMb : M b j
      · rw [hMb] at hle; exact absurd hle (by decide)
      · rfl) i
  simp only [mem_filter, mem_univ, true_and] at key
  simp only [colMat, colHeight]
  by_cases hv : M i j = true
  · rw [hv]; exact decide_eq_true (key.mp hv)
  · have hlt : ¬ (i : ℕ) < (univ.filter fun i' : Fin m => M i' j = true).card :=
      fun h => hv (key.mpr h)
    simp only [Bool.not_eq_true] at hv
    rw [hv]; exact decide_eq_false hlt

open Classical in
/-- 从上到下逐行单调不增（`M 0 ≥ M 1 ≥ ⋯`）、每行都是允许行的 m×k 矩阵个数为 `U_k(m)`。 -/
theorem card_antitone_rows (k m : ℕ) :
    Fintype.card {M : Fin m → Fin k → Bool // (∀ i, AllowedRow (M i)) ∧ Antitone M} = U k m := by
  rw [← card_legalF]
  refine Fintype.card_congr
    { toFun := fun M => ⟨colHeight M.1, ?_⟩
      invFun := fun h => ⟨colMat h.1, (allowed_colMat_iff h.1).mpr h.2, antitone_colMat h.1⟩
      left_inv := fun M => Subtype.ext (colMat_colHeight M.2.2)
      right_inv := fun h => Subtype.ext (colHeight_colMat h.1) }
  have hA := M.2.1
  rw [← colMat_colHeight M.2.2] at hA
  exact (allowed_colMat_iff _).mp hA

/-! ### 多重链 -/

/-- `Λ_k` 中的 m 元多重链（`Monotone`：`x_1 ≤ x_2 ≤ ⋯ ≤ x_m`）倒序后就是逐行单调不增的允许行矩阵。 -/
def multichainEquiv (k m : ℕ) :
    {c : Fin m → Lam k // Monotone c} ≃
      {M : Fin m → Fin k → Bool // (∀ i, AllowedRow (M i)) ∧ Antitone M} where
  toFun c := ⟨fun i => (c.1 (Fin.rev i)).1, fun i => (c.1 (Fin.rev i)).2, by
    intro i i' hii'
    have : c.1 (Fin.rev i') ≤ c.1 (Fin.rev i) := c.2 (Fin.rev_le_rev.mpr hii')
    exact this⟩
  invFun M := ⟨fun i => ⟨M.1 (Fin.rev i), M.2.1 _⟩, by
    intro i i' hii'
    have : M.1 (Fin.rev i) ≤ M.1 (Fin.rev i') := M.2.2 (Fin.rev_le_rev.mpr hii')
    exact this⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simp
  right_inv M := by
    apply Subtype.ext
    funext i
    simp

open Classical in
/-- **T1.0(c)**：`U_k(m)` 等于允许行偏序集 `Λ_k`（逐分量序）中 m 元多重链 `x_1 ≤ x_2 ≤ ⋯ ≤ x_m`
的个数，即 Stanley 约定下 zeta 多项式的取值 `Z(Λ_k, m+1)`；`m = 0` 时只有空链，`U_k(0) = 1`。 -/
theorem U_eq_multichains (k m : ℕ) : Fintype.card {c : Fin m → Lam k // Monotone c} = U k m := by
  rw [Fintype.card_congr (multichainEquiv k m), card_antitone_rows]

open Classical in
/-- 允许行的个数 `R_k = |Λ_k| = U_k(1)`（`m = 1` 的多重链就是单个元素）。 -/
theorem card_Lam (k : ℕ) : Fintype.card (Lam k) = U k 1 := by
  rw [← U_eq_multichains]
  refine Fintype.card_congr
    { toFun := fun r => ⟨fun _ => r, monotone_const⟩
      invFun := fun c => c.1 0
      left_inv := fun r => rfl
      right_inv := fun c => ?_ }
  apply Subtype.ext
  funext i
  rw [Subsingleton.elim i 0]

end A207123
