import A207123.Chains
import A207123.HStruct
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# 报告 T5.3(4) 的 Möbius 解释：Philip Hall 定理与 `Λ_k` 的 Möbius 函数

报告 T5.3(4)：允许行偏序集 `Λ_k`（`Lam k`，最小元 `0`、最大元 `1`）的 Möbius 函数
`μ(0̂,1̂) = Σ_q (−1)^q N(k,q) = U_k(−2)`，`k ≥ 4` 时为 0，`k = 1, 2, 3` 时为 `−1, 1, 1`。后两个等号已在
`HStruct.lean` 形式化（`sum_neg_one_pow_N`、`sum_neg_one_pow_N_eq_zero`、`sum_neg_one_pow_N_small`）；这里补第一个
等号，它是 Philip Hall 定理（报告原来引用、没有重证）：

* `mu_eq_sum_chains`：有限偏序集中 `a < b` 时 `μ(a,b) = Σ_n (−1)^{n+1}·#{a < x_1 < ⋯ < x_n < b}`（`μ` 是 Mathlib 的
  `IncidenceAlgebra.mu`，由 `μ(a,a) = 1`、`μ(a,b) = −Σ_{a≤x<b} μ(a,x)` 定义）。证明对 `b` 做良基归纳：链按最大元
  分类（`chainsIn_succ`：`#_{n+1}(a,b) = Σ_{a<x<b} #_n(a,x)`），再代入 `μ` 的递推。
* `chainsIn_lam`：`Λ_k` 中 `0` 与 `1` 之间的 `n` 元链就是 `Λ̄_k` 中的 `n` 元链（`numChainsBar`，次序反过来）。
* `mobius_lam`：`k ≥ 1` 时 `μ_{Λ_k}(0̂,1̂) = Σ_q (−1)^q N(k,q)`；`mobius_lam_eq_upoly`（`= u_k(−2)`）、
  `mobius_lam_eq_zero`（`k ≥ 4` 时为 0）、`mobius_lam_small`（`k = 1, 2, 3` 时为 `−1, 1, 1`）。
-/

namespace A207123

open Finset

noncomputable section

/-! ## 1. Philip Hall 定理 -/

open Classical in
/-- `a` 与 `b` 之间（严格）的 `n` 元链的个数（链从小到大排列成 `c 0 < ⋯ < c (n−1)`）。 -/
def chainsIn {α : Type*} [Preorder α] [Fintype α] (a b : α) (n : ℕ) : ℕ :=
  (univ.filter fun c : Fin n → α => StrictMono c ∧ ∀ i, a < c i ∧ c i < b).card

theorem chainsIn_zero {α : Type*} [Preorder α] [Fintype α] (a b : α) : chainsIn a b 0 = 1 := by
  classical
  unfold chainsIn
  rw [card_eq_one]
  refine ⟨fun i => i.elim0, ?_⟩
  ext c
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro _
    funext i
    exact i.elim0
  · intro _
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- 链的长度不超过 `|α| − 1`（链的值都不等于 `a`）。 -/
theorem chainsIn_eq_zero {α : Type*} [Preorder α] [Fintype α] (a b : α) {n : ℕ}
    (hn : Fintype.card α ≤ n) : chainsIn a b n = 0 := by
  classical
  unfold chainsIn
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro c - ⟨hc, hab⟩
  have h1 : (univ.image c).card = n := by
    rw [card_image_of_injective _ hc.injective, card_univ, Fintype.card_fin]
  have h2 : univ.image c ⊆ univ.erase a := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    exact mem_erase.2 ⟨(hab i).1.ne', mem_univ _⟩
  have h3 := card_le_card h2
  rw [h1, card_erase_of_mem (mem_univ a), card_univ] at h3
  have h4 : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
  omega

/-- 在严格递增的链后面接一个更大的元素，仍严格递增。 -/
theorem snoc_strictMono {α : Type*} [Preorder α] {n : ℕ} {c : Fin n → α} {x : α} (hc : StrictMono c)
    (hx : ∀ i, c i < x) : StrictMono (Fin.snoc (α := fun _ => α) c x) := fun i j h => by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt h)
  rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hc (Fin.castSucc_lt_castSucc_iff.1 h)
  · rw [Fin.snoc_castSucc, Fin.snoc_last]
    exact hx i

/-- 按最大元分类：`#_{n+1}(a,b) = Σ_{a<x<b} #_n(a,x)`。 -/
theorem chainsIn_succ {α : Type*} [Preorder α] [Fintype α] [LocallyFiniteOrder α] (a b : α) (n : ℕ) :
    chainsIn a b (n + 1) = ∑ x ∈ Ioo a b, chainsIn a x n := by
  classical
  unfold chainsIn
  rw [card_eq_sum_card_fiberwise (f := fun c : Fin (n + 1) → α => c (Fin.last n)) (t := Ioo a b)]
  · refine sum_congr rfl fun x hx => ?_
    rw [mem_Ioo] at hx
    refine card_nbij' (fun c => Fin.init c) (fun c => Fin.snoc (α := fun _ => α) c x) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hc ⊢
      obtain ⟨⟨hmono, hbd⟩, hlast⟩ := hc
      refine ⟨fun i j hij => hmono (Fin.castSucc_lt_castSucc_iff.2 hij), fun i => ⟨(hbd _).1, ?_⟩⟩
      rw [← hlast]
      exact hmono (Fin.castSucc_lt_last i)
    · intro c hc
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hc ⊢
      obtain ⟨hmono, hbd⟩ := hc
      refine ⟨⟨snoc_strictMono hmono fun i => (hbd i).2, fun i => ?_⟩, Fin.snoc_last _ _⟩
      rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact ⟨(hbd i).1, (hbd i).2.trans hx.2⟩
      · rw [Fin.snoc_last]
        exact hx
    · intro c hc
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hc
      rw [← hc.2]
      exact Fin.snoc_init_self c
    · intro c _
      exact Fin.init_snoc _ _
  · intro c hc
    rw [mem_coe, mem_filter] at hc
    rw [mem_coe, mem_Ioo]
    exact hc.2.2 _

/-- **Philip Hall 定理**：有限偏序集中 `a < b` 时 `μ(a,b) = Σ_{n≥0} (−1)^{n+1}·#{a < x_1 < ⋯ < x_n < b}`
（`n ≥ |α|` 的项为 0）。 -/
theorem mu_eq_sum_chains {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α] [LocallyFiniteOrder α] :
    ∀ b a : α, a < b → IncidenceAlgebra.mu ℚ a b =
      ∑ n ∈ range (Fintype.card α + 1), (-1 : ℚ) ^ (n + 1) * (chainsIn a b n : ℚ) := by
  intro b
  induction b using WellFoundedLT.induction with
  | _ b ih =>
    intro a hab
    have hIH : ∀ x ∈ Ioo a b, IncidenceAlgebra.mu ℚ a x =
        ∑ n ∈ range (Fintype.card α), (-1 : ℚ) ^ (n + 1) * (chainsIn a x n : ℚ) := by
      intro x hx
      rw [ih x (mem_Ioo.1 hx).2 a (mem_Ioo.1 hx).1, sum_range_succ, chainsIn_eq_zero a x le_rfl,
        Nat.cast_zero, mul_zero, add_zero]
    rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hab.ne, ← Ioo_insert_left hab,
      sum_insert left_notMem_Ioo, IncidenceAlgebra.mu_self, sum_congr rfl hIH, sum_range_succ',
      chainsIn_zero]
    simp only [chainsIn_succ, Nat.cast_sum, mul_sum, Nat.cast_one]
    have hneg : ∑ n ∈ range (Fintype.card α), ∑ x ∈ Ioo a b, (-1 : ℚ) ^ (n + 1 + 1) * (chainsIn a x n : ℚ)
        = -∑ x ∈ Ioo a b, ∑ n ∈ range (Fintype.card α), (-1 : ℚ) ^ (n + 1) * (chainsIn a x n : ℚ) := by
      rw [sum_comm, ← sum_neg_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun n _ => ?_
      ring
    rw [hneg]
    ring

/-! ## 2. `Λ_k` 的 Möbius 函数 -/

section Lam

open Classical

/-- `Λ_k` 是有限偏序集，取 `Fintype.toLocallyFiniteOrder` 作局部有限序结构（Mathlib 的 `Bool` 没有现成实例；
局部有限序结构是唯一的，所以 `μ` 与这个选择无关）。 -/
noncomputable instance lamLocallyFiniteOrder (k : ℕ) : LocallyFiniteOrder (Lam k) :=
  Fintype.toLocallyFiniteOrder

/-- `Λ_k` 中 `0 < x < 1` 的 `n` 元链（从小到大）与 `Λ̄_k` 的 `n` 元链（从大到小，`numChainsBar`）一一对应。 -/
theorem chainsIn_lam (k n : ℕ) : chainsIn (lamBot k) (lamTop k) n = numChainsBar k n := by
  unfold chainsIn numChainsBar
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun c => ⟨c.1 ∘ Fin.rev, c.2.1.comp_strictAnti Fin.rev_strictAnti,
        fun i => ⟨(c.2.2 _).1.ne', (c.2.2 _).2.ne⟩⟩
      invFun := fun c => ⟨c.1 ∘ Fin.rev, c.2.1.comp Fin.rev_strictAnti,
        fun i => ⟨lt_of_le_of_ne (lamBot_le k _) (c.2.2 _).1.symm, lt_of_le_of_ne (le_lamTop k _) (c.2.2 _).2⟩⟩
      left_inv := fun c => Subtype.ext (funext fun i => by simp)
      right_inv := fun c => Subtype.ext (funext fun i => by simp) }

theorem lamBot_lt_lamTop {k : ℕ} (hk : 1 ≤ k) : lamBot k < lamTop k := by
  refine lt_of_le_of_ne (lamBot_le k _) fun h => ?_
  have := congrArg (fun r : Lam k => r.1 ⟨0, hk⟩) h
  simp [lamBot, lamTop] at this

/-- **报告 T5.3(4)**（Möbius 解释）：`k ≥ 1` 时 `Λ_k` 的 Möbius 函数 `μ(0̂,1̂) = Σ_q (−1)^q·N(k,q)`。 -/
theorem mobius_lam {k : ℕ} (hk : 1 ≤ k) :
    IncidenceAlgebra.mu ℚ (lamBot k) (lamTop k) = ∑ q ∈ range (k + 1), (-1 : ℚ) ^ q * (N k q : ℚ) := by
  rw [mu_eq_sum_chains (lamTop k) (lamBot k) (lamBot_lt_lamTop hk)]
  simp only [chainsIn_lam]
  have hz1 : ∀ n, k ≤ n → numChainsBar k n = 0 := fun n hn => numChainsBar_eq_zero hk hn
  have hz2 : ∀ n, Fintype.card (Lam k) ≤ n → numChainsBar k n = 0 := fun n hn => by
    rw [← chainsIn_lam]
    exact chainsIn_eq_zero _ _ hn
  obtain ⟨M, hM⟩ : ∃ M, M = Fintype.card (Lam k) + 1 + k := ⟨_, rfl⟩
  have e1 : ∑ n ∈ range (Fintype.card (Lam k) + 1), (-1 : ℚ) ^ (n + 1) * (numChainsBar k n : ℚ)
      = ∑ n ∈ range M, (-1 : ℚ) ^ (n + 1) * (numChainsBar k n : ℚ) := by
    rw [← sum_range_add_sum_Ico _ (show Fintype.card (Lam k) + 1 ≤ M by omega),
      sum_eq_zero (s := Ico (Fintype.card (Lam k) + 1) M) fun n hn => by
        rw [hz2 n (by have := (mem_Ico.1 hn).1; omega), Nat.cast_zero, mul_zero],
      add_zero]
  have e2 : ∑ n ∈ range k, (-1 : ℚ) ^ (n + 1) * (numChainsBar k n : ℚ)
      = ∑ n ∈ range M, (-1 : ℚ) ^ (n + 1) * (numChainsBar k n : ℚ) := by
    rw [← sum_range_add_sum_Ico _ (show k ≤ M by omega),
      sum_eq_zero (s := Ico k M) fun n hn => by rw [hz1 n (mem_Ico.1 hn).1, Nat.cast_zero, mul_zero],
      add_zero]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [e1, ← e2, sum_range_succ' _ (j + 1), pow_zero, one_mul, N_succ_zero j, Nat.cast_zero, add_zero]
  refine sum_congr rfl fun n _ => ?_
  rw [numChainsBar_eq_N hk n]

/-- `μ_{Λ_k}(0̂,1̂) = u_k(−2)`（`k ≥ 1`）。 -/
theorem mobius_lam_eq_upoly {k : ℕ} (hk : 1 ≤ k) :
    IncidenceAlgebra.mu ℚ (lamBot k) (lamTop k) = (upoly k).eval (-2) := by
  rw [mobius_lam hk, sum_neg_one_pow_N]

/-- **报告 T5.3(4)**：`k ≥ 4` 时 `μ_{Λ_k}(0̂,1̂) = 0`。 -/
theorem mobius_lam_eq_zero {k : ℕ} (hk : 4 ≤ k) : IncidenceAlgebra.mu ℚ (lamBot k) (lamTop k) = 0 := by
  rw [mobius_lam (by omega), sum_neg_one_pow_N_eq_zero hk]

/-- **报告 T5.3(4)**：`k = 1, 2, 3` 时 `μ_{Λ_k}(0̂,1̂)` 分别为 `−1, 1, 1`。 -/
theorem mobius_lam_small :
    IncidenceAlgebra.mu ℚ (lamBot 1) (lamTop 1) = -1 ∧ IncidenceAlgebra.mu ℚ (lamBot 2) (lamTop 2) = 1 ∧
      IncidenceAlgebra.mu ℚ (lamBot 3) (lamTop 3) = 1 := by
  obtain ⟨h1, h2, h3⟩ := sum_neg_one_pow_N_small
  exact ⟨by rw [mobius_lam (by norm_num), h1], by rw [mobius_lam (by norm_num), h2],
    by rw [mobius_lam (by norm_num), h3]⟩

end Lam

end

end A207123
