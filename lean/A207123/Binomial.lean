import A207123.Basic

/-!
# 二项式基与 `N(k,q)` 的三角递推（报告 T1.4）

`N k q`：长 `k`、值域恰为 `{1,…,q}` 的合法词个数（「合法」与 `U` 相同：每个相邻三元组都好）。

本文件证明：
* `U_eq_sum_N`：`U_k(m) = Σ_{q=0}^{k} N(k,q)·C(m+1,q)`（T1.4(1)）；
* `N_inv`、`N_inv_zero`：容斥式 `N(k,q) = Σ_i (−1)^{q−i}·C(q,i)·U_k(i−1)`（T1.4(1)，
  约定 `U_0(−1) = 1`、`U_k(−1) = 0`（k ≥ 1））；
* `N_tri`：三角递推（T1.4(2)，k ≥ 3），初值 `N_init`，越界为 0（`N_eq_zero_of_lt`、`N_succ_zero`），
  以及报告「初值更正」的两点：`N_tri_fails_at_two`（只给 `N(0,0)=1` 加零边界在 k = 2 出错）与
  `N_tri_one`、`N_tri_two`（约定 `N(−1,0)=1`、`N(−1,q)=0`（q ≥ 1）、`N(−2,·)=0` 时 k = 1, 2 也成立）；
* `N_diag`：`N(k,k) = 2`（k ≥ 2，T1.4(3)）；
* `N_subdiag`：`N(k,k−1) = k²−k−4`（k ≥ 4，T1.4(4)），以及例外 `N(3,2) = 4`、`N(2,1) = 1`。

证明路线：
* 好三元组只用到 `=` 与 `≤`，被严格增映射保持（`good_map_iff`、`legal_map_iff`）。用名次函数
  `rk V v = #{u ∈ V | u < v} + 1` 把值域恰为 `V` 的合法词一一对应到值域恰为 `{1,…,|V|}` 的合法词
  （`card_fiber`），按值域分类即得二项式基展开。
* 三角递推：把引理 1 代入二项式基展开，比较 `C(n,r)` 的系数（`choose_basis_unique`）。报告 T1.4(2)
  写的是组合证明（按最大值首次出现的位置分 6 类）；这里走报告 T3.5(2) 所说「三角递推可由引理 1 推出」
  的路线，陈述相同。
-/

namespace A207123

open Finset

/-! ### 定义 -/

/-- `NW k q`：长 `k`、值域恰为 `{1,…,q}` 的合法词全体。 -/
def NW (k q : ℕ) : Finset (List ℕ) := (L k q).filter fun l => l.toFinset = Icc 1 q

/-- `N k q = |NW k q|`：报告 T1.4 的 `N(k,q)`。 -/
def N (k q : ℕ) : ℕ := (NW k q).card

/-- `NW` 的透明刻画：长 `k`、合法、值域恰为 `{1,…,q}`。 -/
theorem mem_NW {k q : ℕ} {l : List ℕ} :
    l ∈ NW k q ↔ l.length = k ∧ Legal l ∧ l.toFinset = Icc 1 q := by
  unfold NW
  rw [mem_filter, mem_L]
  constructor
  · rintro ⟨⟨h1, -, h3⟩, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨⟨h1, fun x hx => ?_, h3⟩, h4⟩
    have : x ∈ l.toFinset := List.mem_toFinset.mpr hx
    rw [h4, mem_Icc] at this
    exact this.2

/-! ### 保序不变性 -/

/-- 好三元组只依赖大小关系：在严格增映射下不变。 -/
theorem good_map_iff {φ : ℕ → ℕ} {S : Set ℕ} (hφ : StrictMonoOn φ S) {a b c : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : Good (φ a) (φ b) (φ c) ↔ Good a b c := by
  unfold Good
  rw [hφ.injOn.eq_iff hb hc, hφ.le_iff_le hb ha, hφ.le_iff_le hc ha]

/-- 合法性在严格增映射下不变。 -/
theorem legal_map_iff {φ : ℕ → ℕ} {S : Set ℕ} (hφ : StrictMonoOn φ S) :
    ∀ {l : List ℕ}, (∀ x ∈ l, x ∈ S) → (Legal (l.map φ) ↔ Legal l)
  | [], _ => by simp
  | [_], _ => by simp
  | [_, _], _ => by simp
  | a :: b :: c :: t, h => by
    have ih := legal_map_iff hφ (l := b :: c :: t) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons] at ih ⊢
    rw [legal_cons3, legal_cons3, ih,
      good_map_iff hφ (h a (by simp)) (h b (by simp)) (h c (by simp))]

/-! ### 名次函数 -/

/-- `rk V v = #{u ∈ V | u < v} + 1`：`v` 在 `V` 中从小到大的名次（从 1 开始）。 -/
def rk (V : Finset ℕ) (v : ℕ) : ℕ := (V.filter (· < v)).card + 1

/-- 辅助引理（T1.4(1)）：名次函数 `rk V` 在 `V` 上严格增。 -/
theorem rk_strictMonoOn (V : Finset ℕ) : StrictMonoOn (rk V) (V : Set ℕ) := by
  intro u hu v hv huv
  have hu' : u ∈ V := hu
  have hsub : V.filter (· < u) ⊂ V.filter (· < v) := by
    rw [ssubset_iff_of_subset]
    · exact ⟨u, by simp [mem_filter, hu', huv], by simp⟩
    · intro x hx
      rw [mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans huv⟩
  have := card_lt_card hsub
  unfold rk
  omega

/-- 辅助引理（T1.4(1)）：`v ∈ V` 时名次 `rk V v ∈ {1,…,|V|}`。 -/
theorem rk_mem_Icc {V : Finset ℕ} {v : ℕ} (hv : v ∈ V) : rk V v ∈ Icc 1 V.card := by
  have hsub : V.filter (· < v) ⊆ V.erase v := by
    intro x hx
    rw [mem_filter] at hx
    exact mem_erase.mpr ⟨by omega, hx.1⟩
  have h1 := card_le_card hsub
  rw [card_erase_of_mem hv] at h1
  have h2 := card_pos.mpr ⟨v, hv⟩
  rw [mem_Icc]
  unfold rk
  omega

/-- 辅助引理（T1.4(1)）：`rk V` 把 `V` 一一映到 `{1,…,|V|}`。 -/
theorem image_rk (V : Finset ℕ) : V.image (rk V) = Icc 1 V.card := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact rk_mem_Icc hv
  · rw [card_image_of_injOn (rk_strictMonoOn V).injOn, Nat.card_Icc]
    omega

/-- 值域恰为 `V`（`V ⊆ {0,…,m}`）的长 `k` 合法词与值域恰为 `{1,…,|V|}` 的一样多。 -/
theorem card_fiber {k m : ℕ} {V : Finset ℕ} (hV : V ⊆ range (m + 1)) :
    ((L k m).filter fun l => l.toFinset = V).card = N k V.card := by
  classical
  unfold N
  set S : Set ℕ := (V : Set ℕ) with hSdef
  have hSV : ∀ x, x ∈ S ↔ x ∈ V := fun x => Iff.rfl
  -- 值域为 `{1..|V|}` 的词，每个字母都在 `rk V` 的像里
  have himg : ∀ w ∈ NW k V.card, ∀ x ∈ w, ∃ v ∈ S, rk V v = x := by
    intro w hw x hx
    rw [mem_NW] at hw
    have : x ∈ V.image (rk V) := by
      rw [image_rk, ← hw.2.2]; exact List.mem_toFinset.mpr hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp this
    exact ⟨v, hv, rfl⟩
  have hright : ∀ w ∈ NW k V.card,
      (w.map (Function.invFunOn (rk V) S)).map (rk V) = w := by
    intro w hw
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    apply List.map_congr_left
    intro x hx
    exact Function.invFunOn_eq (himg w hw x hx)
  refine card_nbij' (List.map (rk V)) (List.map (Function.invFunOn (rk V) S)) ?_ ?_ ?_ ?_
  · -- 正向映射落在 `NW k |V|` 中
    intro l hl
    rw [mem_coe, mem_filter, mem_L] at hl
    obtain ⟨⟨hlen, -, hleg⟩, hval⟩ := hl
    have hS : ∀ x ∈ l, x ∈ S := fun x hx => by
      rw [hSV, ← hval]; exact List.mem_toFinset.mpr hx
    rw [mem_coe, mem_NW]
    refine ⟨by simp [hlen], (legal_map_iff (rk_strictMonoOn V) hS).mpr hleg, ?_⟩
    have hmap : (l.map (rk V)).toFinset = l.toFinset.image (rk V) := by
      ext x; simp
    rw [hmap, hval, image_rk]
  · -- 反向映射落在值域为 `V` 的合法词中
    intro w hw
    rw [mem_coe] at hw
    have hw' := mem_NW.mp hw
    obtain ⟨hlen, hleg, hval⟩ := hw'
    have hS : ∀ x ∈ w.map (Function.invFunOn (rk V) S), x ∈ S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact Function.invFunOn_mem (himg w hw y hy)
    have hval' : (w.map (Function.invFunOn (rk V) S)).toFinset = V := by
      ext v
      rw [List.mem_toFinset]
      constructor
      · intro hv; exact (hSV v).mp (hS v hv)
      · intro hv
        have hmem : rk V v ∈ w := by
          rw [← List.mem_toFinset, hval]; exact rk_mem_Icc hv
        rw [List.mem_map]
        exact ⟨rk V v, hmem, (rk_strictMonoOn V).injOn.leftInvOn_invFunOn hv⟩
    rw [mem_coe, mem_filter, mem_L]
    refine ⟨⟨by simp [hlen], fun x hx => ?_, ?_⟩, hval'⟩
    · have h1 : x ∈ V := (hSV x).mp (hS x hx)
      have h2 := hV h1
      rw [mem_range] at h2
      omega
    · rw [← legal_map_iff (rk_strictMonoOn V) hS, hright w hw]
      exact hleg
  · -- 左逆
    intro l hl
    rw [mem_coe, mem_filter, mem_L] at hl
    obtain ⟨-, hval⟩ := hl
    show (l.map (rk V)).map (Function.invFunOn (rk V) S) = l
    rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro x hx
    have hx' : x ∈ S := by rw [hSV, ← hval]; exact List.mem_toFinset.mpr hx
    exact (rk_strictMonoOn V).injOn.leftInvOn_invFunOn hx'
  · -- 右逆
    intro w hw
    exact hright w hw

/-! ### 越界为 0 -/

/-- `q > k` 时 `N(k,q) = 0`：长 `k` 的词至多有 `k` 个不同的值。 -/
theorem N_eq_zero_of_lt {k q : ℕ} (h : k < q) : N k q = 0 := by
  unfold N
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro l hl
  rw [mem_NW] at hl
  have := List.toFinset_card_le l
  rw [hl.2.2, Nat.card_Icc, hl.1] at this
  omega

/-- `k ≥ 1` 时 `N(k,0) = 0`：非空词的值域非空。 -/
theorem N_succ_zero (k : ℕ) : N (k + 1) 0 = 0 := by
  unfold N
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro l hl
  rw [mem_NW] at hl
  obtain ⟨hlen, -, hval⟩ := hl
  have hne : l ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne
  have : x ∈ l.toFinset := List.mem_toFinset.mpr hx
  rw [hval] at this
  simp at this

/-! ### T1.4(1)：二项式基 -/

/-- 辅助引理（T1.4）：两端之外的项都为 0 时，可以改变求和上限。 -/
theorem sum_range_eq_of_zero {f : ℕ → ℕ} {a b : ℕ} (ha : ∀ q, a ≤ q → f q = 0)
    (hb : ∀ q, b ≤ q → f q = 0) : ∑ q ∈ range a, f q = ∑ q ∈ range b, f q := by
  rcases le_total a b with hab | hab
  · rw [← sum_range_add_sum_Ico f hab, sum_eq_zero (fun q hq => ha q (mem_Ico.mp hq).1), add_zero]
  · rw [← sum_range_add_sum_Ico f hab, sum_eq_zero (fun q hq => hb q (mem_Ico.mp hq).1), add_zero]

/-- **T1.4(1) 二项式基**：`U_k(m) = Σ_{q=0}^{k} N(k,q)·C(m+1,q)`（按值域分类，值域为 `q` 元集合的
合法词有 `N(k,q)` 个，`{0,…,m}` 的 `q` 元子集有 `C(m+1,q)` 个）。 -/
theorem U_eq_sum_N (k m : ℕ) : U k m = ∑ q ∈ range (k + 1), N k q * (m + 1).choose q := by
  classical
  have H : ((L k m : Finset (List ℕ)) : Set (List ℕ)).MapsTo List.toFinset
      ((range (m + 1)).powerset : Set (Finset ℕ)) := by
    intro l hl
    rw [mem_coe, mem_L] at hl
    rw [mem_coe, mem_powerset]
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [mem_range]
    have := hl.2.1 x hx
    omega
  unfold U
  rw [card_eq_sum_card_fiberwise H,
    sum_congr rfl (fun V hV => card_fiber (k := k) (mem_powerset.mp hV)),
    sum_powerset_apply_card (fun q => N k q), card_range]
  simp only [smul_eq_mul]
  rw [sum_range_eq_of_zero (b := k + 1)]
  · exact sum_congr rfl (fun q _ => mul_comm _ _)
  · intro q hq; rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  · intro q hq; rw [N_eq_zero_of_lt (by omega), mul_zero]

/-! ### 二项式系数的唯一性与两条展开式 -/

/-- 作为 `n` 的函数，`C(n,0), C(n,1), …` 线性无关：系数唯一。 -/
theorem choose_basis_unique {a b : ℕ → ℕ}
    (h : ∀ n, ∑ r ∈ range (n + 1), a r * n.choose r = ∑ r ∈ range (n + 1), b r * n.choose r) :
    a = b := by
  funext r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    have hr := h r
    rw [sum_range_succ, sum_range_succ, Nat.choose_self, mul_one, mul_one] at hr
    have : ∑ i ∈ range r, a i * r.choose i = ∑ i ∈ range r, b i * r.choose i :=
      sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi)]
    omega

/-- Pascal：`Σ_{q≤n+1} f(q)·C(n+1,q) = Σ_{r≤n} (f(r) + f(r+1))·C(n,r)`。 -/
theorem sum_choose_succ (f : ℕ → ℕ) (n : ℕ) :
    ∑ q ∈ range (n + 2), f q * (n + 1).choose q
      = ∑ r ∈ range (n + 1), (f r + f (r + 1)) * n.choose r := by
  have h1 : ∑ q ∈ range (n + 2), f q * (n + 1).choose q
      = ∑ r ∈ range (n + 1), f (r + 1) * (n.choose r + n.choose (r + 1)) + f 0 := by
    rw [sum_range_succ', Nat.choose_zero_right, mul_one]
    simp only [Nat.choose_succ_succ']
  have h2 : ∑ r ∈ range (n + 1), f (r + 1) * n.choose (r + 1) + f 0
      = ∑ r ∈ range (n + 1), f r * n.choose r := by
    rw [sum_range_succ, Nat.choose_succ_self, mul_zero, add_zero]
    rw [sum_range_succ' (fun r => f r * n.choose r), Nat.choose_zero_right, mul_one]
  rw [h1]
  simp only [mul_add, add_mul, sum_add_distrib]
  rw [add_assoc, h2, add_comm]

/-- `n·C(n,r) = r·C(n,r) + (r+1)·C(n,r+1)`。 -/
theorem mul_choose_eq (n r : ℕ) : n * n.choose r = r * n.choose r + (r + 1) * n.choose (r + 1) := by
  have h := Nat.choose_succ_right_eq n r
  rw [mul_comm (r + 1), h]
  by_cases hr : r ≤ n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [Nat.add_sub_cancel_left]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    ring

/-- `n · Σ_{r≤n} a(r)·C(n,r) = Σ_{r≤n} r·(a(r) + a(r−1))·C(n,r)`（`r = 0` 的项为 0）。 -/
theorem mul_sum_choose (a : ℕ → ℕ) (n : ℕ) :
    n * ∑ r ∈ range (n + 1), a r * n.choose r
      = ∑ r ∈ range (n + 1), r * (a r + a (r - 1)) * n.choose r := by
  have h1 : n * ∑ r ∈ range (n + 1), a r * n.choose r
      = ∑ r ∈ range (n + 1), r * a r * n.choose r
        + ∑ r ∈ range (n + 1), (r + 1) * a r * n.choose (r + 1) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    have := mul_choose_eq n r
    calc n * (a r * n.choose r) = a r * (n * n.choose r) := by ring
      _ = a r * (r * n.choose r + (r + 1) * n.choose (r + 1)) := by rw [this]
      _ = r * a r * n.choose r + (r + 1) * a r * n.choose (r + 1) := by ring
  have h2 : ∑ r ∈ range (n + 1), (r + 1) * a r * n.choose (r + 1)
      = ∑ r ∈ range (n + 1), r * a (r - 1) * n.choose r := by
    rw [sum_range_succ (fun r => (r + 1) * a r * n.choose (r + 1)), Nat.choose_succ_self,
      mul_zero, add_zero, sum_range_succ' (fun r => r * a (r - 1) * n.choose r)]
    simp
  rw [h1, h2, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  ring

/-! ### T1.4(2)：三角递推 -/

/-- `Vn k n = Σ_{q≤n} N(k,q)·C(n,q)`；由二项式基，`n ≥ 1` 时它等于 `U_k(n−1)`（`U_eq_Vn`），
`n = 0` 时等于 `N(k,0)`。 -/
def Vn (k n : ℕ) : ℕ := ∑ q ∈ range (n + 1), N k q * n.choose q

/-- 辅助引理（T1.4(2)）：由二项式基，`U_k(m) = Vn k (m+1)`。 -/
theorem U_eq_Vn (k m : ℕ) : U k m = Vn k (m + 1) := by
  rw [U_eq_sum_N, Vn]
  apply sum_range_eq_of_zero
  · intro q hq; rw [N_eq_zero_of_lt (by omega), zero_mul]
  · intro q hq; rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]

/-- 辅助引理（T1.4(2)）：`k ≥ 1` 时 `Vn k 0 = N(k,0) = 0`（对应 `U_k(−1) = 0`）。 -/
theorem Vn_succ_zero (k : ℕ) : Vn (k + 1) 0 = 0 := by
  simp [Vn, N_succ_zero]

/-- 引理 1 用 `Vn` 写出（`n = 0` 对应引理 1 在 `m = 0` 处取 `U_k(−1) = 0`）。 -/
theorem lemma1_Vn (k n : ℕ) :
    Vn (k + 3) (n + 1) = Vn (k + 3) n + Vn (k + 2) (n + 1) + n * Vn k (n + 1) := by
  cases n with
  | zero =>
    rw [← U_eq_Vn, ← U_eq_Vn, U_zero_right, U_zero_right, Vn_succ_zero]
    ring
  | succ m =>
    rw [← U_eq_Vn, ← U_eq_Vn, ← U_eq_Vn, ← U_eq_Vn, lemma1]

/-- **T1.4(2) 三角递推**（k ≥ 3，此处写作 `k + 3`）：
`N(k,r+1) = N(k−1,r) + N(k−1,r+1) + r·[N(k−3,r−1) + 2·N(k−3,r) + N(k−3,r+1)]`。
越界的项为 0（`N_eq_zero_of_lt`）；`r = 0` 时 `r − 1` 在 ℕ 中截断为 0，但该项乘以 `r = 0`，
与「越界取 0」一致。初值见 `N_init`。 -/
theorem N_tri (k r : ℕ) :
    N (k + 3) (r + 1) = N (k + 2) r + N (k + 2) (r + 1)
      + r * (N k (r - 1) + 2 * N k r + N k (r + 1)) := by
  have key : ∀ n, ∑ r ∈ range (n + 1), N (k + 3) (r + 1) * n.choose r
      = ∑ r ∈ range (n + 1), (N (k + 2) r + N (k + 2) (r + 1)
          + r * (N k (r - 1) + 2 * N k r + N k (r + 1))) * n.choose r := by
    intro n
    have h := lemma1_Vn k n
    simp only [Vn] at h
    rw [sum_choose_succ (N (k + 3)), sum_choose_succ (N (k + 2)), sum_choose_succ (N k),
      mul_sum_choose] at h
    simp only [add_mul, sum_add_distrib] at h
    have hc : ∀ r, r * (N k r + N k (r + 1) + (N k (r - 1) + N k (r - 1 + 1)))
        = r * (N k (r - 1) + 2 * N k r + N k (r + 1)) := by
      intro r
      cases r with
      | zero => simp
      | succ r => simp only [Nat.add_sub_cancel]; ring
    simp only [hc] at h
    simp only [add_mul, sum_add_distrib]
    omega
  exact congrFun (choose_basis_unique key) r

/-- 初值：`N(0,0) = 1`，`N(1,1) = 1`，`N(2,1) = 1`，`N(2,2) = 2`。 -/
theorem N_init : N 0 0 = 1 ∧ N 1 1 = 1 ∧ N 2 1 = 1 ∧ N 2 2 = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- 报告 T1.4(2) 的「初值更正」：只给 `N(0,0)=1` 并对越界项取 0 时，递推在 `k = 2, r = 1`
处给出 `N(1,1) + N(1,2) + 1·[0 + 2·0 + 0] = 1`，而 `N(2,2) = 2`。 -/
theorem N_tri_fails_at_two : N 2 2 ≠ N 1 1 + N 1 2 + 1 * (0 + 2 * 0 + 0) := by
  rw [N_init.2.2.2, N_init.2.1, N_eq_zero_of_lt (by omega)]
  omega

/-- 约定 `N(−1,0) = 1`、`N(−1,q) = 0`（q ≥ 1）时，三角递推在 `k = 2` 也成立
（`N(2,r+1) = N(1,r) + N(1,r+1) + r·[N(−1,r−1) + 2·N(−1,r) + N(−1,r+1)]`，此处把 `N(−1,·)` 显式写出）。 -/
theorem N_tri_two (r : ℕ) :
    N 2 (r + 1) = N 1 r + N 1 (r + 1)
      + r * ((if r = 1 then 1 else 0) + 2 * (if r = 0 then 1 else 0) + 0) := by
  match r with
  | 0 => rw [N_init.2.2.1, N_init.2.1, N_succ_zero]; simp
  | 1 => rw [N_init.2.2.2, N_init.2.1, N_eq_zero_of_lt (by omega)]; simp
  | r + 2 =>
    rw [N_eq_zero_of_lt (by omega), N_eq_zero_of_lt (by omega), N_eq_zero_of_lt (by omega)]
    simp

/-- 约定 `N(−2,·) = 0` 时，三角递推在 `k = 1` 也成立：`N(1,r+1) = N(0,r) + N(0,r+1) + r·0`。 -/
theorem N_tri_one (r : ℕ) : N 1 (r + 1) = N 0 r + N 0 (r + 1) + r * 0 := by
  match r with
  | 0 => rw [N_init.2.1, N_init.1, N_eq_zero_of_lt (by omega)]
  | r + 1 =>
    rw [N_eq_zero_of_lt (by omega), N_eq_zero_of_lt (by omega), N_eq_zero_of_lt (by omega)]
    simp

/-! ### T1.4(3)(4)：对角线与次对角线 -/

/-- 辅助引理（T1.4(3)）：三角递推取 `r = k−1`：`N(k,k) = N(k−1,k−1)`（k ≥ 3）。 -/
theorem N_diag_succ (k : ℕ) : N (k + 3) (k + 3) = N (k + 2) (k + 2) := by
  have h := N_tri k (k + 2)
  have e1 : N (k + 2) (k + 2 + 1) = 0 := N_eq_zero_of_lt (by omega)
  have e2 : N k (k + 2 - 1) = 0 := N_eq_zero_of_lt (by omega)
  have e3 : N k (k + 2) = 0 := N_eq_zero_of_lt (by omega)
  have e4 : N k (k + 2 + 1) = 0 := N_eq_zero_of_lt (by omega)
  rw [e1, e2, e3, e4] at h
  simpa using h

/-- **T1.4(3)**：`N(k,k) = 2`（k ≥ 2）。 -/
theorem N_diag (k : ℕ) (hk : 2 ≤ k) : N k k = 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => exact N_init.2.2.2
  | succ j ih =>
    rw [show 2 + (j + 1) = j + 3 by omega, N_diag_succ, show j + 2 = 2 + j by omega]
    exact ih (by omega)

/-- 辅助引理（T1.4(4)）：三角递推取 `r = k−2`：`N(k,k−1) = N(k−1,k−2) + N(k−1,k−1) + (k−2)·N(k−3,k−3)`（k ≥ 3）。 -/
theorem N_subdiag_succ (k : ℕ) :
    N (k + 3) (k + 2) = N (k + 2) (k + 1) + N (k + 2) (k + 2) + (k + 1) * N k k := by
  have h := N_tri k (k + 1)
  have e1 : N k (k + 1) = 0 := N_eq_zero_of_lt (by omega)
  have e2 : N k (k + 1 + 1) = 0 := N_eq_zero_of_lt (by omega)
  rw [e1, e2, show k + 1 - 1 = k by omega] at h
  simpa using h

/-- `k = 3` 时 `N(3,2) = 4`（不满足 `k²−k−4 = 2`）。 -/
theorem N_three_two : N 3 2 = 4 := by
  have h := N_subdiag_succ 0
  rw [N_init.2.2.1, N_init.2.2.2, N_init.1] at h
  simpa using h

/-- **T1.4(4)**：`N(k,k−1) = k²−k−4`（k ≥ 4；`k = 3` 时 `N = 4`，`k = 2` 时 `N = 1`，均为例外，
见 `N_three_two` 与 `N_init`）。 -/
theorem N_subdiag (k : ℕ) (hk : 4 ≤ k) : (N k (k - 1) : ℤ) = (k : ℤ) ^ 2 - k - 4 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero =>
    have h := N_subdiag_succ 1
    rw [N_three_two, N_diag 3 (by omega), N_init.2.1] at h
    simp only [show 4 + 0 - 1 = 1 + 2 by omega, show 4 + 0 = 1 + 3 by omega, h]
    norm_num
  | succ j ih =>
    have h := N_subdiag_succ (j + 2)
    rw [N_diag (j + 2 + 2) (by omega), N_diag (j + 2) (by omega)] at h
    have e1 : 4 + (j + 1) - 1 = j + 2 + 2 := by omega
    have e2 : 4 + (j + 1) = j + 2 + 3 := by omega
    have e3 : 4 + j - 1 = j + 2 + 1 := by omega
    have e4 : 4 + j = j + 2 + 2 := by omega
    rw [e1, e2, h]
    have ih' := ih (by omega)
    rw [e3, e4] at ih'
    push_cast at ih' ⊢
    rw [ih']
    ring

/-! ### T1.4(1)：容斥式（二项式反演） -/

/-- `Σ_{i≤q} (−1)^{q−i} C(q,i) C(i,p) = [p = q]`。 -/
theorem alt_choose_choose (q p : ℕ) :
    ∑ i ∈ range (q + 1), ((-1 : ℤ) ^ (q - i) * q.choose i * i.choose p) = if p = q then 1 else 0 := by
  by_cases hpq : p ≤ q
  · -- 只有 i ≥ p 的项非零；令 i = p + j
    have hsplit : ∑ i ∈ range (q + 1), ((-1 : ℤ) ^ (q - i) * q.choose i * i.choose p)
        = ∑ j ∈ range (q - p + 1), ((-1 : ℤ) ^ (q - p - j) * q.choose p * (q - p).choose j) := by
      rw [show q + 1 = p + (q - p + 1) by omega, sum_range_add]
      rw [sum_eq_zero (fun i hi => by
        rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]; simp), zero_add]
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      have hc := Nat.choose_mul (n := q) (k := p + j) (s := p) (by omega)
      rw [show q - (p + j) = q - p - j by omega, mul_assoc, ← Nat.cast_mul, hc,
        show p + j - p = j by omega]
      push_cast
      ring
    rw [hsplit]
    -- Σ_j (−1)^{n−j} C(n,j) = [n = 0]，n = q − p
    have halt : ∑ j ∈ range (q - p + 1), ((-1 : ℤ) ^ (q - p - j) * ((q - p).choose j : ℤ))
        = if q - p = 0 then 1 else 0 := by
      rw [← Int.alternating_sum_range_choose, ← sum_range_reflect]
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      have e1 : q - p + 1 - 1 - j = q - p - j := by omega
      have e2 : q - p - (q - p - j) = j := by omega
      rw [e1, e2, Nat.choose_symm (by omega)]
    have : ∑ j ∈ range (q - p + 1), ((-1 : ℤ) ^ (q - p - j) * q.choose p * (q - p).choose j)
        = (q.choose p : ℤ) * ∑ j ∈ range (q - p + 1), ((-1 : ℤ) ^ (q - p - j) * (q - p).choose j) := by
      rw [mul_sum]; apply sum_congr rfl; intro j _; ring
    rw [this, halt]
    by_cases h : p = q
    · subst h; simp
    · have h' : q - p ≠ 0 := by omega
      simp [h, h']
  · have h' : p ≠ q := by omega
    simp only [h', ↓reduceIte]
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega : i < p)]
    simp

/-- 二项式反演：`N(k,q) = Σ_{i≤q} (−1)^{q−i}·C(q,i)·Vn(k,i)`。 -/
theorem N_eq_inv_Vn (k q : ℕ) :
    (N k q : ℤ) = ∑ i ∈ range (q + 1), (-1 : ℤ) ^ (q - i) * q.choose i * Vn k i := by
  have hV : ∀ i ∈ range (q + 1), (Vn k i : ℤ) = ∑ p ∈ range (q + 1), (N k p : ℤ) * i.choose p := by
    intro i hi
    rw [mem_range] at hi
    have hN : Vn k i = ∑ p ∈ range (q + 1), N k p * i.choose p := by
      unfold Vn
      apply sum_range_eq_of_zero
      · intro p hp; rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
      · intro p hp; rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
    rw [hN]
    push_cast
    rfl
  rw [sum_congr rfl (fun i hi => by rw [hV i hi])]
  simp only [mul_sum]
  rw [sum_comm]
  have : ∀ p ∈ range (q + 1), ∑ i ∈ range (q + 1), (-1 : ℤ) ^ (q - i) * q.choose i * ((N k p : ℤ) * i.choose p)
      = (N k p : ℤ) * (if p = q then 1 else 0) := by
    intro p _
    rw [← alt_choose_choose q p, mul_sum]
    apply sum_congr rfl; intro i _; ring
  rw [sum_congr rfl this]
  simp

/-- **T1.4(1) 容斥式**（k ≥ 1）：`N(k,q) = Σ_{i=1}^{q} (−1)^{q−i}·C(q,i)·U_k(i−1)`
（约定 `U_k(−1) = 0`，故 `i = 0` 项为 0）。 -/
theorem N_inv (k q : ℕ) (hk : 1 ≤ k) :
    (N k q : ℤ) = ∑ i ∈ Icc 1 q, (-1 : ℤ) ^ (q - i) * q.choose i * U k (i - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [N_eq_inv_Vn, sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
    show 1 + k = k + 1 by omega, Vn_succ_zero]
  simp only [Nat.cast_zero, mul_zero, add_zero, show q + 1 - 1 = q by omega]
  apply sum_congr rfl
  intro i _
  rw [U_eq_Vn, show 1 + i - 1 + 1 = i + 1 by omega, show 1 + i = i + 1 by omega]

/-- **T1.4(1) 容斥式**（k = 0）：约定 `U_0(−1) = 1`，`i = 0` 项为 `(−1)^q`。 -/
theorem N_inv_zero (q : ℕ) :
    (N 0 q : ℤ) = (-1 : ℤ) ^ q + ∑ i ∈ Icc 1 q, (-1 : ℤ) ^ (q - i) * q.choose i * U 0 (i - 1) := by
  rw [N_eq_inv_Vn, sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  have h0 : (Vn 0 0 : ℤ) = 1 := by simp [Vn, N_init.1]
  rw [h0]
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero,
    show q + 1 - 1 = q by omega]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [U_eq_Vn, show 1 + i - 1 + 1 = i + 1 by omega, show 1 + i = i + 1 by omega]

end A207123
