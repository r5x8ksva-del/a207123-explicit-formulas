import A207123.Basic

/-!
# 推荐显式公式（报告 T2.4）

  U_k(m) = Σ_{s ≤ k/3} S(m+s, m)·C(k+m−2s, k−3s)
         + Σ_{j=1}^{m} j · Σ_{s ≤ (k−2)/3} H(m,s,j)·C(k−2+m−j−2s, k−2−3s)，

其中 S 是第二类 Stirling 数（Mathlib 的 `Nat.stirlingSecond`），
`H(m,s,j) = hc s [m, m−1, …, j]` 是完全齐次对称多项式 h_s 在 j,…,m 处的值，第二项在 k < 2 时为空。

证明路线（不用形式幂级数）：
* `E l n := Σ_s h_s(l)·multichoose(|l|+s, n−3s)`，它就是 ∏_{v∈l}(1−x−v x³)^{-1} 的 xⁿ 系数；
* 逐项恒等式 `g_rec` 给出「加入最大变量」的递推 `E_cons`（对应 (1−x−v x³)·Q = Q′）；
* 于是 `F m k := E [m..0] k + Σ_j j·E [m..j] (k−2)` 满足与引理 1 相同的递推与边界（`F_rec` 等），
  归纳即得 `U k m = F m k`（`U_eq_F`），再换成 Stirling 数与二项式（`U_explicit`）。
-/

set_option linter.deprecated false

namespace A207123

open Finset

/-- `hc s l`：完全齐次对称多项式 `h_s` 在变量列表 `l` 处的值，
按标准递推 `h_{s+1}(v, l) = h_{s+1}(l) + v · h_s(v, l)` 定义。 -/
def hc : ℕ → List ℕ → ℕ
  | 0, _ => 1
  | _ + 1, [] => 0
  | s + 1, v :: l => hc (s + 1) l + v * hc s (v :: l)

@[simp] theorem hc_zero (l : List ℕ) : hc 0 l = 1 := by
  cases l <;> simp [hc]

@[simp] theorem hc_succ_nil (s : ℕ) : hc (s + 1) [] = 0 := by
  simp [hc]

theorem hc_succ_cons (s v : ℕ) (l : List ℕ) :
    hc (s + 1) (v :: l) = hc (s + 1) l + v * hc s (v :: l) := by
  rw [hc]

theorem hc_succ_single_zero (s : ℕ) : hc (s + 1) [0] = 0 := by
  rw [hc_succ_cons]; simp

/-- `vars j m = [m, m−1, …, j]`（`j ≤ m` 时）；`j = m + 1` 时为空。 -/
def vars (j : ℕ) : ℕ → List ℕ
  | 0 => if j = 0 then [0] else []
  | m + 1 => if j ≤ m + 1 then (m + 1) :: vars j m else []

theorem vars_succ {j m : ℕ} (h : j ≤ m + 1) : vars j (m + 1) = (m + 1) :: vars j m := by
  simp [vars, h]

theorem vars_self_succ (m : ℕ) : vars (m + 1) m = [] := by
  cases m <;> simp [vars]

theorem vars_zero_zero : vars 0 0 = [0] := by simp [vars]

theorem length_vars {j m : ℕ} (h : j ≤ m + 1) : (vars j m).length = m + 1 - j := by
  induction m with
  | zero =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> simp [vars]
  | succ m ih =>
    by_cases hj : j ≤ m + 1
    · rw [vars_succ hj, List.length_cons, ih hj]; omega
    · have : j = m + 2 := by omega
      subst this
      rw [vars_self_succ]; simp

/-! ### 系数 `E l n` 与逐项递推 -/

/-- 求和项：`[3s ≤ n] · h_s(l) · multichoose(|l| + s, n − 3s)`。 -/
def g (l : List ℕ) (n s : ℕ) : ℕ :=
  if 3 * s ≤ n then hc s l * Nat.multichoose (l.length + s) (n - 3 * s) else 0

/-- `E l n = Σ_{s ≤ n/3} h_s(l) · multichoose(|l|+s, n−3s)`（∏_{v∈l}(1−x−v x³)^{-1} 的 xⁿ 系数）。 -/
def E (l : List ℕ) (n : ℕ) : ℕ := ∑ s ∈ range (n / 3 + 1), g l n s

theorem E_eq_sum (l : List ℕ) {n N : ℕ} (hN : n / 3 + 1 ≤ N) :
    E l n = ∑ s ∈ range N, g l n s := by
  unfold E
  rw [← sum_range_add_sum_Ico _ hN]
  have : ∑ s ∈ Ico (n / 3 + 1) N, g l n s = 0 := by
    apply sum_eq_zero
    intro s hs
    rw [mem_Ico] at hs
    unfold g
    rw [if_neg (by omega)]
  rw [this, add_zero]

/-- 逐项恒等式：`h_s(v::l)` 的递推与 multichoose 的 Pascal 递推合在一起。 -/
theorem g_rec (v : ℕ) (l : List ℕ) (n s : ℕ) :
    g (v :: l) (n + 3) s
      = g l (n + 3) s + (if s = 0 then 0 else v * g (v :: l) n (s - 1)) + g (v :: l) (n + 2) s := by
  cases s with
  | zero =>
    simp only [g, Nat.mul_zero, Nat.zero_le, if_true, Nat.sub_zero, hc_zero, one_mul,
      List.length_cons, add_zero]
    rw [show n + 3 = (n + 2) + 1 from rfl, Nat.multichoose_succ_succ]
  | succ s =>
    simp only [g, List.length_cons, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h : 3 * s ≤ n
    · have h1 : 3 * (s + 1) ≤ n + 3 := by omega
      rw [if_pos h1, if_pos h1, if_pos h, hc_succ_cons]
      have e1 : n + 3 - 3 * (s + 1) = n - 3 * s := by omega
      have eA : l.length + 1 + (s + 1) = (l.length + (s + 1)) + 1 := by ring
      have eB : l.length + 1 + s = l.length + (s + 1) := by ring
      rw [e1, eA, eB]
      by_cases h2 : 3 * (s + 1) ≤ n + 2
      · rw [if_pos h2]
        obtain ⟨r, hr⟩ : ∃ r, n - 3 * s = r + 1 := ⟨n - 3 * s - 1, by omega⟩
        have e2 : n + 2 - 3 * (s + 1) = r := by omega
        rw [e2, hr, Nat.multichoose_succ_succ (l.length + (s + 1)) r]
        ring
      · rw [if_neg h2]
        have e : n - 3 * s = 0 := by omega
        rw [e]
        simp only [Nat.multichoose_zero_right]
        ring
    · have h1 : ¬ 3 * (s + 1) ≤ n + 3 := by omega
      have h2 : ¬ 3 * (s + 1) ≤ n + 2 := by omega
      rw [if_neg h1, if_neg h1, if_neg h, if_neg h2]
      simp

theorem E_cons_add_three (v : ℕ) (l : List ℕ) (n : ℕ) :
    E (v :: l) (n + 3) = E l (n + 3) + v * E (v :: l) n + E (v :: l) (n + 2) := by
  rw [E_eq_sum (v :: l) (n := n + 3) (N := n / 3 + 2) (by omega),
    E_eq_sum l (n := n + 3) (N := n / 3 + 2) (by omega),
    E_eq_sum (v :: l) (n := n + 2) (N := n / 3 + 2) (by omega),
    E_eq_sum (v :: l) (n := n) (N := n / 3 + 1) le_rfl]
  simp only [g_rec, sum_add_distrib]
  rw [sum_range_succ' (fun s => if s = 0 then 0 else v * g (v :: l) n (s - 1))]
  simp [mul_sum]

@[simp] theorem E_zero (l : List ℕ) : E l 0 = 1 := by
  simp [E, g]

theorem E_one (l : List ℕ) : E l 1 = l.length := by
  simp [E, g]

theorem E_two (l : List ℕ) : E l 2 = Nat.multichoose l.length 2 := by
  simp [E, g]

theorem E_nil (n : ℕ) : E [] n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_ne_zero, if_false]
    unfold E
    apply sum_eq_zero
    intro s _
    unfold g
    split_ifs
    · cases s with
      | zero =>
        simp only [hc_zero, List.length_nil, Nat.add_zero, Nat.mul_zero, Nat.sub_zero, one_mul]
        exact Nat.multichoose_zero_succ n
      | succ s => simp
    · rfl

/-- 「加入最大变量」的递推（对一切 n）。 -/
theorem E_cons (v : ℕ) (l : List ℕ) (n : ℕ) :
    E (v :: l) n = E l n + (if 3 ≤ n then v * E (v :: l) (n - 3) else 0)
      + (if 1 ≤ n then E (v :: l) (n - 1) else 0) := by
  match n with
  | 0 => simp
  | 1 => simp [E_one]
  | 2 =>
    simp only [show ¬ (3 ≤ 2) by omega, if_false, add_zero, show 1 ≤ 2 by omega, if_true,
      show 2 - 1 = 1 from rfl, E_two, E_one, List.length_cons]
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.multichoose_succ_succ l.length 1,
      Nat.multichoose_one_right]
  | n + 3 =>
    rw [E_cons_add_three]
    simp only [show 3 ≤ n + 3 by omega, if_true, Nat.add_sub_cancel, show 1 ≤ n + 3 by omega,
      show n + 3 - 1 = n + 2 by omega]

theorem E_single_zero (k : ℕ) : E [0] k = 1 := by
  unfold E
  rw [sum_range_succ']
  have : ∑ s ∈ range (k / 3), g [0] k (s + 1) = 0 := by
    apply sum_eq_zero
    intro s _
    unfold g
    split_ifs <;> simp [hc_succ_single_zero]
  rw [this, zero_add]
  simp [g, Nat.multichoose_one]

/-! ### 闭式 `F m k` 满足引理 1 的递推 -/

/-- 闭式：`F m k = E [m..0] k + [k ≥ 2]·Σ_{j=1}^{m} j·E [m..j] (k−2)`。 -/
def F (m k : ℕ) : ℕ :=
  E (vars 0 m) k + if 2 ≤ k then ∑ j ∈ Icc 1 m, j * E (vars j m) (k - 2) else 0

theorem F_zero_right (m : ℕ) : F m 0 = 1 := by
  simp [F]

theorem F_zero_left (k : ℕ) : F 0 k = 1 := by
  simp [F, vars_zero_zero, E_single_zero]

theorem F_one (m : ℕ) : F (m + 1) 1 = F m 1 + F (m + 1) 0 := by
  simp only [F, show ¬ (2 ≤ 1) by omega, if_false, add_zero, show ¬ (2 ≤ 0) by omega]
  rw [vars_succ (Nat.zero_le _), E_cons]
  simp

theorem F_two (m : ℕ) : F (m + 1) 2 = F m 2 + F (m + 1) 1 + (m + 1) := by
  simp only [F, show 2 ≤ 2 by omega, if_true, show ¬ (2 ≤ 1) by omega, if_false, add_zero,
    Nat.sub_self, E_zero, mul_one]
  rw [sum_Icc_succ_top (by omega), vars_succ (Nat.zero_le _), E_cons]
  simp only [show ¬ (3 ≤ 2) by omega, if_false, add_zero, show 1 ≤ 2 by omega, if_true]
  ring

theorem F_rec (m k : ℕ) :
    F (m + 1) (k + 3) = F m (k + 3) + F (m + 1) (k + 2) + (m + 1) * F (m + 1) k := by
  unfold F
  simp only [show 2 ≤ k + 3 by omega, show 2 ≤ k + 2 by omega, if_true,
    show k + 3 - 2 = k + 1 by omega, show k + 2 - 2 = k by omega]
  rw [vars_succ (Nat.zero_le _), E_cons_add_three]
  -- 把 vars j (m+1) 展开成 (m+1) :: vars j m
  have hv : ∀ j ∈ Icc 1 (m + 1), vars j (m + 1) = (m + 1) :: vars j m := by
    intro j hj
    rw [mem_Icc] at hj
    exact vars_succ hj.2
  rw [sum_congr rfl (fun j hj => by rw [hv j hj])]
  rw [sum_congr rfl (fun j hj => by rw [hv j hj] : ∀ j ∈ Icc 1 (m + 1),
    j * E (vars j (m + 1)) k = j * E ((m + 1) :: vars j m) k)]
  -- 对每个 j 用 E_cons 展开 E ((m+1) :: vars j m) (k+1)
  have hE : ∀ j ∈ Icc 1 (m + 1), j * E ((m + 1) :: vars j m) (k + 1)
      = j * E (vars j m) (k + 1)
        + (m + 1) * (if 2 ≤ k then j * E ((m + 1) :: vars j m) (k - 2) else 0)
        + j * E ((m + 1) :: vars j m) k := by
    intro j _
    rw [E_cons]
    simp only [show 1 ≤ k + 1 by omega, if_true, Nat.add_sub_cancel]
    by_cases hk : 2 ≤ k
    · simp only [show 3 ≤ k + 1 by omega, if_true, hk, show k + 1 - 3 = k - 2 by omega]
      ring
    · simp only [show ¬ (3 ≤ k + 1) by omega, if_false, hk]
      ring
  rw [sum_congr rfl hE, sum_add_distrib, sum_add_distrib, ← mul_sum]
  -- Icc 1 (m+1) 的最后一项 j = m+1 在 E (vars j m) (k+1) 中为 0
  rw [sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun j => j * E (vars j m) (k + 1)),
    vars_self_succ, E_nil]
  simp only [Nat.succ_ne_zero, if_false, mul_zero, add_zero]
  -- 整理 if
  by_cases hk : 2 ≤ k
  · simp only [hk, if_true]
    rw [sum_congr rfl (fun j hj => by rw [hv j hj] : ∀ j ∈ Icc 1 (m + 1),
      j * E (vars j (m + 1)) (k - 2) = j * E ((m + 1) :: vars j m) (k - 2))]
    ring
  · simp only [hk, if_false, sum_const_zero, mul_zero, add_zero]
    ring

/-! ### 主定理 -/

/-- `U k m` 等于闭式 `F m k`（由引理 1 归纳）。 -/
theorem U_eq_F (k m : ℕ) : U k m = F m k := by
  induction m generalizing k with
  | zero => rw [U_zero_right, F_zero_left]
  | succ m ihm =>
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      match k with
      | 0 => rw [U_zero_left, F_zero_right]
      | 1 => rw [lemma1_one, ihm 1, ihk 0 (by omega), F_one]
      | 2 => rw [lemma1_two, ihm 2, ihk 1 (by omega), F_two]; ring
      | k + 3 => rw [lemma1, ihm (k + 3), ihk (k + 2) (by omega), ihk k (by omega), F_rec]

theorem hc_vars_zero (m s : ℕ) : hc s (vars 0 m) = Nat.stirlingSecond (m + s) m := by
  induction m generalizing s with
  | zero =>
    rw [vars_zero_zero]
    cases s with
    | zero => simp
    | succ s => rw [hc_succ_single_zero]; simp
  | succ m ihm =>
    induction s with
    | zero => simp [Nat.stirlingSecond_self]
    | succ s ihs =>
      rw [vars_succ (Nat.zero_le _), hc_succ_cons, ← vars_succ (Nat.zero_le _), ihs, ihm (s + 1)]
      rw [show m + 1 + (s + 1) = (m + 1 + s) + 1 by ring,
        Nat.stirlingSecond_succ_succ (m + 1 + s) m, show m + (s + 1) = m + 1 + s by ring]
      ring

/-- **推荐显式公式（报告 T2.4）**。`H(m,s,j) = hc s (vars j m) = h_s(j,…,m)`；
二项式 `C(a,b)` 只在 `0 ≤ b ≤ a` 时出现（求和范围已截断）。 -/
theorem U_explicit (k m : ℕ) :
    U k m = (∑ s ∈ range (k / 3 + 1),
        Nat.stirlingSecond (m + s) m * Nat.choose (k + m - 2 * s) (k - 3 * s))
      + if 2 ≤ k then
          ∑ j ∈ Icc 1 m, j * ∑ s ∈ range ((k - 2) / 3 + 1),
            hc s (vars j m) * Nat.choose (k - 2 + m - j - 2 * s) (k - 2 - 3 * s)
        else 0 := by
  rw [U_eq_F, F]
  congr 1
  · unfold E
    apply sum_congr rfl
    intro s hs
    rw [mem_range] at hs
    have h3 : 3 * s ≤ k := by omega
    simp only [g, if_pos h3, length_vars (Nat.zero_le _), hc_vars_zero, Nat.multichoose_eq]
    congr 2
    omega
  · split_ifs with hk
    · apply sum_congr rfl
      intro j hj
      rw [mem_Icc] at hj
      congr 1
      unfold E
      apply sum_congr rfl
      intro s hs
      rw [mem_range] at hs
      have h3 : 3 * s ≤ k - 2 := by omega
      simp only [g, if_pos h3, length_vars (show j ≤ m + 1 by omega), Nat.multichoose_eq]
      congr 2
      omega
    · rfl

end A207123
