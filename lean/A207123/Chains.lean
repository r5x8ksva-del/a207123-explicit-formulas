import A207123.Multichain
import A207123.CLT

/-!
# 论文注记 8.16：链多项式与序复形

论文注记 8.16（`k ≥ 1`）：`Λ̄_k = Λ_k \ {0, 1}`（`0`、`1` 是全 0 行与全 1 行，`Λ_k` 的最小元与最大元）。对
`w ∈ {1,…,q}^k` 与 `1 ≤ r < q` 令 `y_r = ([w_1 > r], …, [w_k > r])`：`w` 合法当且仅当各 `y_r ∈ Λ_k`，`w` 用到每个
字母 `1,…,q` 当且仅当 `1 > y_1 > ⋯ > y_{q−1} > 0`，并且 `w_j = 1 + #{r : (y_r)_j = 1}`。所以 `N(k,q)` 是 `Λ̄_k` 中
`q − 1` 元链的个数（`numChainsBar_eq_N`、`N_eq_numChainsBar`），`n_k` 是 `Λ̄_k` 的链多项式（`nR_eq_chainPoly`），
`h_k` 是序复形 `Δ(Λ̄_k)`（维数 `k − 2`，`numChainsBar_eq_zero`、`numChainsBar_pos`）的 `h`-多项式
（`hpoly_eq_hPoly_orderComplex`）。若一个 `d − 1` 维序复形的 `h`-多项式系数非负，则链多项式
`(1+z)^d h(z/(1+z))` 在 `(−∞, −1)` 中没有零点（`no_root_lt_neg_one`）；`n_k` 在那里有 `⌊k/3⌋` 个零点
（`nBelow_nR`，`RootLocation.lean`），所以 `k ≥ 3` 时 `h_k` 有负系数（`hpoly_exists_coeff_neg`）。

链按从大到小排列成 `y_1 > y_2 > ⋯ > y_n`（`StrictAnti`），这样一条 `n` 元链对应唯一一个序列。证明复用
`Multichain.lean` 的高度表述：`y_1 ≥ ⋯ ≥ y_n` 对应各列 1 的个数 `h_j = w_j − 1`（`colMat`、`colHeight`），
严格递减且不含 `0`、`1` 当且仅当 `h` 取遍 `0,…,n`（`surjective_iff_colMat`）。

未形式化（论文是引用）：Boolean 格 `{0,1}^k` 的类比（`(m+1)^k`、`q!·S(k,q)` 与 Euler 多项式）；`h`-多项式有负系数
推出序复形不是 Cohen–Macaulay 的（Stanley）；[BL26] 关于 TN 偏序集与 `P`-正偏序集的结果。
-/

namespace A207123

open Polynomial Finset

noncomputable section

/-! ## 1. `Λ_k` 的最小元、最大元与 `Λ̄_k` 中的链 -/

/-- `Λ_k` 的最小元 `0`（全 0 行），它是允许行。 -/
def lamBot (k : ℕ) : Lam k := ⟨fun _ => false, fun _ _ => ⟨by simp, by simp⟩⟩

/-- `Λ_k` 的最大元 `1`（全 1 行），它是允许行。 -/
def lamTop (k : ℕ) : Lam k := ⟨fun _ => true, fun _ _ => ⟨by simp, by simp⟩⟩

theorem lamBot_le (k : ℕ) (x : Lam k) : lamBot k ≤ x := fun _ => Bool.false_le _

theorem le_lamTop (k : ℕ) (x : Lam k) : x ≤ lamTop k := fun _ => Bool.le_true _

open Classical in
/-- `Λ̄_k = Λ_k \ {0, 1}` 中 `n` 元链的个数（链从大到小排列成 `y_1 > y_2 > ⋯ > y_n`）。 -/
def numChainsBar (k n : ℕ) : ℕ :=
  Fintype.card {c : Fin n → Lam k // StrictAnti c ∧ ∀ i, c i ≠ lamBot k ∧ c i ≠ lamTop k}

/-! ## 2. 高度：严格递减且不含 `0`、`1` ⟺ 取遍所有高度 -/

theorem bool_lt_iff (a b : Bool) : a < b ↔ a = false ∧ b = true := by
  cases a <;> cases b <;> decide

/-- 由高度 `h : Fin k → {0,…,n}` 拼出的 `n` 行矩阵（第 `i` 行是 `y_{i+1}`）逐行严格递减、没有全 0 行与全 1 行，
当且仅当 `h` 取遍 `0,…,n`（`k ≥ 1`）。 -/
theorem surjective_iff_colMat {k n : ℕ} (hk : 1 ≤ k) (h : Fin k → Fin (n + 1)) :
    Function.Surjective h ↔
      StrictAnti (colMat h) ∧ ∀ i, colMat h i ≠ (fun _ => false) ∧ colMat h i ≠ (fun _ => true) := by
  constructor
  · intro hs
    refine ⟨fun i i' hii' => ?_, fun i => ⟨fun heq => ?_, fun heq => ?_⟩⟩
    · refine lt_of_le_of_ne (antitone_colMat h hii'.le) fun heq => ?_
      obtain ⟨j, hj⟩ := hs ⟨i'.val, by omega⟩
      have hj' : (h j : ℕ) = i' := by rw [hj]
      have h1 := congrFun heq j
      have hlt : (i : ℕ) < i' := hii'
      simp only [colMat, hj'] at h1
      simp [hlt] at h1
    · obtain ⟨j, hj⟩ := hs (Fin.last n)
      have hj' : (h j : ℕ) = n := by rw [hj, Fin.val_last]
      have h1 := congrFun heq j
      have hlt : (i : ℕ) < n := i.isLt
      simp only [colMat, hj'] at h1
      simp [hlt] at h1
    · obtain ⟨j, hj⟩ := hs 0
      have hj' : (h j : ℕ) = 0 := by rw [hj, Fin.val_zero]
      have h1 := congrFun heq j
      simp only [colMat, hj'] at h1
      simp at h1
  · rintro ⟨hsa, hne⟩ v
    by_cases hn : n = 0
    · subst hn
      refine ⟨⟨0, hk⟩, Fin.ext ?_⟩
      have h1 := (h ⟨0, hk⟩).isLt
      have h2 := v.isLt
      omega
    have hv := v.isLt
    rcases Nat.eq_zero_or_pos v.val with hv0 | hv0
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 (hne ⟨0, by omega⟩).2
      simp only [colMat] at hj
      have h0 : ¬ (0 < (h j : ℕ)) := by simpa using hj
      exact ⟨j, Fin.ext (by omega)⟩
    · rcases Nat.lt_or_ge v.val n with hvn | hvn
      · have hlt := hsa (show (⟨v.val - 1, by omega⟩ : Fin n) < ⟨v.val, hvn⟩ by
          rw [Fin.mk_lt_mk]
          omega)
        rw [Pi.lt_def] at hlt
        obtain ⟨-, j, hj⟩ := hlt
        rw [bool_lt_iff] at hj
        simp only [colMat, decide_eq_false_iff_not, decide_eq_true_eq] at hj
        exact ⟨j, Fin.ext (by omega)⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 (hne ⟨n - 1, by omega⟩).1
        simp only [colMat] at hj
        have h1 : n - 1 < (h j : ℕ) := by simpa using hj
        have h2 := (h j).isLt
        exact ⟨j, Fin.ext (by omega)⟩

open Classical in
/-- `Λ̄_k` 中的 `n` 元链 ↔ 取遍 `0,…,n` 的合法高度向量（`k ≥ 1`）。 -/
theorem numChainsBar_eq_card_heights {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    numChainsBar k n =
      Fintype.card {h : Fin k → Fin (n + 1) // LegalF h ∧ Function.Surjective h} := by
  unfold numChainsBar
  refine Fintype.card_congr
    { toFun := fun c => ⟨colHeight (fun i => (c.1 i).1), ?_, ?_⟩
      invFun := fun h => ⟨fun i => ⟨colMat h.1 i, (allowed_colMat_iff h.1).mpr h.2.1 i⟩, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- 合法
    have hanti : Antitone (fun i => (c.1 i).1) := fun i i' hii' => c.2.1.antitone hii'
    have hA : ∀ i, AllowedRow (colMat (colHeight fun i => (c.1 i).1) i) := by
      rw [colMat_colHeight hanti]
      exact fun i => (c.1 i).2
    exact (allowed_colMat_iff _).mp hA
  · -- 取遍所有高度
    have hanti : Antitone (fun i => (c.1 i).1) := fun i i' hii' => c.2.1.antitone hii'
    rw [surjective_iff_colMat hk, colMat_colHeight hanti]
    refine ⟨fun i i' hii' => Subtype.coe_lt_coe.2 (c.2.1 hii'), fun i => ⟨fun heq => ?_, fun heq => ?_⟩⟩
    · exact (c.2.2 i).1 (Subtype.ext heq)
    · exact (c.2.2 i).2 (Subtype.ext heq)
  · -- 严格递减
    have hs := (surjective_iff_colMat hk h.1).mp h.2.2
    exact fun i i' hii' => Subtype.coe_lt_coe.1 (hs.1 hii')
  · -- 不含 0、1
    have hs := (surjective_iff_colMat hk h.1).mp h.2.2
    intro i
    exact ⟨fun heq => (hs.2 i).1 (congrArg Subtype.val heq),
      fun heq => (hs.2 i).2 (congrArg Subtype.val heq)⟩
  · intro c
    have hanti : Antitone (fun i => (c.1 i).1) := fun i i' hii' => c.2.1.antitone hii'
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (colMat_colHeight hanti) i
  · intro h
    apply Subtype.ext
    exact colHeight_colMat h.1

/-! ## 3. 高度 ↔ 词 -/

theorem good_succ_iff (a b c : ℕ) : Good (a + 1) (b + 1) (c + 1) ↔ Good a b c := by
  unfold Good
  omega

theorem legal_ofFn_succ_iff {k m : ℕ} (h : Fin k → Fin (m + 1)) :
    Legal (List.ofFn fun j => (h j : ℕ) + 1) ↔ LegalF h := by
  rw [legal_iff_getElem]
  simp only [List.length_ofFn, List.getElem_ofFn, LegalF, good_succ_iff]

open Classical in
/-- 取遍 `0,…,m` 的合法高度向量 ↔ 长 `k`、值域恰为 `{1,…,m+1}` 的合法词（`w_j = h_j + 1`）。 -/
theorem card_legalF_surjective (k m : ℕ) :
    Fintype.card {h : Fin k → Fin (m + 1) // LegalF h ∧ Function.Surjective h} = N k (m + 1) := by
  unfold N
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun h => ⟨List.ofFn fun j => (h.1 j : ℕ) + 1, ?_⟩
      invFun := fun l => ⟨fun j => ⟨l.1[j.val]'?_ - 1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mem_NW]
    refine ⟨by simp, (legal_ofFn_succ_iff h.1).mpr h.2.1, ?_⟩
    ext v
    rw [List.mem_toFinset, List.mem_ofFn, Finset.mem_Icc]
    constructor
    · rintro ⟨j, rfl⟩
      have := (h.1 j).isLt
      omega
    · intro hv
      obtain ⟨j, hj⟩ := h.2.2 ⟨v - 1, by omega⟩
      refine ⟨j, ?_⟩
      rw [hj]
      simp only
      omega
  · have := (mem_NW.mp l.2).1
    omega
  · have hl := mem_NW.mp l.2
    have hmem : l.1[j.val]'(by omega) ∈ l.1.toFinset := List.mem_toFinset.2 (List.getElem_mem _)
    rw [hl.2.2, Finset.mem_Icc] at hmem
    omega
  · have hl := mem_NW.mp l.2
    have hge : ∀ (i : ℕ) (hi : i < l.1.length), 1 ≤ l.1[i] := by
      intro i hi
      have hmem : l.1[i] ∈ l.1.toFinset := List.mem_toFinset.2 (List.getElem_mem _)
      rw [hl.2.2, Finset.mem_Icc] at hmem
      exact hmem.1
    refine ⟨?_, fun v => ?_⟩
    · rw [← legal_ofFn_succ_iff]
      have e : (List.ofFn fun j : Fin k => ((l.1[j.val]'(by omega) - 1 : ℕ)) + 1) = l.1 := by
        apply List.ext_getElem
        · simp [hl.1]
        · intro i h1 h2
          simp only [List.getElem_ofFn]
          have := hge i h2
          omega
      simp only
      rw [e]
      exact hl.2.1
    · have hmem : (v : ℕ) + 1 ∈ l.1.toFinset := by
        rw [hl.2.2, Finset.mem_Icc]
        have := v.isLt
        omega
      obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 (List.mem_toFinset.1 hmem)
      refine ⟨⟨i, by omega⟩, Fin.ext ?_⟩
      simp only
      omega
  · intro h
    apply Subtype.ext
    funext j
    apply Fin.ext
    simp
  · intro l
    apply Subtype.ext
    have hl := mem_NW.mp l.2
    apply List.ext_getElem
    · simp [hl.1]
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      have hmem : l.1[i] ∈ l.1.toFinset := List.mem_toFinset.2 (List.getElem_mem _)
      rw [hl.2.2, Finset.mem_Icc] at hmem
      omega

/-! ## 4. 论文注记 8.16 -/

/-- 论文注记 8.16：`k ≥ 1` 时 `Λ̄_k` 中 `n` 元链的个数是 `N(k, n+1)`。 -/
theorem numChainsBar_eq_N {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : numChainsBar k n = N k (n + 1) := by
  rw [numChainsBar_eq_card_heights hk, card_legalF_surjective]

/-- 论文注记 8.16：`k, q ≥ 1` 时 `N(k,q)` 是 `Λ̄_k` 中 `q − 1` 元链的个数。 -/
theorem N_eq_numChainsBar {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) : N k q = numChainsBar k (q - 1) := by
  rw [numChainsBar_eq_N hk, Nat.sub_add_cancel hq]

/-- `Λ̄_k` 中没有 `k` 元以上的链。 -/
theorem numChainsBar_eq_zero {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) : numChainsBar k n = 0 := by
  rw [numChainsBar_eq_N hk]
  exact N_eq_zero_of_lt (by omega)

/-- `Λ̄_k` 中有 `k − 1` 元链（所以序复形 `Δ(Λ̄_k)` 的维数是 `k − 2`）。 -/
theorem numChainsBar_pos {k : ℕ} (hk : 1 ≤ k) : 0 < numChainsBar k (k - 1) := by
  rw [numChainsBar_eq_N hk, Nat.sub_add_cancel hk]
  exact N_self_pos k

/-- 论文注记 8.16：`n_k` 是 `Λ̄_k` 的链多项式 `Σ_n (n 元链的个数)·z^n`（`n < k`；更长的链不存在，
`numChainsBar_eq_zero`）。 -/
theorem nR_eq_chainPoly {k : ℕ} (hk : 1 ≤ k) :
    nR k = ∑ n ∈ Finset.range k, C (numChainsBar k n : ℝ) * X ^ n := by
  rw [nR]
  refine Finset.sum_nbij' (fun q => q - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_range]
    omega
  · intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc]
    omega
  · intro q hq
    rw [Finset.mem_Icc] at hq
    omega
  · intro n _
    omega
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [N_eq_numChainsBar hk hq.1]

/-- 论文注记 8.16：`h_k` 是序复形 `Δ(Λ̄_k)`（`d − 1 = k − 2` 维）的 `h`-多项式
`Σ_{i=0}^{d} f_{i−1} t^i (1−t)^{d−i}`，`d = k − 1`，`f_{i−1}` 是 `i` 个顶点的面（`i` 元链）的个数。 -/
theorem hpoly_eq_hPoly_orderComplex {k : ℕ} (hk : 1 ≤ k) :
    hpoly k = ∑ i ∈ Finset.range k, C (numChainsBar k i : ℚ) * X ^ i * (1 - X) ^ (k - 1 - i) := by
  rw [hpoly_of_one_le hk]
  refine Finset.sum_nbij' (fun q => q - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_range]
    omega
  · intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc]
    omega
  · intro q hq
    rw [Finset.mem_Icc] at hq
    omega
  · intro n _
    omega
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [N_eq_numChainsBar hk hq.1, show k - 1 - (q - 1) = k - q by omega]

/-- 系数非负的非零多项式在正数处取正值。 -/
theorem eval_pos_of_coeff_nonneg {p : ℝ[X]} (hp : p ≠ 0) (hc : ∀ i, 0 ≤ p.coeff i) {x : ℝ}
    (hx : 0 < x) : 0 < p.eval x := by
  rw [eval_eq_sum_range]
  have hlc : 0 < p.leadingCoeff := lt_of_le_of_ne (hc _) (Ne.symm (leadingCoeff_ne_zero.2 hp))
  calc 0 < p.leadingCoeff * x ^ p.natDegree := mul_pos hlc (pow_pos hx _)
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i :=
        Finset.single_le_sum (f := fun i => p.coeff i * x ^ i)
          (fun i _ => mul_nonneg (hc i) (pow_nonneg hx.le i)) (Finset.self_mem_range_succ _)

/-- 论文注记 8.16：`h ≠ 0` 的系数都非负时，`f(z) = (1+z)^d h(z/(1+z))` 在 `(−∞, −1)` 中没有零点
（`z < −1` 时 `z/(1+z) > 1`，`h` 在那里取正值）。 -/
theorem no_root_lt_neg_one {h f : ℝ[X]} (d : ℕ) (hh : h ≠ 0) (hc : ∀ i, 0 ≤ h.coeff i)
    (hf : ∀ z : ℝ, 1 + z ≠ 0 → f.eval z = (1 + z) ^ d * h.eval (z / (1 + z))) {z : ℝ} (hz : z < -1) :
    f.eval z ≠ 0 := by
  have h1 : 1 + z ≠ 0 := by
    intro h0
    linarith
  rw [hf z h1]
  exact mul_ne_zero (pow_ne_zero _ h1)
    (eval_pos_of_coeff_nonneg hh hc (div_pos_of_neg_of_neg (by linarith) (by linarith))).ne'

/-- 论文注记 8.16：`k ≥ 3` 时 `h_k` 有负系数（`n_k` 在 `(−∞, −1)` 中有 `⌊k/3⌋ ≥ 1` 个零点，`nBelow_nR`）。 -/
theorem hpoly_exists_coeff_neg {k : ℕ} (hk : 3 ≤ k) : ∃ i, (hpoly k).coeff i < 0 := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hc : ∀ i, 0 ≤ (hR k).coeff i := fun i => by
    rw [hR, coeff_map, eq_ratCast]
    exact_mod_cast hcon i
  have hnb := nBelow_nR (k := k) (by omega)
  have hpos : 0 < nBelow (nR k) (-1) := by
    rw [hnb]
    omega
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  rw [Multiset.mem_filter] at hz
  exact no_root_lt_neg_one (k - 1) (hR_ne_zero k) hc (fun w hw => nR_eval_hR (by omega) w hw) hz.2
    (isRoot_of_mem_roots hz.1)

end

end A207123
