import A207123.Parity
import A207123.RootExpansion

/-!
# 论文注记 3.5（OEIS 条目）：能形式化的部分

论文注记 3.5 有四句数学陈述，这里形式化其中三句；第四句是精确算术核对，不在 Lean 里。

* **列**：A207118–A207122（原表第 k = 3,…,7 列）里记的经验递推，特征多项式恰为
  `(x−1)^{2k+1}(x+1)^{2k−1}`，所以由推论 3.4 对一切 n 成立。`parDen_three` … `parDen_seven`：
  `(1−x)^{2k+1}(1+x)^{2k−1}`（推论 3.4 的形式化 `Parity.lean` 里的 `parDen k`）的系数恰是 OEIS 递推系数取反、
  首项补 1（等价于特征多项式恰为 `(x−1)^{2k+1}(x+1)^{2k−1}`）；`oeis_A207118` … `oeis_A207122`：OEIS 的经验递推
  按原样对一切 `n ≥ 4k` 成立。五个定理的陈述与系数表由 `code/main_extra/oeis_columns_lean.py` 从 OEIS 快照
  `data/lit/oeis/A207118.txt` … `A207122.txt` 的 `%F Empirical` 一行逐字生成（脚本同时在 Python 里核对系数）。
* **行**：`a_k(n) = U_k(⌈n/2⌉)·U_k(⌊n/2⌋)`（`a_eq`），两个因子各满足 `3⌈n/2⌉+1`、`3⌊n/2⌋+1` 阶递推
  （定理 3.2(2)；`min_order` 与 `thm_asym_two`）。`row_rec`：乘积 `k ↦ a_k(n)` 满足
  `Δ_n = (3⌈n/2⌉+1)(3⌊n/2⌋+1)` 阶首一常系数递推，对一切 `k ≥ 0` 成立（特征多项式 `rowPoly n` 是
  `∏ (X − στ)`，`σ`、`τ` 取遍两个因子的特征根）；`row_rec_of_consecutive`：任何常系数递推只要在 `Δ_n` 个
  相邻的 `k` 上成立，就对其后的一切 `k` 成立。这是论文核对行递推所用的判据。
* **标题**：A207069、A207070 的标题写的列规则是 001/101，而不是 001/011；两行、三行时两种规则给出同样的数
  （`aAlt_two`：两行时两种列规则都是空条件；`aAlt_three`：交换前两行把一种规则变成另一种）。

本文件没有形式化的：注记里「用这一判据，以精确算术核对了行 n = 2,…,7 的经验递推（A207069、A207070、
A207124–A207127）对一切 k 成立，Berlekamp–Massey 给出的阶 10、22、28、49、55、85 是最小的，并且等于两个因子的
特征根之积中不同值的个数」这一句（数值计算；前半句后来在 `OeisRows.lean`、后半句在 `OeisRowOrders.lean` 形式化）；
对 [DBKTZ] 定理 2 的引用（没有形式化）。

`a k n` 是 `Reduction.lean` 中按原题定义的 n 行 k 列 0/1 矩阵个数。列条目 A207118–A207122 的 `a(n)` 是 `a k n`
（k = 3,…,7 固定，n 是行数）；行条目 A207069、A207070 的 `a(n)` 是 n 列矩阵的个数，即这里的 `aAlt n 2`、
`aAlt n 3`。OEIS 从 `n = 1` 编号；这里的列递推对一切 `n ≥ 4k` 成立，还含用到 `a_k(0) = 1`（零行矩阵只有
一个）的 `n = 4k`。
-/

namespace A207123

open Polynomial Finset

/-! ## 列：A207118–A207122 -/

/-- 系数表 `l = [d_0, d_1, …]` 对应的多项式 `Σ_i d_i X^i`。 -/
noncomputable def ofList (l : List ℤ) : ℚ[X] := ∑ i ∈ range l.length, C ((l.getD i 0 : ℤ) : ℚ) * X ^ i

/-- 辅助引理（注记 3.5）：`ofList l` 的第 `i` 项系数是 `l` 的第 `i` 项。 -/
theorem coeff_ofList (l : List ℤ) {i : ℕ} (hi : i < l.length) : (ofList l).coeff i = (l.getD i 0 : ℚ) := by
  rw [ofList, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hi)]

/-- 辅助引理（注记 3.5）：`(1−x)^{2k+1}(1+x)^{2k−1} = Σ_i l_i x^i`（`l` 有 `4k+1` 项）时，
`Σ_{i=0}^{4k} l_i·a_k(n−i) = 0` 对一切 `n ≥ 4k` 成立（推论 3.4 的递推 `parity_recurrence`）。 -/
theorem col_rec {k : ℕ} (hk : 1 ≤ k) {l : List ℤ} (hD : parDen k = ofList l) (hl : l.length = 4 * k + 1)
    {n : ℕ} (hn : 4 * k ≤ n) : ∑ i ∈ range (4 * k + 1), (l.getD i 0 : ℚ) * (a k (n - i) : ℚ) = 0 := by
  rw [← parity_recurrence k hk n hn]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hD, coeff_ofList l (by rw [hl]; exact Finset.mem_range.mp hi)]
/-- 第 k = 3 列：`(1−x)^7(1+x)^5` 的系数（A207118 的经验递推的系数取反，首项 1）。 -/
theorem parDen_three :
    parDen 3 = ofList [1, -2, -4, 10, 5, -20, 0, 20, -5, -10, 4, 2, -1] := by
  simp [parDen, ofList, Finset.sum_range_succ]
  ring

/-- **注记 3.5**（A207118，第 k = 3 列）：OEIS 记的经验递推
`a(n) = 2*a(n-1) +4*a(n-2) -10*a(n-3) -5*a(n-4) +20*a(n-5) -20*a(n-7) +5*a(n-8) +10*a(n-9) -4*a(n-10)
-2*a(n-11) +a(n-12)`
对一切 `n ≥ 12` 成立（OEIS 从 `n = 1` 编号；这里还含用到 `a_3(0) = 1` 的 `n = 12`）。 -/
theorem oeis_A207118 (n : ℕ) (hn : 12 ≤ n) :
    (a 3 n : ℤ) = 2 * a 3 (n - 1) + 4 * a 3 (n - 2) - 10 * a 3 (n - 3) - 5 * a 3 (n - 4) + 20 * a 3 (n - 5)
      - 20 * a 3 (n - 7) + 5 * a 3 (n - 8) + 10 * a 3 (n - 9) - 4 * a 3 (n - 10) - 2 * a 3 (n - 11)
      + a 3 (n - 12) := by
  have h := col_rec (by norm_num) parDen_three rfl hn
  simp [Finset.sum_range_succ] at h
  qify
  linarith

/-- 第 k = 4 列：`(1−x)^9(1+x)^7` 的系数（A207119 的经验递推的系数取反，首项 1）。 -/
theorem parDen_four :
    parDen 4 = ofList [1, -2, -6, 14, 14, -42, -14, 70, 0, -70, 14, 42, -14, -14, 6, 2, -1] := by
  simp [parDen, ofList, Finset.sum_range_succ]
  ring

/-- **注记 3.5**（A207119，第 k = 4 列）：OEIS 记的经验递推
`a(n) = 2*a(n-1) +6*a(n-2) -14*a(n-3) -14*a(n-4) +42*a(n-5) +14*a(n-6) -70*a(n-7) +70*a(n-9) -14*a(n-10)
-42*a(n-11) +14*a(n-12) +14*a(n-13) -6*a(n-14) -2*a(n-15) +a(n-16)`
对一切 `n ≥ 16` 成立（OEIS 从 `n = 1` 编号；这里还含用到 `a_4(0) = 1` 的 `n = 16`）。 -/
theorem oeis_A207119 (n : ℕ) (hn : 16 ≤ n) :
    (a 4 n : ℤ) = 2 * a 4 (n - 1) + 6 * a 4 (n - 2) - 14 * a 4 (n - 3) - 14 * a 4 (n - 4) + 42 * a 4 (n - 5)
      + 14 * a 4 (n - 6) - 70 * a 4 (n - 7) + 70 * a 4 (n - 9) - 14 * a 4 (n - 10) - 42 * a 4 (n - 11)
      + 14 * a 4 (n - 12) + 14 * a 4 (n - 13) - 6 * a 4 (n - 14) - 2 * a 4 (n - 15) + a 4 (n - 16) := by
  have h := col_rec (by norm_num) parDen_four rfl hn
  simp [Finset.sum_range_succ] at h
  qify
  linarith

/-- 第 k = 5 列：`(1−x)^11(1+x)^9` 的系数（A207120 的经验递推的系数取反，首项 1）。 -/
theorem parDen_five :
    parDen 5 = ofList [1, -2, -8, 18, 27, -72, -48, 168, 42, -252, 0, 252, -42, -168, 48, 72, -27, -18, 8, 2,
      -1] := by
  simp [parDen, ofList, Finset.sum_range_succ]
  ring

/-- **注记 3.5**（A207120，第 k = 5 列）：OEIS 记的经验递推
`a(n) = 2*a(n-1) +8*a(n-2) -18*a(n-3) -27*a(n-4) +72*a(n-5) +48*a(n-6) -168*a(n-7) -42*a(n-8) +252*a(n-9)
-252*a(n-11) +42*a(n-12) +168*a(n-13) -48*a(n-14) -72*a(n-15) +27*a(n-16) +18*a(n-17) -8*a(n-18) -2*a(n-19)
+a(n-20)`
对一切 `n ≥ 20` 成立（OEIS 从 `n = 1` 编号；这里还含用到 `a_5(0) = 1` 的 `n = 20`）。 -/
theorem oeis_A207120 (n : ℕ) (hn : 20 ≤ n) :
    (a 5 n : ℤ) = 2 * a 5 (n - 1) + 8 * a 5 (n - 2) - 18 * a 5 (n - 3) - 27 * a 5 (n - 4) + 72 * a 5 (n - 5)
      + 48 * a 5 (n - 6) - 168 * a 5 (n - 7) - 42 * a 5 (n - 8) + 252 * a 5 (n - 9) - 252 * a 5 (n - 11)
      + 42 * a 5 (n - 12) + 168 * a 5 (n - 13) - 48 * a 5 (n - 14) - 72 * a 5 (n - 15) + 27 * a 5 (n - 16)
      + 18 * a 5 (n - 17) - 8 * a 5 (n - 18) - 2 * a 5 (n - 19) + a 5 (n - 20) := by
  have h := col_rec (by norm_num) parDen_five rfl hn
  simp [Finset.sum_range_succ] at h
  qify
  linarith

/-- 第 k = 6 列：`(1−x)^13(1+x)^11` 的系数（A207121 的经验递推的系数取反，首项 1）。 -/
theorem parDen_six :
    parDen 6 = ofList [1, -2, -10, 22, 44, -110, -110, 330, 165, -660, -132, 924, 0, -924, 132, 660, -165,
      -330, 110, 110, -44, -22, 10, 2, -1] := by
  simp [parDen, ofList, Finset.sum_range_succ]
  ring

/-- **注记 3.5**（A207121，第 k = 6 列）：OEIS 记的经验递推
`a(n) = 2*a(n-1) +10*a(n-2) -22*a(n-3) -44*a(n-4) +110*a(n-5) +110*a(n-6) -330*a(n-7) -165*a(n-8) +660*a(n-9)
+132*a(n-10) -924*a(n-11) +924*a(n-13) -132*a(n-14) -660*a(n-15) +165*a(n-16) +330*a(n-17) -110*a(n-18)
-110*a(n-19) +44*a(n-20) +22*a(n-21) -10*a(n-22) -2*a(n-23) +a(n-24)`
对一切 `n ≥ 24` 成立（OEIS 从 `n = 1` 编号；这里还含用到 `a_6(0) = 1` 的 `n = 24`）。 -/
theorem oeis_A207121 (n : ℕ) (hn : 24 ≤ n) :
    (a 6 n : ℤ) = 2 * a 6 (n - 1) + 10 * a 6 (n - 2) - 22 * a 6 (n - 3) - 44 * a 6 (n - 4) + 110 * a 6 (n - 5)
      + 110 * a 6 (n - 6) - 330 * a 6 (n - 7) - 165 * a 6 (n - 8) + 660 * a 6 (n - 9) + 132 * a 6 (n - 10)
      - 924 * a 6 (n - 11) + 924 * a 6 (n - 13) - 132 * a 6 (n - 14) - 660 * a 6 (n - 15) + 165 * a 6 (n - 16)
      + 330 * a 6 (n - 17) - 110 * a 6 (n - 18) - 110 * a 6 (n - 19) + 44 * a 6 (n - 20) + 22 * a 6 (n - 21)
      - 10 * a 6 (n - 22) - 2 * a 6 (n - 23) + a 6 (n - 24) := by
  have h := col_rec (by norm_num) parDen_six rfl hn
  simp [Finset.sum_range_succ] at h
  qify
  linarith

/-- 第 k = 7 列：`(1−x)^15(1+x)^13` 的系数（A207122 的经验递推的系数取反，首项 1）。 -/
theorem parDen_seven :
    parDen 7 = ofList [1, -2, -12, 26, 65, -156, -208, 572, 429, -1430, -572, 2574, 429, -3432, 0, 3432, -429,
      -2574, 572, 1430, -429, -572, 208, 156, -65, -26, 12, 2, -1] := by
  simp [parDen, ofList, Finset.sum_range_succ]
  ring

/-- **注记 3.5**（A207122，第 k = 7 列）：OEIS 记的经验递推
`a(n) = 2*a(n-1) +12*a(n-2) -26*a(n-3) -65*a(n-4) +156*a(n-5) +208*a(n-6) -572*a(n-7) -429*a(n-8) +1430*a(n-9)
+572*a(n-10) -2574*a(n-11) -429*a(n-12) +3432*a(n-13) -3432*a(n-15) +429*a(n-16) +2574*a(n-17) -572*a(n-18)
-1430*a(n-19) +429*a(n-20) +572*a(n-21) -208*a(n-22) -156*a(n-23) +65*a(n-24) +26*a(n-25) -12*a(n-26)
-2*a(n-27) +a(n-28)`
对一切 `n ≥ 28` 成立（OEIS 从 `n = 1` 编号；这里还含用到 `a_7(0) = 1` 的 `n = 28`）。 -/
theorem oeis_A207122 (n : ℕ) (hn : 28 ≤ n) :
    (a 7 n : ℤ) = 2 * a 7 (n - 1) + 12 * a 7 (n - 2) - 26 * a 7 (n - 3) - 65 * a 7 (n - 4) + 156 * a 7 (n - 5)
      + 208 * a 7 (n - 6) - 572 * a 7 (n - 7) - 429 * a 7 (n - 8) + 1430 * a 7 (n - 9) + 572 * a 7 (n - 10)
      - 2574 * a 7 (n - 11) - 429 * a 7 (n - 12) + 3432 * a 7 (n - 13) - 3432 * a 7 (n - 15)
      + 429 * a 7 (n - 16) + 2574 * a 7 (n - 17) - 572 * a 7 (n - 18) - 1430 * a 7 (n - 19)
      + 429 * a 7 (n - 20) + 572 * a 7 (n - 21) - 208 * a 7 (n - 22) - 156 * a 7 (n - 23) + 65 * a 7 (n - 24)
      + 26 * a 7 (n - 25) - 12 * a 7 (n - 26) - 2 * a 7 (n - 27) + a 7 (n - 28) := by
  have h := col_rec (by norm_num) parDen_seven rfl hn
  simp [Finset.sum_range_succ] at h
  qify
  linarith

/-! ## 行：递推的阶与核对判据 -/

/-- 行 `n` 的阶 `Δ_n = (3⌈n/2⌉+1)(3⌊n/2⌋+1)`。 -/
def rowOrd (n : ℕ) : ℕ := (3 * ((n + 1) / 2) + 1) * (3 * (n / 2) + 1)

/-- 行 `n` 的特征多项式 `∏ (X − στ)`，`(σ, τ)` 取遍 `sig ⌈n/2⌉ × sig ⌊n/2⌋`（定理 3.2(2) 的特征根）。 -/
noncomputable def rowPoly (n : ℕ) : ℂ[X] := ∏ p ∈ sig ((n + 1) / 2) ×ˢ sig (n / 2), (X - C (p.1 * p.2))

/-- 辅助引理（注记 3.5）：`rowPoly n` 首一。 -/
theorem rowPoly_monic (n : ℕ) : (rowPoly n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- 辅助引理（注记 3.5）：`rowPoly n` 的次数是 `Δ_n`。 -/
theorem natDegree_rowPoly (n : ℕ) : (rowPoly n).natDegree = rowOrd n := by
  rw [rowPoly, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_product]
  rw [(thm_asym_two _).1, (thm_asym_two _).1, rowOrd]

/-- 辅助引理（注记 3.5）：`rowPoly n` 的 `X^{Δ_n}` 系数是 1。 -/
theorem coeff_rowPoly_top (n : ℕ) : (rowPoly n).coeff (rowOrd n) = 1 := by
  have h := (rowPoly_monic n).coeff_natDegree
  rwa [natDegree_rowPoly] at h

/-- 辅助引理（注记 3.5）：`a_k(n) = Σ_{σ,τ} α_{⌈n/2⌉}(σ)·α_{⌊n/2⌋}(τ)·(στ)^k`（`a_eq` 与定理 3.2(2)）。 -/
theorem a_row_expansion (n k : ℕ) :
    (a k n : ℂ) = ∑ p ∈ sig ((n + 1) / 2) ×ˢ sig (n / 2),
      alpha ((n + 1) / 2) p.1 * alpha (n / 2) p.2 * (p.1 * p.2) ^ k := by
  rw [a_eq, Nat.cast_mul, (thm_asym_two ((n + 1) / 2)).2.2 k, (thm_asym_two (n / 2)).2.2 k,
    Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  dsimp only
  ring

/-- **注记 3.5**（行递推的阶）：`k ↦ a_k(n)` 满足 `Δ_n = (3⌈n/2⌉+1)(3⌊n/2⌋+1)` 阶的首一常系数递推
`Σ_{i=0}^{Δ_n} γ_i·a_{k+i}(n) = 0`（`γ_i` 是 `rowPoly n` 的系数，`γ_{Δ_n} = 1`），对一切 `k ≥ 0` 成立。 -/
theorem row_rec (n k : ℕ) :
    ∑ i ∈ range (rowOrd n + 1), (rowPoly n).coeff i * (a (k + i) n : ℂ) = 0 := by
  simp_rw [a_row_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hroot : (rowPoly n).eval (p.1 * p.2) = 0 := by
    rw [rowPoly, eval_prod]
    exact Finset.prod_eq_zero hp (by rw [eval_sub, eval_X, eval_C, sub_self])
  rw [eval_eq_sum_range, natDegree_rowPoly] at hroot
  calc ∑ i ∈ range (rowOrd n + 1), (rowPoly n).coeff i *
        (alpha ((n + 1) / 2) p.1 * alpha (n / 2) p.2 * (p.1 * p.2) ^ (k + i))
      = alpha ((n + 1) / 2) p.1 * alpha (n / 2) p.2 * (p.1 * p.2) ^ k *
          ∑ i ∈ range (rowOrd n + 1), (rowPoly n).coeff i * (p.1 * p.2) ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by rw [hroot, mul_zero]

/-- **注记 3.5**（核对判据）：设 `c_0, …, c_r ∈ ℂ`。若 `Σ_{j=0}^{r} c_j·a_{k+j}(n) = 0` 对 `Δ_n` 个相邻的
`k = k_0, …, k_0 + Δ_n − 1` 成立，则对一切 `k ≥ k_0` 成立。 -/
theorem row_rec_of_consecutive (n r k0 : ℕ) (c : ℕ → ℂ)
    (h : ∀ k, k0 ≤ k → k < k0 + rowOrd n → ∑ j ∈ range (r + 1), c j * (a (k + j) n : ℂ) = 0) :
    ∀ k, k0 ≤ k → ∑ j ∈ range (r + 1), c j * (a (k + j) n : ℂ) = 0 := by
  -- `e(k) = Σ_j c_j a_{k+j}(n)` 也被 `rowPoly n` 零化
  have hrec : ∀ k, ∑ i ∈ range (rowOrd n + 1),
      (rowPoly n).coeff i * ∑ j ∈ range (r + 1), c j * (a (k + i + j) n : ℂ) = 0 := by
    intro k
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc ∑ i ∈ range (rowOrd n + 1), (rowPoly n).coeff i * (c j * (a (k + i + j) n : ℂ))
        = c j * ∑ i ∈ range (rowOrd n + 1), (rowPoly n).coeff i * (a (k + j + i) n : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show k + i + j = k + j + i by omega]
          ring
      _ = 0 := by rw [row_rec n (k + j), mul_zero]
  -- 对 `k` 强归纳：`k ≥ k_0 + Δ_n` 时用 `rowPoly n` 首一，`e(k)` 由前 `Δ_n` 项决定
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hlt : k < k0 + rowOrd n
    · exact h k hk hlt
    · have h2 : ∑ i ∈ range (rowOrd n), (rowPoly n).coeff i *
          ∑ j ∈ range (r + 1), c j * (a (k - rowOrd n + i + j) n : ℂ) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_range] at hi
          rw [ih (k - rowOrd n + i) (by omega) (by omega), mul_zero]
      have h1 := hrec (k - rowOrd n)
      rw [Finset.sum_range_succ, h2, zero_add, coeff_rowPoly_top, one_mul,
        show k - rowOrd n + rowOrd n = k by omega] at h1
      exact h1

/-! ## 标题：A207069、A207070 的列规则 -/

/-- A207069、A207070 标题里的列规则：每一列从上到下读，任意连续三个位置都不是 001，也不是 101。 -/
def ColRuleAlt {n k : ℕ} (M : Mat n k) : Prop :=
  ∀ (j : Fin k) (i : ℕ) (h : i + 2 < n),
    ¬ (M ⟨i, by omega⟩ j = false ∧ M ⟨i + 1, by omega⟩ j = false ∧ M ⟨i + 2, h⟩ j = true) ∧
    ¬ (M ⟨i, by omega⟩ j = true ∧ M ⟨i + 1, by omega⟩ j = false ∧ M ⟨i + 2, h⟩ j = true)

open Classical in
/-- `aAlt k n`：满足行规则与上面的列规则的 n×k 0/1 矩阵个数（A207069 是 `aAlt k 2`，A207070 是 `aAlt k 3`，
OEIS 的 n 是这里的列数 k）。 -/
noncomputable def aAlt (k n : ℕ) : ℕ := Fintype.card {M : Mat n k // RowRule M ∧ ColRuleAlt M}

open Classical in
/-- **注记 3.5**（A207069 的标题）：两行时两种列规则都是空条件，`aAlt k 2 = a k 2`。 -/
theorem aAlt_two (k : ℕ) : aAlt k 2 = a k 2 := by
  unfold aAlt a
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun M => and_congr_right fun _ =>
    ⟨fun _ _ i h => absurd h (by omega), fun _ _ i h => absurd h (by omega)⟩)

/-- 辅助引理（注记 3.5）：三行时列规则 001/011 只看 `i = 0` 一个位置。 -/
theorem colRule_three {k : ℕ} (M : Mat 3 k) :
    ColRule M ↔ ∀ j, ¬ (M 0 j = false ∧ M 1 j = false ∧ M 2 j = true) ∧
      ¬ (M 0 j = false ∧ M 1 j = true ∧ M 2 j = true) := by
  constructor
  · intro h j
    exact h j 0 (by norm_num)
  · intro h j i hi
    obtain rfl : i = 0 := by omega
    exact h j

/-- 辅助引理（注记 3.5）：三行时列规则 001/101 只看 `i = 0` 一个位置。 -/
theorem colRuleAlt_three {k : ℕ} (M : Mat 3 k) :
    ColRuleAlt M ↔ ∀ j, ¬ (M 0 j = false ∧ M 1 j = false ∧ M 2 j = true) ∧
      ¬ (M 0 j = true ∧ M 1 j = false ∧ M 2 j = true) := by
  constructor
  · intro h j
    exact h j 0 (by norm_num)
  · intro h j i hi
    obtain rfl : i = 0 := by omega
    exact h j

/-- 交换三行矩阵的前两行。 -/
def swap01 {k : ℕ} (M : Mat 3 k) : Mat 3 k := fun i => M (Equiv.swap (0 : Fin 3) 1 i)

/-- 辅助引理（注记 3.5）：交换两次还原。 -/
theorem swap01_swap01 {k : ℕ} (M : Mat 3 k) : swap01 (swap01 M) = M := by
  funext i
  simp [swap01]

/-- 辅助引理（注记 3.5）：交换前两行不改变行规则（行规则逐行检查）。 -/
theorem rowRule_swap01 {k : ℕ} (M : Mat 3 k) : RowRule (swap01 M) ↔ RowRule M := by
  constructor
  · intro h i j hj
    simpa [swap01] using h (Equiv.swap (0 : Fin 3) 1 i) j hj
  · intro h i j hj
    exact h _ j hj

/-- 辅助引理（注记 3.5）：交换前两行把列规则 001/011 变成 001/101（列 `(x, y, z)` 变成 `(y, x, z)`）。 -/
theorem colRule_iff_swap01 {k : ℕ} (M : Mat 3 k) : ColRule M ↔ ColRuleAlt (swap01 M) := by
  rw [colRule_three, colRuleAlt_three]
  simp only [swap01, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 1 by decide)]
  refine forall_congr' fun j => ?_
  generalize M 0 j = x
  generalize M 1 j = y
  generalize M 2 j = z
  cases x <;> cases y <;> cases z <;> simp

open Classical in
/-- **注记 3.5**（A207070 的标题）：三行时两种列规则给出同样的数，`aAlt k 3 = a k 3`
（交换前两行是两类矩阵之间的双射）。 -/
theorem aAlt_three (k : ℕ) : aAlt k 3 = a k 3 := by
  unfold aAlt a
  exact Fintype.card_congr
    { toFun := fun M => ⟨swap01 M.1, (rowRule_swap01 _).mpr M.2.1,
        (colRule_iff_swap01 _).mpr (by rw [swap01_swap01]; exact M.2.2)⟩
      invFun := fun M => ⟨swap01 M.1, (rowRule_swap01 _).mpr M.2.1, (colRule_iff_swap01 _).mp M.2.2⟩
      left_inv := fun M => Subtype.ext (swap01_swap01 M.1)
      right_inv := fun M => Subtype.ext (swap01_swap01 M.1) }

end A207123
