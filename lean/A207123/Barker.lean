import A207123.AsympNumerics
import A207123.SmallK

/-!
# 报告 T5.4(2)：Colin Barker 在 A207118、A207069 中的猜想

报告 T5.4(2) 说 Barker 在 A207118、A207069、A326247 中的 g.f./闭式猜想都成立。这里形式化前两个条目（A326247 的
三条要先形式化它在 OEIS 的原始定义，不在本文件）：

* **A207118**（原表第 3 列，`a(n) = a_3(n)`，`n ≥ 1`）：
  - `barker_A207118_even`、`barker_A207118_odd`：`n` 偶时 `a(n) = (n⁶+24n⁵+208n⁴+816n³+1600n²+1536n+576)/576`，
    `n` 奇时 `a(n) = (n⁶+24n⁵+205n⁴+768n³+1315n²+936n+207)/576`（由 `a_even`、`a_odd` 与 `U_three`；对 `n = 0` 也对）；
  - `barker_A207118_gf`：g.f. `x(6+24x+6x²+x³+16x⁴−4x⁵−20x⁶+6x⁷+10x⁸−4x⁹−2x¹⁰+x¹¹)/((1−x)^7(1+x)^5)`，
    写成 `(1−x)^7(1+x)^5·Σ_{n≥1} a_3(n)xⁿ = 分子`（`Σ_{n≥1} a_3(n)xⁿ = aSer 3 − 1`，因为 `a_3(0) = 1`）。
* **A207069**（2×n 矩阵，`a(n) = aAlt n 2`，即 A207069 标题里的列规则；`aAlt_two`：它等于 `a_n(2)`）：
  - `barker_A207069_gf`：g.f. `x(4+4x−4x²−7x³+x⁴+3x⁵+3x⁶+x⁷−x⁸−x⁹)/((1−x)(1+x²−x³)(1−x−x³)(1−x−2x²−x³))`，
    同样写成分母乘 `Σ_{n≥1} a(n)xⁿ`（`aAlt 0 2 = 1`）。

证明：`gf_of_rec` 把这类等式化为三件事——数列满足以分母系数为系数的递推（`n` 大时；A207118 用推论 3.4 的
`parity_recurrence`，A207069 用注记 3.5 的 `oeis_A207069`）、前 `d` 项的值、整数表上的有限核对（`decide +kernel`）。
前 `d` 项的值：A207118 由上面的闭式算出，A207069 由可在内核里计算的 `rowList`（`rowList_eq`）读出。
-/

namespace A207123

open Polynomial Finset

/-! ## 1. 由递推与初值得母函数 -/

/-- 辅助引理（T5.4(2)）：`ofList l` 在 `i ≥ |l|` 处的系数为 0。 -/
theorem coeff_ofList_of_le (l : List ℤ) {i : ℕ} (hi : l.length ≤ i) : (ofList l).coeff i = 0 := by
  rw [ofList, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  refine Finset.sum_eq_zero fun j hj => ite_eq_right ?_
  have := Finset.mem_range.1 hj
  omega

/-- 辅助引理（T5.4(2)）：`ofList l` 的第 `i` 项系数是 `l.getD i 0`（对一切 `i`）。 -/
theorem coeff_ofList_getD (l : List ℤ) (i : ℕ) : (ofList l).coeff i = (l.getD i 0 : ℚ) := by
  rcases lt_or_ge i l.length with hi | hi
  · exact coeff_ofList l hi
  · rw [coeff_ofList_of_le l hi, List.getD_eq_default _ _ hi, Int.cast_zero]

/-- 辅助引理（T5.4(2)）：设 `l = [l_0, …, l_d]`、`|l'| ≤ d + 1`。若数列 `f` 满足 `Σ_{i≤d} l_i f(n−i) = 0`（`n ≥ d`），
`f` 的前 `d` 项是 `vals` 的前 `d` 项，并且整数表满足 `Σ_{i≤n} l_i (vals_{n−i} − [n = i]) = l'_n`（`n < d`）与
`−l_d = l'_d`，则 `(Σ l_i xⁱ)·(Σ_n f(n)xⁿ − 1) = Σ l'_i xⁱ`。 -/
theorem gf_of_rec (l l' : List ℤ) (vals : List ℕ) (d : ℕ) (hl : l.length = d + 1) (hl' : l'.length ≤ d + 1)
    (f : ℕ → ℚ) (hrec : ∀ n, d ≤ n → ∑ i ∈ range (d + 1), (l.getD i 0 : ℚ) * f (n - i) = 0)
    (hf : ∀ k, k < d → f k = (vals.getD k 0 : ℚ))
    (hsmall : ∀ n, n < d →
      ∑ i ∈ range (n + 1), l.getD i 0 * ((vals.getD (n - i) 0 : ℤ) - if n - i = 0 then 1 else 0) = l'.getD n 0)
    (htop : -l.getD d 0 = l'.getD d 0) :
    (↑(ofList l) : PowerSeries ℚ) * (PowerSeries.mk f - 1) = ↑(ofList l') := by
  ext n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one, coeff_ofList_getD]
  rcases lt_or_ge n d with hn | hn
  · have e : ∀ i ∈ range (n + 1), (l.getD i 0 : ℚ) * (f (n - i) - if n - i = 0 then 1 else 0) =
        ((l.getD i 0 * ((vals.getD (n - i) 0 : ℤ) - if n - i = 0 then 1 else 0) : ℤ) : ℚ) := by
      intro i hi
      rw [hf (n - i) (by have := Finset.mem_range.1 hi; omega)]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl e, ← Int.cast_sum, hsmall n hn]
  · have h1 : ∑ i ∈ range (n + 1), (l.getD i 0 : ℚ) * f (n - i) = 0 := by
      refine Eq.trans (Finset.sum_subset ?_ ?_).symm (hrec n hn)
      · intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      · intro i _ hi'
        simp only [Finset.mem_range, not_lt] at hi'
        rw [List.getD_eq_default _ _ (by omega), Int.cast_zero, zero_mul]
    have h2 : ∑ i ∈ range (n + 1), (l.getD i 0 : ℚ) * (if n - i = 0 then (1 : ℚ) else 0) = (l.getD n 0 : ℚ) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro i hi hin
        rw [ite_eq_right (by simp only [Finset.mem_range] at hi; omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2]
    rcases eq_or_lt_of_le hn with rfl | hlt
    · rw [zero_sub, ← Int.cast_neg, htop]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      simp

/-! ## 2. A207118（第 3 列） -/

/-- 辅助引理（T5.4(2)）：`U_3(m) = (m+1)(m²+5m+3)/3`（`ℚ` 中，由 `U_three`）。 -/
theorem U_three_rat (m : ℕ) : (U 3 m : ℚ) = ((m : ℚ) + 1) * ((m : ℚ) ^ 2 + 5 * m + 3) / 3 := by
  have h : (3 : ℚ) * (U 3 m : ℚ) = ((m : ℚ) + 1) * ((m : ℚ) ^ 2 + 5 * m + 3) := by exact_mod_cast U_three m
  linarith

/-- **T5.4(2)**（Barker 在 A207118 的猜想）：`n` 偶时 `a_3(n) = (n⁶+24n⁵+208n⁴+816n³+1600n²+1536n+576)/576`。 -/
theorem barker_A207118_even (n : ℕ) (hn : Even n) :
    (a 3 n : ℚ) =
      ((n : ℚ) ^ 6 + 24 * n ^ 5 + 208 * n ^ 4 + 816 * n ^ 3 + 1600 * n ^ 2 + 1536 * n + 576) / 576 := by
  obtain ⟨j, rfl⟩ := hn
  rw [← two_mul, a_even, U_three_rat]
  push_cast
  ring

/-- **T5.4(2)**（Barker 在 A207118 的猜想）：`n` 奇时 `a_3(n) = (n⁶+24n⁵+205n⁴+768n³+1315n²+936n+207)/576`。 -/
theorem barker_A207118_odd (n : ℕ) (hn : Odd n) :
    (a 3 n : ℚ) =
      ((n : ℚ) ^ 6 + 24 * n ^ 5 + 205 * n ^ 4 + 768 * n ^ 3 + 1315 * n ^ 2 + 936 * n + 207) / 576 := by
  obtain ⟨j, rfl⟩ := hn
  rw [a_odd, U_three_rat, U_three_rat]
  push_cast
  ring

/-- 辅助引理（T5.4(2)）：两个闭式合在一起。 -/
theorem a_three_eq (m : ℕ) : (a 3 m : ℚ) =
    if m % 2 = 0 then
      ((m : ℚ) ^ 6 + 24 * m ^ 5 + 208 * m ^ 4 + 816 * m ^ 3 + 1600 * m ^ 2 + 1536 * m + 576) / 576
    else ((m : ℚ) ^ 6 + 24 * m ^ 5 + 205 * m ^ 4 + 768 * m ^ 3 + 1315 * m ^ 2 + 936 * m + 207) / 576 := by
  split_ifs with h
  · exact barker_A207118_even m (Nat.even_iff.2 h)
  · exact barker_A207118_odd m (Nat.odd_iff.2 (by omega))

/-- **T5.4(2)**（Barker 在 A207118 的猜想）：A207118 的 g.f. 是
`x(6+24x+6x²+x³+16x⁴−4x⁵−20x⁶+6x⁷+10x⁸−4x⁹−2x¹⁰+x¹¹)/((1−x)^7(1+x)^5)`，即
`(1−x)^7(1+x)^5·Σ_{n≥1} a_3(n)xⁿ` 等于分子（`aSer 3 − 1 = Σ_{n≥1} a_3(n)xⁿ`）。 -/
theorem barker_A207118_gf :
    (↑((1 - X) ^ 7 * (1 + X) ^ 5 : ℚ[X]) : PowerSeries ℚ) * (aSer 3 - 1) =
      ↑(X * (6 + 24 * X + 6 * X ^ 2 + X ^ 3 + 16 * X ^ 4 - 4 * X ^ 5 - 20 * X ^ 6 + 6 * X ^ 7 + 10 * X ^ 8
        - 4 * X ^ 9 - 2 * X ^ 10 + X ^ 11) : ℚ[X]) := by
  have hD : ((1 - X) ^ 7 * (1 + X) ^ 5 : ℚ[X]) = ofList [1, -2, -4, 10, 5, -20, 0, 20, -5, -10, 4, 2, -1] :=
    parDen_three
  have hN : (X * (6 + 24 * X + 6 * X ^ 2 + X ^ 3 + 16 * X ^ 4 - 4 * X ^ 5 - 20 * X ^ 6 + 6 * X ^ 7 + 10 * X ^ 8
      - 4 * X ^ 9 - 2 * X ^ 10 + X ^ 11) : ℚ[X]) = ofList [0, 6, 24, 6, 1, 16, -4, -20, 6, 10, -4, -2, 1] := by
    simp [ofList, Finset.sum_range_succ]
    ring
  rw [hD, hN, aSer]
  refine gf_of_rec _ _ [1, 6, 36, 102, 289, 612, 1296, 2340, 4225, 6890, 11236, 17066] 12 rfl (by simp) _
    ?_ ?_ (by decide +kernel) (by decide +kernel)
  · intro n hn
    have h := parity_recurrence 3 (by norm_num) n hn
    rw [parDen_three] at h
    simp only [coeff_ofList_getD] at h
    exact h
  · intro k hk
    rw [a_three_eq]
    interval_cases k <;> norm_num

/-! ## 3. A207069（第 2 行） -/

/-- **T5.4(2)**（Barker 在 A207069 的猜想）：A207069（`a(n) = aAlt n 2`，2×n 矩阵）的 g.f. 是
`x(4+4x−4x²−7x³+x⁴+3x⁵+3x⁶+x⁷−x⁸−x⁹)/((1−x)(1+x²−x³)(1−x−x³)(1−x−2x²−x³))`，即分母乘
`Σ_{n≥1} a(n)xⁿ` 等于分子（`aAlt 0 2 = 1`）。 -/
theorem barker_A207069_gf :
    (↑((1 - X) * (1 + X ^ 2 - X ^ 3) * (1 - X - X ^ 3) * (1 - X - 2 * X ^ 2 - X ^ 3) : ℚ[X]) : PowerSeries ℚ) *
        (PowerSeries.mk (fun n => (aAlt n 2 : ℚ)) - 1) =
      ↑(X * (4 + 4 * X - 4 * X ^ 2 - 7 * X ^ 3 + X ^ 4 + 3 * X ^ 5 + 3 * X ^ 6 + X ^ 7 - X ^ 8 - X ^ 9) : ℚ[X]) := by
  have hD : ((1 - X) * (1 + X ^ 2 - X ^ 3) * (1 - X - X ^ 3) * (1 - X - 2 * X ^ 2 - X ^ 3) : ℚ[X]) =
      ofList [1, -3, 2, -3, 6, 0, 0, -3, -1, 0, 1] := by
    simp [ofList, Finset.sum_range_succ]
    ring
  have hN : (X * (4 + 4 * X - 4 * X ^ 2 - 7 * X ^ 3 + X ^ 4 + 3 * X ^ 5 + 3 * X ^ 6 + X ^ 7 - X ^ 8 - X ^ 9) : ℚ[X]) =
      ofList [0, 4, 4, -4, -7, 1, 3, 3, 1, -1, -1] := by
    simp [ofList, Finset.sum_range_succ]
    ring
  have hvals : rowList 2 9 = [1, 4, 16, 36, 81, 196, 441, 961, 2116, 4624] := by decide +kernel
  rw [hD, hN]
  refine gf_of_rec _ _ [1, 4, 16, 36, 81, 196, 441, 961, 2116, 4624] 10 rfl (by simp) _ ?_ ?_
    (by decide +kernel) (by decide +kernel)
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h : (aAlt (k + 10) 2 : ℚ) = 3 * aAlt (k + 9) 2 - 2 * aAlt (k + 8) 2 + 3 * aAlt (k + 7) 2
        - 6 * aAlt (k + 6) 2 + 3 * aAlt (k + 3) 2 + aAlt (k + 2) 2 - aAlt k 2 := by
      exact_mod_cast oeis_A207069 k
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linear_combination h
  · intro k hk
    rw [aAlt_two, ← hvals, rowList_eq, seg_getD _ 0 (9 + 1) k hk, zero_add]

end A207123
