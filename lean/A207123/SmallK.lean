import A207123.Recurrence
import A207123.Formula
import A207123.Binomial

/-!
# 报告 T5.4(3)(4)(5) 的代数部分与 T2.8(1) 的三层和

* **T5.4(3)**（`R_k := U_k(1)`，允许行的个数）：`Σ_k R_k x^k = (1 + x² − x³)/((1 − x)(1 − x − x³))`
  （`gf_R`），以及提示词的写法 `(1 − x + x²)/((1 − x)(1 − x − x³))` 实际上是 `1 + x·Σ_k R_k x^k`
  （`gf_R_shift`），它不等于 `Σ_k R_k x^k`（`gf_R_prompt_wrong`；`x¹` 系数为 1，而 `R_1 = 2`）。
  「`R_k = A038718(k+2)`」以及「允许行 ↔ `P_{k+2}²` 中的 Hamilton 路」的双射没有形式化
  （A038718 在 OEIS 中按排列的组合条件定义，要形式化就得证明 Hamilton 路的计数递推）。
* **T5.4(4)**：`U_3(m) = (m+1)(m²+5m+3)/3 = 2C(m+3,3) − (m+1) = A084990(m+1)`（`U_three`、`U_three_choose`、
  `U_three_eq_A084990`；A084990 在 OEIS 中的定义就是闭式 `a(n) = n(n² + 3n − 1)/3`，照抄为 `A084990`）。
* **T5.4(5)**：`U_4(m) = (m+1)(m+2)(m²+11m+6)/12 = C(m+2,2)² − 4C(m+2,4)`（`U_four`、`U_four_choose`）。
  与 OEIS 条目 A326247 的对应（该条目按「不交叉也不嵌套的边对」组合定义）、两处保值集双射、
  「Q_3 与 Λ_3 不同构」等没有形式化。
* **T2.8(1)**：`k ≥ 1` 时 `N(k,q) = Σ_{i=1}^{q} (−1)^{q−i} C(q,i)·U_k(i−1)` 即 `Binomial.lean` 的 `N_inv`
  （`k = 0` 时为 `N_inv_zero`）；代入 T2.4（`U_explicit`）得三层和 `N_explicit`。
-/

open Polynomial Finset

namespace A207123

/-! ### T5.4(3)：`R_k` 的母函数 -/

/-- 辅助引理（T5.4(3)）：`P_1 = (1 − x)(1 − x − x³)`。 -/
theorem Ppoly_one : Ppoly ℚ 1 = (1 - X) * (1 - X - X ^ 3) := by
  rw [Ppoly_succ, Ppoly_zero, bpoly, bpoly]
  simp

/-- 辅助引理（T5.4(3)）：`W_1 = 1 + x² − x³`。 -/
theorem Wpoly_one : Wpoly ℚ 1 = 1 + X ^ 2 - X ^ 3 := by
  rw [Wpoly_succ, Wpoly_zero, Ppoly_zero, bpoly]
  simp
  ring

/-- **T5.4(3)**：`Σ_k R_k x^k = (1 + x² − x³)/((1 − x)(1 − x − x³))`（`R_k = U_k(1)`），
写成 `(1 − x)(1 − x − x³)·Σ_k R_k x^k = 1 + x² − x³`。 -/
theorem gf_R : (↑((1 - X) * (1 - X - X ^ 3) : ℚ[X]) : PowerSeries ℚ) * Gser 1
    = ↑(1 + X ^ 2 - X ^ 3 : ℚ[X]) := by
  rw [← Ppoly_one, ← Wpoly_one, P_mul_G]

/-- **T5.4(3)**：提示词的 `(1 − x + x²)/((1 − x)(1 − x − x³))` 等于 `1 + x·Σ_k R_k x^k`
（即 `Σ_{n≥1} A038718(n)·x^{n−1}` 的写法，offset 为 1）。 -/
theorem gf_R_shift :
    (((((1 - X) * (1 - X - X ^ 3) : ℚ[X])) : PowerSeries ℚ) * (1 + PowerSeries.X * Gser 1) : PowerSeries ℚ)
      = (((1 - X + X ^ 2 : ℚ[X])) : PowerSeries ℚ) := by
  have h := gf_R
  set P : PowerSeries ℚ := ((((1 - X) * (1 - X - X ^ 3) : ℚ[X])) : PowerSeries ℚ) with hP
  calc P * (1 + PowerSeries.X * Gser 1) = P + PowerSeries.X * (P * Gser 1) := by ring
    _ = P + PowerSeries.X * (((1 + X ^ 2 - X ^ 3 : ℚ[X])) : PowerSeries ℚ) := by rw [h]
    _ = (((1 - X + X ^ 2 : ℚ[X])) : PowerSeries ℚ) := by
      rw [hP]
      simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_one,
        Polynomial.coe_pow, Polynomial.coe_X]
      ring

/-- **T5.4(3)**（提示词的 g.f. 写法有误）：`(1 − x + x²)/((1 − x)(1 − x − x³))` 不是 `Σ_k R_k x^k`。 -/
theorem gf_R_prompt_wrong : (↑((1 - X) * (1 - X - X ^ 3) : ℚ[X]) : PowerSeries ℚ) * Gser 1
    ≠ ↑(1 - X + X ^ 2 : ℚ[X]) := by
  rw [gf_R]
  intro h
  have h2 := congrArg (PowerSeries.coeff 1) h
  simp only [Polynomial.coeff_coe] at h2
  simp [Polynomial.coeff_one, Polynomial.coeff_X] at h2

/-! ### T5.4(4)(5)：`U_3`、`U_4` 的闭式 -/

/-- **T5.4(4)**：`U_3(m) = (m+1)(m²+5m+3)/3`。 -/
theorem U_three (m : ℕ) : 3 * U 3 m = (m + 1) * (m ^ 2 + 5 * m + 3) := by
  induction m with
  | zero => simp [U_zero_right]
  | succ m ih =>
    have h : U 3 (m + 1) = U 3 m + U 2 (m + 1) + (m + 1) * U 0 (m + 1) := lemma1 0 m
    rw [U_of_le_two (k := 2) (by norm_num) (m + 1), U_zero_left] at h
    rw [h, mul_add, mul_add, ih]
    ring

/-- 辅助引理（T5.4）：`3!·C(n+3,3) = (n+3)(n+2)(n+1)`。 -/
theorem six_mul_choose_three (n : ℕ) : 6 * Nat.choose (n + 3) 3 = (n + 3) * (n + 2) * (n + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  rw [show (3 : ℕ).factorial = 6 by rfl] at h
  rw [← h]
  have e1 : n + 3 - 2 = n + 1 := by omega
  have e2 : n + 3 - 1 = n + 2 := by omega
  rw [e1, e2, Nat.sub_zero]
  ring

/-- **T5.4(4)**：`U_3(m) = 2C(m+3,3) − (m+1)`，写成 `U_3(m) + (m+1) = 2C(m+3,3)`。 -/
theorem U_three_choose (m : ℕ) : U 3 m + (m + 1) = 2 * Nat.choose (m + 3) 3 := by
  have h1 := U_three m
  have h2 := six_mul_choose_three m
  nlinarith

/-- OEIS A084990，按条目本身的定义（%N 行，快照 `data/oeis/A084990.txt`）：`a(n) = n(n² + 3n − 1)/3`。
`n(n² + 3n − 1) ≡ (n−1)n(n+1) (mod 3)` 总被 3 整除，所以 ℕ 中的除法没有截断；`n = 0` 时 ℕ 减法给出
`0·0/3 = 0`，与条目的 `a(0) = 0` 相同。 -/
def A084990 (n : ℕ) : ℕ := n * (n ^ 2 + 3 * n - 1) / 3

/-- **T5.4(4)**：`U_3(m) = A084990(m+1)`（A084990 按条目的定义 `a(n) = n(n² + 3n − 1)/3`）。 -/
theorem U_three_eq_A084990 (m : ℕ) : U 3 m = A084990 (m + 1) := by
  have h : (m + 1) * ((m + 1) ^ 2 + 3 * (m + 1) - 1) = 3 * U 3 m := by
    rw [U_three, Nat.sub_eq_of_eq_add (by ring : (m + 1) ^ 2 + 3 * (m + 1) = m ^ 2 + 5 * m + 3 + 1)]
  rw [A084990, h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]

/-- **T5.4(5)**：`U_4(m) = (m+1)(m+2)(m²+11m+6)/12`。 -/
theorem U_four (m : ℕ) : 12 * U 4 m = (m + 1) * (m + 2) * (m ^ 2 + 11 * m + 6) := by
  induction m with
  | zero => simp [U_zero_right]
  | succ m ih =>
    have h : U 4 (m + 1) = U 4 m + U 3 (m + 1) + (m + 1) * U 1 (m + 1) := lemma1 1 m
    rw [U_of_le_two (k := 1) (by norm_num) (m + 1)] at h
    have h3 := U_three (m + 1)
    have e : 12 * U 3 (m + 1) = 4 * (3 * U 3 (m + 1)) := by ring
    rw [h, mul_add, mul_add, ih, e, h3]
    ring

/-- 辅助引理（T5.4）：`2·C(n+2,2) = (n+2)(n+1)`。 -/
theorem two_mul_choose_two (n : ℕ) : 2 * Nat.choose (n + 2) 2 = (n + 2) * (n + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 2) 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  rw [show (2 : ℕ).factorial = 2 by rfl] at h
  rw [← h]
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1, Nat.sub_zero]
  ring

/-- 辅助引理（T5.4）：`4!·C(n+3,4) = (n+3)(n+2)(n+1)n`。 -/
theorem tf_mul_choose_four (n : ℕ) :
    24 * Nat.choose (n + 3) 4 = (n + 3) * (n + 2) * (n + 1) * n := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 4
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  rw [show (4 : ℕ).factorial = 24 by rfl] at h
  rw [← h]
  have e1 : n + 3 - 3 = n := by omega
  have e2 : n + 3 - 2 = n + 1 := by omega
  have e3 : n + 3 - 1 = n + 2 := by omega
  rw [e1, e2, e3, Nat.sub_zero]
  ring

/-- **T5.4(5)**：`U_4(m) = C(m+2,2)² − 4C(m+2,4)`（在 `ℤ` 中）。 -/
theorem U_four_choose (m : ℕ) :
    (U 4 m : ℤ) = (Nat.choose (m + 2) 2 : ℤ) ^ 2 - 4 * Nat.choose (m + 2) 4 := by
  have h1 : (12 * U 4 m : ℤ) = (m + 1) * (m + 2) * (m ^ 2 + 11 * m + 6) := by
    exact_mod_cast U_four m
  have h2 : (2 * Nat.choose (m + 2) 2 : ℤ) = (m + 2) * (m + 1) := by
    exact_mod_cast two_mul_choose_two m
  rcases m with _ | n
  · simp [U_zero_right, Nat.choose_eq_zero_of_lt (show 2 < 4 by norm_num)]
  · have h3 : (24 * Nat.choose (n + 1 + 2) 4 : ℤ) = (n + 3) * (n + 2) * (n + 1) * n := by
      have := tf_mul_choose_four n
      rw [show n + 1 + 2 = n + 3 by omega]
      exact_mod_cast this
    push_cast at h1 h2 ⊢
    nlinarith [h1, h2, h3]

/-! ### T2.8(1)：`N(k,q)` 的三层和 -/

/-- **T2.8(1)**：`k ≥ 1` 时 `N(k,q) = Σ_{i=1}^{q} (−1)^{q−i}·C(q,i)·U_k(i−1)`，代入 T2.4 的显式公式得
三层和（`S` 为第二类 Stirling 数，`H(m,s,j) = hc s (vars j m)`；二项式按组合约定截断）。 -/
theorem N_explicit (k q : ℕ) (hk : 1 ≤ k) :
    (N k q : ℤ) = ∑ i ∈ Icc 1 q, (-1 : ℤ) ^ (q - i) * q.choose i *
      (((∑ s ∈ range (k / 3 + 1),
          Nat.stirlingSecond (i - 1 + s) (i - 1) * Nat.choose (k + (i - 1) - 2 * s) (k - 3 * s))
        + if 2 ≤ k then
            ∑ j ∈ Icc 1 (i - 1), j * ∑ s ∈ range ((k - 2) / 3 + 1),
              hc s (vars j (i - 1)) * Nat.choose (k - 2 + (i - 1) - j - 2 * s) (k - 2 - 3 * s)
          else 0 : ℕ) : ℤ) := by
  rw [N_inv k q hk]
  apply sum_congr rfl
  intro i _
  rw [U_explicit k (i - 1)]

end A207123
