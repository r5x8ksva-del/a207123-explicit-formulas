import A207123.HNum

/-!
# 报告 T4.3：(C7) 分子 `Num_q` 的结构

记 `F_q = Σ_k N(k,q)·x^k`（`Nser q`），`Num_q = P_{q−1}·F_q`（`HNum.lean` 的 `Numq`，按容斥闭式定义，
`P_mul_Nser` 说明它等于报告的乘积定义）。

* **T4.3(1)**：`Nser_three_term`（`q ≥ 1` 时 `b_{q−1}F_q = (x+2(q−1)x³)F_{q−1} + (q−1)x³F_{q−2} + [q=2]x²`）与
  反例 `Nser_three_term_needs_boundary`（去掉边界项 `q = 2` 时不成立）；`Numq_three_term`（`q ≥ 3` 的三项递推）、
  `Numq_three_term_boundary`（含边界项的统一写法）、`Numq_three_term_fails_at_two`；首项递推 `leadingCoeff_Numq_rec`；
  次数、首项、最低项汇总 `Numq_deg_lead_low`。
* **T4.3(2)**：`Num_eq_IE_closed_form`、`P_mul_Nser_eq_IE`（容斥闭式，`W_{−1} = 1`）。
* **T4.3(3)**：正项全历史递推 `Numq_full_history`（`q ≥ 3`）与 `q = 2` 的反例 `full_history_at_two`；
  系数全非负 `Numq_hasNonnegCoeffs`、`Numq_coeff_nonneg`；`[x^{3q−3}]Num_q = 0`（`Numq_coeff_gap`）；
  支撑 `Numq_coeff_pos_iff`、`Numq_coeff_ne_zero_iff`（`q ≥ 2` 时非零项恰为 `x^q,…,x^{3q−4}` 与 `x^{3q−2}`）。
* **T4.3(4)**（部分）：`x = 1` 处的递推 `Numq_eval_one_rec` 与初值 `Numq_eval_one_init`，它们与 A000262 的递推
  `a(n) = (2n−1)a(n−1) − (n−1)(n−2)a(n−2)`、初值 1, 3 相同。「`Num_q(1) = A000262(q)`」本身没有形式化：
  A000262 在 OEIS 中按「集合划分为有序块」的组合条件定义。
* **T4.3(5)**（部分）：一般恒等式 `Numq_coeff_q_add`（`ν_j(q) = Σ_{i≤j} π_i(q)·N(q+j−i, q)`）；`j = 1, 2` 的显式式
  `Numq_coeff_q_add_one`、`Numq_coeff_q_add_two`；`j = 0, 1, 2` 的门槛精确 `Numq_coeff_exception_zero/one/two`。
  一般 `j` 的「`q ≥ j+2` 时是 `2j` 次多项式、首项、门槛」没有在本文件中形式化（要用 T4.1，见 `NearDiag.lean`）。
* T4.3(6)(7)(8) 没有形式化。

写法上的约束：`N_six_four` 的 docstring 说明了为什么不能用 `simp`/`omega` 去化简含具体数字的 `N a b`
（内核会展开 `N` 的组合定义；2026-10-05 一版这样写的文件编译时内存超过 18 GB）。
-/

namespace A207123

open Polynomial Finset

/-! ## T4.3(1)：`F_q` 的递推（含边界缺陷）与 `Num_q` 的三项递推 -/

section ThreeTerm

/-- `F_{n−1}`：`NserPrev 0 = F_{−1} = 0`，`NserPrev (n+1) = F_n = Σ_k N(k,n)·x^k`。 -/
noncomputable def NserPrev : ℕ → PowerSeries ℚ
  | 0 => 0
  | n + 1 => Nser n

/-- 辅助引理（T4.3）：`[x^k]F_q = N(k,q)`。 -/
theorem coeff_Nser (k q : ℕ) : PowerSeries.coeff k (Nser q) = (N k q : ℚ) := by
  rw [Nser, PowerSeries.coeff_mk]

/-- **T4.3(1)**（初值 `F_0 = 1`）：`Σ_k N(k,0)·x^k = 1`。 -/
theorem Nser_zero_eq_one : Nser 0 = 1 := by
  ext k
  rw [coeff_Nser, PowerSeries.coeff_one]
  cases k with
  | zero => simp [N_init.1]
  | succ k => simp [N_succ_zero]

/-- 辅助引理（T4.3(1)）：右边 `(x + a x³)·F + b x³·G` 的 `x^k` 系数。 -/
theorem coeff_rhs_three_term (F G : PowerSeries ℚ) (a b : ℚ) (k : ℕ) :
    PowerSeries.coeff k ((PowerSeries.X + PowerSeries.C a * PowerSeries.X ^ 3) * F
        + PowerSeries.C b * PowerSeries.X ^ 3 * G)
      = (if 1 ≤ k then PowerSeries.coeff (k - 1) F else 0)
        + a * (if 3 ≤ k then PowerSeries.coeff (k - 3) F else 0)
        + b * (if 3 ≤ k then PowerSeries.coeff (k - 3) G else 0) := by
  have h1 : (PowerSeries.X + PowerSeries.C a * PowerSeries.X ^ 3) * F
        + PowerSeries.C b * PowerSeries.X ^ 3 * G
      = PowerSeries.X ^ 1 * F + PowerSeries.C a * (PowerSeries.X ^ 3 * F)
        + PowerSeries.C b * (PowerSeries.X ^ 3 * G) := by ring
  rw [h1, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']

/-- **T4.3(1)**（`F_q` 的一阶递推，含边界缺陷）：对 `q ≥ 1`，
`b_{q−1}·F_q = (x + 2(q−1)x³)·F_{q−1} + (q−1)x³·F_{q−2} + [q = 2]·x²`，
其中 `F_q = Σ_k N(k,q)·x^k`（`Nser q`），`F_0 = 1`（`Nser_zero_eq_one`），`F_{−1} = 0`
（`F_{q−2}` 写成 `NserPrev (q − 1)`）。证明：比较 `x^k` 系数；`k ≥ 3` 用三角递推 `N_tri`，
`k ≤ 2` 直接用初值（`k = 2` 时三角递推不成立，缺的正是 `[q = 2]x²`）。 -/
theorem Nser_three_term {q : ℕ} (hq : 1 ≤ q) :
    (↑(bpoly ℚ (q - 1)) : PowerSeries ℚ) * Nser q
      = (PowerSeries.X + PowerSeries.C (2 * ((q : ℚ) - 1)) * PowerSeries.X ^ 3) * Nser (q - 1)
        + PowerSeries.C ((q : ℚ) - 1) * PowerSeries.X ^ 3 * NserPrev (q - 1)
        + (if q = 2 then PowerSeries.X ^ 2 else 0) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : ((r + 1 : ℕ) : ℚ) - 1 = r := by push_cast; ring
  rw [hr, Nat.add_sub_cancel]
  ext k
  rw [coe_bpoly, coeff_b_mul, map_add, coeff_rhs_three_term, apply_ite (PowerSeries.coeff k),
    map_zero, PowerSeries.coeff_X_pow]
  simp only [coeff_Nser]
  match k with
  | 0 =>
    simp [N_eq_zero_of_lt (show 0 < r + 1 by omega)]
  | 1 =>
    rcases r with _ | s
    · simp [N_init.1, N_init.2.1, N_eq_zero_of_lt (show 0 < 1 by omega)]
    · simp [N_eq_zero_of_lt (show 1 < s + 1 + 1 by omega),
        N_eq_zero_of_lt (show 0 < s + 1 + 1 by omega), N_eq_zero_of_lt (show 0 < s + 1 by omega)]
  | 2 =>
    rcases r with _ | _ | s
    · simp [N_init.2.2.1, N_init.2.1, N_succ_zero]
    · simp [N_init.2.2.2, N_init.2.1, N_eq_zero_of_lt (show 1 < 2 by omega)]
      norm_num
    · simp [N_eq_zero_of_lt (show 2 < s + 1 + 1 + 1 by omega),
        N_eq_zero_of_lt (show 1 < s + 1 + 1 + 1 by omega),
        N_eq_zero_of_lt (show 1 < s + 1 + 1 by omega)]
  | k + 3 =>
    have h := N_tri k r
    have hq : ((N (k + 3) (r + 1) : ℕ) : ℚ)
        = N (k + 2) r + N (k + 2) (r + 1) + r * (N k (r - 1) + 2 * N k r + N k (r + 1)) := by
      exact_mod_cast h
    simp only [show 1 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega, ↓reduceIte,
      show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel, show k + 3 ≠ 2 by omega, ite_self]
    rcases r with _ | s
    · simp only [NserPrev, map_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero,
        sub_zero] at hq ⊢
      linarith
    · simp only [NserPrev, coeff_Nser, Nat.add_sub_cancel] at hq ⊢
      push_cast at hq ⊢
      linarith

/-- **T4.3(1)**（注：边界项 `[q = 2]x²` 必不可少）：去掉它，`q = 2` 时等式不成立：
`b_1·F_2 ≠ (x + 2x³)·F_1 + x³·F_0`（比较 `x²` 系数：左边 `N(2,2) − N(1,2) = 2`，右边 `N(1,1) = 1`）。 -/
theorem Nser_three_term_needs_boundary :
    (↑(bpoly ℚ 1) : PowerSeries ℚ) * Nser 2
      ≠ (PowerSeries.X + PowerSeries.C (2 * ((2 : ℚ) - 1)) * PowerSeries.X ^ 3) * Nser 1
        + PowerSeries.C ((2 : ℚ) - 1) * PowerSeries.X ^ 3 * Nser 0 := by
  intro h
  have h2 := congrArg (PowerSeries.coeff 2) h
  rw [coe_bpoly, coeff_b_mul, coeff_rhs_three_term] at h2
  simp only [coeff_Nser] at h2
  norm_num [N_init.2.2.2, N_init.2.1, N_eq_zero_of_lt (show 1 < 2 by omega)] at h2

/-- 辅助引理（T4.3）：`q ≥ 1` 时 `Num_q` 看成幂级数等于 `P_{q−1}·F_q`（`P_mul_Nser` 的反向）。 -/
theorem coe_Numq_eq {q : ℕ} (hq : 1 ≤ q) :
    (↑(Numq q) : PowerSeries ℚ) = ↑(Ppoly ℚ (q - 1)) * Nser q := (P_mul_Nser hq).symm

/-- **T4.3(1)**（约定 `Num_0 := P_{−1}·F_0 = 1`）：`Num_0 = 1`。 -/
theorem Numq_zero_eq_one : Numq 0 = 1 := by
  simp [Numq, Wprev]

/-- 辅助引理（T4.3(1)）：三项递推写成 `q = p + 3`（系数仍按 `q` 写）。证明：`Nser_three_term`
两边乘 `P_{p+1}`（`P_{p+2} = P_{p+1}·b_{p+2}`，`P_{p+1} = P_p·b_{p+1}`），再用 `P_{n−1}·F_n = Num_n`
（`P_mul_Nser`）与 `ℚ[x] → ℚ[[x]]` 的单射。 -/
theorem Numq_three_term_core (p : ℕ) :
    Numq (p + 3) = (X + C (2 * (((p + 3 : ℕ) : ℚ) - 1)) * X ^ 3) * Numq (p + 2)
      + C (((p + 3 : ℕ) : ℚ) - 1) * X ^ 3 * bpoly ℚ (p + 1) * Numq (p + 1) := by
  have hF := Nser_three_term (q := p + 3) (by omega)
  rw [show p + 3 - 1 = p + 2 by omega] at hF
  simp only [NserPrev, show p + 3 ≠ 2 by omega, ↓reduceIte, add_zero] at hF
  apply Polynomial.coe_injective ℚ
  simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X,
    Polynomial.coe_C]
  rw [coe_Numq_eq (q := p + 3) (by omega), coe_Numq_eq (q := p + 2) (by omega),
    coe_Numq_eq (q := p + 1) (by omega)]
  have hP2 : Ppoly ℚ (p + 3 - 1) = Ppoly ℚ (p + 1) * bpoly ℚ (p + 2) := by
    rw [show p + 3 - 1 = p + 1 + 1 by omega]; exact Ppoly_succ ℚ (p + 1)
  have hP1 : Ppoly ℚ (p + 2 - 1) = Ppoly ℚ p * bpoly ℚ (p + 1) := by
    rw [show p + 2 - 1 = p + 1 by omega]; exact Ppoly_succ ℚ p
  rw [hP2, hP1, show p + 1 - 1 = p by omega, Ppoly_succ ℚ p]
  simp only [Polynomial.coe_mul]
  linear_combination (↑(Ppoly ℚ p) * ↑(bpoly ℚ (p + 1)) : PowerSeries ℚ) * hF

/-- 辅助引理（T4.3(1)）：三项递推写成 `q = p + 3`、系数写成 `ℚ[x]` 中的自然数：
`Num_{p+3} = (x + 2(p+2)x³)·Num_{p+2} + (p+2)x³·b_{p+1}·Num_{p+1}`。 -/
theorem Numq_succ_three (p : ℕ) :
    Numq (p + 3) = (X + 2 * ((p : ℚ[X]) + 2) * X ^ 3) * Numq (p + 2)
      + ((p : ℚ[X]) + 2) * X ^ 3 * bpoly ℚ (p + 1) * Numq (p + 1) := by
  rw [Numq_three_term_core]
  simp only [map_mul, map_sub, map_add, map_natCast, map_ofNat, map_one, Nat.cast_add,
    Nat.cast_ofNat]
  ring

/-- **T4.3(1)**（三项递推）：对 `q ≥ 3`，
`Num_q = (x + 2(q−1)x³)·Num_{q−1} + (q−1)x³·b_{q−2}·Num_{q−2}`；初值 `Num_1 = x`、
`Num_2 = 2x² + x⁴`（`Numq_one`、`Numq_two`，见 HNum）。证明：`Nser_three_term` 两边乘
`P_{q−2}`（`P_{q−1} = P_{q−2}·b_{q−1}`，`P_{q−2} = P_{q−3}·b_{q−2}`），再用
`P_{n−1}·F_n = Num_n`（`P_mul_Nser`）与 `ℚ[x] → ℚ[[x]]` 的单射（`Numq_three_term_core`）。 -/
theorem Numq_three_term {q : ℕ} (hq : 3 ≤ q) :
    Numq q = (X + C (2 * ((q : ℚ) - 1)) * X ^ 3) * Numq (q - 1)
      + C ((q : ℚ) - 1) * X ^ 3 * bpoly ℚ (q - 2) * Numq (q - 2) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 3 := ⟨q - 3, by omega⟩
  rw [show p + 3 - 1 = p + 2 by omega, show p + 3 - 2 = p + 1 by omega]
  exact Numq_three_term_core p

/-- **T4.3(1)**（含边界项的统一写法，`c4.md` §4.2）：对 `q ≥ 2`，约定 `Num_0 = 1`，
`Num_q = (x + 2(q−1)x³)·Num_{q−1} + (q−1)x³·b_{q−2}·Num_{q−2} + [q = 2]·x²(1 − x)`。 -/
theorem Numq_three_term_boundary {q : ℕ} (hq : 2 ≤ q) :
    Numq q = (X + C (2 * ((q : ℚ) - 1)) * X ^ 3) * Numq (q - 1)
      + C ((q : ℚ) - 1) * X ^ 3 * bpoly ℚ (q - 2) * Numq (q - 2)
      + (if q = 2 then X ^ 2 * (1 - X) else 0) := by
  rcases (show q = 2 ∨ 3 ≤ q by omega) with rfl | h3
  · simp only [↓reduceIte, show 2 - 1 = 1 by rfl, show 2 - 2 = 0 by rfl, Numq_two, Numq_one,
      Numq_zero_eq_one, bpoly]
    simp only [map_mul, map_sub, map_one, map_ofNat, Nat.cast_ofNat, Nat.cast_zero, map_zero]
    ring
  · simp only [show q ≠ 2 by omega, ↓reduceIte, add_zero]
    exact Numq_three_term h3

/-- **T4.3(1)**（边界项必不可少）：若去掉 `[q = 2]x²(1 − x)`，`q = 2` 时三项递推给出
`x² + x³ + x⁴ ≠ Num_2 = 2x² + x⁴`（两边在 `x = −1` 处的值为 `1` 与 `3`）。 -/
theorem Numq_three_term_fails_at_two :
    Numq 2 ≠ (X + C (2 * ((2 : ℚ) - 1)) * X ^ 3) * Numq 1
      + C ((2 : ℚ) - 1) * X ^ 3 * bpoly ℚ 0 * Numq 0 := by
  rw [Numq_two, Numq_one, Numq_zero_eq_one]
  intro h
  have h2 := congrArg (Polynomial.eval (-1 : ℚ)) h
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one, eval_bpoly, eval_ofNat,
    Nat.cast_zero] at h2
  norm_num at h2

/-- **T4.3(1)**（首项递推）：对 `q ≥ 3`，`L_q = (q−1)·[2·L_{q−1} − (q−2)·L_{q−2}]`
（`L_q` 为 `Num_q` 的首项系数；由 HNum 的 `leadingCoeff_Numq`，`L_q = (q−1)!`）。 -/
theorem leadingCoeff_Numq_rec {q : ℕ} (hq : 3 ≤ q) :
    (Numq q).leadingCoeff = ((q : ℚ) - 1)
      * (2 * (Numq (q - 1)).leadingCoeff - ((q : ℚ) - 2) * (Numq (q - 2)).leadingCoeff) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 3 := ⟨q - 3, by omega⟩
  rw [show p + 3 - 1 = p + 2 by omega, show p + 3 - 2 = p + 1 by omega,
    leadingCoeff_Numq (by omega), leadingCoeff_Numq (by omega), leadingCoeff_Numq (by omega),
    show p + 3 - 1 = p + 1 + 1 by omega, show p + 2 - 1 = p + 1 by omega, Nat.add_sub_cancel,
    Nat.factorial_succ (p + 1), Nat.factorial_succ p]
  push_cast
  ring

/-- **T4.3(1)**（「由此次数 `3q−2`、首项 `(q−1)!`、最低项 `2x^q`（`q ≥ 2`）」，汇总 HNum 的
`natDegree_Numq`、`leadingCoeff_Numq`、`Numq_lowest`）。 -/
theorem Numq_deg_lead_low {q : ℕ} (hq : 2 ≤ q) :
    (Numq q).natDegree = 3 * q - 2 ∧ (Numq q).leadingCoeff = ((q - 1).factorial : ℚ) ∧
      (∀ j < q, (Numq q).coeff j = 0) ∧ (Numq q).coeff q = 2 :=
  ⟨natDegree_Numq (by omega), leadingCoeff_Numq (by omega), (Numq_lowest hq).1, (Numq_lowest hq).2⟩

end ThreeTerm

/-! ## T4.3(2)：容斥闭式 -/

section ClosedForm

/-- **T4.3(2)**（约定 `W_{−1} = 1`）。 -/
theorem Wprev_zero_eq_one : Wprev 0 = 1 := rfl

/-- **T4.3(2)**：`W_m = 1 + x²·Σ_{j=1}^{m} j·P_{j−1}`（`Wprev (m+1) = W_m`）。 -/
theorem Wprev_succ_eq (m : ℕ) :
    Wprev (m + 1) = 1 + X ^ 2 * ∑ j ∈ Icc 1 m, C (j : ℚ) * Ppoly ℚ (j - 1) := rfl

/-- **T4.3(2)**（容斥闭式）：对 `q ≥ 1`，若多项式 `Num` 作为幂级数等于报告的定义
`P_{q−1}·Σ_k N(k,q)x^k`，则 `Num = Σ_{i=0}^{q} (−1)^{q−i}·C(q,i)·W_{i−1}·∏_{v=i}^{q−1} b_v`
（`W_{−1} = 1`）。存在性见 `P_mul_Nser_eq_IE`。 -/
theorem Num_eq_IE_closed_form {q : ℕ} (hq : 1 ≤ q) (Num : ℚ[X])
    (hNum : (↑Num : PowerSeries ℚ) = ↑(Ppoly ℚ (q - 1)) * Nser q) :
    Num = ∑ i ∈ range (q + 1),
      C ((-1 : ℚ) ^ (q - i) * (q.choose i : ℚ)) * Wprev i * ∏ v ∈ Ico i q, bpoly ℚ v := by
  apply Polynomial.coe_injective ℚ
  rw [hNum, P_mul_Nser hq, Numq]

/-- **T4.3(2)**（存在性）：`q ≥ 1` 时 `P_{q−1}·Σ_k N(k,q)x^k` 等于容斥闭式多项式。 -/
theorem P_mul_Nser_eq_IE {q : ℕ} (hq : 1 ≤ q) :
    (↑(Ppoly ℚ (q - 1)) : PowerSeries ℚ) * Nser q
      = ↑(∑ i ∈ range (q + 1),
          C ((-1 : ℚ) ^ (q - i) * (q.choose i : ℚ)) * Wprev i * ∏ v ∈ Ico i q, bpoly ℚ v) :=
  P_mul_Nser hq

end ClosedForm

/-! ## T4.3(3)：正项全历史递推、系数非负与支撑 -/

section FullHistory

/-- 辅助定义（T4.3(3)）：`Zfh n s = (n+1)·Num_{s+2} + n·b_{s+1}·Num_{s+1}`，即 `c4.md` §4.6 的
`Y_{s+3}^{(c)}` 乘以 `n`，`c = (n+1)/n`（`n = 1` 时为 `Y^{(2)} = 2·Num_{q−1} + b_{q−2}·Num_{q−2}`）。 -/
noncomputable def Zfh (n s : ℕ) : ℚ[X] :=
  ((n : ℚ[X]) + 1) * Numq (s + 2) + (n : ℚ[X]) * bpoly ℚ (s + 1) * Numq (s + 1)

/-- 辅助引理（T4.3(3)）：`Z_{s+4}^{(n)} = (n + x)·Num_{s+2} + (s+2)x³·Z_{s+3}^{(n+1)}`
（即 `c4.md` §4.6 的 `Y_q^{(c)} = (1+(c−1)x)Num_{q−2} + c(q−2)x³Y_{q−1}^{(2−1/c)}` 乘以 `n`）。 -/
theorem Zfh_succ (n s : ℕ) :
    Zfh n (s + 1) = ((n : ℚ[X]) + X) * Numq (s + 2) + ((s : ℚ[X]) + 2) * X ^ 3 * Zfh (n + 1) s := by
  have h3 := Numq_succ_three s
  simp only [Zfh, show s + 1 + 2 = s + 3 from rfl, show s + 1 + 1 = s + 2 from rfl]
  rw [h3]
  simp only [bpoly, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_natCast, map_one,
    map_ofNat]
  ring

/-- 辅助引理（T4.3(3)）：`Z_3^{(n)} = n·x + (n+2)·x² + x⁴`。 -/
theorem Zfh_zero (n : ℕ) : Zfh n 0 = (n : ℚ[X]) * X + ((n : ℚ[X]) + 2) * X ^ 2 + X ^ 4 := by
  simp only [Zfh, zero_add, Numq_two, Numq_one, bpoly, Nat.cast_one, map_one]
  ring

/-- 辅助引理（T4.3(3)）：把 `Zfh_succ` 迭代 `s` 次：
`Z_{s+3}^{(n)} = Σ_{t<s} (s+1)^{\underline t}·x^{3t}·(n+t+x)·Num_{s+1−t} + (s+1)!·x^{3s}·Z_3^{(n+s)}`。 -/
theorem Zfh_unroll (s : ℕ) : ∀ n : ℕ, Zfh n s
    = ∑ t ∈ range s, ((Nat.descFactorial (s + 1) t : ℕ) : ℚ[X]) * X ^ (3 * t)
        * (((n + t : ℕ) : ℚ[X]) + X) * Numq (s + 1 - t)
      + (((s + 1).factorial : ℕ) : ℚ[X]) * X ^ (3 * s) * Zfh (n + s) 0 := by
  induction s with
  | zero => intro n; simp
  | succ s ih =>
    intro n
    rw [Zfh_succ, ih (n + 1), Finset.sum_range_succ']
    have hterm : ∀ t ∈ range s,
        ((Nat.descFactorial (s + 1 + 1) (t + 1) : ℕ) : ℚ[X]) * X ^ (3 * (t + 1))
          * (((n + (t + 1) : ℕ) : ℚ[X]) + X) * Numq (s + 1 + 1 - (t + 1))
        = ((s : ℚ[X]) + 2) * X ^ 3 * (((Nat.descFactorial (s + 1) t : ℕ) : ℚ[X]) * X ^ (3 * t)
          * (((n + 1 + t : ℕ) : ℚ[X]) + X) * Numq (s + 1 - t)) := by
      intro t _
      rw [Nat.succ_descFactorial_succ, show s + 1 + 1 - (t + 1) = s + 1 - t by omega,
        show n + (t + 1) = n + 1 + t by omega]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Nat.descFactorial_zero,
      show n + 1 + s = n + (s + 1) by omega, Nat.factorial_succ (s + 1),
      show s + 1 + 1 - 0 = s + 2 by omega]
    push_cast
    ring

/-- 辅助引理（T4.3(3)）：`(s+2)!/(s+1−t)! = (s+2)·(s+1)^{\underline t}`（`t ≤ s+1`）。 -/
theorem factorial_div_eq_descFactorial {s t : ℕ} (ht : t ≤ s + 1) :
    (((s + 2).factorial : ℚ) / ((s + 1 - t).factorial : ℚ))
      = ((s : ℚ) + 2) * (Nat.descFactorial (s + 1) t : ℚ) := by
  have h := Nat.factorial_mul_descFactorial ht
  have h' : ((s + 1 - t).factorial : ℚ) * ((s + 1).descFactorial t : ℚ) = ((s + 1).factorial : ℚ) := by
    exact_mod_cast h
  have hf : ((s + 2).factorial : ℚ) = ((s : ℚ) + 2) * ((s + 1).factorial : ℚ) := by
    rw [show s + 2 = s + 1 + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  rw [div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), hf, ← h']
  ring

/-- **T4.3(3)**（正项全历史递推，`c4.md` 定理 4.6）：对 `q ≥ 3`，
`Num_q = x·Num_{q−1} + Σ_{m=2}^{q−2} ((q−1)!/m!)·x^{3(q−1−m)}·(q−1−m+x)·Num_m
  + (q−1)!·((q−2)x^{3q−5} + q·x^{3q−4} + x^{3q−2})`。
证明：`Num_q = x·Num_{q−1} + (q−1)x³·Z_q^{(1)}`（三项递推），再把 `Zfh_succ` 迭代到 `Z_3`
（`Zfh_unroll`、`Zfh_zero`），令 `m = q − 2 − t` 重排求和指标。 -/
theorem Numq_full_history {q : ℕ} (hq : 3 ≤ q) :
    Numq q = X * Numq (q - 1)
      + ∑ m ∈ Icc 2 (q - 2), C (((q - 1).factorial : ℚ) / (m.factorial : ℚ))
          * X ^ (3 * (q - 1 - m)) * (C ((q : ℚ) - 1 - m) + X) * Numq m
      + C (((q - 1).factorial : ℚ))
          * (C ((q : ℚ) - 2) * X ^ (3 * q - 5) + C (q : ℚ) * X ^ (3 * q - 4) + X ^ (3 * q - 2)) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 3 := ⟨q - 3, by omega⟩
  have h1 : Numq (s + 3) = X * Numq (s + 2) + ((s : ℚ[X]) + 2) * X ^ 3 * Zfh 1 s := by
    rw [Numq_succ_three]
    simp only [Zfh, Nat.cast_one]
    ring
  rw [h1, Zfh_unroll s 1, Zfh_zero]
  rw [show s + 3 - 1 = s + 2 by omega, show s + 3 - 2 = s + 1 by omega]
  have hsum : ∑ m ∈ Icc 2 (s + 1), C (((s + 2).factorial : ℚ) / (m.factorial : ℚ))
          * X ^ (3 * (s + 2 - m)) * (C (((s + 3 : ℕ) : ℚ) - 1 - m) + X) * Numq m
      = ((s : ℚ[X]) + 2) * X ^ 3 * ∑ t ∈ range s, ((Nat.descFactorial (s + 1) t : ℕ) : ℚ[X])
          * X ^ (3 * t) * (((1 + t : ℕ) : ℚ[X]) + X) * Numq (s + 1 - t) := by
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_nbij' (fun t => s + 1 - t) (fun m => s + 1 - m)
    · intro t ht
      rw [Finset.mem_range] at ht
      rw [Finset.mem_Icc]
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_range]
      omega
    · intro t ht
      rw [Finset.mem_range] at ht
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      omega
    · intro t ht
      simp only [Finset.mem_range] at ht
      rw [factorial_div_eq_descFactorial (by omega), show 3 * (s + 2 - (s + 1 - t)) = 3 + 3 * t by omega]
      have hc : ((s + 3 : ℕ) : ℚ) - 1 - ((s + 1 - t : ℕ) : ℚ) = 1 + t := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hc]
      simp only [map_mul, map_add, map_natCast, map_one, map_ofNat, Nat.cast_add, Nat.cast_one]
      ring
  rw [hsum, show 3 * (s + 3) - 5 = 3 * s + 4 by omega, show 3 * (s + 3) - 4 = 3 * s + 5 by omega,
    show 3 * (s + 3) - 2 = 3 * s + 7 by omega,
    show (s + 2).factorial = (s + 2) * (s + 1).factorial from Nat.factorial_succ (s + 1)]
  simp only [map_mul, map_add, map_sub, map_natCast, map_ofNat, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- **T4.3(3)**（注：`q = 2` 时全历史递推不成立）：`q = 2` 时右边（求和为空）是
`x·Num_1 + 1!·(0·x + 2x² + x⁴) = 3x² + x⁴`，而 `Num_2 = 2x² + x⁴`。 -/
theorem full_history_at_two :
    X * Numq 1 + C ((Nat.factorial 1 : ℕ) : ℚ)
        * (C ((2 : ℚ) - 2) * X ^ (3 * 2 - 5) + C (2 : ℚ) * X ^ (3 * 2 - 4) + X ^ (3 * 2 - 2))
      = 3 * X ^ 2 + X ^ 4 ∧ (3 * X ^ 2 + X ^ 4 : ℚ[X]) ≠ Numq 2 := by
  refine ⟨?_, ?_⟩
  · rw [Numq_one]
    simp only [Nat.factorial_one, Nat.cast_one, map_one, one_mul, sub_self, map_zero, zero_mul,
      zero_add, show 3 * 2 - 4 = 2 by rfl, show 3 * 2 - 2 = 4 by rfl, map_ofNat]
    ring
  · rw [Numq_two]
    intro h
    have h2 := congrArg (Polynomial.eval (1 : ℚ)) h
    simp only [eval_add, eval_mul, eval_X, eval_pow, eval_ofNat, one_pow, mul_one] at h2
    norm_num at h2

/-- 辅助定义（T4.3(3)）：多项式的系数全非负。 -/
def HasNonnegCoeffs (p : ℚ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

theorem hasNonnegCoeffs_add {p q : ℚ[X]} (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p + q) := fun n => by rw [coeff_add]; exact add_nonneg (hp n) (hq n)

theorem hasNonnegCoeffs_mul {p q : ℚ[X]} (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p * q) := fun n => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem hasNonnegCoeffs_C {c : ℚ} (hc : 0 ≤ c) : HasNonnegCoeffs (C c) := fun n => by
  rw [coeff_C]; split_ifs <;> simp [hc]

theorem hasNonnegCoeffs_X : HasNonnegCoeffs (X : ℚ[X]) := fun n => by
  rw [coeff_X]; split_ifs <;> norm_num

theorem hasNonnegCoeffs_X_pow (k : ℕ) : HasNonnegCoeffs ((X : ℚ[X]) ^ k) := fun n => by
  rw [coeff_X_pow]; split_ifs <;> norm_num

theorem hasNonnegCoeffs_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X])
    (h : ∀ i ∈ s, HasNonnegCoeffs (f i)) : HasNonnegCoeffs (∑ i ∈ s, f i) := fun n => by
  rw [finsetSum_coeff]; exact Finset.sum_nonneg fun i hi => h i hi n

/-- 辅助引理（T4.3(3)）：`(C a·(C b·x^{e₁} + C c·x^{e₂} + x^{e₃}))` 的 `x^j` 系数。 -/
theorem coeff_bdry_term (a b c : ℚ) (e1 e2 e3 j : ℕ) :
    (C a * (C b * X ^ e1 + C c * X ^ e2 + X ^ e3)).coeff j
      = a * ((if j = e1 then b else 0) + (if j = e2 then c else 0) + (if j = e3 then 1 else 0)) := by
  simp only [coeff_C_mul, coeff_add, coeff_X_pow, mul_ite, mul_one, mul_zero]

/-- 辅助引理（T4.3(3)）：`Numq_full_history` 写成 `q = s + 3`。 -/
theorem Numq_full_history' (s : ℕ) :
    Numq (s + 3) = X * Numq (s + 2)
      + ∑ m ∈ Icc 2 (s + 1), C (((s + 2).factorial : ℚ) / (m.factorial : ℚ))
          * X ^ (3 * (s + 2 - m)) * (C (((s + 3 : ℕ) : ℚ) - 1 - m) + X) * Numq m
      + C (((s + 2).factorial : ℚ))
          * (C ((s : ℚ) + 1) * X ^ (3 * s + 4) + C ((s : ℚ) + 3) * X ^ (3 * s + 5)
            + X ^ (3 * s + 7)) := by
  have h := Numq_full_history (q := s + 3) (by omega)
  rw [show s + 3 - 1 = s + 2 by omega, show s + 3 - 2 = s + 1 by omega,
    show 3 * (s + 3) - 5 = 3 * s + 4 by omega, show 3 * (s + 3) - 4 = 3 * s + 5 by omega,
    show 3 * (s + 3) - 2 = 3 * s + 7 by omega] at h
  have hb1 : (C (((s + 3 : ℕ) : ℚ) - 2) : ℚ[X]) = C ((s : ℚ) + 1) := by
    congr 1; push_cast; ring
  have hb2 : (C ((s + 3 : ℕ) : ℚ) : ℚ[X]) = C ((s : ℚ) + 3) := by
    congr 1; push_cast; ring
  rw [hb1, hb2] at h
  exact h

/-- **T4.3(3)**（系数全非负）：对一切 `q ≥ 0`，`Num_q` 的系数全 `≥ 0`。
证明：对 `q` 强归纳，`q ≤ 2` 直接验证，`q ≥ 3` 用正项全历史递推 `Numq_full_history`。 -/
theorem Numq_hasNonnegCoeffs (q : ℕ) : HasNonnegCoeffs (Numq q) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q, ih with
    | 0, _ =>
      rw [Numq_zero_eq_one, ← C_1]; exact hasNonnegCoeffs_C zero_le_one
    | 1, _ => rw [Numq_one]; exact hasNonnegCoeffs_X
    | 2, _ =>
      rw [Numq_two, show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm]
      exact hasNonnegCoeffs_add
        (hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by norm_num)) (hasNonnegCoeffs_X_pow 2))
        (hasNonnegCoeffs_X_pow 4)
    | s + 3, ih =>
      rw [Numq_full_history' s]
      refine hasNonnegCoeffs_add (hasNonnegCoeffs_add
        (hasNonnegCoeffs_mul hasNonnegCoeffs_X (ih (s + 2) (by omega)))
        (hasNonnegCoeffs_sum _ _ fun m hm => ?_)) ?_
      · rw [Finset.mem_Icc] at hm
        have hm' : (m : ℚ) ≤ s + 1 := by exact_mod_cast hm.2
        refine hasNonnegCoeffs_mul (hasNonnegCoeffs_mul (hasNonnegCoeffs_mul
          (hasNonnegCoeffs_C (by positivity)) (hasNonnegCoeffs_X_pow _))
          (hasNonnegCoeffs_add (hasNonnegCoeffs_C ?_) hasNonnegCoeffs_X))
          (ih m (by omega))
        push_cast
        linarith
      · exact hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by positivity))
          (hasNonnegCoeffs_add (hasNonnegCoeffs_add
            (hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by positivity)) (hasNonnegCoeffs_X_pow _))
            (hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by positivity)) (hasNonnegCoeffs_X_pow _)))
            (hasNonnegCoeffs_X_pow _))

/-- **T4.3(3)**（系数全非负）：`[x^j]Num_q ≥ 0`。 -/
theorem Numq_coeff_nonneg (q j : ℕ) : 0 ≤ (Numq q).coeff j := Numq_hasNonnegCoeffs q j

/-- 辅助引理（T4.3(3)）：`Num_{s+3}` 的三部分（`x·Num_{s+2}`、求和、边界项）系数都非负，
所以 `Num_{s+3}` 的系数不小于其中任一部分的系数。 -/
theorem Numq_full_history_parts (s : ℕ) :
    ∃ T1 T2 T3 : ℚ[X], Numq (s + 3) = T1 + T2 + T3 ∧ T1 = X * Numq (s + 2) ∧
      HasNonnegCoeffs T1 ∧ HasNonnegCoeffs T2 ∧ HasNonnegCoeffs T3 ∧
      T3 = C (((s + 2).factorial : ℚ))
          * (C ((s : ℚ) + 1) * X ^ (3 * s + 4) + C ((s : ℚ) + 3) * X ^ (3 * s + 5)
            + X ^ (3 * s + 7)) ∧
      (T1 + T2).natDegree ≤ 3 * s + 5 := by
  refine ⟨_, _, _, Numq_full_history' s, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · exact hasNonnegCoeffs_mul hasNonnegCoeffs_X (Numq_hasNonnegCoeffs _)
  · refine hasNonnegCoeffs_sum _ _ fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hm' : (m : ℚ) ≤ s + 1 := by exact_mod_cast hm.2
    refine hasNonnegCoeffs_mul (hasNonnegCoeffs_mul (hasNonnegCoeffs_mul
      (hasNonnegCoeffs_C (by positivity)) (hasNonnegCoeffs_X_pow _))
      (hasNonnegCoeffs_add (hasNonnegCoeffs_C ?_) hasNonnegCoeffs_X)) (Numq_hasNonnegCoeffs m)
    push_cast
    linarith
  · exact hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by positivity))
      (hasNonnegCoeffs_add (hasNonnegCoeffs_add
        (hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by positivity)) (hasNonnegCoeffs_X_pow _))
        (hasNonnegCoeffs_mul (hasNonnegCoeffs_C (by positivity)) (hasNonnegCoeffs_X_pow _)))
        (hasNonnegCoeffs_X_pow _))
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      have h1 := natDegree_X_le (R := ℚ)
      have h2 := natDegree_Numq (q := s + 2) (by omega)
      omega
    · refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      refine natDegree_mul_le.trans ?_
      have hA : (C (((s + 2).factorial : ℚ) / (m.factorial : ℚ)) * X ^ (3 * (s + 2 - m))
          * (C (((s + 3 : ℕ) : ℚ) - 1 - m) + X)).natDegree ≤ 3 * (s + 2 - m) + 1 := by
        refine natDegree_mul_le.trans ?_
        have h1 := (natDegree_C_mul_le (((s + 2).factorial : ℚ) / (m.factorial : ℚ))
          (X ^ (3 * (s + 2 - m)) : ℚ[X])).trans (natDegree_X_pow_le _)
        have h2 : (C (((s + 3 : ℕ) : ℚ) - 1 - m) + X : ℚ[X]).natDegree ≤ 1 := by
          rw [natDegree_C_add]; exact natDegree_X_le
        omega
      have hB := natDegree_Numq (q := m) (by omega)
      omega

/-- **T4.3(3)**（`[x^{3q−3}]Num_q = 0`，`q ≥ 2`）。 -/
theorem Numq_coeff_gap {q : ℕ} (hq : 2 ≤ q) : (Numq q).coeff (3 * q - 3) = 0 := by
  rcases (show q = 2 ∨ 3 ≤ q by omega) with rfl | h3
  · rw [Numq_two]; simp [coeff_X_pow]
  · obtain ⟨s, rfl⟩ : ∃ s, q = s + 3 := ⟨q - 3, by omega⟩
    obtain ⟨T1, T2, T3, hN, -, -, -, -, hT3, hdeg⟩ := Numq_full_history_parts s
    rw [hN, coeff_add, coeff_eq_zero_of_natDegree_lt (by omega), zero_add, hT3,
      coeff_bdry_term, show 3 * (s + 3) - 3 = 3 * s + 6 by omega]
    simp only [show 3 * s + 6 ≠ 3 * s + 4 by omega, show 3 * s + 6 ≠ 3 * s + 5 by omega,
      show 3 * s + 6 ≠ 3 * s + 7 by omega, ↓reduceIte, add_zero, mul_zero]

/-- 辅助引理（T4.3(3)）：`q ≥ 2`、`q ≤ j ≤ 3q − 4` 时 `[x^j]Num_q > 0`。 -/
theorem Numq_coeff_pos_of_le {q : ℕ} (hq : 2 ≤ q) :
    ∀ j, q ≤ j → j ≤ 3 * q - 4 → 0 < (Numq q).coeff j := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro j h1 h2
    rcases (show q = 2 ∨ 3 ≤ q by omega) with rfl | h3
    · have hj : j = 2 := by omega
      subst hj
      rw [Numq_two]; simp [coeff_X_pow]
    · obtain ⟨s, rfl⟩ : ∃ s, q = s + 3 := ⟨q - 3, by omega⟩
      obtain ⟨T1, T2, T3, hN, hT1, h1n, h2n, h3n, hT3, -⟩ := Numq_full_history_parts s
      rw [hN]
      rcases (show j ≤ 3 * s + 3 ∨ j = 3 * s + 4 ∨ j = 3 * s + 5 by omega) with hj | hj | hj
      · -- 来自 `x·Num_{s+2}`
        have hpos : 0 < T1.coeff j := by
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          rw [hT1, coeff_X_mul]
          exact ih (s + 2) (by omega) (by omega) j' (by omega) (by omega)
        rw [coeff_add, coeff_add]
        linarith [h2n j, h3n j]
      · -- 来自边界项 `(q−1)!(q−2)x^{3q−5}`
        have hpos : 0 < T3.coeff j := by
          rw [hT3, coeff_bdry_term, hj]
          simp only [show 3 * s + 4 ≠ 3 * s + 5 by omega, show 3 * s + 4 ≠ 3 * s + 7 by omega,
            eq_self, ↓reduceIte, add_zero]
          positivity
        rw [coeff_add, coeff_add]
        linarith [h1n j, h2n j]
      · -- 来自边界项 `(q−1)!·q·x^{3q−4}`
        have hpos : 0 < T3.coeff j := by
          rw [hT3, coeff_bdry_term, hj]
          simp only [show 3 * s + 5 ≠ 3 * s + 4 by omega, show 3 * s + 5 ≠ 3 * s + 7 by omega,
            eq_self, ↓reduceIte, zero_add, add_zero]
          positivity
        rw [coeff_add, coeff_add]
        linarith [h1n j, h2n j]

/-- **T4.3(3)**（支撑）：对 `q ≥ 2`，`[x^j]Num_q > 0` 当且仅当 `q ≤ j ≤ 3q − 4` 或 `j = 3q − 2`；
其余系数为 0（与 `Numq_coeff_nonneg` 合起来：非零项恰为 `x^q, …, x^{3q−4}` 与 `x^{3q−2}`）。 -/
theorem Numq_coeff_pos_iff {q : ℕ} (hq : 2 ≤ q) (j : ℕ) :
    0 < (Numq q).coeff j ↔ (q ≤ j ∧ j ≤ 3 * q - 4) ∨ j = 3 * q - 2 := by
  constructor
  · intro hpos
    by_contra hcon
    rcases (show j < q ∨ j = 3 * q - 3 ∨ 3 * q - 2 < j by omega) with hj | hj | hj
    · rw [coeff_Numq_of_lt (by omega) hj] at hpos; exact lt_irrefl 0 hpos
    · rw [hj, Numq_coeff_gap hq] at hpos; exact lt_irrefl 0 hpos
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_Numq (by omega)]; exact hj)] at hpos
      exact lt_irrefl 0 hpos
  · rintro (⟨h1, h2⟩ | h)
    · exact Numq_coeff_pos_of_le hq j h1 h2
    · subst h
      have hlc : (Numq q).coeff (3 * q - 2) = (Numq q).leadingCoeff := by
        rw [leadingCoeff, natDegree_Numq (by omega)]
      rw [hlc, leadingCoeff_Numq (by omega)]
      exact_mod_cast Nat.factorial_pos _

/-- **T4.3(3)**（支撑，`≠ 0` 的写法）：对 `q ≥ 2`，`[x^j]Num_q ≠ 0` 当且仅当
`q ≤ j ≤ 3q − 4` 或 `j = 3q − 2`。 -/
theorem Numq_coeff_ne_zero_iff {q : ℕ} (hq : 2 ≤ q) (j : ℕ) :
    (Numq q).coeff j ≠ 0 ↔ (q ≤ j ∧ j ≤ 3 * q - 4) ∨ j = 3 * q - 2 := by
  rw [← Numq_coeff_pos_iff hq j]
  exact ⟨fun h => lt_of_le_of_ne (Numq_coeff_nonneg q j) (Ne.symm h), fun h => ne_of_gt h⟩

end FullHistory

/-! ## T4.3(4)：`Num_q(1)` 与 A000262 -/

section EvalOne

/-- **T4.3(4)**（`x = 1` 处的递推）：对 `q ≥ 3`，
`Num_q(1) = (2q−1)·Num_{q−1}(1) − (q−1)(q−2)·Num_{q−2}(1)`（因为 `b_v(1) = −v`）。
这正是 A000262 的递推 `a(n) = (2n−1)a(n−1) − (n−1)(n−2)a(n−2)`。 -/
theorem Numq_eval_one_rec {q : ℕ} (hq : 3 ≤ q) :
    (Numq q).eval 1 = (2 * (q : ℚ) - 1) * (Numq (q - 1)).eval 1
      - ((q : ℚ) - 1) * ((q : ℚ) - 2) * (Numq (q - 2)).eval 1 := by
  rw [Numq_three_term hq]
  simp only [eval_add, eval_mul, eval_X, eval_C, eval_pow, eval_bpoly, one_pow, mul_one]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **T4.3(4)**（初值）：`Num_1(1) = 1`、`Num_2(1) = 3`。 -/
theorem Numq_eval_one_init : (Numq 1).eval 1 = 1 ∧ (Numq 2).eval 1 = 3 := by
  rw [Numq_one, Numq_two]
  norm_num

end EvalOne

/-! ## T4.3(5)：低次系数 `[x^{q+j}]Num_q`（`j = 1, 2`） -/

section LowCoeff

/-- 辅助引理（T4.3(5)）：`[x^n](p·b_i) = [x^n]p − [x^{n−1}]p − i·[x^{n−3}]p`（越界取 0）。 -/
theorem coeff_mul_bpoly (p : ℚ[X]) (i n : ℕ) :
    (p * bpoly ℚ i).coeff n = p.coeff n - (if 1 ≤ n then p.coeff (n - 1) else 0)
      - (i : ℚ) * (if 3 ≤ n then p.coeff (n - 3) else 0) := by
  have h : p * bpoly ℚ i = p - p * X ^ 1 - C (i : ℚ) * (p * X ^ 3) := by
    simp only [bpoly, pow_one]; ring
  rw [h, coeff_sub, coeff_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mul_X_pow']

/-- 辅助引理（T4.3(5)）：`π_1 = [x]P_m = −(m+1)`。 -/
theorem coeff_one_Ppoly (m : ℕ) : (Ppoly ℚ m).coeff 1 = -((m : ℚ) + 1) := by
  induction m with
  | zero => rw [Ppoly_zero]; simp [bpoly, coeff_X, coeff_one]
  | succ m ih =>
    rw [Ppoly_succ, coeff_mul_bpoly, ih]
    simp only [le_refl, ↓reduceIte, Nat.sub_self, coeff_zero_P,
      show ¬ (3 ≤ 1) by norm_num, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
    ring

/-- 辅助引理（T4.3(5)）：`π_2 = [x²]P_m = (m+1)m/2 = C(m+1, 2)`。 -/
theorem coeff_two_Ppoly (m : ℕ) : (Ppoly ℚ m).coeff 2 = ((m : ℚ) + 1) * m / 2 := by
  induction m with
  | zero => rw [Ppoly_zero]; simp [bpoly, coeff_X, coeff_one]
  | succ m ih =>
    rw [Ppoly_succ, coeff_mul_bpoly, ih]
    simp only [show (1 : ℕ) ≤ 2 by norm_num, ↓reduceIte, show (2 : ℕ) - 1 = 1 by norm_num,
      coeff_one_Ppoly, show ¬ (3 ≤ 2) by norm_num, mul_zero, sub_zero, Nat.cast_add,
      Nat.cast_one]
    ring

/-- **T4.3(5)**（证明中的恒等式，一切 `j`）：对 `q ≥ 1`，
`ν_j(q) := [x^{q+j}]Num_q = Σ_{i=0}^{j} π_i(q)·N(q+j−i, q)`，`π_i(q) := [x^i]P_{q−1}`；
`N(q+j−i, q) = D(q+j−i, j−i)` 即近对角线 `N(k, k−d)`。 -/
theorem Numq_coeff_q_add (q j : ℕ) (hq : 1 ≤ q) :
    (Numq q).coeff (q + j)
      = ∑ i ∈ range (j + 1), (Ppoly ℚ (q - 1)).coeff i * (N (q + j - i) q : ℚ) := by
  rw [coeff_Numq hq]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [N_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- 辅助引理（T4.3(5)）：`N(k, k−1) = k² − k − 4`（`k ≥ 4`，HNum/Binomial 的 `N_subdiag` 搬到 `ℚ`）。 -/
theorem N_subdiag_rat {k : ℕ} (hk : 4 ≤ k) :
    (N k (k - 1) : ℚ) = (k : ℚ) ^ 2 - k - 4 := by
  have h := congrArg (Int.cast : ℤ → ℚ) (N_subdiag k hk)
  push_cast at h
  exact h

/-- 辅助引理（T4.3(5)）：`N(6,4) = 65` 的纯算术部分。各个 `N` 值写成变量 `a_{kq}`，由三角递推的四个实例与
已知的小值推出 `a_{64} = 65`。 -/
theorem N_six_four_aux {a64 a53 a54 a32 a33 a34 a42 a43 a21 a22 a23 a31 a20 a10 a11 a12 : ℕ}
    (h64 : a64 = a53 + a54 + 3 * (a32 + 2 * a33 + a34))
    (h53 : a53 = a42 + a43 + 2 * (a21 + 2 * a22 + a23))
    (h42 : a42 = a31 + a32 + (a10 + 2 * a11 + a12))
    (h31 : a31 = a20 + a21)
    (h43 : a43 = 8) (h54 : a54 = 16) (h32 : a32 = 4) (h33 : a33 = 2) (h20 : a20 = 0)
    (h10 : a10 = 0) (h12 : a12 = 0) (h23 : a23 = 0) (h34 : a34 = 0) (h11 : a11 = 1)
    (h21 : a21 = 1) (h22 : a22 = 2) : a64 = 65 := by
  subst h43 h54 h32 h33 h20 h10 h12 h23 h34 h11 h21 h22
  omega

/-- 辅助引理（T4.3(5)）：三角递推在 `(k, r) = (0, 0)` 的实例 `N(3,1) = N(2,0) + N(2,1)`。 -/
theorem N_tri_three_one : N 3 1 = N 2 0 + N 2 1 := by
  have h := N_tri 0 0
  simp only [Nat.reduceAdd, Nat.reduceSub, zero_mul, add_zero] at h
  exact h

/-- 辅助引理（T4.3(5)）：三角递推在 `(k, r) = (1, 1)` 的实例。 -/
theorem N_tri_four_two : N 4 2 = N 3 1 + N 3 2 + (N 1 0 + 2 * N 1 1 + N 1 2) := by
  have h := N_tri 1 1
  simp only [Nat.reduceAdd, Nat.reduceSub, one_mul] at h
  exact h

/-- 辅助引理（T4.3(5)）：三角递推在 `(k, r) = (2, 2)` 的实例。数字的化简用 `rw` 代入数字等式完成：
若用 `simp` 把 `N (2+3) (2+1)` 化成 `N 5 3`，内核核对这一步时会展开 `N` 的组合定义去计算（2026-10-05 实测：
`(kernel) deterministic timeout`，不设上限时内存超过 18 GB，曾把机器拖崩）。 -/
theorem N_tri_five_three : N 5 3 = N 4 2 + N 4 3 + 2 * (N 2 1 + 2 * N 2 2 + N 2 3) := by
  have h := N_tri 2 2
  rw [show (2 : ℕ) + 3 = 5 from rfl, show (2 : ℕ) + 2 = 4 from rfl, show (2 : ℕ) + 1 = 3 from rfl,
    show (2 : ℕ) - 1 = 1 from rfl] at h
  exact h

/-- 辅助引理（T4.3(5)）：三角递推在 `(k, r) = (3, 3)` 的实例（写法同 `N_tri_five_three`）。 -/
theorem N_tri_six_four : N 6 4 = N 5 3 + N 5 4 + 3 * (N 3 2 + 2 * N 3 3 + N 3 4) := by
  have h := N_tri 3 3
  rw [show (3 : ℕ) + 3 = 6 from rfl, show (3 : ℕ) + 2 = 5 from rfl, show (3 : ℕ) + 1 = 4 from rfl,
    show (3 : ℕ) - 1 = 2 from rfl] at h
  exact h

/-- 辅助引理（T4.3(5)）：`N(4,3) = 8`、`N(5,4) = 16`（`N_subdiag` 取 `k = 4, 5`）。 -/
theorem N_four_three_five_four : N 4 3 = 8 ∧ N 5 4 = 16 := by
  constructor
  · have h := N_subdiag 4 (by norm_num)
    rw [show (4 : ℕ) - 1 = 3 from rfl] at h
    have h' : ((N 4 3 : ℕ) : ℤ) = ((8 : ℕ) : ℤ) := by rw [h]; norm_num
    exact Nat.cast_injective h'
  · have h := N_subdiag 5 (by norm_num)
    rw [show (5 : ℕ) - 1 = 4 from rfl] at h
    have h' : ((N 5 4 : ℕ) : ℤ) = ((16 : ℕ) : ℤ) := by rw [h]; norm_num
    exact Nat.cast_injective h'

/-- 辅助引理（T4.3(5)）：`N(6,4) = 65`（由三角递推逐步算出）。
写法上的约束（2026-10-05 实测）：不能让内核去核对「含具体数字的 `N a b` 之间」或「`N a b` 与数字之间」的
定义相等，否则内核会展开 `N` 的组合定义、枚举全部序列（`N 6 4` 要枚举 `5^6` 个），编译时内存超过 18 GB。
这里先在变量层面做算术（`N_six_four_aux`），再把已经单独证好的各个实例代进去，代入时类型逐字一致。 -/
theorem N_six_four : N 6 4 = 65 :=
  N_six_four_aux N_tri_six_four N_tri_five_three N_tri_four_two N_tri_three_one
    N_four_three_five_four.1 N_four_three_five_four.2 N_three_two (N_diag 3 (by norm_num))
    (N_succ_zero 1) (N_succ_zero 0) (N_eq_zero_of_lt (by norm_num)) (N_eq_zero_of_lt (by norm_num))
    (N_eq_zero_of_lt (by norm_num)) N_init.2.1 N_init.2.2.1 N_init.2.2.2

/-- 辅助引理（T4.3(5)，T4.1 的 `d = 2` 情形，本文件独立证明）：`k ≥ 6` 时
`N(k, k−2) = p_2(k) = (k⁴ − 10k³ + 43k² − 98k + 164)/4`（写成 `k = s + 6`）。 -/
theorem N_sub_two (s : ℕ) :
    (N (s + 6) (s + 4) : ℚ) = (((s : ℚ) + 6) ^ 4 - 10 * ((s : ℚ) + 6) ^ 3
      + 43 * ((s : ℚ) + 6) ^ 2 - 98 * ((s : ℚ) + 6) + 164) / 4 := by
  induction s with
  | zero => norm_num [N_six_four]
  | succ s ih =>
    have h := N_tri (s + 4) (s + 4)
    have e1 : N (s + 4) (s + 4 + 1) = 0 := N_eq_zero_of_lt (by omega)
    have e2 : N (s + 4) (s + 4) = 2 := N_diag (s + 4) (by omega)
    rw [e1, e2, show s + 4 - 1 = s + 3 by omega] at h
    have hq : (N (s + 4 + 3) (s + 4 + 1) : ℚ)
        = N (s + 4 + 2) (s + 4) + N (s + 4 + 2) (s + 4 + 1)
          + (s + 4 : ℚ) * (N (s + 4) (s + 3) + 2 * 2 + 0) := by
      exact_mod_cast h
    have hA := N_subdiag_rat (k := s + 6) (by omega)
    have hB := N_subdiag_rat (k := s + 4) (by omega)
    rw [show s + 6 - 1 = s + 4 + 1 by omega] at hA
    rw [show s + 4 - 1 = s + 3 by omega] at hB
    rw [show s + 1 + 6 = s + 4 + 3 by omega, show s + 1 + 4 = s + 4 + 1 by omega, hq,
      show s + 4 + 2 = s + 6 by omega, ih, hA, hB]
    push_cast
    ring

/-- **T4.3(5)**（`j = 1`）：`q ≥ 3` 时 `[x^{q+1}]Num_q = q² − q − 4`。 -/
theorem Numq_coeff_q_add_one {q : ℕ} (hq : 3 ≤ q) :
    (Numq q).coeff (q + 1) = (q : ℚ) ^ 2 - q - 4 := by
  rw [Numq_coeff_q_add q 1 (by omega), Finset.sum_range_succ, Finset.sum_range_one,
    coeff_zero_P, coeff_one_Ppoly, Nat.sub_zero, Nat.add_sub_cancel, N_diag q (by omega)]
  have hA := N_subdiag_rat (k := q + 1) (by omega)
  rw [Nat.add_sub_cancel] at hA
  rw [hA, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **T4.3(5)**（`j = 2`）：`q ≥ 4` 时 `[x^{q+2}]Num_q = (q⁴ − 6q³ + 7q² − 2q + 76)/4`。 -/
theorem Numq_coeff_q_add_two {q : ℕ} (hq : 4 ≤ q) :
    (Numq q).coeff (q + 2) = ((q : ℚ) ^ 4 - 6 * q ^ 3 + 7 * q ^ 2 - 2 * q + 76) / 4 := by
  rw [Numq_coeff_q_add q 2 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, coeff_zero_P, coeff_one_Ppoly, coeff_two_Ppoly, Nat.sub_zero,
    show q + 2 - 1 = q + 1 by omega, show q + 2 - 2 = q by omega, N_diag q (by omega)]
  have hA := N_subdiag_rat (k := q + 1) (by omega)
  rw [Nat.add_sub_cancel] at hA
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 4 := ⟨q - 4, by omega⟩
  have hB := N_sub_two s
  rw [show s + 4 + 2 = s + 6 by omega, hA, hB, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **T4.3(5)**（门槛精确，`j = 0`）：`q = 1` 时 `[x^1]Num_1 − 2 = −1 = (−1)^{1}·1!`
（`ν_0 = 2` 对 `q ≥ 2` 成立，见 HNum 的 `Numq_lowest`）。 -/
theorem Numq_coeff_exception_zero :
    (Numq 1).coeff (1 + 0) - 2 = (-1) ^ (0 + 1) * ((0 + 1).factorial : ℚ) := by
  rw [Numq_one]
  norm_num [coeff_X, Nat.factorial]

/-- **T4.3(5)**（门槛精确，`j = 1`）：`q = 2` 时 `[x³]Num_2 − (2² − 2 − 4) = 2 = (−1)^{2}·2!`，
所以 `ν_1 = q² − q − 4` 的门槛 `q ≥ 3` 是精确的。 -/
theorem Numq_coeff_exception_one :
    (Numq 2).coeff (2 + 1) - ((2 : ℚ) ^ 2 - 2 - 4) = (-1) ^ (1 + 1) * ((1 + 1).factorial : ℚ) := by
  rw [Numq_two]
  norm_num [coeff_X_pow, Nat.factorial]

/-- **T4.3(5)**（门槛精确，`j = 2`）：`q = 3` 时 `[x⁵]Num_3 − (3⁴ − 6·3³ + 7·3² − 2·3 + 76)/4
= 7 − 13 = −6 = (−1)^{3}·3!`，所以 `ν_2` 的门槛 `q ≥ 4` 是精确的。 -/
theorem Numq_coeff_exception_two :
    (Numq 3).coeff (3 + 2) - (((3 : ℚ) ^ 4 - 6 * 3 ^ 3 + 7 * 3 ^ 2 - 2 * 3 + 76) / 4)
      = (-1) ^ (2 + 1) * ((2 + 1).factorial : ℚ) := by
  rw [Numq_three]
  norm_num [coeff_X_pow, Nat.factorial]

end LowCoeff

end A207123
