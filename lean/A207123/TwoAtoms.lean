import A207123.NThreeAtoms

/-!
# 「每个 i 两个原子」的存在例子（猜想总表 A25 (d) 的 m ≤ 2、A26 (iii) 的 q ≤ 3）

原子 `c_i(n) = [xⁿ] 1/b_i`（`n < 0` 时取 0：`ciZ`）。notes/12 定理 3 与 notes/13 注 5.2 给出的例子：
* `U_one_two_atoms`：一切 `k` 有 `U_k(1) = c_1(k+2) + c_1(k+1) − 1`（notes/12 定理 3 的 `m = 1`，只有 `i = 1`）；
  `U_one_atoms` 是 T2.5(3) 直接给出的等价写法 `U_k(1) = c_1(k+3) + c_1(k−2) − 1`。
* `U_two_two_atoms`：`k = 0` 与 `k ≥ 2` 时 `U_k(2) = 1/2 − ¼c_1(k+10) + ¼c_1(k−4) + (5/2)c_2(k+3) + 6c_2(k−2)`
  （猜想总表 A25 (d) 的例子）；`k = 1` 时不成立（`U_two_two_atoms_one`）。
* `N_two_two_atoms`：`k ≥ 1` 时 `N(k,2) = c_1(k+3) + c_1(k−2) − 3`。
* `N_three_two_atoms`：`k ≥ 1` 时 `N(k,3) = 13/2 − c_1(k+8) − 2c_1(k−2) + (5/2)c_2(k+3) + 6c_2(k−2)`（猜想总表 A26 (iii)
  的例子）；`k = 0` 时不成立（式子给 1，`N(0,3) = 0`：`N_three_two_atoms_zero`）。

证明：`U_k(1)`、`U_k(2)` 由 T2.5(3) 的部分分式式 `U_F4`（对一切 `k`）在 `m = 1, 2` 展开（`U_two_atoms_F4`）；`N` 由容斥式
`N_eq_sum_U` 化为 `U_k(0)`、`U_k(1)`、`U_k(2)`；剩下的是 `c_1`、`c_2` 的恒等式，由递推 `c_i(n+3) = c_i(n+2) + i·c_i(n)` 的
线性组合得到（`ci_one_id_C1`、`ci_two_id_C2`、`ci_one_id_C3`），小的 `k` 直接代入数值（`ci_one_vals`、`ci_two_vals`）。
「m ≥ 3 时不存在」与「4 ≤ q ≤ 30 时不存在」是计算机辅助的有限计算（前者用证书素数排除 45,151,680 个剩余类；q ≥ 31
未判定），不在这里。
-/

namespace A207123

open Finset

/-- `c_1(n+3) = c_1(n+2) + c_1(n)`。 -/
theorem ci_one_rec (n : ℕ) : ci 1 (n + 3) = ci 1 (n + 2) + ci 1 n := by
  rw [ci_add_three]
  push_cast
  ring

/-- `c_2(n+3) = c_2(n+2) + 2·c_2(n)`。 -/
theorem ci_two_rec (n : ℕ) : ci 2 (n + 3) = ci 2 (n + 2) + 2 * ci 2 n := by
  rw [ci_add_three]
  push_cast
  ring

/-- `c_1(0..13) = 1, 1, 1, 2, 3, 4, 6, 9, 13, 19, 28, 41, 60, 88`。 -/
theorem ci_one_vals : ci 1 0 = 1 ∧ ci 1 1 = 1 ∧ ci 1 2 = 1 ∧ ci 1 3 = 2 ∧ ci 1 4 = 3 ∧ ci 1 5 = 4 ∧
    ci 1 6 = 6 ∧ ci 1 7 = 9 ∧ ci 1 8 = 13 ∧ ci 1 9 = 19 ∧ ci 1 10 = 28 ∧ ci 1 11 = 41 ∧ ci 1 12 = 60 ∧
    ci 1 13 = 88 := by
  have h0 := (ci_small 1).1
  have h1 := (ci_small 1).2.1
  have h2 := (ci_small 1).2.2
  have e3 : ci 1 3 = ci 1 2 + ci 1 0 := ci_one_rec 0
  have e4 : ci 1 4 = ci 1 3 + ci 1 1 := ci_one_rec 1
  have e5 : ci 1 5 = ci 1 4 + ci 1 2 := ci_one_rec 2
  have e6 : ci 1 6 = ci 1 5 + ci 1 3 := ci_one_rec 3
  have e7 : ci 1 7 = ci 1 6 + ci 1 4 := ci_one_rec 4
  have e8 : ci 1 8 = ci 1 7 + ci 1 5 := ci_one_rec 5
  have e9 : ci 1 9 = ci 1 8 + ci 1 6 := ci_one_rec 6
  have e10 : ci 1 10 = ci 1 9 + ci 1 7 := ci_one_rec 7
  have e11 : ci 1 11 = ci 1 10 + ci 1 8 := ci_one_rec 8
  have e12 : ci 1 12 = ci 1 11 + ci 1 9 := ci_one_rec 9
  have e13 : ci 1 13 = ci 1 12 + ci 1 10 := ci_one_rec 10
  refine ⟨h0, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `c_2(0..7) = 1, 1, 1, 3, 5, 7, 13, 23`。 -/
theorem ci_two_vals : ci 2 0 = 1 ∧ ci 2 1 = 1 ∧ ci 2 2 = 1 ∧ ci 2 3 = 3 ∧ ci 2 4 = 5 ∧ ci 2 5 = 7 ∧
    ci 2 6 = 13 ∧ ci 2 7 = 23 := by
  have h0 := (ci_small 2).1
  have h1 := (ci_small 2).2.1
  have h2 := (ci_small 2).2.2
  have e3 : ci 2 3 = ci 2 2 + 2 * ci 2 0 := ci_two_rec 0
  have e4 : ci 2 4 = ci 2 3 + 2 * ci 2 1 := ci_two_rec 1
  have e5 : ci 2 5 = ci 2 4 + 2 * ci 2 2 := ci_two_rec 2
  have e6 : ci 2 6 = ci 2 5 + 2 * ci 2 3 := ci_two_rec 3
  have e7 : ci 2 7 = ci 2 6 + 2 * ci 2 4 := ci_two_rec 4
  refine ⟨h0, h1, h2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `c_1(n+10) = c_1(n+8) + 3c_1(n+5) + c_1(n+3) + c_1(n)`。 -/
theorem ci_one_id_C1 (n : ℕ) :
    ci 1 (n + 10) = ci 1 (n + 8) + 3 * ci 1 (n + 5) + ci 1 (n + 3) + ci 1 n := by
  have r0 : ci 1 (n + 3) = ci 1 (n + 2) + ci 1 n := ci_one_rec n
  have r1 : ci 1 (n + 4) = ci 1 (n + 3) + ci 1 (n + 1) := ci_one_rec (n + 1)
  have r2 : ci 1 (n + 5) = ci 1 (n + 4) + ci 1 (n + 2) := ci_one_rec (n + 2)
  have r3 : ci 1 (n + 6) = ci 1 (n + 5) + ci 1 (n + 3) := ci_one_rec (n + 3)
  have r4 : ci 1 (n + 7) = ci 1 (n + 6) + ci 1 (n + 4) := ci_one_rec (n + 4)
  have r5 : ci 1 (n + 8) = ci 1 (n + 7) + ci 1 (n + 5) := ci_one_rec (n + 5)
  have r6 : ci 1 (n + 9) = ci 1 (n + 8) + ci 1 (n + 6) := ci_one_rec (n + 6)
  have r7 : ci 1 (n + 10) = ci 1 (n + 9) + ci 1 (n + 7) := ci_one_rec (n + 7)
  linarith

/-- `c_2(n+8) + 2c_2(n+3) = 5c_2(n+5) + 8c_2(n)`。 -/
theorem ci_two_id_C2 (n : ℕ) :
    ci 2 (n + 8) + 2 * ci 2 (n + 3) = 5 * ci 2 (n + 5) + 8 * ci 2 n := by
  have r0 : ci 2 (n + 3) = ci 2 (n + 2) + 2 * ci 2 n := ci_two_rec n
  have r1 : ci 2 (n + 4) = ci 2 (n + 3) + 2 * ci 2 (n + 1) := ci_two_rec (n + 1)
  have r2 : ci 2 (n + 5) = ci 2 (n + 4) + 2 * ci 2 (n + 2) := ci_two_rec (n + 2)
  have r3 : ci 2 (n + 6) = ci 2 (n + 5) + 2 * ci 2 (n + 3) := ci_two_rec (n + 3)
  have r4 : ci 2 (n + 7) = ci 2 (n + 6) + 2 * ci 2 (n + 4) := ci_two_rec (n + 4)
  have r5 : ci 2 (n + 8) = ci 2 (n + 7) + 2 * ci 2 (n + 5) := ci_two_rec (n + 5)
  linarith

/-- `4c_1(n+10) + 4c_1(n+5) = c_1(n+14) − c_1(n)`。 -/
theorem ci_one_id_C3 (n : ℕ) :
    4 * ci 1 (n + 10) + 4 * ci 1 (n + 5) = ci 1 (n + 14) - ci 1 n := by
  have r0 : ci 1 (n + 3) = ci 1 (n + 2) + ci 1 n := ci_one_rec n
  have r1 : ci 1 (n + 4) = ci 1 (n + 3) + ci 1 (n + 1) := ci_one_rec (n + 1)
  have r2 : ci 1 (n + 5) = ci 1 (n + 4) + ci 1 (n + 2) := ci_one_rec (n + 2)
  have r3 : ci 1 (n + 6) = ci 1 (n + 5) + ci 1 (n + 3) := ci_one_rec (n + 3)
  have r4 : ci 1 (n + 7) = ci 1 (n + 6) + ci 1 (n + 4) := ci_one_rec (n + 4)
  have r5 : ci 1 (n + 8) = ci 1 (n + 7) + ci 1 (n + 5) := ci_one_rec (n + 5)
  have r6 : ci 1 (n + 9) = ci 1 (n + 8) + ci 1 (n + 6) := ci_one_rec (n + 6)
  have r7 : ci 1 (n + 10) = ci 1 (n + 9) + ci 1 (n + 7) := ci_one_rec (n + 7)
  have r8 : ci 1 (n + 11) = ci 1 (n + 10) + ci 1 (n + 8) := ci_one_rec (n + 8)
  have r9 : ci 1 (n + 12) = ci 1 (n + 11) + ci 1 (n + 9) := ci_one_rec (n + 9)
  have r10 : ci 1 (n + 13) = ci 1 (n + 12) + ci 1 (n + 10) := ci_one_rec (n + 10)
  have r11 : ci 1 (n + 14) = ci 1 (n + 13) + ci 1 (n + 11) := ci_one_rec (n + 11)
  linarith

/-- `ciZ i n = 0`（`n < 0`）。 -/
theorem ciZ_of_neg (i : ℕ) {n : ℤ} (h : n < 0) : ciZ i n = 0 := by
  simp [ciZ, not_le.2 h]

/-- T2.5(3) 在 `m = 1`（一切 `k`）：`U_k(1) = c_1(k+3) + c_1(k−2) − 1`。 -/
theorem U_one_atoms (k : ℕ) : (U k 1 : ℚ) = ci 1 (k + 3) + ciZ 1 ((k : ℤ) - 2) - 1 := by
  have h := U_F4 k 1
  rw [sum_range_succ, sum_range_one, show Icc 1 0 = (∅ : Finset ℕ) by decide, sum_empty, Icc_self,
    sum_singleton, ci_zero,
    show (k : ℤ) + 3 * ((1 : ℕ) : ℤ) - 3 * ((1 : ℕ) : ℤ) - 2 = (k : ℤ) - 2 by push_cast; ring] at h
  norm_num [Nat.descFactorial_self] at h
  linarith

/-- **notes/12 定理 3 的 `m = 1`**：一切 `k` 有 `U_k(1) = c_1(k+2) + c_1(k+1) − 1`。 -/
theorem U_one_two_atoms (k : ℕ) : (U k 1 : ℚ) = ci 1 (k + 2) + ci 1 (k + 1) - 1 := by
  rw [U_one_atoms]
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := ci_one_vals
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rw [ciZ_of_neg 1 (n := (k : ℤ) - 2) (by omega)]
    interval_cases k
    · norm_num [v1, v2, v3]
    · norm_num [v2, v3, v4]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have e2 : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by push_cast; ring
    rw [e2, ciZ_natCast]
    have r0 : ci 1 (n + 2 + 1) = ci 1 (n + 2) + ci 1 n := ci_one_rec n
    have r2 : ci 1 (n + 2 + 3) = ci 1 (n + 2 + 2) + ci 1 (n + 2) := ci_one_rec (n + 2)
    linarith

/-- T2.5(3) 在 `m = 2`（一切 `k`）：
`U_k(2) = 1/2 − c_1(k+6) − c_1(k+1) + ½c_2(k+6) + c_2(k+1) + 2c_2(k−2)`。 -/
theorem U_two_atoms_F4 (k : ℕ) :
    (U k 2 : ℚ) = 1 / 2 - ci 1 (k + 6) - ci 1 (k + 1) + 1 / 2 * ci 2 (k + 6) + ci 2 (k + 1) +
      2 * ciZ 2 ((k : ℤ) - 2) := by
  have h := U_F4 k 2
  rw [sum_range_succ, sum_range_succ, sum_range_one, show Icc 1 0 = (∅ : Finset ℕ) by decide, sum_empty,
    Icc_self, sum_singleton, show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, sum_pair (by norm_num), ci_zero,
    show (k : ℤ) + 3 * ((2 : ℕ) : ℤ) - 3 * ((1 : ℕ) : ℤ) - 2 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
    show (k : ℤ) + 3 * ((2 : ℕ) : ℤ) - 3 * ((2 : ℕ) : ℤ) - 2 = (k : ℤ) - 2 by push_cast; ring] at h
  simp only [ciZ_natCast] at h
  norm_num [Nat.descFactorial_self, Nat.descFactorial_one] at h
  linarith

/-- **A25 (d) 的例子**：`k = 0` 与 `k ≥ 2` 时
`U_k(2) = 1/2 − ¼c_1(k+10) + ¼c_1(k−4) + (5/2)c_2(k+3) + 6c_2(k−2)`（每个 `i` 两个原子）。 -/
theorem U_two_two_atoms (k : ℕ) (hk : k ≠ 1) :
    (U k 2 : ℚ) = 1 / 2 - 1 / 4 * ci 1 (k + 10) + 1 / 4 * ciZ 1 ((k : ℤ) - 4) + 5 / 2 * ci 2 (k + 3) +
      6 * ciZ 2 ((k : ℤ) - 2) := by
  rw [U_two_atoms_F4]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := ci_one_vals
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := ci_two_vals
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 0 := by omega
    rw [ciZ_of_neg 1 (n := ((0 : ℕ) : ℤ) - 4) (by norm_num),
      ciZ_of_neg 2 (n := ((0 : ℕ) : ℤ) - 2) (by norm_num)]
    norm_num [v1, v6, v10, w1, w3, w6]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have e2 : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by push_cast; ring
    rw [e2, ciZ_natCast]
    have hC2 : ci 2 (n + 2 + 6) + 2 * ci 2 (n + 2 + 1) = 5 * ci 2 (n + 2 + 3) + 8 * ci 2 n :=
      ci_two_id_C2 n
    have hC3 : 4 * ci 1 (n + 2 + 6) + 4 * ci 1 (n + 2 + 1) =
        ci 1 (n + 2 + 10) - ciZ 1 (((n + 2 : ℕ) : ℤ) - 4) := by
      rcases Nat.lt_or_ge n 2 with hn | hn
      · rw [ciZ_of_neg 1 (n := ((n + 2 : ℕ) : ℤ) - 4) (by push_cast; omega)]
        interval_cases n
        · norm_num [v3, v8, v12]
        · norm_num [v4, v9, v13]
      · obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
        have e4 : ((p + 2 + 2 : ℕ) : ℤ) - 4 = (p : ℤ) := by push_cast; ring
        rw [e4, ciZ_natCast]
        exact ci_one_id_C3 p
    linarith

/-- `k = 1` 时 `U_two_two_atoms` 的式子不成立：左边 `U_1(2) = 3`，右边是 `11/4`。 -/
theorem U_two_two_atoms_one :
    (U 1 2 : ℚ) ≠ 1 / 2 - 1 / 4 * ci 1 (1 + 10) + 1 / 4 * ciZ 1 (((1 : ℕ) : ℤ) - 4) +
      5 / 2 * ci 2 (1 + 3) + 6 * ciZ 2 (((1 : ℕ) : ℤ) - 2) := by
  rw [U_two_atoms_F4, ciZ_of_neg 1 (n := ((1 : ℕ) : ℤ) - 4) (by norm_num),
    ciZ_of_neg 2 (n := ((1 : ℕ) : ℤ) - 2) (by norm_num)]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := ci_one_vals
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := ci_two_vals
  norm_num [v2, v7, v11, w2, w4, w7]

/-- **A26 (iii) `q = 2`**：`k ≥ 1` 时 `N(k,2) = c_1(k+3) + c_1(k−2) − 3`。 -/
theorem N_two_two_atoms {k : ℕ} (hk : 1 ≤ k) : (N k 2 : ℚ) = ci 1 (k + 3) + ciZ 1 ((k : ℤ) - 2) - 3 := by
  have hN : (N k 2 : ℚ) = (U k 1 : ℚ) - 2 * (U k 0 : ℚ) := by
    rw [N_eq_sum_U hk, sum_range_succ, sum_range_one]
    norm_num
    ring
  rw [hN, U_zero_right, Nat.cast_one, U_one_atoms]
  ring

/-- **A26 (iii) 的例子 `q = 3`**：`k ≥ 1` 时
`N(k,3) = 13/2 − c_1(k+8) − 2c_1(k−2) + (5/2)c_2(k+3) + 6c_2(k−2)`。 -/
theorem N_three_two_atoms {k : ℕ} (hk : 1 ≤ k) :
    (N k 3 : ℚ) = 13 / 2 - ci 1 (k + 8) - 2 * ciZ 1 ((k : ℤ) - 2) + 5 / 2 * ci 2 (k + 3) +
      6 * ciZ 2 ((k : ℤ) - 2) := by
  have c32 : Nat.choose 3 2 = 3 := by decide
  have hN : (N k 3 : ℚ) = 3 * (U k 0 : ℚ) - 3 * (U k 1 : ℚ) + (U k 2 : ℚ) := by
    rw [N_eq_sum_U hk, sum_range_succ, sum_range_succ, sum_range_one]
    norm_num [c32]
    ring
  rw [hN, U_zero_right, Nat.cast_one, U_one_atoms, U_two_atoms_F4]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := ci_one_vals
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := ci_two_vals
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    rw [ciZ_of_neg 1 (n := ((1 : ℕ) : ℤ) - 2) (by norm_num),
      ciZ_of_neg 2 (n := ((1 : ℕ) : ℤ) - 2) (by norm_num)]
    norm_num [v2, v4, v7, v9, w2, w4, w7]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have e2 : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by push_cast; ring
    rw [e2, ciZ_natCast, ciZ_natCast]
    have hC1 : ci 1 (n + 2 + 8) = ci 1 (n + 2 + 6) + 3 * ci 1 (n + 2 + 3) + ci 1 (n + 2 + 1) + ci 1 n :=
      ci_one_id_C1 n
    have hC2 : ci 2 (n + 2 + 6) + 2 * ci 2 (n + 2 + 1) = 5 * ci 2 (n + 2 + 3) + 8 * ci 2 n :=
      ci_two_id_C2 n
    linarith

/-- `k = 0` 时 `N_three_two_atoms` 的式子不成立：右边是 `1`，而 `N(0,3) = 0`。 -/
theorem N_three_two_atoms_zero :
    (N 0 3 : ℚ) ≠ 13 / 2 - ci 1 (0 + 8) - 2 * ciZ 1 (((0 : ℕ) : ℤ) - 2) + 5 / 2 * ci 2 (0 + 3) +
      6 * ciZ 2 (((0 : ℕ) : ℤ) - 2) := by
  rw [N_eq_zero_of_lt (by norm_num), ciZ_of_neg 1 (n := ((0 : ℕ) : ℤ) - 2) (by norm_num),
    ciZ_of_neg 2 (n := ((0 : ℕ) : ℤ) - 2) (by norm_num)]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := ci_one_vals
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := ci_two_vals
  norm_num [v8, w3]

end A207123
