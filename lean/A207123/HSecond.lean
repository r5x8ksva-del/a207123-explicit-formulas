import A207123.NegZeros

/-!
# 报告 T5.3(7)（猜想总表 A29 (ii)）：`h_k` 的次高项与首项的符号关系（对一切 `k`）

记 `s = s_k = ⌊(k+2)/3⌋`，`d = deg h_k = k − s = ⌊2k/3⌋`（`HStruct.lean` 的 `natDegree_hpoly`），`c` 为无符号
第一类 Stirling 数（Mathlib 的 `Nat.stirlingFirst`）。

* `upoly_eval_neg_second`、`hpoly_coeff_second`（互反式在 `−(s+2)` 处，`k ≥ 2`）：
  `u_k(−(s+2)) = (−1)^k·(h_{k,d−1} + (k+1)·h_{k,d})`，所以 `h_{k,d−1} = (−1)^k·(u_k(−(s+2)) − (k+1)·u_k(−(s+1)))`。
* c5a 定理 4.4(d) 的三个闭式（代入 `HStruct.lean`、`NegZeros.lean` 中 `G_{−j}` 顶端各层的闭式）：
  `hpoly_second_three_mul`：`k = 3a`（`a ≥ 1`）时 `h_{k,d−1} = (−1)^{a+1}·2a·a!`；
  `hpoly_second_three_mul_add_one`：`k = 3a+1`（`a ≥ 1`）时 `h_{k,d−1} = (−1)^a·B_1(a)`，
  `B_1(a) = c(a+3,2) + c(a+3,3) − (a+2)! − (3a+2)·c(a+2,2)`（`hB1`）；
  `hpoly_second_three_mul_add_two`：`k = 3a+2` 时 `h_{k,d−1} = (−1)^a·B_2(a)`，
  `B_2(a) = c(a+3,2) + c(a+3,3) − 3(a+1)·(a+1)!`（`hB2`）。
* `hB2_pos`：`B_2(a) > 0`（一切 `a`；递推 `hB2_succ`：`B_2(a+1) = (a+3)B_2(a) + c(a+3,2) + (a+2)! − 3(a+1)!`）。
  `hB1_neg`、`hB1_pos`：`1 ≤ a ≤ 54` 时 `B_1(a) < 0`，`a ≥ 55` 时 `B_1(a) > 0`。递推 `hB1_succ`：
  `B_1(a+1) = (a+3)B_1(a) + E(a)`，`E(a) = (a−2)c(a+2,2) − 2(a+1)(a+1)!`（`hE`），`hE_pos`：`a ≥ 9` 时 `E(a) > 0`
  （`hE_succ` 与 `stirlingFirst_two_ge`：`a ≥ 3` 时 `c(a+2,2) ≥ 2(a+1)!`）。`a ≤ 55` 的符号与 `E(9) > 0` 用内核求值
  `decide +kernel` 核对（不引入公理），Stirling 数用线性递推的求值器 `c2v`、`c3v`（`c2v_eq`、`c3v_eq`）。
  `notes/16` 定理 3 用 `φ_1(n) = B_1(n−2)/n!` 与调和数，这里改用整数递推，结论相同。
* **`hpoly_second_sign`**（`notes/16` 定理 3）：`k ≥ 3` 时次高项 `h_{k,d−1}` 与首项 `h_{k,d}`：`k ≡ 0 (mod 3)` 异号；
  `k ≡ 2` 同号；`k ≡ 1` 时 `k ≤ 163` 异号、`k ≥ 166` 同号。
-/

namespace A207123

open Polynomial Finset
open scoped Nat

/-! ## 1. 互反式在 `−(s_k+2)` 处 -/

/-- `k ≥ 2` 时 `u_k(−(s+2)) = (−1)^k·(h_{k,d−1} + (k+1)·h_{k,d})`（`s = ⌊(k+2)/3⌋`，`d = k − s`）。 -/
theorem upoly_eval_neg_second {k : ℕ} (hk : 2 ≤ k) :
    (upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 2)) = (-1) ^ k *
      ((hpoly k).coeff (k - (k + 2) / 3 - 1)
        + ((k : ℚ) + 1) * (hpoly k).coeff (k - (k + 2) / 3)) := by
  have hrec := upoly_eval_neg_recip k ((k + 2) / 3 + 2) (by omega)
  rw [show -((((k + 2) / 3 : ℕ) : ℚ) + 2) = -((((k + 2) / 3 + 2 : ℕ) : ℚ)) by push_cast; ring, hrec]
  congr 1
  rw [Finset.sum_eq_add (k - (k + 2) / 3 - 1) (k - (k + 2) / 3) (by omega)]
  · rw [ite_eq_left (show k < k - (k + 2) / 3 - 1 + ((k + 2) / 3 + 2) by omega),
      ite_eq_left (show k < k - (k + 2) / 3 + ((k + 2) / 3 + 2) by omega),
      show k - (k + 2) / 3 - 1 + ((k + 2) / 3 + 2) - 1 = k by omega,
      show k - (k + 2) / 3 + ((k + 2) / 3 + 2) - 1 = k + 1 by omega,
      Nat.choose_self, Nat.choose_succ_self_right]
    push_cast
    ring
  · intro c _ hne
    by_cases h : k < c + ((k + 2) / 3 + 2)
    · rw [ite_eq_left h, hpoly_coeff_vanish k ((k + 2) / 3) le_rfl c (by omega), zero_mul]
    · exact ite_eq_right h
  · intro h
    exact absurd (mem_range.2 (by omega)) h
  · intro h
    exact absurd (mem_range.2 (by omega)) h

/-- `k ≥ 2` 时 `h_{k,d−1} = (−1)^k·(u_k(−(s+2)) − (k+1)·u_k(−(s+1)))`（`notes/16` 注 3.1 取 `n = 1`）。 -/
theorem hpoly_coeff_second {k : ℕ} (hk : 2 ≤ k) :
    (hpoly k).coeff (k - (k + 2) / 3 - 1) = (-1) ^ k *
      ((upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 2))
        - ((k : ℚ) + 1) * (upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 1))) := by
  have ht := hpoly_coeff_top k
  have hp : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [upoly_eval_neg_second hk]
  linear_combination
    (-1 : ℚ) * ((hpoly k).coeff (k - (k + 2) / 3 - 1)
      + ((k : ℚ) + 1) * (hpoly k).coeff (k - (k + 2) / 3)) * hp - ((k : ℚ) + 1) * ht

/-! ## 2. 三个剩余类的闭式（c5a 定理 4.4(d)） -/

/-- `B_1(a) = c(a+3,2) + c(a+3,3) − (a+2)! − (3a+2)·c(a+2,2)`。 -/
def hB1 (a : ℕ) : ℤ :=
  (Nat.stirlingFirst (a + 3) 2 : ℤ) + (Nat.stirlingFirst (a + 3) 3 : ℤ) - ((a + 2)! : ℤ)
    - (3 * a + 2) * (Nat.stirlingFirst (a + 2) 2 : ℤ)

/-- `B_2(a) = c(a+3,2) + c(a+3,3) − 3(a+1)·(a+1)!`。 -/
def hB2 (a : ℕ) : ℤ :=
  (Nat.stirlingFirst (a + 3) 2 : ℤ) + (Nat.stirlingFirst (a + 3) 3 : ℤ) - 3 * (a + 1) * ((a + 1)! : ℤ)

/-- **c5a 定理 4.4(d)**（`k = 3a`，`a ≥ 1`，`d = 2a`）：`h_{k,d−1} = (−1)^{a+1}·2a·a!`。 -/
theorem hpoly_second_three_mul {a : ℕ} (ha : 1 ≤ a) :
    (hpoly (3 * a)).coeff (2 * a - 1) = (-1) ^ (a + 1) * (2 * a * a ! : ℚ) := by
  have h := hpoly_coeff_second (k := 3 * a) (by omega)
  rw [show 3 * a - (3 * a + 2) / 3 - 1 = 2 * a - 1 by omega, show (3 * a + 2) / 3 = a by omega,
    upoly_three_mul_eval, show -((a : ℚ) + 2) = -(((a + 1 : ℕ) : ℚ) + 1) by push_cast; ring,
    upoly_eval_neg_succ, coeff_gnegPoly_top_three] at h
  rw [h, show ((-1 : ℚ)) ^ (3 * a) = (-1) ^ a by rw [pow_mul]; norm_num, Nat.factorial_succ]
  push_cast
  ring

/-- **c5a 定理 4.4(d)**（`k = 3a+1`，`a ≥ 1`，`d = 2a`）：`h_{k,d−1} = (−1)^a·B_1(a)`。 -/
theorem hpoly_second_three_mul_add_one {a : ℕ} (ha : 1 ≤ a) :
    (hpoly (3 * a + 1)).coeff (2 * a - 1) = (-1) ^ a * (hB1 a : ℚ) := by
  have h := hpoly_coeff_second (k := 3 * a + 1) (by omega)
  rw [show 3 * a + 1 - (3 * a + 1 + 2) / 3 - 1 = 2 * a - 1 by omega,
    show (3 * a + 1 + 2) / 3 = a + 1 by omega,
    show -(((a + 1 : ℕ) : ℚ) + 1) = -((a : ℚ) + 2) by push_cast; ring,
    upoly_three_mul_add_one_eval,
    show -(((a + 1 : ℕ) : ℚ) + 2) = -(((a + 2 : ℕ) : ℚ) + 1) by push_cast; ring,
    upoly_eval_neg_succ, coeff_gnegPoly_top_five] at h
  rw [h, hB1, show ((-1 : ℚ)) ^ (3 * a + 1) = -(-1) ^ a by rw [pow_succ, pow_mul]; norm_num]
  push_cast
  ring

/-- **c5a 定理 4.4(d)**（`k = 3a+2`，`d = 2a+1`）：`h_{k,d−1} = (−1)^a·B_2(a)`。 -/
theorem hpoly_second_three_mul_add_two (a : ℕ) :
    (hpoly (3 * a + 2)).coeff (2 * a) = (-1) ^ a * (hB2 a : ℚ) := by
  have h := hpoly_coeff_second (k := 3 * a + 2) (by omega)
  rw [show 3 * a + 2 - (3 * a + 2 + 2) / 3 - 1 = 2 * a by omega,
    show (3 * a + 2 + 2) / 3 = a + 1 by omega,
    show -(((a + 1 : ℕ) : ℚ) + 1) = -((a : ℚ) + 2) by push_cast; ring,
    upoly_three_mul_add_two_eval,
    show -(((a + 1 : ℕ) : ℚ) + 2) = -(((a + 2 : ℕ) : ℚ) + 1) by push_cast; ring,
    upoly_eval_neg_succ, coeff_gnegPoly_top_four] at h
  rw [h, hB2, show ((-1 : ℚ)) ^ (3 * a + 2) = (-1) ^ a by rw [pow_add, pow_mul]; norm_num]
  push_cast
  ring

/-! ## 3. `B_2 > 0`；`B_1` 的符号在 `a = 55` 处翻转 -/

/-- 辅助引理：`c(a+4, 2) = (a+3)·c(a+3, 2) + (a+2)!`。 -/
theorem stirlingFirst_four_two (a : ℕ) :
    Nat.stirlingFirst (a + 4) 2 = (a + 3) * Nat.stirlingFirst (a + 3) 2 + (a + 2)! :=
  stirlingFirst_two_succ_hs (a + 2)

/-- 辅助引理：`c(a+3, 2) = (a+2)·c(a+2, 2) + (a+1)!`。 -/
theorem stirlingFirst_three_two (a : ℕ) :
    Nat.stirlingFirst (a + 3) 2 = (a + 2) * Nat.stirlingFirst (a + 2) 2 + (a + 1)! :=
  stirlingFirst_two_succ_hs (a + 1)

/-- 辅助引理：`c(a+4, 3) = (a+3)·c(a+3, 3) + c(a+3, 2)`。 -/
theorem stirlingFirst_four_three (a : ℕ) :
    Nat.stirlingFirst (a + 4) 3 = (a + 3) * Nat.stirlingFirst (a + 3) 3 + Nat.stirlingFirst (a + 3) 2 :=
  Nat.stirlingFirst_succ_succ (a + 3) 2

/-- 辅助引理：`(a+2)! = (a+2)·(a+1)!`（在 `ℤ` 中）。 -/
theorem fact_two_int (a : ℕ) : ((a + 2)! : ℤ) = (a + 2) * ((a + 1)! : ℤ) := by
  have h : (a + 2)! = (a + 2) * (a + 1)! := Nat.factorial_succ (a + 1)
  rw [h]
  push_cast
  ring

/-- 辅助引理：`(a+3)! = (a+3)·(a+2)!`（在 `ℤ` 中）。 -/
theorem fact_three_int (a : ℕ) : ((a + 3)! : ℤ) = (a + 3) * ((a + 2)! : ℤ) := by
  have h : (a + 3)! = (a + 3) * (a + 2)! := Nat.factorial_succ (a + 2)
  rw [h]
  push_cast
  ring

/-- `B_2(a+1) = (a+3)·B_2(a) + c(a+3,2) + (a+2)! − 3·(a+1)!`。 -/
theorem hB2_succ (a : ℕ) :
    hB2 (a + 1) = (a + 3) * hB2 a + (Nat.stirlingFirst (a + 3) 2 : ℤ) + ((a + 2)! : ℤ)
      - 3 * ((a + 1)! : ℤ) := by
  unfold hB2
  rw [show a + 1 + 3 = a + 4 by ring, show a + 1 + 1 = a + 2 by ring, stirlingFirst_four_two,
    stirlingFirst_four_three]
  push_cast
  rw [fact_two_int a]
  ring

/-- `B_2(a) > 0`（一切 `a`）。 -/
theorem hB2_pos : ∀ a : ℕ, 0 < hB2 a
  | 0 => by
    have e2 : Nat.stirlingFirst 3 2 = 3 := by decide
    have e3 : Nat.stirlingFirst 3 3 = 1 := by decide
    rw [hB2]
    norm_num [e2, e3]
  | a + 1 => by
    rw [hB2_succ]
    have h1 := hB2_pos a
    have h2 : ((a + 2)! : ℤ) < (Nat.stirlingFirst (a + 3) 2 : ℤ) := by
      exact_mod_cast factorial_lt_stirlingFirst_two a
    have h3 := fact_two_int a
    have h4 : (0 : ℤ) < ((a + 1)! : ℤ) := by exact_mod_cast Nat.factorial_pos _
    have h5 : (0 : ℤ) < (a + 3) * hB2 a := mul_pos (by positivity) h1
    have h6 : (0 : ℤ) ≤ (a : ℤ) * ((a + 1)! : ℤ) := mul_nonneg (by positivity) h4.le
    nlinarith

/-- `E(a) = (a−2)·c(a+2,2) − 2(a+1)·(a+1)!`。 -/
def hE (a : ℕ) : ℤ :=
  ((a : ℤ) - 2) * (Nat.stirlingFirst (a + 2) 2 : ℤ) - 2 * (a + 1) * ((a + 1)! : ℤ)

/-- `B_1(a+1) = (a+3)·B_1(a) + E(a)`。 -/
theorem hB1_succ (a : ℕ) : hB1 (a + 1) = (a + 3) * hB1 a + hE a := by
  unfold hB1 hE
  rw [show a + 1 + 3 = a + 4 by ring, show a + 1 + 2 = a + 3 by ring, stirlingFirst_four_two,
    stirlingFirst_four_three, stirlingFirst_three_two]
  push_cast
  rw [fact_three_int a, fact_two_int a]
  ring

/-- `E(a+1) = (a+2)·E(a) + (a+2)·c(a+2,2) − (a+5)·(a+1)!`。 -/
theorem hE_succ (a : ℕ) :
    hE (a + 1) = (a + 2) * hE a + (a + 2) * (Nat.stirlingFirst (a + 2) 2 : ℤ)
      - (a + 5) * ((a + 1)! : ℤ) := by
  unfold hE
  rw [show a + 1 + 2 = a + 3 by ring, show a + 1 + 1 = a + 2 by ring, stirlingFirst_three_two]
  push_cast
  rw [fact_two_int a]
  ring

/-- `a ≥ 3` 时 `c(a+2, 2) ≥ 2·(a+1)!`（`c(n+1,2) = n!·H_n`，`H_4 > 2`）。 -/
theorem stirlingFirst_two_ge {a : ℕ} (ha : 3 ≤ a) : 2 * (a + 1)! ≤ Nat.stirlingFirst (a + 2) 2 := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [stirlingFirst_two_succ_hs (n + 1), Nat.factorial_succ (n + 1),
      show n + 1 + 1 = n + 2 by ring]
    nlinarith [Nat.mul_le_mul_left (n + 2) ih]

/-- `c(n+1, 2)` 的求值器（线性递推 `c(n+2,2) = (n+1)·c(n+1,2) + n!`）。 -/
def c2v : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * c2v n + n !

/-- `c(n+1, 3)` 的求值器（`c(n+2,3) = (n+1)·c(n+1,3) + c(n+1,2)`）。 -/
def c3v : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * c3v n + c2v n

theorem c2v_eq : ∀ n : ℕ, c2v n = Nat.stirlingFirst (n + 1) 2
  | 0 => rfl
  | n + 1 => by
    rw [c2v, c2v_eq n, show n + 1 + 1 = n + 2 by ring, stirlingFirst_two_succ_hs n]

theorem c3v_eq : ∀ n : ℕ, c3v n = Nat.stirlingFirst (n + 1) 3
  | 0 => rfl
  | n + 1 => by
    have s3 : Nat.stirlingFirst (n + 2) 3
        = (n + 1) * Nat.stirlingFirst (n + 1) 3 + Nat.stirlingFirst (n + 1) 2 :=
      Nat.stirlingFirst_succ_succ (n + 1) 2
    rw [c3v, c3v_eq n, c2v_eq n, show n + 1 + 1 = n + 2 by ring, s3]

theorem stirlingFirst_three_two_v (a : ℕ) : Nat.stirlingFirst (a + 3) 2 = c2v (a + 2) :=
  (c2v_eq (a + 2)).symm

theorem stirlingFirst_three_three_v (a : ℕ) : Nat.stirlingFirst (a + 3) 3 = c3v (a + 2) :=
  (c3v_eq (a + 2)).symm

theorem stirlingFirst_two_two_v (a : ℕ) : Nat.stirlingFirst (a + 2) 2 = c2v (a + 1) :=
  (c2v_eq (a + 1)).symm

theorem hB1_neg_iff (a : ℕ) :
    hB1 a < 0 ↔ c2v (a + 2) + c3v (a + 2) < (a + 2)! + (3 * a + 2) * c2v (a + 1) := by
  rw [hB1, stirlingFirst_three_two_v, stirlingFirst_three_three_v, stirlingFirst_two_two_v]
  constructor
  · intro h
    have h' : ((c2v (a + 2) + c3v (a + 2) : ℕ) : ℤ) < (((a + 2)! + (3 * a + 2) * c2v (a + 1) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h'
  · intro h
    have h' : ((c2v (a + 2) + c3v (a + 2) : ℕ) : ℤ) < (((a + 2)! + (3 * a + 2) * c2v (a + 1) : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

theorem hB1_pos_iff (a : ℕ) :
    0 < hB1 a ↔ (a + 2)! + (3 * a + 2) * c2v (a + 1) < c2v (a + 2) + c3v (a + 2) := by
  rw [hB1, stirlingFirst_three_two_v, stirlingFirst_three_three_v, stirlingFirst_two_two_v]
  constructor
  · intro h
    have h' : (((a + 2)! + (3 * a + 2) * c2v (a + 1) : ℕ) : ℤ) < ((c2v (a + 2) + c3v (a + 2) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h'
  · intro h
    have h' : (((a + 2)! + (3 * a + 2) * c2v (a + 1) : ℕ) : ℤ) < ((c2v (a + 2) + c3v (a + 2) : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

theorem hE_pos_iff {a : ℕ} (ha : 2 ≤ a) :
    0 < hE a ↔ 2 * (a + 1) * (a + 1)! < (a - 2) * c2v (a + 1) := by
  rw [hE, stirlingFirst_two_two_v]
  have hs : ((a - 2 : ℕ) : ℤ) = (a : ℤ) - 2 := by rw [Nat.cast_sub ha]; norm_num
  constructor
  · intro h
    have h' : ((2 * (a + 1) * (a + 1)! : ℕ) : ℤ) < (((a - 2) * c2v (a + 1) : ℕ) : ℤ) := by
      rw [Nat.cast_mul (a - 2), hs]
      push_cast
      linarith
    exact_mod_cast h'
  · intro h
    have h' : ((2 * (a + 1) * (a + 1)! : ℕ) : ℤ) < (((a - 2) * c2v (a + 1) : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [Nat.cast_mul (a - 2), hs] at h'
    push_cast at h'
    linarith

/-- 有限核对（内核求值）：`1 ≤ a ≤ 54` 时 `B_1(a) < 0`。 -/
theorem hB1_table : ∀ a ∈ List.range 55, 1 ≤ a →
    c2v (a + 2) + c3v (a + 2) < (a + 2)! + (3 * a + 2) * c2v (a + 1) := by
  decide +kernel

/-- 有限核对（内核求值）：`B_1(55) > 0`。 -/
theorem hB1_fiftyfive :
    (55 + 2)! + (3 * 55 + 2) * c2v (55 + 1) < c2v (55 + 2) + c3v (55 + 2) := by
  decide +kernel

/-- `a ≥ 9` 时 `E(a) > 0`。 -/
theorem hE_pos {a : ℕ} (ha : 9 ≤ a) : 0 < hE a := by
  induction a, ha using Nat.le_induction with
  | base => exact (hE_pos_iff (by norm_num)).2 (by decide +kernel)
  | succ n hn ih =>
    rw [hE_succ]
    have hc : (2 * ((n + 1)! : ℤ)) ≤ (Nat.stirlingFirst (n + 2) 2 : ℤ) := by
      exact_mod_cast stirlingFirst_two_ge (a := n) (by omega)
    have hf : (0 : ℤ) < ((n + 1)! : ℤ) := by exact_mod_cast Nat.factorial_pos _
    have h1 : ((n : ℤ) + 2) * (2 * ((n + 1)! : ℤ)) ≤ ((n : ℤ) + 2) * (Nat.stirlingFirst (n + 2) 2 : ℤ) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have h2 : (0 : ℤ) ≤ ((n : ℤ) - 1) * ((n + 1)! : ℤ) := by
      have : (9 : ℤ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (by linarith) hf.le
    have h3 : (0 : ℤ) < ((n : ℤ) + 2) * hE n := mul_pos (by positivity) ih
    nlinarith

/-- `1 ≤ a ≤ 54` 时 `B_1(a) < 0`。 -/
theorem hB1_neg {a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ 54) : hB1 a < 0 :=
  (hB1_neg_iff a).2 (hB1_table a (List.mem_range.2 (by omega)) h1)

/-- `a ≥ 55` 时 `B_1(a) > 0`。 -/
theorem hB1_pos {a : ℕ} (ha : 55 ≤ a) : 0 < hB1 a := by
  induction a, ha using Nat.le_induction with
  | base => exact (hB1_pos_iff 55).2 hB1_fiftyfive
  | succ n hn ih =>
    rw [hB1_succ]
    have h1 : (0 : ℤ) < ((n : ℤ) + 3) * hB1 n := mul_pos (by positivity) ih
    have h2 := hE_pos (a := n) (by omega)
    linarith

/-! ## 4. 次高项与首项的符号关系（`notes/16` 定理 3） -/

/-- **T5.3(7) / 猜想总表 A29 (ii)**（`notes/16` 定理 3）：`k ≥ 3`，`d = deg h_k`。次高项 `h_{k,d−1}` 与首项
`h_{k,d}`：`k ≡ 0 (mod 3)` 时异号；`k ≡ 2` 时同号；`k ≡ 1` 时 `k ≤ 163` 异号、`k ≥ 166` 同号。 -/
theorem hpoly_second_sign (k : ℕ) (hk : 3 ≤ k) :
    (k % 3 = 0 → (hpoly k).leadingCoeff * (hpoly k).coeff ((hpoly k).natDegree - 1) < 0) ∧
    (k % 3 = 2 → 0 < (hpoly k).leadingCoeff * (hpoly k).coeff ((hpoly k).natDegree - 1)) ∧
    (k % 3 = 1 → k ≤ 163 → (hpoly k).leadingCoeff * (hpoly k).coeff ((hpoly k).natDegree - 1) < 0) ∧
    (k % 3 = 1 → 166 ≤ k → 0 < (hpoly k).leadingCoeff * (hpoly k).coeff ((hpoly k).natDegree - 1)) := by
  have hP : ∀ a : ℕ, ((-1 : ℚ) ^ a) * (-1) ^ a = 1 := fun a => by rw [← mul_pow]; norm_num
  obtain ⟨a, rfl | rfl | rfl⟩ : ∃ a, k = 3 * a ∨ k = 3 * a + 1 ∨ k = 3 * a + 2 := ⟨k / 3, by omega⟩
  · have hdeg : (hpoly (3 * a)).natDegree - 1 = 2 * a - 1 := by rw [natDegree_hpoly]; omega
    refine ⟨fun _ => ?_, fun h => absurd h (by omega), fun h _ => absurd h (by omega),
      fun h _ => absurd h (by omega)⟩
    rw [hdeg, leadingCoeff_hpoly_three_mul, hpoly_second_three_mul (by omega)]
    have ha : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    have hf : (0 : ℚ) < (a ! : ℚ) := by exact_mod_cast Nat.factorial_pos a
    have e : (-1 : ℚ) ^ a * (a ! : ℚ) * ((-1) ^ (a + 1) * (2 * a * a ! : ℚ))
        = -(2 * (a : ℚ) * (a ! : ℚ) * (a ! : ℚ)) := by
      rw [pow_succ]
      linear_combination (-(2 * (a : ℚ) * (a ! : ℚ) * (a ! : ℚ))) * hP a
    rw [e]
    have h2 : (0 : ℚ) < 2 * (a : ℚ) := by linarith
    have : 0 < 2 * (a : ℚ) * (a ! : ℚ) * (a ! : ℚ) := mul_pos (mul_pos h2 hf) hf
    linarith
  · have hdeg : (hpoly (3 * a + 1)).natDegree - 1 = 2 * a - 1 := by rw [natDegree_hpoly]; omega
    have hc : (0 : ℚ) < (Nat.stirlingFirst (a + 2) 2 : ℚ) := by
      exact_mod_cast stirlingFirst_two_pos_hs a
    have e : (-1 : ℚ) ^ a * (Nat.stirlingFirst (a + 2) 2 : ℚ) * ((-1) ^ a * (hB1 a : ℚ))
        = (Nat.stirlingFirst (a + 2) 2 : ℚ) * (hB1 a : ℚ) := by
      linear_combination ((Nat.stirlingFirst (a + 2) 2 : ℚ) * (hB1 a : ℚ)) * hP a
    refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ hle => ?_,
      fun _ hge => ?_⟩
    · rw [hdeg, leadingCoeff_hpoly_three_mul_add_one, hpoly_second_three_mul_add_one (by omega), e]
      have hb : (hB1 a : ℚ) < 0 := by exact_mod_cast hB1_neg (a := a) (by omega) (by omega)
      exact mul_neg_of_pos_of_neg hc hb
    · rw [hdeg, leadingCoeff_hpoly_three_mul_add_one, hpoly_second_three_mul_add_one (by omega), e]
      have hb : (0 : ℚ) < (hB1 a : ℚ) := by exact_mod_cast hB1_pos (a := a) (by omega)
      exact mul_pos hc hb
  · have hdeg : (hpoly (3 * a + 2)).natDegree - 1 = 2 * a := by rw [natDegree_hpoly]; omega
    refine ⟨fun h => absurd h (by omega), fun _ => ?_, fun h _ => absurd h (by omega),
      fun h _ => absurd h (by omega)⟩
    rw [hdeg, leadingCoeff_hpoly_three_mul_add_two, hpoly_second_three_mul_add_two]
    have hf : (0 : ℚ) < ((a + 1)! : ℚ) := by exact_mod_cast Nat.factorial_pos (a + 1)
    have hb : (0 : ℚ) < (hB2 a : ℚ) := by exact_mod_cast hB2_pos a
    have e : (-1 : ℚ) ^ a * ((a + 1)! : ℚ) * ((-1) ^ a * (hB2 a : ℚ)) = ((a + 1)! : ℚ) * (hB2 a : ℚ) := by
      linear_combination (((a + 1)! : ℚ) * (hB2 a : ℚ)) * hP a
    rw [e]
    exact mul_pos hf hb

end A207123
