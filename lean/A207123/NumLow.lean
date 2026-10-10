import A207123.MCoeff

/-!
# 报告 T4.3(5)（一切 `j`）：`Num_q` 的低次系数

记 `ν_j(q) := [x^{q+j}]Num_q`，`π_i(q) := [x^i]P_{q−1}`。`NumStruct.lean` 的 `Numq_coeff_q_add` 给出
`ν_j(q) = Σ_{i≤j} π_i(q)·N(q+j−i, q)`（`q ≥ 1`），其中 `N(q+j−i, q) = D(q+j−i, j−i)` 是近对角线的值。

* `piSeq i n := [x^i] ∏_{v<n} b_v`（`q ≥ 1` 时 `π_i(q) = piSeq i q`）与递推 `piSeq_succ`（`b_n = 1 − x − n x³`）。
  `piSeq_poly`：`piSeq i` 是 `n` 的次数 `≤ i` 的多项式（对 `i` 归纳：前向差分是 `−π_{i−1}(n) − n·π_{i−3}(n)`，
  用 `MCoeff.lean` 的 `exists_poly_of_fwdDiff_iter`）。`piPoly i` 是这个多项式；`piPoly_eval`：`q ≥ 1` 时
  `piPoly i (q) = π_i(q)`；`piPoly_zero`：`piPoly 0 = 1`。
* `numLowPoly j := Σ_{i≤j} π_i(X)·p_{j−i}(X + (j−i))`（`p_d = ndPoly d`，T4.1）。`numLowPoly_spec`：`q ≥ j+2` 时
  `ν_j(q) = numLowPoly j (q)`；`numLowPoly_natDegree`：`2j` 次，首项 `2/(2^j·j!)`（`i ≥ 1` 的项次数 `≤ 2j − i`，
  只有 `i = 0` 项达到 `2j` 次）；`numLowPoly_threshold`：`ν_j(j+1) − numLowPoly j (j+1) = (−1)^{j+1}(j+1)!`
  （`i ≥ 1` 的项在 `q = j+1` 处仍等于多项式的值，只有 `i = 0` 项偏离，偏差是 T4.1 的缺陷 `ndE1_closed`）。
* **`T4_3_five`**（汇总，写法与 `NearDiag.lean` 的 `T4_1` 相同）与 **`T4_3_five_threshold`**（没有多项式在一切
  `q ≥ j+1` 处等于 `ν_j(q)`）。`numLowPoly_one`、`numLowPoly_two`：与 `NumStruct.lean` 中 `j = 1, 2` 的显式式
  `Numq_coeff_q_add_one`、`Numq_coeff_q_add_two` 一致。
-/

namespace A207123

open Polynomial Finset
open scoped Nat

noncomputable section

/-! ## 1. `π_i(q) = [x^i]P_{q−1}` 是 `q` 的次数 `≤ i` 的多项式 -/

/-- `[x^i] ∏_{v<n} b_v`。`q ≥ 1` 时 `P_{q−1} = ∏_{v<q} b_v`，所以 `π_i(q) = piSeq i q`。 -/
def piSeq (i n : ℕ) : ℚ := (∏ v ∈ range n, bpoly ℚ v).coeff i

/-- 递推：`[x^i](p·b_n) = [x^i]p − [x^{i−1}]p − n·[x^{i−3}]p`（越界取 0）。 -/
theorem piSeq_succ (i n : ℕ) :
    piSeq i (n + 1) = piSeq i n - (if 1 ≤ i then piSeq (i - 1) n else 0)
      - (n : ℚ) * (if 3 ≤ i then piSeq (i - 3) n else 0) := by
  unfold piSeq
  rw [prod_range_succ, coeff_mul_bpoly]

/-- `[x^0] ∏_{v<n} b_v = 1`。 -/
theorem piSeq_zero_left (n : ℕ) : piSeq 0 n = 1 := by
  unfold piSeq
  rw [coeff_zero_eq_eval_zero, eval_prod]
  simp [eval_bpoly]

/-- 前向差分是次数 `< D` 的多项式时，数列是次数 `≤ D` 的多项式。 -/
theorem poly_of_fwdDiff_step {f : ℕ → ℚ} {R : ℚ[X]} {D : ℕ} (hR : R.natDegree < D)
    (hf : ∀ n : ℕ, f (n + 1) - f n = R.eval (n : ℚ)) :
    ∃ P : ℚ[X], P.natDegree ≤ D ∧ ∀ n : ℕ, P.eval (n : ℚ) = f n := by
  have hD : fwdDiff (1 : ℕ) f = fun n : ℕ => R.eval (n : ℚ) := by
    funext n
    rw [ndFD_apply, hf]
  refine exists_poly_of_fwdDiff_iter (f := f) (D := D) ?_
  rw [Function.iterate_succ_apply, hD]
  exact fwdDiff_iter_poly_eq_zero hR

/-- `piSeq i` 是 `n` 的次数 `≤ i` 的多项式。 -/
theorem piSeq_poly : ∀ i : ℕ, ∃ P : ℚ[X], P.natDegree ≤ i ∧ ∀ n : ℕ, P.eval (n : ℚ) = piSeq i n
  | 0 => ⟨1, by simp, fun n => by rw [eval_one, piSeq_zero_left]⟩
  | 1 => by
    refine poly_of_fwdDiff_step (R := C (-1)) (by simp) fun n => ?_
    rw [piSeq_succ, eval_C, ite_eq_left (show (1 : ℕ) ≤ 1 from le_rfl),
      ite_eq_right (show ¬ ((3 : ℕ) ≤ 1) by norm_num), Nat.sub_self, piSeq_zero_left]
    ring
  | 2 => by
    obtain ⟨P, hPd, hP⟩ := piSeq_poly 1
    refine poly_of_fwdDiff_step (R := -P) (by rw [natDegree_neg]; omega) fun n => ?_
    rw [piSeq_succ, eval_neg, hP, ite_eq_left (show (1 : ℕ) ≤ 2 by norm_num),
      ite_eq_right (show ¬ ((3 : ℕ) ≤ 2) by norm_num), show (2 : ℕ) - 1 = 1 from rfl]
    ring
  | i + 3 => by
    obtain ⟨P, hPd, hP⟩ := piSeq_poly (i + 2)
    obtain ⟨Q, hQd, hQ⟩ := piSeq_poly i
    have hdeg : (-(P + X * Q)).natDegree < i + 3 := by
      rw [natDegree_neg]
      have h2 := natDegree_mul_le (p := (X : ℚ[X])) (q := Q)
      have h3 : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
      have h4 : (P + X * Q).natDegree ≤ i + 2 :=
        natDegree_add_le_of_degree_le hPd (by omega)
      omega
    refine poly_of_fwdDiff_step hdeg fun n => ?_
    rw [piSeq_succ, eval_neg, eval_add, eval_mul, eval_X, hP, hQ,
      ite_eq_left (show 1 ≤ i + 3 by omega), ite_eq_left (show 3 ≤ i + 3 by omega),
      show i + 3 - 1 = i + 2 by omega, show i + 3 - 3 = i by omega]
    ring

/-- `π_i` 作为多项式（次数 `≤ i`）。 -/
def piPoly (i : ℕ) : ℚ[X] := Classical.choose (piSeq_poly i)

theorem piPoly_natDegree_le (i : ℕ) : (piPoly i).natDegree ≤ i :=
  (Classical.choose_spec (piSeq_poly i)).1

theorem piPoly_eval_nat (i n : ℕ) : (piPoly i).eval (n : ℚ) = piSeq i n :=
  (Classical.choose_spec (piSeq_poly i)).2 n

/-- `P_{q−1} = ∏_{v<q} b_v`（`q ≥ 1`）。 -/
theorem Ppoly_pred_eq_prod {q : ℕ} (hq : 1 ≤ q) : Ppoly ℚ (q - 1) = ∏ v ∈ range q, bpoly ℚ v := by
  unfold Ppoly
  rw [Nat.sub_add_cancel hq]

/-- `q ≥ 1` 时 `piPoly i (q) = π_i(q) = [x^i]P_{q−1}`。 -/
theorem piPoly_eval {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (piPoly i).eval (q : ℚ) = (Ppoly ℚ (q - 1)).coeff i := by
  rw [piPoly_eval_nat, piSeq, Ppoly_pred_eq_prod hq]

theorem piPoly_zero : piPoly 0 = 1 :=
  ndPoly_eq_of_eval_ge 0 fun n _ => by rw [piPoly_eval_nat, piSeq_zero_left, eval_one]

/-! ## 2. `ν_j(q)` 在 `q ≥ j+2` 时是 `2j` 次多项式，门槛 `j+2` 精确 -/

/-- `ν_j` 的多项式：`Σ_{i≤j} π_i(X)·p_{j−i}(X + (j−i))`。 -/
def numLowPoly (j : ℕ) : ℚ[X] :=
  ∑ i ∈ range (j + 1), piPoly i * (ndPoly (j - i)).comp (X + C ((j - i : ℕ) : ℚ))

/-- 第 `i` 项：`q ≥ j−i+2` 时它在 `q` 处的值是 `π_i(q)·N(q+j−i, q)`（T4.1(a)：`N(k, k−d) = p_d(k)`，`k ≥ 2d+2`）。 -/
theorem numLowTerm_eval {i j q : ℕ} (hi : i ≤ j) (hq : j - i + 2 ≤ q) :
    (piPoly i * (ndPoly (j - i)).comp (X + C ((j - i : ℕ) : ℚ))).eval (q : ℚ)
      = (Ppoly ℚ (q - 1)).coeff i * (N (q + j - i) q : ℚ) := by
  rw [eval_mul, eval_comp, eval_add, eval_X, eval_C, piPoly_eval (by omega)]
  congr 1
  have h := ndPoly_spec (j - i) (q + j - i) (by omega)
  rw [show q + j - i - (j - i) = q by omega] at h
  rw [h, show q + j - i = q + (j - i) by omega, Nat.cast_add]

/-- **T4.3(5)**：`q ≥ j+2` 时 `ν_j(q) = [x^{q+j}]Num_q` 等于多项式 `numLowPoly j` 在 `q` 处的值。 -/
theorem numLowPoly_spec (j q : ℕ) (hq : j + 2 ≤ q) :
    (Numq q).coeff (q + j) = (numLowPoly j).eval (q : ℚ) := by
  rw [Numq_coeff_q_add q j (by omega), numLowPoly, eval_finsetSum]
  refine sum_congr rfl fun i hi => ?_
  rw [numLowTerm_eval (Nat.lt_succ_iff.1 (mem_range.1 hi)) (by omega)]

/-- **T4.3(5)**：`numLowPoly j` 是 `2j` 次多项式，首项 `2/(2^j·j!)`（与 `p_j` 相同）。 -/
theorem numLowPoly_natDegree (j : ℕ) :
    (numLowPoly j).natDegree = 2 * j ∧ (numLowPoly j).leadingCoeff = 2 / (2 ^ j * j ! : ℚ) := by
  set rest : ℚ[X] := ∑ i ∈ range j,
      piPoly (i + 1) * (ndPoly (j - (i + 1))).comp (X + C ((j - (i + 1) : ℕ) : ℚ)) with hrest
  set A : ℚ[X] := (ndPoly j).comp (X + C (j : ℚ)) with hA
  have hsplit : numLowPoly j = rest + A := by
    rw [numLowPoly, sum_range_succ', piPoly_zero, one_mul, Nat.sub_zero]
  have hAdeg : A.natDegree = 2 * j := by
    rw [hA, natDegree_comp, natDegree_X_add_C, mul_one, ndPoly_natDegree]
  have hAlead : A.leadingCoeff = 2 / (2 ^ j * j ! : ℚ) := by
    rw [hA, leadingCoeff_comp (by rw [natDegree_X_add_C]; norm_num), leadingCoeff_X_add_C, one_pow,
      mul_one, ndPoly_leadingCoeff]
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, leadingCoeff_zero] at hAlead
    have hpos : (0 : ℚ) < 2 / (2 ^ j * j ! : ℚ) := by positivity
    exact hpos.ne hAlead
  have hlow : rest.degree < A.degree := by
    rw [degree_eq_natDegree hA0, hAdeg]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hrest]
    · have hnd : rest.natDegree ≤ 2 * j - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
        have hi' := mem_range.1 hi
        refine natDegree_mul_le.trans ?_
        have h1 := piPoly_natDegree_le (i + 1)
        have h2 : ((ndPoly (j - (i + 1))).comp (X + C ((j - (i + 1) : ℕ) : ℚ))).natDegree
            ≤ 2 * (j - (i + 1)) := by
          refine natDegree_comp_le.trans ?_
          rw [natDegree_X_add_C, mul_one, ndPoly_natDegree]
        omega
      refine (degree_le_natDegree).trans_lt ?_
      exact_mod_cast (show rest.natDegree < 2 * j by omega)
  rw [hsplit]
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_right_of_degree_lt hlow, hAdeg]
  · rw [leadingCoeff_add_of_degree_lt hlow, hAlead]

/-- **T4.3(5)**（门槛）：`ν_j(j+1) − numLowPoly j (j+1) = (−1)^{j+1}(j+1)!`。`i ≥ 1` 的项在 `q = j+1` 处仍等于
多项式的值；`i = 0` 项的偏差 `N(2j+1, j+1) − p_j(2j+1)` 是 T4.1 的缺陷。 -/
theorem numLowPoly_threshold (j : ℕ) :
    (Numq (j + 1)).coeff (j + 1 + j) - (numLowPoly j).eval ((j + 1 : ℕ) : ℚ)
      = (-1) ^ (j + 1) * ((j + 1) ! : ℚ) := by
  rw [Numq_coeff_q_add (j + 1) j (by omega), numLowPoly, eval_finsetSum, ← sum_sub_distrib,
    sum_range_succ']
  have hz : ∀ i ∈ range j,
      (Ppoly ℚ (j + 1 - 1)).coeff (i + 1) * (N (j + 1 + j - (i + 1)) (j + 1) : ℚ)
        - (piPoly (i + 1) * (ndPoly (j - (i + 1))).comp (X + C ((j - (i + 1) : ℕ) : ℚ))).eval
          ((j + 1 : ℕ) : ℚ) = 0 := by
    intro i hi
    have hi' := mem_range.1 hi
    rw [numLowTerm_eval (by omega) (by omega), sub_self]
  rw [sum_eq_zero hz, zero_add, coeff_zero_P, one_mul, piPoly_zero, one_mul, eval_comp, eval_add,
    eval_X, eval_C, ← ndE1_closed j, ndE1, show j + 1 + j - 0 = 2 * j + 1 by omega, Nat.sub_zero,
    show ((j + 1 : ℕ) : ℚ) + (j : ℚ) = 2 * (j : ℚ) + 1 by push_cast; ring]

/-- **T4.3(5)**（汇总，一切 `j`）。记 `ν_j(q) := [x^{q+j}]Num_q`：
* 存在唯一 `p ∈ ℚ[X]` 使 `ν_j(q) = p(q)` 对一切 `q ≥ j+2` 成立；
* 对这个 `p`（即任何满足上一条的多项式）：`deg p = 2j`，首项 `2/(2^j·j!)`，`q = j+1` 处的缺陷
  `ν_j(j+1) − p(j+1) = (−1)^{j+1}(j+1)!`。 -/
theorem T4_3_five (j : ℕ) :
    (∃! p : ℚ[X], ∀ q : ℕ, j + 2 ≤ q → (Numq q).coeff (q + j) = p.eval (q : ℚ)) ∧
    ∀ p : ℚ[X], (∀ q : ℕ, j + 2 ≤ q → (Numq q).coeff (q + j) = p.eval (q : ℚ)) →
      p.natDegree = 2 * j ∧ p.leadingCoeff = 2 / (2 ^ j * j ! : ℚ) ∧
      (Numq (j + 1)).coeff (j + 1 + j) - p.eval ((j + 1 : ℕ) : ℚ)
        = (-1) ^ (j + 1) * ((j + 1) ! : ℚ) := by
  have huniq : ∀ p : ℚ[X], (∀ q : ℕ, j + 2 ≤ q → (Numq q).coeff (q + j) = p.eval (q : ℚ)) →
      p = numLowPoly j := fun p hp =>
    ndPoly_eq_of_eval_ge (j + 2) fun q hq => by rw [← hp q hq, numLowPoly_spec j q hq]
  refine ⟨⟨numLowPoly j, fun q hq => numLowPoly_spec j q hq, huniq⟩, fun p hp => ?_⟩
  obtain rfl := huniq p hp
  exact ⟨(numLowPoly_natDegree j).1, (numLowPoly_natDegree j).2, numLowPoly_threshold j⟩

/-- **T4.3(5)**（门槛精确）：没有多项式在一切 `q ≥ j+1` 处等于 `ν_j(q)`，即 `q = j+1` 永远是例外。 -/
theorem T4_3_five_threshold (j : ℕ) :
    ¬ ∃ p : ℚ[X], ∀ q : ℕ, j + 1 ≤ q → (Numq q).coeff (q + j) = p.eval (q : ℚ) := by
  rintro ⟨p, hp⟩
  have hpn : p = numLowPoly j :=
    ndPoly_eq_of_eval_ge (j + 2) fun q hq => by rw [← hp q (by omega), numLowPoly_spec j q hq]
  have h1 := hp (j + 1) le_rfl
  have h2 := numLowPoly_threshold j
  rw [← hpn, ← h1, sub_self] at h2
  have h3 : ((j + 1) ! : ℚ) ≠ 0 := by positivity
  have h4 : ((-1 : ℚ)) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero h4 h3 h2.symm

/-- `numLowPoly 1 = X² − X − 4`（与 `Numq_coeff_q_add_one` 一致）。 -/
theorem numLowPoly_one : numLowPoly 1 = X ^ 2 - X - C 4 :=
  ndPoly_eq_of_eval_ge 3 fun q hq => by
    rw [← numLowPoly_spec 1 q (by omega), Numq_coeff_q_add_one hq]
    simp only [eval_sub, eval_pow, eval_X, eval_C]

/-- `numLowPoly 2 = (X⁴ − 6X³ + 7X² − 2X + 76)/4`（与 `Numq_coeff_q_add_two` 一致）。 -/
theorem numLowPoly_two :
    numLowPoly 2 = C (1 / 4 : ℚ) * (X ^ 4 - C 6 * X ^ 3 + C 7 * X ^ 2 - C 2 * X + C 76) :=
  ndPoly_eq_of_eval_ge 4 fun q hq => by
    rw [← numLowPoly_spec 2 q (by omega), Numq_coeff_q_add_two hq]
    simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_C]
    ring

end

end A207123
