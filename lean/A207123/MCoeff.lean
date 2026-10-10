import A207123.NearDiag
import A207123.NumStruct

/-!
# 报告 T5.2 的其余部分：固定 `k`、`m → ∞` 时 `U_k(m)` 的高次系数

记 `B_d(k) := (k−d)!·[m^{k−d}] u_k`（`u_k = upoly k` 是 `U_k(m)` 关于 `m` 的插值多项式）。`NearDiag.lean` 的
`T5_2_formula` 给出 `B_d(k) = Σ_{e≤d} (−1)^{d−e}·N(k,k−e)·ẽ_{d−e}(k−e)`，`ẽ_j(n) = e_j(−1,0,…,n−2)/n^{\underline j}`。

* `exists_poly_of_fwdDiff_iter`：`ℕ` 上的数列前向差分 `D + 1` 次为 0 时等于一个次数 `≤ D` 的多项式（Newton
  公式）；`fwdDiff_iter_poly_eq_zero`：反过来，次数 `< n` 的多项式在自然数上的值差分 `n` 次为 0（由 Mathlib 的
  `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`）。
* `esPoly j`：`e_j(−1,…,n−2)` 是 `n` 的次数 `≤ 2j` 的多项式（递推 `e_{j+1}(n+1) = e_{j+1}(n) + (n−1)e_j(n)`，
  `ndEsym_succ`）；它在 `n = 0,…,j−1` 处为 0（不足 `j` 个数），所以被 `n^{\underline j}` 整除
  （`descPochhammer_dvd_of_eval`），商 `esQ j` 的次数 `≤ j`，`n ≥ j` 时 `esQ j (n) = ẽ_j(n)`（`esQ_eval`）。
* `bPoly d := Σ_e (−1)^{d−e}·p_e(X)·ẽ_{d−e}(X−e)`（`p_e = ndPoly e`）：`B_eq_bPoly`：`k ≥ 2d+2` 时
  `B_d(k) = b_d(k)`；`bPoly_natDegree`：`b_d` 是 `2d` 次，首项 `2/(2^d·d!)`；`B_threshold`：
  `B_d(2d+1) − b_d(2d+1) = (−1)^{d+1}(d+1)!`；`B_threshold_exact`：没有多项式在一切 `k ≥ 2d+1` 处等于 `B_d(k)`。
* 显式（`d = 2, 3`）：`N_eight_five`（`N(8,5) = 574`）、`N_sub_three`（`k ≥ 8` 时
  `N(k,k−3) = p_3(k) = (k⁶−27k⁵+331k⁴−2225k³+8560k²−17392k+11088)/24`）、`etilde_one`–`etilde_three`
  （`ẽ_1(n) = (n−3)/2`、`ẽ_2(n) = (n−2)(3n−13)/24`、`ẽ_3(n) = (n−3)(n²−7n+8)/48`）；
  `T5_2_coeff_two`：`k ≥ 6` 时 `[m^{k−2}]U_k = (3k⁴−36k³+162k²−313k+422)/(12·(k−2)!)`；
  `T5_2_coeff_three`：`k ≥ 8` 时 `[m^{k−3}]U_k = (k⁶−30k⁵+379k⁴−2533k³+9570k²−19331k+13380)/(24·(k−3)!)`。
* 报告 T4.1 的 `d ≤ 5` 公式：`N_sub_three`（上面）、`N_sub_four`（`k ≥ 10`）、`N_sub_five`（`k ≥ 12`），基点
  `N(10,6) = 6012`、`N(12,7) = 70674` 由三角递推算出（`N_table`）；论文第 7 节的例子 `p_2`、`p_3`
  （`ndPoly_two`、`ndPoly_three`）与表 4（门槛以下的值与缺陷，`table_exc`）。
* `T5_2_asymp`：`k ≥ 4` 时 `U_k(m) = (2/k!)(m+μ_k)^k(1+O(m^{−2}))`，`μ_k = (k²−2k−1)/2`；`upoly_top_three`：
  `k ≥ 6` 时 `u_k = 2·C(m+1,k) + (k²−k−4)·C(m+1,k−1) + p_2(k)·C(m+1,k−2) + Σ_{q<k−2} N(k,q)·C(m+1,q)`。
-/

namespace A207123

open Polynomial Finset
open scoped Nat

noncomputable section

/-! ## 1. 前向差分与多项式 -/

/-- `ℕ` 上的前向差分与 `ℚ` 上的前向差分在自然数处相同。 -/
theorem fwdDiff_iter_natCast (g : ℚ → ℚ) (n y : ℕ) :
    (fwdDiff (1 : ℕ))^[n] (fun k : ℕ => g k) y = (fwdDiff (1 : ℚ))^[n] g (y : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun i _ => ?_
  simp [nsmul_eq_mul]

/-- 次数 `< n` 的多项式在自然数上的值，前向差分 `n` 次为 0。 -/
theorem fwdDiff_iter_poly_eq_zero {P : ℚ[X]} {n : ℕ} (hP : P.natDegree < n) :
    (fwdDiff (1 : ℕ))^[n] (fun k : ℕ => P.eval (k : ℚ)) = 0 := by
  funext y
  rw [fwdDiff_iter_natCast P.eval n y, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP]
  rfl

/-- 前向差分 `D + 1` 次为 0 的数列等于一个次数 `≤ D` 的多项式（Newton 公式）。 -/
theorem exists_poly_of_fwdDiff_iter {f : ℕ → ℚ} {D : ℕ} (hf : (fwdDiff (1 : ℕ))^[D + 1] f = 0) :
    ∃ P : ℚ[X], P.natDegree ≤ D ∧ ∀ n : ℕ, P.eval (n : ℚ) = f n := by
  have hz : ∀ i, D + 1 ≤ i → (fwdDiff (1 : ℕ))^[i] f 0 = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [add_comm, Function.iterate_add_apply, hf]
    exact congrFun (ndNC_zero_fun (R := ℚ) j) 0
  refine ⟨∑ i ∈ range (D + 1), C ((fwdDiff (1 : ℕ))^[i] f 0 / (i ! : ℚ)) * descPochhammer ℚ i, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [descPochhammer_natDegree]
    exact Nat.lt_succ_iff.1 (mem_range.1 hi)
  · intro n
    have hN := shift_eq_sum_fwdDiff_iter 1 f n 0
    simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at hN
    rw [hN, eval_finsetSum]
    have e1 : ∑ i ∈ range (D + 1),
          (C ((fwdDiff (1 : ℕ))^[i] f 0 / (i ! : ℚ)) * descPochhammer ℚ i).eval (n : ℚ)
        = ∑ i ∈ range (n + D + 2), ((n.choose i : ℕ) : ℚ) * (fwdDiff (1 : ℕ))^[i] f 0 := by
      rw [← sum_range_add_sum_Ico _ (show D + 1 ≤ n + D + 2 by omega),
        sum_eq_zero (s := Ico (D + 1) (n + D + 2)) fun i hi => by rw [hz i (mem_Ico.1 hi).1, mul_zero],
        add_zero]
      refine sum_congr rfl fun i _ => ?_
      have hf : (i ! : ℚ) ≠ 0 := by positivity
      rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
        Nat.cast_mul, ← mul_assoc, div_mul_cancel₀ _ hf, mul_comm]
    have e2 : ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℚ) * (fwdDiff (1 : ℕ))^[i] f 0
        = ∑ i ∈ range (n + D + 2), ((n.choose i : ℕ) : ℚ) * (fwdDiff (1 : ℕ))^[i] f 0 := by
      rw [← sum_range_add_sum_Ico _ (show n + 1 ≤ n + D + 2 by omega),
        sum_eq_zero (s := Ico (n + 1) (n + D + 2)) fun i hi => by
          rw [Nat.choose_eq_zero_of_lt (by have := (mem_Ico.1 hi).1; omega), Nat.cast_zero, zero_mul],
        add_zero]
    rw [e1, ← e2]

/-! ## 2. `e_j(−1,…,n−2)` 是 `n` 的多项式，`ẽ_j` 也是 -/

theorem msEsymm_cons (a : ℚ) (s : Multiset ℚ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem ndEsym_zero_left (n : ℕ) : ndEsym 0 n = 1 := Multiset.esymm_zero _

theorem ndEsym_eq_zero_of_lt {j n : ℕ} (h : n < j) : ndEsym j n = 0 :=
  Multiset.esymm_of_card_lt (by simpa using h)

/-- 递推：`e_{j+1}(n+1) = e_{j+1}(n) + (n−1)·e_j(n)`（多加的数是 `n − 1`）。 -/
theorem ndEsym_succ (j n : ℕ) :
    ndEsym (j + 1) (n + 1) = ndEsym (j + 1) n + ((n : ℚ) - 1) * ndEsym j n := by
  simp only [ndEsym, Multiset.range_succ, Multiset.map_cons]
  exact msEsymm_cons _ _ _

theorem ndEsym_poly (j : ℕ) :
    ∃ P : ℚ[X], P.natDegree ≤ 2 * j ∧ ∀ n : ℕ, P.eval (n : ℚ) = ndEsym j n := by
  induction j with
  | zero => exact ⟨1, by simp, fun n => by simp [ndEsym_zero_left]⟩
  | succ j ih =>
    obtain ⟨P, hPd, hP⟩ := ih
    have hD : fwdDiff (1 : ℕ) (fun n => ndEsym (j + 1) n) = fun n => ((X - 1) * P).eval (n : ℚ) := by
      funext n
      rw [ndFD_apply, ndEsym_succ, eval_mul, eval_sub, eval_X, eval_one, hP]
      ring
    have hdeg : ((X - 1 : ℚ[X]) * P).natDegree < 2 * j + 2 := by
      have h1 : (X - 1 : ℚ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
      have h2 := natDegree_mul_le (p := (X - 1 : ℚ[X])) (q := P)
      omega
    refine exists_poly_of_fwdDiff_iter (f := fun n => ndEsym (j + 1) n) (D := 2 * (j + 1)) ?_
    rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by ring, Function.iterate_succ_apply, hD]
    exact fwdDiff_iter_poly_eq_zero hdeg

/-- `e_j(−1,…,n−2)` 作为 `n` 的多项式（次数 `≤ 2j`）。 -/
def esPoly (j : ℕ) : ℚ[X] := Classical.choose (ndEsym_poly j)

theorem esPoly_natDegree_le (j : ℕ) : (esPoly j).natDegree ≤ 2 * j :=
  (Classical.choose_spec (ndEsym_poly j)).1

theorem esPoly_eval (j n : ℕ) : (esPoly j).eval (n : ℚ) = ndEsym j n :=
  (Classical.choose_spec (ndEsym_poly j)).2 n

/-- 在 `0, 1, …, j−1` 处为 0 的多项式被 `X^{\underline j}` 整除。 -/
theorem descPochhammer_dvd_of_eval {P : ℚ[X]} :
    ∀ j : ℕ, (∀ i : ℕ, i < j → P.eval (i : ℚ) = 0) → descPochhammer ℚ j ∣ P
  | 0, _ => by
    rw [descPochhammer_zero]
    exact one_dvd P
  | j + 1, h => by
    obtain ⟨Q, hQ⟩ := descPochhammer_dvd_of_eval j fun i hi => h i (by omega)
    have hj := h j (by omega)
    rw [hQ, eval_mul, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self] at hj
    have hf : ((j ! : ℕ) : ℚ) ≠ 0 := by positivity
    have hQj : Q.IsRoot (j : ℚ) := (mul_eq_zero.1 hj).resolve_left hf
    obtain ⟨R, hR⟩ := dvd_iff_isRoot.2 hQj
    refine ⟨R, ?_⟩
    rw [hQ, hR, descPochhammer_succ_right, map_natCast C j]
    ring

theorem esPoly_dvd (j : ℕ) : descPochhammer ℚ j ∣ esPoly j :=
  descPochhammer_dvd_of_eval j fun i hi => by
    rw [esPoly_eval]
    exact ndEsym_eq_zero_of_lt hi

/-- 商多项式：`n ≥ j` 时 `esQ j (n) = ẽ_j(n) = e_j(−1,…,n−2)/n^{\underline j}`。 -/
def esQ (j : ℕ) : ℚ[X] := Classical.choose (esPoly_dvd j)

theorem esPoly_eq_mul (j : ℕ) : esPoly j = descPochhammer ℚ j * esQ j :=
  Classical.choose_spec (esPoly_dvd j)

theorem esQ_eval {j n : ℕ} (h : j ≤ n) :
    (esQ j).eval (n : ℚ) = ndEsym j n / (n.descFactorial j : ℚ) := by
  have hpos : (n.descFactorial j : ℚ) ≠ 0 := by
    have : n.descFactorial j ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
      omega
    exact_mod_cast this
  rw [← esPoly_eval, esPoly_eq_mul, eval_mul, descPochhammer_eval_eq_descFactorial,
    mul_div_cancel_left₀ _ hpos]

theorem esQ_natDegree_le (j : ℕ) : (esQ j).natDegree ≤ j := by
  by_cases hQ : esQ j = 0
  · rw [hQ, natDegree_zero]
    exact Nat.zero_le _
  · have h1 := esPoly_natDegree_le j
    rw [esPoly_eq_mul, natDegree_mul (monic_descPochhammer ℚ j).ne_zero hQ, descPochhammer_natDegree] at h1
    omega

theorem esQ_zero : esQ 0 = 1 := by
  have h0 := esPoly_eq_mul 0
  rw [descPochhammer_zero, one_mul] at h0
  have hd : (esPoly 0).natDegree ≤ 0 := by simpa using esPoly_natDegree_le 0
  have h1 := esPoly_eval 0 0
  rw [ndEsym_zero_left, eq_C_of_natDegree_le_zero hd, eval_C] at h1
  rw [← h0, eq_C_of_natDegree_le_zero hd, h1, C_1]

/-! ## 3. `B_d(k)` 是 `2d` 次多项式，门槛 `2d + 2` 精确 -/

/-- `b_d(X) = Σ_{e≤d} (−1)^{d−e}·p_e(X)·ẽ_{d−e}(X−e)`。 -/
def bPoly (d : ℕ) : ℚ[X] :=
  ∑ e ∈ range (d + 1), C ((-1 : ℚ) ^ (d - e)) * ndPoly e * (esQ (d - e)).comp (X - C (e : ℚ))

theorem bTerm_eval {d e k : ℕ} (he : e ≤ d) (hk : d ≤ k) (hN : 2 * e + 2 ≤ k) :
    (C ((-1 : ℚ) ^ (d - e)) * ndPoly e * (esQ (d - e)).comp (X - C (e : ℚ))).eval (k : ℚ) =
      (-1 : ℚ) ^ (d - e) * (N k (k - e) : ℚ) *
        (ndEsym (d - e) (k - e) / ((k - e).descFactorial (d - e) : ℚ)) := by
  rw [eval_mul, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, ← ndPoly_spec e k hN,
    ← Nat.cast_sub (by omega : e ≤ k), esQ_eval (by omega)]

/-- **T5.2**：`k ≥ 2d + 2` 时 `B_d(k) = (k−d)!·[m^{k−d}] u_k` 等于多项式 `b_d` 在 `k` 处的值。 -/
theorem B_eq_bPoly (d k : ℕ) (hk : 2 * d + 2 ≤ k) :
    ((k - d) ! : ℚ) * (upoly k).coeff (k - d) = (bPoly d).eval (k : ℚ) := by
  rw [T5_2_formula d k (by omega), bPoly, eval_finsetSum]
  refine sum_congr rfl fun e he => ?_
  have he' : e ≤ d := Nat.lt_succ_iff.1 (mem_range.1 he)
  rw [bTerm_eval he' (by omega) (by omega)]

/-- **T5.2**：`b_d` 是 `2d` 次多项式，首项 `2/(2^d·d!)`（与 `p_d` 相同）。 -/
theorem bPoly_natDegree (d : ℕ) :
    (bPoly d).natDegree = 2 * d ∧ (bPoly d).leadingCoeff = 2 / (2 ^ d * d ! : ℚ) := by
  set rest : ℚ[X] := ∑ e ∈ range d, C ((-1 : ℚ) ^ (d - e)) * ndPoly e * (esQ (d - e)).comp (X - C (e : ℚ))
    with hrest
  have hsplit : bPoly d = rest + ndPoly d := by
    rw [bPoly, sum_range_succ, Nat.sub_self, pow_zero, C_1, one_mul, esQ_zero, one_comp, mul_one]
  have hpd0 : ndPoly d ≠ 0 := by
    intro h
    have := ndPoly_leadingCoeff d
    rw [h, leadingCoeff_zero] at this
    have hpos : (0 : ℚ) < 2 / (2 ^ d * d ! : ℚ) := by positivity
    exact hpos.ne this
  have hdeg_pd : (ndPoly d).degree = ((2 * d : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hpd0, ndPoly_natDegree]
  have hlow : rest.degree < (ndPoly d).degree := by
    rw [hdeg_pd]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hrest]
    · have hnd : rest.natDegree ≤ 2 * d - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun e he => ?_
        have he' := mem_range.1 he
        refine (natDegree_mul_le).trans ?_
        have h1 : (C ((-1 : ℚ) ^ (d - e)) * ndPoly e).natDegree ≤ 2 * e :=
          (natDegree_C_mul_le _ _).trans (ndPoly_natDegree e).le
        have h2 : ((esQ (d - e)).comp (X - C (e : ℚ))).natDegree ≤ d - e := by
          refine natDegree_comp_le.trans ?_
          rw [natDegree_X_sub_C, mul_one]
          exact esQ_natDegree_le _
        omega
      refine (degree_le_natDegree).trans_lt ?_
      exact_mod_cast (show rest.natDegree < 2 * d by omega)
  rw [hsplit]
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_right_of_degree_lt hlow, ndPoly_natDegree]
  · rw [leadingCoeff_add_of_degree_lt hlow, ndPoly_leadingCoeff]

/-- **T5.2**（门槛）：`B_d(2d+1) − b_d(2d+1) = (−1)^{d+1}(d+1)!`（只有 `e = d` 一项偏离多项式，偏差就是 T4.1
的缺陷 `N(2d+1, d+1) − p_d(2d+1)`）。 -/
theorem B_threshold (d : ℕ) :
    ((d + 1) ! : ℚ) * (upoly (2 * d + 1)).coeff (d + 1) - (bPoly d).eval ((2 * d + 1 : ℕ) : ℚ)
      = (-1) ^ (d + 1) * ((d + 1) ! : ℚ) := by
  have h := T5_2_formula d (2 * d + 1) (by omega)
  rw [show 2 * d + 1 - d = d + 1 by omega] at h
  rw [h, bPoly, eval_finsetSum, sum_range_succ, sum_range_succ, ← ndE1_closed d, ndE1]
  have hrest : ∑ e ∈ range d, (-1 : ℚ) ^ (d - e) * (N (2 * d + 1) (2 * d + 1 - e) : ℚ) *
        (ndEsym (d - e) (2 * d + 1 - e) / ((2 * d + 1 - e).descFactorial (d - e) : ℚ))
      = ∑ e ∈ range d, (C ((-1 : ℚ) ^ (d - e)) * ndPoly e * (esQ (d - e)).comp (X - C (e : ℚ))).eval
          ((2 * d + 1 : ℕ) : ℚ) := by
    refine sum_congr rfl fun e he => ?_
    have he' := mem_range.1 he
    rw [bTerm_eval he'.le (by omega) (by omega)]
  rw [hrest, Nat.sub_self, pow_zero, one_mul, ndEsym_zero_left, Nat.descFactorial_zero, Nat.cast_one,
    div_one, mul_one, eval_mul, eval_mul, eval_C, one_mul, esQ_zero, one_comp, eval_one, mul_one,
    show 2 * d + 1 - d = d + 1 by omega]
  push_cast
  ring

/-- **T5.2**（门槛精确）：没有多项式在一切 `k ≥ 2d+1` 处等于 `B_d(k)`。 -/
theorem B_threshold_exact (d : ℕ) :
    ¬ ∃ P : ℚ[X], ∀ k : ℕ, 2 * d + 1 ≤ k →
      P.eval (k : ℚ) = ((k - d) ! : ℚ) * (upoly k).coeff (k - d) := by
  rintro ⟨P, hP⟩
  have hPb : P = bPoly d := ndPoly_eq_of_eval_ge (2 * d + 2) fun k hk => by
    rw [hP k (by omega), B_eq_bPoly d k hk]
  have h1 := hP (2 * d + 1) le_rfl
  rw [hPb, show 2 * d + 1 - d = d + 1 by omega] at h1
  have h2 := B_threshold d
  rw [← h1, sub_self] at h2
  have h3 : ((d + 1) ! : ℚ) ≠ 0 := by positivity
  have h4 : ((-1 : ℚ)) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero h4 h3 h2.symm

/-! ## 4. `d = 2, 3` 的显式式 -/

theorem ndEsym_one (n : ℕ) : ndEsym 1 n = (n : ℚ) * (n - 3) / 2 := by
  induction n with
  | zero =>
    rw [ndEsym_eq_zero_of_lt (by norm_num)]
    simp
  | succ n ih =>
    rw [ndEsym_succ, ih, ndEsym_zero_left]
    push_cast
    ring

theorem ndEsym_two (n : ℕ) : ndEsym 2 n = (n : ℚ) * (n - 1) * (n - 2) * (3 * n - 13) / 24 := by
  induction n with
  | zero =>
    rw [ndEsym_eq_zero_of_lt (by norm_num)]
    simp
  | succ n ih =>
    rw [ndEsym_succ, ih, ndEsym_one]
    push_cast
    ring

theorem ndEsym_three (n : ℕ) :
    ndEsym 3 n = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) * (n ^ 2 - 7 * n + 8) / 48 := by
  induction n with
  | zero =>
    rw [ndEsym_eq_zero_of_lt (by norm_num)]
    simp
  | succ n ih =>
    rw [ndEsym_succ, ih, ndEsym_two]
    push_cast
    ring

/-- `ẽ_1(n) = (n−3)/2`（`n ≥ 1`）。 -/
theorem etilde_one {n : ℕ} (hn : 1 ≤ n) : ndEsym 1 n / (n.descFactorial 1 : ℚ) = ((n : ℚ) - 3) / 2 := by
  have h0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [ndEsym_one, Nat.descFactorial_one, div_eq_div_iff h0 two_ne_zero]
  ring

/-- `ẽ_2(n) = (n−2)(3n−13)/24`（`n ≥ 2`）。 -/
theorem etilde_two {n : ℕ} (hn : 2 ≤ n) :
    ndEsym 2 n / (n.descFactorial 2 : ℚ) = ((n : ℚ) - 2) * (3 * n - 13) / 24 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hd : (m + 2).descFactorial 2 = (m + 2) * (m + 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, show m + 2 - 1 = m + 1 by omega]
    ring
  have h0 : (((m + 2) * (m + 1) : ℕ) : ℚ) ≠ 0 := by positivity
  rw [ndEsym_two, hd, div_eq_div_iff h0 (by norm_num)]
  push_cast
  ring

/-- `ẽ_3(n) = (n−3)(n²−7n+8)/48`（`n ≥ 3`）。 -/
theorem etilde_three {n : ℕ} (hn : 3 ≤ n) :
    ndEsym 3 n / (n.descFactorial 3 : ℚ) = ((n : ℚ) - 3) * (n ^ 2 - 7 * n + 8) / 48 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hd : (m + 3).descFactorial 3 = (m + 3) * (m + 2) * (m + 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one,
      show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
    ring
  have h0 : (((m + 3) * (m + 2) * (m + 1) : ℕ) : ℚ) ≠ 0 := by positivity
  rw [ndEsym_three, hd, div_eq_div_iff h0 (by norm_num)]
  push_cast
  ring

/-! 下面的数值计算沿用 `NumStruct.lean` 中 `N_six_four` 的写法：三角递推的各个实例先用 `rw` 代入数字等式化成
字面量下标（不用 `simp` 化简 `N (a+b) c`，否则内核核对时可能展开 `N` 的组合定义去枚举序列），算术在变量层面
做完（`N_eight_five_aux`），再把各实例代进去，代入时类型逐字一致。 -/

theorem N_tri_four_one : N 4 1 = N 3 0 + N 3 1 := by
  have h := N_tri 1 0
  rw [show (1 : ℕ) + 3 = 4 from rfl, show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 2 = 3 from rfl,
    zero_mul, add_zero] at h
  exact h

theorem N_tri_five_two : N 5 2 = N 4 1 + N 4 2 + (N 2 0 + 2 * N 2 1 + N 2 2) := by
  have h := N_tri 2 1
  rw [show (2 : ℕ) + 3 = 5 from rfl, show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) + 2 = 4 from rfl,
    show (1 : ℕ) - 1 = 0 from rfl, one_mul] at h
  exact h

theorem N_tri_six_three : N 6 3 = N 5 2 + N 5 3 + 2 * (N 3 1 + 2 * N 3 2 + N 3 3) := by
  have h := N_tri 3 2
  rw [show (3 : ℕ) + 3 = 6 from rfl, show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 2 = 5 from rfl,
    show (2 : ℕ) - 1 = 1 from rfl] at h
  exact h

theorem N_tri_seven_four : N 7 4 = N 6 3 + N 6 4 + 3 * (N 4 2 + 2 * N 4 3 + N 4 4) := by
  have h := N_tri 4 3
  rw [show (4 : ℕ) + 3 = 7 from rfl, show (3 : ℕ) + 1 = 4 from rfl, show (4 : ℕ) + 2 = 6 from rfl,
    show (3 : ℕ) - 1 = 2 from rfl] at h
  exact h

theorem N_tri_seven_five : N 7 5 = N 6 4 + N 6 5 + 4 * (N 4 3 + 2 * N 4 4 + N 4 5) := by
  have h := N_tri 4 4
  rw [show (4 : ℕ) + 3 = 7 from rfl, show (4 : ℕ) + 1 = 5 from rfl, show (4 : ℕ) + 2 = 6 from rfl,
    show (4 : ℕ) - 1 = 3 from rfl] at h
  exact h

theorem N_tri_eight_five : N 8 5 = N 7 4 + N 7 5 + 4 * (N 5 3 + 2 * N 5 4 + N 5 5) := by
  have h := N_tri 5 4
  rw [show (5 : ℕ) + 3 = 8 from rfl, show (4 : ℕ) + 1 = 5 from rfl, show (5 : ℕ) + 2 = 7 from rfl,
    show (4 : ℕ) - 1 = 3 from rfl] at h
  exact h

/-- `N(6,5) = 26`（`N_subdiag` 取 `k = 6`）。 -/
theorem N_six_five : N 6 5 = 26 := by
  have h := N_subdiag 6 (by norm_num)
  rw [show (6 : ℕ) - 1 = 5 from rfl] at h
  have h' : ((N 6 5 : ℕ) : ℤ) = ((26 : ℕ) : ℤ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_eight_five_aux {a85 a74 a75 a53 a54 a55 a63 a64 a65 a42 a43 a44 a45 a52 a41 a31 a32 a33 a30
      a20 a21 a22 a23 a10 a11 a12 : ℕ}
    (h85 : a85 = a74 + a75 + 4 * (a53 + 2 * a54 + a55))
    (h75 : a75 = a64 + a65 + 4 * (a43 + 2 * a44 + a45))
    (h74 : a74 = a63 + a64 + 3 * (a42 + 2 * a43 + a44))
    (h63 : a63 = a52 + a53 + 2 * (a31 + 2 * a32 + a33))
    (h53 : a53 = a42 + a43 + 2 * (a21 + 2 * a22 + a23))
    (h52 : a52 = a41 + a42 + (a20 + 2 * a21 + a22))
    (h42 : a42 = a31 + a32 + (a10 + 2 * a11 + a12))
    (h41 : a41 = a30 + a31)
    (h31 : a31 = a20 + a21)
    (v54 : a54 = 16) (v55 : a55 = 2) (v64 : a64 = 65) (v65 : a65 = 26) (v43 : a43 = 8) (v44 : a44 = 2)
    (v45 : a45 = 0) (v32 : a32 = 4) (v33 : a33 = 2) (v30 : a30 = 0) (v20 : a20 = 0) (v21 : a21 = 1)
    (v22 : a22 = 2) (v23 : a23 = 0) (v10 : a10 = 0) (v11 : a11 = 1) (v12 : a12 = 0) : a85 = 574 := by
  subst v54 v55 v64 v65 v43 v44 v45 v32 v33 v30 v20 v21 v22 v23 v10 v11 v12
  omega

/-- `N(8,5) = 574`（由三角递推从小的值算出）。 -/
theorem N_eight_five : N 8 5 = 574 :=
  N_eight_five_aux N_tri_eight_five N_tri_seven_five N_tri_seven_four N_tri_six_three N_tri_five_three
    N_tri_five_two N_tri_four_two N_tri_four_one N_tri_three_one
    N_four_three_five_four.2 (N_diag 5 (by norm_num)) N_six_four N_six_five N_four_three_five_four.1
    (N_diag 4 (by norm_num)) (N_eq_zero_of_lt (by norm_num)) N_three_two (N_diag 3 (by norm_num))
    (N_succ_zero 2) (N_succ_zero 1) N_init.2.2.1 N_init.2.2.2 (N_eq_zero_of_lt (by norm_num))
    (N_succ_zero 0) N_init.2.1 (N_eq_zero_of_lt (by norm_num))

/-- `k ≥ 8` 时 `N(k, k−3) = p_3(k) = (k⁶ − 27k⁵ + 331k⁴ − 2225k³ + 8560k² − 17392k + 11088)/24`（写成 `k = s + 8`）。 -/
theorem N_sub_three (s : ℕ) :
    (N (s + 8) (s + 5) : ℚ) = (((s : ℚ) + 8) ^ 6 - 27 * ((s : ℚ) + 8) ^ 5 + 331 * ((s : ℚ) + 8) ^ 4
      - 2225 * ((s : ℚ) + 8) ^ 3 + 8560 * ((s : ℚ) + 8) ^ 2 - 17392 * ((s : ℚ) + 8) + 11088) / 24 := by
  induction s with
  | zero =>
    rw [N_eight_five]
    norm_num
  | succ s ih =>
    have h := N_tri (s + 6) (s + 5)
    have e1 : N (s + 6) (s + 5 + 1) = 2 := N_diag (s + 6) (by omega)
    rw [e1, show s + 5 - 1 = s + 4 by omega] at h
    have hq : (N (s + 6 + 3) (s + 5 + 1) : ℚ)
        = N (s + 6 + 2) (s + 5) + N (s + 6 + 2) (s + 5 + 1)
          + (s + 5 : ℚ) * (N (s + 6) (s + 4) + 2 * N (s + 6) (s + 5) + 2) := by
      exact_mod_cast h
    have hA := N_sub_two (s + 2)
    have hB := N_sub_two s
    have hC := N_subdiag_rat (k := s + 6) (by omega)
    rw [show s + 2 + 6 = s + 6 + 2 by omega, show s + 2 + 4 = s + 5 + 1 by omega] at hA
    rw [show s + 6 - 1 = s + 5 by omega] at hC
    rw [show s + 1 + 8 = s + 6 + 3 by omega, show s + 1 + 5 = s + 5 + 1 by omega, hq, hA,
      show s + 6 + 2 = s + 8 by omega, ih, hB, hC]
    push_cast
    ring

/-- **T5.2**（显式）：`k ≥ 6` 时 `[m^{k−2}] u_k = (3k⁴ − 36k³ + 162k² − 313k + 422)/(12·(k−2)!)`。 -/
theorem T5_2_coeff_two (k : ℕ) (hk : 6 ≤ k) :
    (upoly k).coeff (k - 2) =
      (3 * (k : ℚ) ^ 4 - 36 * k ^ 3 + 162 * k ^ 2 - 313 * k + 422) / (12 * ((k - 2) ! : ℚ)) := by
  have h := T5_2_formula 2 k (by omega)
  rw [sum_range_succ, sum_range_succ, sum_range_one] at h
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero, one_mul, ndEsym_zero_left, Nat.descFactorial_zero,
    Nat.cast_one, div_one, mul_one, show (2 : ℕ) - 1 = 1 from rfl] at h
  rw [etilde_two (n := k) (by omega), etilde_one (n := k - 1) (by omega), N_diag k (by omega)] at h
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 6 := ⟨k - 6, by omega⟩
  have hA := N_subdiag_rat (k := s + 6) (by omega)
  have hB := N_sub_two s
  rw [show s + 6 - 2 = s + 4 by omega] at h ⊢
  rw [show s + 6 - 1 = s + 5 by omega] at h hA
  rw [hA, hB] at h
  rw [eq_div_iff (by positivity)]
  push_cast at h ⊢
  linear_combination (12 : ℚ) * h

/-- **T5.2**（显式）：`k ≥ 8` 时
`[m^{k−3}] u_k = (k⁶ − 30k⁵ + 379k⁴ − 2533k³ + 9570k² − 19331k + 13380)/(24·(k−3)!)`。 -/
theorem T5_2_coeff_three (k : ℕ) (hk : 8 ≤ k) :
    (upoly k).coeff (k - 3) =
      ((k : ℚ) ^ 6 - 30 * k ^ 5 + 379 * k ^ 4 - 2533 * k ^ 3 + 9570 * k ^ 2 - 19331 * k + 13380)
        / (24 * ((k - 3) ! : ℚ)) := by
  have h := T5_2_formula 3 k (by omega)
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one] at h
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero, one_mul, ndEsym_zero_left, Nat.descFactorial_zero,
    Nat.cast_one, div_one, mul_one, show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) - 2 = 1 from rfl] at h
  rw [etilde_three (n := k) (by omega), etilde_two (n := k - 1) (by omega),
    etilde_one (n := k - 2) (by omega), N_diag k (by omega)] at h
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 8 := ⟨k - 8, by omega⟩
  have hA := N_subdiag_rat (k := s + 8) (by omega)
  have hB := N_sub_two (s + 2)
  have hC := N_sub_three s
  rw [show s + 2 + 6 = s + 8 by omega, show s + 2 + 4 = s + 6 by omega] at hB
  rw [show s + 8 - 3 = s + 5 by omega] at h ⊢
  rw [show s + 8 - 2 = s + 6 by omega, show s + 8 - 1 = s + 7 by omega] at h
  rw [show s + 8 - 1 = s + 7 by omega] at hA
  rw [hA, hB, hC] at h
  rw [eq_div_iff (by positivity)]
  push_cast at h ⊢
  linear_combination (24 : ℚ) * h

/-! ## 6. `p_4`、`p_5` 的显式式（报告 T4.1，`d ≤ 5`）

基点 `N(10,6) = 6012`、`N(12,7) = 70674` 用同样的写法从三角递推算出（`N_table_aux`），再对 `k` 归纳。 -/

theorem N_tri_five_one : N 5 1 = N 4 0 + N 4 1 := by
  have h := N_tri 2 0
  rw [show (2 : ℕ) + 3 = 5 from rfl, show (0 : ℕ) + 1 = 1 from rfl, show (2 : ℕ) + 2 = 4 from rfl, zero_mul, add_zero] at h
  exact h

theorem N_tri_six_one : N 6 1 = N 5 0 + N 5 1 := by
  have h := N_tri 3 0
  rw [show (3 : ℕ) + 3 = 6 from rfl, show (0 : ℕ) + 1 = 1 from rfl, show (3 : ℕ) + 2 = 5 from rfl, zero_mul, add_zero] at h
  exact h

theorem N_tri_six_two : N 6 2 = N 5 1 + N 5 2 + (N 3 0 + 2 * N 3 1 + N 3 2) := by
  have h := N_tri 3 1
  rw [show (3 : ℕ) + 3 = 6 from rfl, show (1 : ℕ) + 1 = 2 from rfl, show (3 : ℕ) + 2 = 5 from rfl, show (1 : ℕ) - 1 = 0 from rfl] at h
  simp only [one_mul] at h
  exact h

theorem N_tri_seven_two : N 7 2 = N 6 1 + N 6 2 + (N 4 0 + 2 * N 4 1 + N 4 2) := by
  have h := N_tri 4 1
  rw [show (4 : ℕ) + 3 = 7 from rfl, show (1 : ℕ) + 1 = 2 from rfl, show (4 : ℕ) + 2 = 6 from rfl, show (1 : ℕ) - 1 = 0 from rfl] at h
  simp only [one_mul] at h
  exact h

theorem N_tri_seven_three : N 7 3 = N 6 2 + N 6 3 + 2 * (N 4 1 + 2 * N 4 2 + N 4 3) := by
  have h := N_tri 4 2
  rw [show (4 : ℕ) + 3 = 7 from rfl, show (2 : ℕ) + 1 = 3 from rfl, show (4 : ℕ) + 2 = 6 from rfl, show (2 : ℕ) - 1 = 1 from rfl] at h
  exact h

theorem N_tri_eight_three : N 8 3 = N 7 2 + N 7 3 + 2 * (N 5 1 + 2 * N 5 2 + N 5 3) := by
  have h := N_tri 5 2
  rw [show (5 : ℕ) + 3 = 8 from rfl, show (2 : ℕ) + 1 = 3 from rfl, show (5 : ℕ) + 2 = 7 from rfl, show (2 : ℕ) - 1 = 1 from rfl] at h
  exact h

theorem N_tri_eight_four : N 8 4 = N 7 3 + N 7 4 + 3 * (N 5 2 + 2 * N 5 3 + N 5 4) := by
  have h := N_tri 5 3
  rw [show (5 : ℕ) + 3 = 8 from rfl, show (3 : ℕ) + 1 = 4 from rfl, show (5 : ℕ) + 2 = 7 from rfl, show (3 : ℕ) - 1 = 2 from rfl] at h
  exact h

theorem N_tri_nine_four : N 9 4 = N 8 3 + N 8 4 + 3 * (N 6 2 + 2 * N 6 3 + N 6 4) := by
  have h := N_tri 6 3
  rw [show (6 : ℕ) + 3 = 9 from rfl, show (3 : ℕ) + 1 = 4 from rfl, show (6 : ℕ) + 2 = 8 from rfl, show (3 : ℕ) - 1 = 2 from rfl] at h
  exact h

theorem N_tri_nine_five : N 9 5 = N 8 4 + N 8 5 + 4 * (N 6 3 + 2 * N 6 4 + N 6 5) := by
  have h := N_tri 6 4
  rw [show (6 : ℕ) + 3 = 9 from rfl, show (4 : ℕ) + 1 = 5 from rfl, show (6 : ℕ) + 2 = 8 from rfl, show (4 : ℕ) - 1 = 3 from rfl] at h
  exact h

theorem N_tri_ten_five : N 10 5 = N 9 4 + N 9 5 + 4 * (N 7 3 + 2 * N 7 4 + N 7 5) := by
  have h := N_tri 7 4
  rw [show (7 : ℕ) + 3 = 10 from rfl, show (4 : ℕ) + 1 = 5 from rfl, show (7 : ℕ) + 2 = 9 from rfl, show (4 : ℕ) - 1 = 3 from rfl] at h
  exact h

theorem N_tri_ten_six : N 10 6 = N 9 5 + N 9 6 + 5 * (N 7 4 + 2 * N 7 5 + N 7 6) := by
  have h := N_tri 7 5
  rw [show (7 : ℕ) + 3 = 10 from rfl, show (5 : ℕ) + 1 = 6 from rfl, show (7 : ℕ) + 2 = 9 from rfl, show (5 : ℕ) - 1 = 4 from rfl] at h
  exact h

theorem N_tri_eleven_six : N 11 6 = N 10 5 + N 10 6 + 5 * (N 8 4 + 2 * N 8 5 + N 8 6) := by
  have h := N_tri 8 5
  rw [show (8 : ℕ) + 3 = 11 from rfl, show (5 : ℕ) + 1 = 6 from rfl, show (8 : ℕ) + 2 = 10 from rfl, show (5 : ℕ) - 1 = 4 from rfl] at h
  exact h

theorem N_tri_eleven_seven : N 11 7 = N 10 6 + N 10 7 + 6 * (N 8 5 + 2 * N 8 6 + N 8 7) := by
  have h := N_tri 8 6
  rw [show (8 : ℕ) + 3 = 11 from rfl, show (6 : ℕ) + 1 = 7 from rfl, show (8 : ℕ) + 2 = 10 from rfl, show (6 : ℕ) - 1 = 5 from rfl] at h
  exact h

theorem N_tri_twelve_seven : N 12 7 = N 11 6 + N 11 7 + 6 * (N 9 5 + 2 * N 9 6 + N 9 7) := by
  have h := N_tri 9 6
  rw [show (9 : ℕ) + 3 = 12 from rfl, show (6 : ℕ) + 1 = 7 from rfl, show (9 : ℕ) + 2 = 11 from rfl, show (6 : ℕ) - 1 = 5 from rfl] at h
  exact h

theorem N_seven_six : N 7 6 = 38 := by
  have h := N_subdiag 7 (by norm_num)
  rw [show (7 : ℕ) - 1 = 6 from rfl] at h
  have h' : ((N 7 6 : ℕ) : ℤ) = ((38 : ℕ) : ℤ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_eight_seven : N 8 7 = 52 := by
  have h := N_subdiag 8 (by norm_num)
  rw [show (8 : ℕ) - 1 = 7 from rfl] at h
  have h' : ((N 8 7 : ℕ) : ℤ) = ((52 : ℕ) : ℤ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_eight_six : N 8 6 = 277 := by
  have h := N_sub_two 2
  rw [show (2 : ℕ) + 6 = 8 from rfl, show (2 : ℕ) + 4 = 6 from rfl] at h
  have h' : ((N 8 6 : ℕ) : ℚ) = ((277 : ℕ) : ℚ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_nine_seven : N 9 7 = 509 := by
  have h := N_sub_two 3
  rw [show (3 : ℕ) + 6 = 9 from rfl, show (3 : ℕ) + 4 = 7 from rfl] at h
  have h' : ((N 9 7 : ℕ) : ℚ) = ((509 : ℕ) : ℚ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_nine_six : N 9 6 = 1446 := by
  have h := N_sub_three 1
  rw [show (1 : ℕ) + 8 = 9 from rfl, show (1 : ℕ) + 5 = 6 from rfl] at h
  have h' : ((N 9 6 : ℕ) : ℚ) = ((1446 : ℕ) : ℚ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_ten_seven : N 10 7 = 3257 := by
  have h := N_sub_three 2
  rw [show (2 : ℕ) + 8 = 10 from rfl, show (2 : ℕ) + 5 = 7 from rfl] at h
  have h' : ((N 10 7 : ℕ) : ℚ) = ((3257 : ℕ) : ℚ) := by
    rw [h]
    norm_num
  exact Nat.cast_injective h'

theorem N_table_aux {a31 a41 a42 a51 a52 a53 a61 a62 a63 a72 a73 a74 a75 a83 a84 a85 a94 a95 a105 a106
      a116 a117 a127 a10 a11 a12 a20 a21 a22 a23 a30 a32 a33 a40 a43 a44 a45 a50 a54 a55 a64 a65 a76 a86
      a87 a96 a97 a107 : ℕ}
    (h31 : a31 = a20 + a21) (h41 : a41 = a30 + a31)
    (h42 : a42 = a31 + a32 + (a10 + 2 * a11 + a12)) (h51 : a51 = a40 + a41)
    (h52 : a52 = a41 + a42 + (a20 + 2 * a21 + a22))
    (h53 : a53 = a42 + a43 + 2 * (a21 + 2 * a22 + a23)) (h61 : a61 = a50 + a51)
    (h62 : a62 = a51 + a52 + (a30 + 2 * a31 + a32))
    (h63 : a63 = a52 + a53 + 2 * (a31 + 2 * a32 + a33))
    (h72 : a72 = a61 + a62 + (a40 + 2 * a41 + a42))
    (h73 : a73 = a62 + a63 + 2 * (a41 + 2 * a42 + a43))
    (h74 : a74 = a63 + a64 + 3 * (a42 + 2 * a43 + a44))
    (h75 : a75 = a64 + a65 + 4 * (a43 + 2 * a44 + a45))
    (h83 : a83 = a72 + a73 + 2 * (a51 + 2 * a52 + a53))
    (h84 : a84 = a73 + a74 + 3 * (a52 + 2 * a53 + a54))
    (h85 : a85 = a74 + a75 + 4 * (a53 + 2 * a54 + a55))
    (h94 : a94 = a83 + a84 + 3 * (a62 + 2 * a63 + a64))
    (h95 : a95 = a84 + a85 + 4 * (a63 + 2 * a64 + a65))
    (h105 : a105 = a94 + a95 + 4 * (a73 + 2 * a74 + a75))
    (h106 : a106 = a95 + a96 + 5 * (a74 + 2 * a75 + a76))
    (h116 : a116 = a105 + a106 + 5 * (a84 + 2 * a85 + a86))
    (h117 : a117 = a106 + a107 + 6 * (a85 + 2 * a86 + a87))
    (h127 : a127 = a116 + a117 + 6 * (a95 + 2 * a96 + a97))
    (v10 : a10 = 0) (v11 : a11 = 1) (v12 : a12 = 0) (v20 : a20 = 0) (v21 : a21 = 1) (v22 : a22 = 2)
    (v23 : a23 = 0) (v30 : a30 = 0) (v32 : a32 = 4) (v33 : a33 = 2) (v40 : a40 = 0) (v43 : a43 = 8)
    (v44 : a44 = 2) (v45 : a45 = 0) (v50 : a50 = 0) (v54 : a54 = 16) (v55 : a55 = 2) (v64 : a64 = 65)
    (v65 : a65 = 26) (v76 : a76 = 38) (v86 : a86 = 277) (v87 : a87 = 52) (v96 : a96 = 1446)
    (v97 : a97 = 509) (v107 : a107 = 3257) :
    a31 = 1 ∧ a41 = 1 ∧ a42 = 7 ∧ a52 = 12 ∧ a53 = 25 ∧ a63 = 59 ∧ a74 = 199 ∧ a85 = 574 ∧ a106 = 6012 ∧
      a127 = 70674 := by
  subst v10 v11 v12 v20 v21 v22 v23 v30 v32 v33 v40 v43 v44 v45 v50 v54 v55 v64 v65 v76 v86 v87 v96 v97
    v107
  subst h31 h41 h42 h51 h52 h53 h61 h62 h63 h72 h73 h74 h75 h83 h84 h85 h94 h95 h105 h106 h116 h117 h127
  norm_num

/-- 由三角递推算出的小值：`N(3,1) = 1`、`N(4,1) = 1`、`N(4,2) = 7`、`N(5,2) = 12`、`N(5,3) = 25`、`N(6,3) = 59`、
`N(7,4) = 199`、`N(8,5) = 574`、`N(10,6) = 6012`、`N(12,7) = 70674`（后两个是报告 B10 的锚点 `D(2d+2, d)`，
`d = 4, 5`）。 -/
theorem N_table : N 3 1 = 1 ∧ N 4 1 = 1 ∧ N 4 2 = 7 ∧ N 5 2 = 12 ∧ N 5 3 = 25 ∧ N 6 3 = 59 ∧ N 7 4 = 199 ∧
    N 8 5 = 574 ∧ N 10 6 = 6012 ∧ N 12 7 = 70674 :=
  N_table_aux (h31 := N_tri_three_one) (h41 := N_tri_four_one) (h42 := N_tri_four_two)
    (h51 := N_tri_five_one) (h52 := N_tri_five_two) (h53 := N_tri_five_three) (h61 := N_tri_six_one)
    (h62 := N_tri_six_two) (h63 := N_tri_six_three) (h72 := N_tri_seven_two) (h73 := N_tri_seven_three)
    (h74 := N_tri_seven_four) (h75 := N_tri_seven_five) (h83 := N_tri_eight_three)
    (h84 := N_tri_eight_four) (h85 := N_tri_eight_five) (h94 := N_tri_nine_four) (h95 := N_tri_nine_five)
    (h105 := N_tri_ten_five) (h106 := N_tri_ten_six) (h116 := N_tri_eleven_six)
    (h117 := N_tri_eleven_seven) (h127 := N_tri_twelve_seven)
    (v10 := N_succ_zero 0) (v11 := N_init.2.1) (v12 := N_eq_zero_of_lt (by norm_num))
    (v20 := N_succ_zero 1) (v21 := N_init.2.2.1) (v22 := N_init.2.2.2)
    (v23 := N_eq_zero_of_lt (by norm_num)) (v30 := N_succ_zero 2) (v32 := N_three_two)
    (v33 := N_diag 3 (by norm_num)) (v40 := N_succ_zero 3) (v43 := N_four_three_five_four.1)
    (v44 := N_diag 4 (by norm_num)) (v45 := N_eq_zero_of_lt (by norm_num)) (v50 := N_succ_zero 4)
    (v54 := N_four_three_five_four.2) (v55 := N_diag 5 (by norm_num)) (v64 := N_six_four)
    (v65 := N_six_five) (v76 := N_seven_six) (v86 := N_eight_six) (v87 := N_eight_seven)
    (v96 := N_nine_six) (v97 := N_nine_seven) (v107 := N_ten_seven)

theorem N_ten_six_twelve_seven : N 10 6 = 6012 ∧ N 12 7 = 70674 := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2⟩ := N_table
  exact ⟨h1, h2⟩

/-- `k ≥ 10` 时 `N(k,k−4) = p_4(k)
= (k⁸−52k⁷+1242k⁶−17280k⁵+151217k⁴−845644k³+2926356k²−5702176k+5014464)/192`（写成 `k = s + 10`）。 -/
theorem N_sub_four (s : ℕ) :
    (N (s + 10) (s + 6) : ℚ) = (((s : ℚ) + 10) ^ 8 - 52 * ((s : ℚ) + 10) ^ 7 + 1242 * ((s : ℚ) + 10) ^ 6
      - 17280 * ((s : ℚ) + 10) ^ 5 + 151217 * ((s : ℚ) + 10) ^ 4 - 845644 * ((s : ℚ) + 10) ^ 3
      + 2926356 * ((s : ℚ) + 10) ^ 2 - 5702176 * ((s : ℚ) + 10) + 5014464) / 192 := by
  induction s with
  | zero =>
    rw [N_ten_six_twelve_seven.1]
    norm_num
  | succ s ih =>
    have h := N_tri (s + 8) (s + 6)
    rw [show s + 6 - 1 = s + 5 by omega] at h
    have hq : (N (s + 8 + 3) (s + 6 + 1) : ℚ)
        = N (s + 8 + 2) (s + 6) + N (s + 8 + 2) (s + 6 + 1)
          + (s + 6 : ℚ) * (N (s + 8) (s + 5) + 2 * N (s + 8) (s + 6) + N (s + 8) (s + 6 + 1)) := by
      exact_mod_cast h
    have hA := N_sub_three (s + 2)
    have hB := N_sub_three s
    have hC := N_sub_two (s + 2)
    have hD := N_subdiag_rat (k := s + 8) (by omega)
    rw [show s + 2 + 8 = s + 8 + 2 by omega, show s + 2 + 5 = s + 6 + 1 by omega] at hA
    rw [show s + 2 + 6 = s + 8 by omega, show s + 2 + 4 = s + 6 by omega] at hC
    rw [show s + 8 - 1 = s + 6 + 1 by omega] at hD
    rw [show s + 1 + 10 = s + 8 + 3 by omega, show s + 1 + 6 = s + 6 + 1 by omega, hq, hA,
      show s + 8 + 2 = s + 10 by omega, ih, hB, hC, hD]
    push_cast
    ring

/-- `k ≥ 12` 时 `N(k,k−5) = p_5(k) = (k¹⁰−85k⁹+3350k⁸−79370k⁷+1241073k⁶−13308173k⁵+98708360k⁴
−498528820k³+1637903536k²−3158022432k+2686170240)/1920`（写成 `k = s + 12`）。 -/
theorem N_sub_five (s : ℕ) :
    (N (s + 12) (s + 7) : ℚ) = (((s : ℚ) + 12) ^ 10 - 85 * ((s : ℚ) + 12) ^ 9 + 3350 * ((s : ℚ) + 12) ^ 8
      - 79370 * ((s : ℚ) + 12) ^ 7 + 1241073 * ((s : ℚ) + 12) ^ 6 - 13308173 * ((s : ℚ) + 12) ^ 5
      + 98708360 * ((s : ℚ) + 12) ^ 4 - 498528820 * ((s : ℚ) + 12) ^ 3 + 1637903536 * ((s : ℚ) + 12) ^ 2
      - 3158022432 * ((s : ℚ) + 12) + 2686170240) / 1920 := by
  induction s with
  | zero =>
    rw [N_ten_six_twelve_seven.2]
    norm_num
  | succ s ih =>
    have h := N_tri (s + 10) (s + 7)
    rw [show s + 7 - 1 = s + 6 by omega] at h
    have hq : (N (s + 10 + 3) (s + 7 + 1) : ℚ)
        = N (s + 10 + 2) (s + 7) + N (s + 10 + 2) (s + 7 + 1)
          + (s + 7 : ℚ) * (N (s + 10) (s + 6) + 2 * N (s + 10) (s + 7) + N (s + 10) (s + 7 + 1)) := by
      exact_mod_cast h
    have hA := N_sub_four (s + 2)
    have hB := N_sub_four s
    have hC := N_sub_three (s + 2)
    have hD := N_sub_two (s + 4)
    rw [show s + 2 + 10 = s + 10 + 2 by omega, show s + 2 + 6 = s + 7 + 1 by omega] at hA
    rw [show s + 2 + 8 = s + 10 by omega, show s + 2 + 5 = s + 7 by omega] at hC
    rw [show s + 4 + 6 = s + 10 by omega, show s + 4 + 4 = s + 7 + 1 by omega] at hD
    rw [show s + 1 + 12 = s + 10 + 3 by omega, show s + 1 + 7 = s + 7 + 1 by omega, hq, hA,
      show s + 10 + 2 = s + 12 by omega, ih, hB, hC, hD]
    push_cast
    ring

/-- 论文第 7 节的例子：`p_2 = (k⁴ − 10k³ + 43k² − 98k + 164)/4`。 -/
theorem ndPoly_two :
    ndPoly 2 = C (1 / 4 : ℚ) * (X ^ 4 - C 10 * X ^ 3 + C 43 * X ^ 2 - C 98 * X + C 164) := by
  symm
  apply eq_ndPoly
  intro k hk
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 6 := ⟨k - 6, by omega⟩
  rw [show s + 6 - 2 = s + 4 by omega, N_sub_two s]
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_pow, eval_X]
  push_cast
  ring

/-- 论文第 7 节的例子：`p_3 = (k⁶ − 27k⁵ + 331k⁴ − 2225k³ + 8560k² − 17392k + 11088)/24`。 -/
theorem ndPoly_three :
    ndPoly 3 = C (1 / 24 : ℚ) * (X ^ 6 - C 27 * X ^ 5 + C 331 * X ^ 4 - C 2225 * X ^ 3 + C 8560 * X ^ 2
      - C 17392 * X + C 11088) := by
  symm
  apply eq_ndPoly
  intro k hk
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 8 := ⟨k - 8, by omega⟩
  rw [show s + 8 - 3 = s + 5 by omega, N_sub_three s]
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_pow, eval_X]
  push_cast
  ring

/-- 论文表 4（`tab:exc`）：门槛以下 `d + 1 ≤ k ≤ 2d + 1`（`d ≤ 3`）的 `D(k,d) = N(k,k−d)` 与 `p_d(k)`；缺陷
`e_d(k) = D(k,d) − p_d(k)` 是两者之差（`−1; 3, 2; −16, −12, −6; 115, 90, 60, 24`）。 -/
theorem table_exc :
    ((N 1 1 : ℚ) = 1 ∧ (ndPoly 0).eval 1 = 2) ∧
    ((N 2 1 : ℚ) = 1 ∧ (ndPoly 1).eval 2 = -2) ∧ ((N 3 2 : ℚ) = 4 ∧ (ndPoly 1).eval 3 = 2) ∧
    ((N 3 1 : ℚ) = 1 ∧ (ndPoly 2).eval 3 = 17) ∧ ((N 4 2 : ℚ) = 7 ∧ (ndPoly 2).eval 4 = 19) ∧
    ((N 5 3 : ℚ) = 25 ∧ (ndPoly 2).eval 5 = 31) ∧
    ((N 4 1 : ℚ) = 1 ∧ (ndPoly 3).eval 4 = -114) ∧ ((N 5 2 : ℚ) = 12 ∧ (ndPoly 3).eval 5 = -78) ∧
    ((N 6 3 : ℚ) = 59 ∧ (ndPoly 3).eval 6 = -1) ∧ ((N 7 4 : ℚ) = 199 ∧ (ndPoly 3).eval 7 = 175) := by
  obtain ⟨h31, h41, h42, h52, h53, h63, h74, -, -, -⟩ := N_table
  have h11 := N_init.2.1
  have h21 := N_init.2.2.1
  have h32 := N_three_two
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  · exact_mod_cast h11
  · rw [ndPoly_zero_one.1, eval_C]
  · exact_mod_cast h21
  · rw [ndPoly_zero_one.2]
    norm_num
  · exact_mod_cast h32
  · rw [ndPoly_zero_one.2]
    norm_num
  · exact_mod_cast h31
  · rw [ndPoly_two]
    norm_num
  · exact_mod_cast h42
  · rw [ndPoly_two]
    norm_num
  · exact_mod_cast h53
  · rw [ndPoly_two]
    norm_num
  · exact_mod_cast h41
  · rw [ndPoly_three]
    norm_num
  · exact_mod_cast h52
  · rw [ndPoly_three]
    norm_num
  · exact_mod_cast h63
  · rw [ndPoly_three]
    norm_num
  · exact_mod_cast h74
  · rw [ndPoly_three]
    norm_num

/-! ## 5. `m → ∞` 的形状与 `C(m+1, ·)` 基下的前三项 -/

/-- `μ_k = (k² − 2k − 1)/2`。 -/
def muK (k : ℕ) : ℚ := ((k : ℚ) ^ 2 - 2 * k - 1) / 2

/-- `u_k − (2/k!)(X + μ_k)^k` 的次数 `≤ k − 2`（`k ≥ 4`）。 -/
theorem upoly_sub_shape_natDegree (k : ℕ) (hk : 4 ≤ k) :
    (upoly k - C (2 / (k ! : ℚ)) * (X + C (muK k)) ^ k).natDegree ≤ k - 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hpow : ((X + C (muK k)) ^ k).natDegree ≤ k := by
    refine natDegree_pow_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
  rw [coeff_sub, coeff_C_mul, coeff_X_add_C_pow]
  rcases (show n = k ∨ n = k - 1 ∨ k < n by omega) with rfl | rfl | hlt
  · rw [T5_2_top n (by omega), Nat.sub_self, pow_zero, Nat.choose_self]
    push_cast
    ring
  · rw [T5_2_sub k hk, show k - (k - 1) = 1 by omega, pow_one, Nat.choose_symm (by omega), Nat.choose_one_right]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega, Nat.factorial_succ]
    have hf : (j ! : ℚ) ≠ 0 := by positivity
    unfold muK
    push_cast
    field_simp
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_upoly]; exact hlt), Nat.choose_eq_zero_of_lt hlt,
      Nat.cast_zero, mul_zero, mul_zero, sub_zero]

/-- **T5.2**（推论 3.3）：`k ≥ 4` 时 `U_k(m) = (2/k!)(m + μ_k)^k·(1 + O(m^{−2}))`，`μ_k = (k² − 2k − 1)/2`。 -/
theorem T5_2_asymp (k : ℕ) (hk : 4 ≤ k) :
    ∃ Cst : ℚ, ∀ m : ℕ, 1 ≤ m →
      |(U k m : ℚ) / (2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k) - 1| ≤ Cst / (m : ℚ) ^ 2 := by
  obtain ⟨D, hD⟩ : ∃ D : ℚ[X], D = upoly k - C (2 / (k ! : ℚ)) * (X + C (muK k)) ^ k := ⟨_, rfl⟩
  have hDdeg : D.natDegree ≤ k - 2 := by rw [hD]; exact upoly_sub_shape_natDegree k hk
  obtain ⟨S, hS⟩ : ∃ S : ℚ, S = ∑ i ∈ range (k - 1), |D.coeff i| := ⟨_, rfl⟩
  refine ⟨S * (k ! : ℚ) / 2, fun m hm => ?_⟩
  have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℚ) < m := by linarith
  have hmu : 0 ≤ muK k := by
    unfold muK
    have : (4 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hA0 : 0 < 2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k := by positivity
  have hAm : 2 / (k ! : ℚ) * (m : ℚ) ^ k ≤ 2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k := by
    gcongr
    linarith
  -- `U_k(m) − A = D(m)`
  have hUD : (U k m : ℚ) - 2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k = D.eval (m : ℚ) := by
    rw [hD, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_C, upoly_eval_nat]
  -- `|D(m)| ≤ S·m^{k−2}`
  have hDb : |D.eval (m : ℚ)| ≤ S * (m : ℚ) ^ (k - 2) := by
    rw [eval_eq_sum_range' (show D.natDegree < k - 1 by omega), hS, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [abs_mul, abs_pow, abs_of_pos hm0]
    have hi' : i ≤ k - 2 := by have := mem_range.1 hi; omega
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 hi') (abs_nonneg _)
  have hkey : |(U k m : ℚ) / (2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k) - 1|
      = |D.eval (m : ℚ)| / (2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k) := by
    rw [← hUD, div_sub_one hA0.ne', abs_div, abs_of_pos hA0]
  rw [hkey, div_le_iff₀ hA0]
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact sum_nonneg fun i _ => abs_nonneg _
  have hmk : (m : ℚ) ^ k = (m : ℚ) ^ (k - 2) * (m : ℚ) ^ 2 := by
    rw [← pow_add, show k - 2 + 2 = k by omega]
  have hf : (0 : ℚ) < (k ! : ℚ) := by positivity
  calc |D.eval (m : ℚ)| ≤ S * (m : ℚ) ^ (k - 2) := hDb
    _ = S * (k ! : ℚ) / 2 / (m : ℚ) ^ 2 * (2 / (k ! : ℚ) * (m : ℚ) ^ k) := by
        have hb : (m : ℚ) ^ 2 ≠ 0 := by positivity
        rw [hmk, show S * (k ! : ℚ) / 2 / (m : ℚ) ^ 2 * (2 / (k ! : ℚ) * ((m : ℚ) ^ (k - 2) * (m : ℚ) ^ 2))
            = S * (m : ℚ) ^ (k - 2) * ((k ! : ℚ) / (k ! : ℚ)) * ((m : ℚ) ^ 2 / (m : ℚ) ^ 2) by ring_nf,
          div_self hf.ne', div_self hb, mul_one, mul_one]
    _ ≤ S * (k ! : ℚ) / 2 / (m : ℚ) ^ 2 * (2 / (k ! : ℚ) * ((m : ℚ) + muK k) ^ k) := by
        gcongr

/-- **T5.2**：`k ≥ 6` 时在 `C(m+1, ·)` 基下 `u_k = 2·C(m+1,k) + (k²−k−4)·C(m+1,k−1) + p_2(k)·C(m+1,k−2) + …`。 -/
theorem upoly_top_three (k : ℕ) (hk : 6 ≤ k) :
    upoly k = C 2 * binomPoly k + C ((k : ℚ) ^ 2 - k - 4) * binomPoly (k - 1)
      + C (((k : ℚ) ^ 4 - 10 * k ^ 3 + 43 * k ^ 2 - 98 * k + 164) / 4) * binomPoly (k - 2)
      + ∑ q ∈ range (k - 2), C (N k q : ℚ) * binomPoly q := by
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 6 := ⟨k - 6, by omega⟩
  rw [upoly, show s + 6 + 1 = (s + 4) + 1 + 1 + 1 by omega, sum_range_succ, sum_range_succ, sum_range_succ,
    show s + 6 - 2 = s + 4 by omega, show s + 6 - 1 = s + 4 + 1 by omega, show s + 6 = s + 4 + 1 + 1 by omega,
    N_diag (s + 4 + 1 + 1) (by omega)]
  have hA := N_subdiag_rat (k := s + 4 + 1 + 1) (by omega)
  rw [show s + 4 + 1 + 1 - 1 = s + 4 + 1 by omega] at hA
  have hB := N_sub_two s
  rw [show s + 6 = s + 4 + 1 + 1 by omega] at hB
  rw [hA, hB]
  push_cast
  ring_nf

end

end A207123
