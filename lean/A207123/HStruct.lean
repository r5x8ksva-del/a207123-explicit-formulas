import A207123.HNum
import A207123.Poly

/-!
# 报告 T5.3(1)–(5)：`h_k(t)` 的结构

`h_k` 是 `HNum.lean` 的 `hpoly k`（`Σ_m U_k(m)t^m = h_k(t)/(1−t)^{k+1}`），`u_k` 是 `Poly.lean` 的 `upoly k`
（T1.2 中唯一的插值多项式，`u_k(−j)` 就是报告的 `U_k(−j)`）。

* **T5.3(1)**：`hpoly_eval_zero_eq_one`（`h_k(0) = 1`）、`hpoly_eval_one_two`（`h_k(1) = 2`，`k ≥ 2`）、
  `hpoly_coeff_one`（`[t¹]h_k = R_k − k − 1`）与 `hpoly_coeff_one_pos`、`hpoly_coeff_one_eq_zero`、母函数
  `hpoly_coeff_one_gf`；反演式 `hpoly_coeff_eq_sum`；`t = 1` 处的各阶导数 `iterate_derivative_hpoly_eval_one`
  （`k ≥ 1`；`k = 0` 的反例 `iterate_derivative_hpoly_eval_one_k_zero`）与 `hpoly_derivative_eval_one`；
  N 行多项式 `nrowPoly`（`k ≥ 1`）与 `nrowPoly_eval`、`nrowPoly_eq`。
* **T5.3(2)**：`Gneg j`（`G_{−j}(x) = Σ_k u_k(−j)x^k`）：`Gneg_one`、`Gneg_succ`、`Gneg_isPoly`（`3j−3` 次多项式）
  与最高三项 `coeff_gnegPoly_top`、`coeff_gnegPoly_top_one`、`coeff_gnegPoly_top_two`；`upoly_eval_neg_eq_zero`
  （`1 ≤ j ≤ ⌊(k+2)/3⌋` 时 `u_k(−j) = 0`）、`upoly_eval_neg_ne_zero`、`prod_dvd_upoly`、`upoly_three_mul_eval`。
  「`U_k` 没有其他负整数零点」是有限范围的计算核对，没有形式化。
* **T5.3(3)**：互反引理 `upoly_eval_neg_recip`；`natDegree_hpoly`（`deg h_k = ⌊2k/3⌋`）与首项系数
  `leadingCoeff_hpoly_three_mul`、`leadingCoeff_hpoly_three_mul_add_one`、`leadingCoeff_hpoly_three_mul_add_two`、
  符号 `leadingCoeff_hpoly_sign`。第二首项的闭式没有形式化。
* **T5.3(4)**：`sum_neg_one_pow_N`（`Σ_q (−1)^q N(k,q) = u_k(−2)`）、`sum_neg_one_pow_N_eq_zero`（`k ≥ 4`）、
  `sum_neg_one_pow_N_small`（`k = 1, 2, 3`）；`rootMultiplicity_nrowPoly`、`rootMultiplicity_nrowPoly_ceil`
  （`n_k` 在 `z = −1` 处的根重数恰为 `⌈k/3⌉ − 1`）。第一个等号 `μ(0̂,1̂) = Σ_q (−1)^q N(k,q)`（Philip Hall 定理）
  没有形式化。
* **T5.3(5)**：`hpoly_pos_of_mem_Icc`、`hpoly_ne_zero_of_mem_Icc`（`h_k` 在 `[0,1]` 上没有根；另有
  `hpoly_aeval_eq_tsum`）。「每个固定位置的系数最终为正」与「`Σ_k h_k(t)z^k` 的收敛半径为 0」没有形式化。
-/

namespace A207123

open Polynomial Finset
open scoped Nat

/-! ## 0. 预备：`(1 − t)^n` 的系数、`h_k` 的次数上界 -/

section Prelim

/-- 辅助引理（T5.3）：`[t^i](1 − t)^n = (−1)^i·C(n,i)`。 -/
theorem coeff_one_sub_X_pow_hs (n i : ℕ) :
    ((1 - X : ℚ[X]) ^ n).coeff i = (-1) ^ i * (n.choose i : ℚ) := by
  have h : (1 - X : ℚ[X]) ^ n = C ((-1 : ℚ) ^ n) * (X + C (-1)) ^ n := by
    rw [map_pow, ← mul_pow]
    congr 1
    rw [map_neg, map_one]
    ring
  rw [h, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt i n with hi | hi
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left, pow_add]
    have h2 : ((-1 : ℚ) ^ d) * (-1) ^ d = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination ((-1 : ℚ) ^ i * ((i + d).choose i : ℚ)) * h2
  · rw [Nat.choose_eq_zero_of_lt hi]; simp

/-- 辅助引理（T5.3）：`k ≥ 1` 时 `deg h_k ≤ k − 1`（由 `h_k = Σ_q N(k,q)·t^{q−1}(1−t)^{k−q}`）。 -/
theorem natDegree_hpoly_le_pred {k : ℕ} (hk : 1 ≤ k) : (hpoly k).natDegree ≤ k - 1 := by
  rw [hpoly_of_one_le hk]
  refine natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
  rw [Finset.mem_Icc] at hq
  refine natDegree_mul_le.trans ?_
  have h1 : (C (N k q : ℚ) * X ^ (q - 1)).natDegree ≤ q - 1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  have h2 : ((1 - X : ℚ[X]) ^ (k - q)).natDegree ≤ k - q := by
    refine natDegree_pow_le.trans ?_
    have : (1 - X : ℚ[X]).natDegree ≤ 1 := by compute_degree
    calc (k - q) * (1 - X : ℚ[X]).natDegree ≤ (k - q) * 1 := Nat.mul_le_mul_left _ this
      _ = k - q := mul_one _
  omega

/-- 辅助引理（T5.3）：`i ≥ 1` 且 `i ≥ k` 时 `[t^i]h_k = 0`（`k ≥ 1` 时 `deg h_k ≤ k − 1`，`h_0 = 1`）。 -/
theorem coeff_hpoly_eq_zero {k i : ℕ} (h1 : 1 ≤ i) (h2 : k ≤ i) : (hpoly k).coeff i = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hpoly_zero, coeff_one]; simp; omega
  · exact coeff_eq_zero_of_natDegree_lt ((natDegree_hpoly_le_pred hk).trans_lt (by omega))

end Prelim

/-! ## 1. T5.3(1)：基本事实 -/

section Basic

/-- 辅助引理（T5.3(1)）：`h_{k,i} = Σ_{r≤i} (−1)^r·C(k+1, r)·U_k(i−r)`（`hpoly_spec` 两边取 `t^i` 系数）。 -/
theorem hpoly_coeff_eq_sum_r (k i : ℕ) :
    (hpoly k).coeff i
      = ∑ r ∈ range (i + 1), (-1) ^ r * ((k + 1).choose r : ℚ) * (U k (i - r) : ℚ) := by
  rw [← Polynomial.coeff_coe, ← hpoly_spec, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a ((1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1))
        * PowerSeries.coeff b (fser k))]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e : ((1 - PowerSeries.X : PowerSeries ℚ) ^ (k + 1))
      = (↑((1 - X : ℚ[X]) ^ (k + 1)) : PowerSeries ℚ) := by
    simp only [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
  rw [e, Polynomial.coeff_coe, coeff_one_sub_X_pow_hs, fser, PowerSeries.coeff_mk]

/-- **T5.3(1)**：`h_{k,i} = Σ_{j=0}^{i} (−1)^{i−j}·C(k+1, i−j)·U_k(j)`（对一切 `k, i ≥ 0`）。 -/
theorem hpoly_coeff_eq_sum (k i : ℕ) :
    (hpoly k).coeff i
      = ∑ j ∈ range (i + 1), (-1) ^ (i - j) * ((k + 1).choose (i - j) : ℚ) * (U k j : ℚ) := by
  rw [hpoly_coeff_eq_sum_r, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show i + 1 - 1 - j = i - j by omega, show i - (i - j) = j by omega]

/-- **T5.3(1)**：`h_k(0) = 1`（对一切 `k ≥ 0`）。 -/
theorem hpoly_eval_zero_eq_one (k : ℕ) : (hpoly k).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, hpoly_coeff_eq_sum]
  simp [U_zero_right]

/-- **T5.3(1)**：`h_k(1) = 2`（`k ≥ 2`；即 HNum 中的 `hpoly_eval_one_eq_two`，这里只是重新引用）。 -/
theorem hpoly_eval_one_two {k : ℕ} (hk : 2 ≤ k) : (hpoly k).eval 1 = 2 :=
  hpoly_eval_one_eq_two hk

/-- **T5.3(1)**：`[t¹]h_k = R_k − k − 1`，`R_k := U_k(1)`（对一切 `k ≥ 0`）。 -/
theorem hpoly_coeff_one (k : ℕ) : (hpoly k).coeff 1 = (U k 1 : ℚ) - k - 1 := by
  rw [hpoly_coeff_eq_sum]
  simp [Finset.sum_range_succ, U_zero_right]
  ring

/-- 辅助引理（T5.3(1)）：`R_{k+3} = R_{k+2} + R_k + 1`（引理 1 取 `m = 0`）。 -/
theorem U_one_rec (k : ℕ) : U (k + 3) 1 = U (k + 2) 1 + U k 1 + 1 := by
  have h := lemma1 k 0
  rw [show (0 : ℕ) + 1 = 1 from rfl, U_zero_right, one_mul] at h
  rw [h]
  ring

/-- 辅助引理（T5.3(1)）：`k ≥ 2` 时 `R_k ≥ k + 2`。 -/
theorem U_one_ge {k : ℕ} (hk : 2 ≤ k) : k + 2 ≤ U k 1 := by
  induction k, hk using Nat.le_induction with
  | base => rw [U_of_le_two (le_refl 2)]; norm_num
  | succ n hn ih =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    rw [show j + 2 + 1 = j + 3 by omega, U_one_rec]
    omega

/-- **T5.3(1)**：`k ≥ 2` 时 `[t¹]h_k = R_k − k − 1 > 0`。 -/
theorem hpoly_coeff_one_pos {k : ℕ} (hk : 2 ≤ k) : 0 < (hpoly k).coeff 1 := by
  rw [hpoly_coeff_one]
  have h : ((k + 2 : ℕ) : ℚ) ≤ (U k 1 : ℚ) := by exact_mod_cast U_one_ge hk
  push_cast at h
  linarith

/-- **T5.3(1)**：`k = 0, 1` 时 `[t¹]h_k = 0`。 -/
theorem hpoly_coeff_one_eq_zero {k : ℕ} (hk : k ≤ 1) : (hpoly k).coeff 1 = 0 := by
  rw [hpoly_coeff_one, U_of_le_two (by omega)]
  interval_cases k <;> norm_num

/-- **T5.3(1)**（[t¹]h_k 的母函数）：在 `ℚ[[x]]` 中
`(1−x)²(1−x−x³)·Σ_k [t¹]h_k·x^k = x²(1−x+x²)`，
即 `Σ_k [t¹]h_k·x^k = x²(1−x+x²)/((1−x)²(1−x−x³))`。证明：`Σ_k R_k x^k = G_1 = W_1/P_1`（`P_mul_G`），
`Σ_k (k+1)x^k = 1/(1−x)²`。 -/
theorem hpoly_coeff_one_gf :
    (1 - PowerSeries.X) ^ 2 * (1 - PowerSeries.X - PowerSeries.X ^ 3)
        * PowerSeries.mk (fun k => (hpoly k).coeff 1)
      = (PowerSeries.X ^ 2 * (1 - PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℚ) := by
  have hmk : PowerSeries.mk (fun k => (hpoly k).coeff 1)
      = Gser 1 - PowerSeries.mk (fun n => (((1 + n).choose 1 : ℕ) : ℚ)) := by
    ext k
    rw [PowerSeries.coeff_mk, map_sub, coeff_Gser, PowerSeries.coeff_mk, hpoly_coeff_one,
      Nat.choose_one_right]
    push_cast
    ring
  have hP : (↑(Ppoly ℚ 1) : PowerSeries ℚ)
      = (1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 3) := by
    rw [Ppoly_succ, Ppoly_zero, Polynomial.coe_mul, coe_bpoly, coe_bpoly]
    simp
  have hW : (↑(Wpoly ℚ 1) : PowerSeries ℚ) = 1 + PowerSeries.X ^ 2 * (1 - PowerSeries.X) := by
    rw [Wpoly_succ, Wpoly_zero, Ppoly_zero]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_one, Polynomial.coe_C, coe_bpoly]
    simp
  have hG := P_mul_G 1
  rw [hP, hW] at hG
  have hinv := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℚ 1
  rw [hmk]
  linear_combination (1 - PowerSeries.X) * hG - (1 - PowerSeries.X - PowerSeries.X ^ 3) * hinv

/-- 辅助引理（T5.3）：若 `f` 在 `q ≥ a` 时为 0、在 `q ≥ b` 时也为 0，则 `Σ_{q<a} f = Σ_{q<b} f`。 -/
theorem sum_range_eq_of_zero_hs {f : ℕ → ℚ} {a b : ℕ} (ha : ∀ q, a ≤ q → f q = 0)
    (hb : ∀ q, b ≤ q → f q = 0) : ∑ q ∈ range a, f q = ∑ q ∈ range b, f q := by
  rcases le_total a b with hab | hab
  · rw [← sum_range_add_sum_Ico f hab, sum_eq_zero (fun q hq => ha q (mem_Ico.mp hq).1), add_zero]
  · rw [← sum_range_add_sum_Ico f hab, sum_eq_zero (fun q hq => hb q (mem_Ico.mp hq).1), add_zero]

/-- 辅助引理（T5.3(1)）：`h_k = Σ_{e=0}^{k−1} N(k,k−e)·t^{k−1−e}·(1−t)^e`（`k ≥ 1`；把 `hpoly_of_one_le`
的下标换成 `e = k − q`）。 -/
theorem hpoly_eq_sum_e {k : ℕ} (hk : 1 ≤ k) :
    hpoly k = ∑ e ∈ range k, C (N k (k - e) : ℚ) * X ^ (k - 1 - e) * (1 - X) ^ e := by
  rw [hpoly_of_one_le hk]
  refine Finset.sum_nbij' (fun q => k - q) (fun e => k - e) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_range]
    omega
  · intro e he
    rw [Finset.mem_range] at he
    rw [Finset.mem_Icc]
    omega
  · intro q hq
    rw [Finset.mem_Icc] at hq
    show k - (k - q) = q
    omega
  · intro e he
    rw [Finset.mem_range] at he
    show k - (k - e) = e
    omega
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [show k - (k - q) = q by omega, show k - 1 - (k - q) = q - 1 by omega]

/-- 辅助引理（T5.3(1)）：`h_k(1 + s) = Σ_{e=0}^{k−1} N(k,k−e)·(1+s)^{k−1−e}·(−s)^e`（`k ≥ 1`），
即报告 §4.7 的 `h_k(1−s) = Σ_e N(k,k−e)·s^e·(1−s)^{k−1−e}` 换 `s ↦ −s`。 -/
theorem taylor_one_hpoly {k : ℕ} (hk : 1 ≤ k) :
    taylor 1 (hpoly k)
      = ∑ e ∈ range k, C (N k (k - e) : ℚ) * (X + 1) ^ (k - 1 - e) * (-X) ^ e := by
  rw [hpoly_eq_sum_e hk, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [taylor_apply]
  simp only [mul_comp, C_comp, pow_comp, sub_comp, one_comp, X_comp, map_one]
  ring

/-- 辅助引理（T5.3(1)）：`p^{(d)}(r) = d!·[s^d]p(r + s)`（Hasse 导数与 Taylor 展开）。 -/
theorem iterate_derivative_eval_hs (p : ℚ[X]) (d : ℕ) (r : ℚ) :
    (derivative^[d] p).eval r = (d ! : ℚ) * (taylor r p).coeff d := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul, nsmul_eq_mul]

/-- **T5.3(1)**：`h_k^{(d)}(1) = d!·Σ_{e=0}^{d} (−1)^e·C(k−1−e, d−e)·N(k,k−e)`（`k ≥ 1`，一切 `d ≥ 0`；
`e ≥ k` 的项因 `N(k,0) = 0` 为零，所以 ℕ 减法的截断不影响）。 -/
theorem iterate_derivative_hpoly_eval_one {k : ℕ} (hk : 1 ≤ k) (d : ℕ) :
    (derivative^[d] (hpoly k)).eval 1
      = (d ! : ℚ) * ∑ e ∈ range (d + 1),
          (-1) ^ e * ((k - 1 - e).choose (d - e) : ℚ) * (N k (k - e) : ℚ) := by
  rw [iterate_derivative_eval_hs, taylor_one_hpoly hk, finsetSum_coeff]
  congr 1
  set F : ℕ → ℚ := fun e => (-1) ^ e * ((k - 1 - e).choose (d - e) : ℚ) * (N k (k - e) : ℚ)
    with hF
  have hterm : ∀ e, (C (N k (k - e) : ℚ) * (X + 1) ^ (k - 1 - e) * (-X) ^ e).coeff d
      = if e ≤ d then F e else 0 := by
    intro e
    have h1 : C (N k (k - e) : ℚ) * (X + 1) ^ (k - 1 - e) * (-X) ^ e
        = C ((N k (k - e) : ℚ) * (-1) ^ e) * (X ^ e * (X + 1) ^ (k - 1 - e)) := by
      rw [map_mul, map_pow, map_neg, map_one, neg_pow (X : ℚ[X])]
      ring
    rw [h1, coeff_C_mul, coeff_X_pow_mul', coeff_X_add_one_pow ℚ]
    simp only [hF]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun e _ => hterm e]
  have hF0 : ∀ e, k ≤ e → F e = 0 := by
    intro e he
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [hF]
    rw [show k' + 1 - e = 0 by omega, N_succ_zero]
    simp
  rw [sum_range_eq_of_zero_hs (b := d + 1)
    (fun e he => by simp only [hF0 e he, ite_self])
    (fun e he => by simp [show ¬ e ≤ d by omega])]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.mem_range] at he
  simp [show e ≤ d by omega]

/-- **T5.3(1)**（例）：`h_k'(1) = −(k² − 3k − 2)`（`k ≥ 4`）。 -/
theorem hpoly_derivative_eval_one {k : ℕ} (hk : 4 ≤ k) :
    (derivative (hpoly k)).eval 1 = -((k : ℚ) ^ 2 - 3 * k - 2) := by
  have h := iterate_derivative_hpoly_eval_one (by omega : 1 ≤ k) 1
  rw [Function.iterate_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]
  have hs : (N k (k - 1) : ℚ) = (k : ℚ) ^ 2 - k - 4 := by
    have := N_subdiag k hk
    exact_mod_cast this
  have hd : (N k (k - 0) : ℚ) = 2 := by
    rw [Nat.sub_zero, N_diag k (by omega)]; norm_num
  rw [hd, hs, show k - 1 - 0 = k - 1 by omega, show 1 - 0 = 1 by omega, show 1 - 1 = 0 by omega,
    Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_sub (by omega : 1 ≤ k)]
  norm_num
  ring

/-- **T5.3(1)**（导数公式的适用范围是 `k ≥ 1`；反例）：`k = 0` 时 `h_0 = 1`，`h_0'(1) = 0`，而公式右边
`1!·Σ_{e≤1} (−1)^e·C(0−1−e, 1−e)·N(0, 0−e)`（按 ℕ 减法截断理解）等于
`C(0,1)·N(0,0) − C(0,0)·N(0,0) = −1`。（若按广义二项式 `C(−1,1) = −1`、`N(0,−1) = 0` 理解，右边同样是 `−1`。）
c5a §4.1 的 `h_k = Σ_q N(k,q)t^{q−1}(1−t)^{k−q}` 只对 `k ≥ 1` 成立，§4.7 的公式由它推出，所以按 notes 的写法
取 `k ≥ 1`（`iterate_derivative_hpoly_eval_one`）。 -/
theorem iterate_derivative_hpoly_eval_one_k_zero :
    (derivative^[1] (hpoly 0)).eval 1 = 0 ∧
    ((1 ! : ℚ) * ∑ e ∈ range (1 + 1),
      (-1) ^ e * ((0 - 1 - e).choose (1 - e) : ℚ) * (N 0 (0 - e) : ℚ)) = -1 := by
  constructor
  · rw [Function.iterate_one, hpoly_zero, derivative_one, eval_zero]
  · -- `rw [show (0 : ℕ) - 1 - 0 = 0 from rfl]` 会把目标里所有定义上等于 0 的自然数减法（`0 − 0`、`0 − 1`、
    -- `1 − 1`、`0 − 1 − 1`）一并改写成 0（数字字面量的减法按定义相等匹配），之后不能再逐个改写它们
    -- （2026-10-07 实测：原先接着写 `show (0 : ℕ) - 0 = 0 from rfl`，报「找不到这个式子」）。
    rw [Finset.sum_range_succ, Finset.sum_range_one,
      show (0 : ℕ) - 1 - 0 = 0 from rfl, show (1 : ℕ) - 0 = 1 from rfl, N_init.1,
      show Nat.choose 0 1 = 0 from rfl, show Nat.choose 0 0 = 1 from rfl]
    norm_num

/-- 报告 T5.3(1) 的 N 行多项式 `n_k(z) := Σ_{q=1}^{k} N(k,q)·z^{q−1}`（`k ≥ 1` 时 `N(k,0) = 0`，
与对一切 `q` 求和相同；`k = 0` 时报告的式子给出 `z^{−1}`，不是多项式，本文件只对 `k ≥ 1` 陈述）。 -/
noncomputable def nrowPoly (k : ℕ) : ℚ[X] := ∑ q ∈ Icc 1 k, C (N k q : ℚ) * X ^ (q - 1)

/-- **T5.3(1)**：`n_k(z) = (1+z)^{k−1}·h_k(z/(1+z))`（`k ≥ 1`，`z ≠ −1`）。 -/
theorem nrowPoly_eval {k : ℕ} (hk : 1 ≤ k) (z : ℚ) (hz : 1 + z ≠ 0) :
    (nrowPoly k).eval z = (1 + z) ^ (k - 1) * (hpoly k).eval (z / (1 + z)) := by
  rw [nrowPoly, hpoly_of_one_le hk, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_Icc] at hq
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  have h1 : 1 - z / (1 + z) = 1 / (1 + z) := by field_simp; ring
  have hp : (1 + z) ^ (k - 1) = (1 + z) ^ (q - 1) * (1 + z) ^ (k - q) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, hp, div_pow, div_pow, one_pow]
  field_simp

/-- **T5.3(1)**（无除法的多项式恒等式）：`k ≥ 1` 时
`n_k(z) = Σ_{i=0}^{k−1} h_{k,i}·z^i·(1+z)^{k−1−i}`，右边就是 `(1+z)^{k−1}·h_k(z/(1+z))` 展开后的多项式
（`deg h_k ≤ k − 1`）。 -/
theorem nrowPoly_eq {k : ℕ} (hk : 1 ≤ k) :
    nrowPoly k = ∑ i ∈ range k, C ((hpoly k).coeff i) * X ^ i * (1 + X) ^ (k - 1 - i) := by
  apply poly_eq_of_eval_nat
  intro m
  have hz : (1 + (m : ℚ)) ≠ 0 := by positivity
  have hdeg : (hpoly k).natDegree < k := by
    have := natDegree_hpoly_le_pred hk; omega
  rw [nrowPoly_eval hk _ hz, eval_eq_sum_range' hdeg, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
  have hp : (1 + (m : ℚ)) ^ (k - 1) = (1 + m) ^ i * (1 + m) ^ (k - 1 - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hp, div_pow]
  field_simp

end Basic

/-! ## 2. T5.3(2)：负整数处的值 -/

section Neg

/-- 报告 T5.3(2) 的 `G_{−j}(x) := Σ_k u_k(−j)·x^k ∈ ℚ[[x]]`，`u_k` 是 `U_k` 的插值多项式（`upoly k`，
T1.2），`u_k(−j)` 是多项式在 `−j` 处的值。 -/
noncomputable def Gneg (j : ℕ) : PowerSeries ℚ := PowerSeries.mk fun k => (upoly k).eval (-(j : ℚ))

/-- 辅助引理（T5.3(2)）：`u_0 = 1`。 -/
theorem upoly_zero_eq_one : upoly 0 = 1 := by
  rw [upoly_le_two (by norm_num), pow_zero]

/-- 辅助引理（T5.3(2)）：`u_1 = y + 1`。 -/
theorem upoly_one_eq : upoly 1 = X + 1 := by
  rw [upoly_le_two (by norm_num), pow_one]

/-- 辅助引理（T5.3(2)）：`u_2 = (y + 1)²`。 -/
theorem upoly_two_eq : upoly 2 = (X + 1) ^ 2 := upoly_le_two (by norm_num)

/-- **T5.3(2)**：`G_{−1} = 1`（`u_0 = 1`，`k ≥ 1` 时 `u_k(−1) = 0`）。 -/
theorem Gneg_one : Gneg 1 = 1 := by
  ext k
  rw [Gneg, PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.cast_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [upoly_zero_eq_one]
  · simp [upoly_eval_neg_one k hk, show k ≠ 0 by omega]

/-- 辅助引理（T5.3(2)）：`[x^k]((1 − x + c x³)·F + c x²)
= [x^k]F − [k ≥ 1]·[x^{k−1}]F + c·[k ≥ 3]·[x^{k−3}]F + [k = 2]·c`（`F ∈ ℚ[[x]]` 任意）。 -/
theorem coeff_negRec (c : ℚ) (F : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 3) * F
        + PowerSeries.C c * PowerSeries.X ^ 2)
      = PowerSeries.coeff k F - (if 1 ≤ k then PowerSeries.coeff (k - 1) F else 0)
        + c * (if 3 ≤ k then PowerSeries.coeff (k - 3) F else 0) + (if k = 2 then c else 0) := by
  have e : (1 - PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 3) * F
        + PowerSeries.C c * PowerSeries.X ^ 2
      = F - PowerSeries.X ^ 1 * F + PowerSeries.C c * (PowerSeries.X ^ 3 * F)
        + PowerSeries.C c * PowerSeries.X ^ 2 := by ring
  rw [e, map_add, map_add, map_sub, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']

/-- 辅助引理（T5.3(2)）：`coeff_negRec` 在 `k = 0` 处。 -/
theorem coeff_negRec_zero (c : ℚ) (F : PowerSeries ℚ) :
    PowerSeries.coeff 0 ((1 - PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 3) * F
        + PowerSeries.C c * PowerSeries.X ^ 2) = PowerSeries.coeff 0 F := by
  rw [coeff_negRec]; simp

/-- 辅助引理（T5.3(2)）：`coeff_negRec` 在 `k = 1` 处。 -/
theorem coeff_negRec_one (c : ℚ) (F : PowerSeries ℚ) :
    PowerSeries.coeff 1 ((1 - PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 3) * F
        + PowerSeries.C c * PowerSeries.X ^ 2) = PowerSeries.coeff 1 F - PowerSeries.coeff 0 F := by
  rw [coeff_negRec]; simp

/-- 辅助引理（T5.3(2)）：`coeff_negRec` 在 `k = 2` 处。 -/
theorem coeff_negRec_two (c : ℚ) (F : PowerSeries ℚ) :
    PowerSeries.coeff 2 ((1 - PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 3) * F
        + PowerSeries.C c * PowerSeries.X ^ 2)
      = PowerSeries.coeff 2 F - PowerSeries.coeff 1 F + c := by
  rw [coeff_negRec]; simp

/-- 辅助引理（T5.3(2)）：`coeff_negRec` 在 `k + 3` 处。 -/
theorem coeff_negRec_add_three (c : ℚ) (F : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff (k + 3) ((1 - PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 3) * F
        + PowerSeries.C c * PowerSeries.X ^ 2)
      = PowerSeries.coeff (k + 3) F - PowerSeries.coeff (k + 2) F + c * PowerSeries.coeff k F := by
  rw [coeff_negRec]
  have h1 : (1 : ℕ) ≤ k + 3 := by omega
  have h3 : (3 : ℕ) ≤ k + 3 := by omega
  have h2 : k + 3 ≠ 2 := by omega
  simp only [h1, h3, h2, ↓reduceIte, show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel,
    add_zero]

/-- **T5.3(2)**：`G_{−j−1} = (1 − x + j x³)·G_{−j} + j x²`。对一切 `j ≥ 0` 成立（`j = 0` 时
`G_0 = Σ_k U_k(0)x^k`）。证明：T1.2 的差分恒等式 `u_k(y) − u_k(y−1) = u_{k−1}(y) + y·u_{k−3}(y)`
（`upoly_sub_comp_succ_three`，`k ≤ 2` 用 `u_k = (y+1)^k`）在 `y = −j` 处取值。 -/
theorem Gneg_succ (j : ℕ) :
    Gneg (j + 1) = (1 - PowerSeries.X + PowerSeries.C (j : ℚ) * PowerSeries.X ^ 3) * Gneg j
      + PowerSeries.C (j : ℚ) * PowerSeries.X ^ 2 := by
  have hy : (-(((j + 1 : ℕ) : ℚ))) = -(j : ℚ) - 1 := by push_cast; ring
  ext k
  match k with
  | 0 =>
    rw [coeff_negRec_zero]
    simp only [Gneg, PowerSeries.coeff_mk, upoly_zero_eq_one, eval_one]
  | 1 =>
    rw [coeff_negRec_one]
    simp only [Gneg, PowerSeries.coeff_mk, hy, upoly_one_eq, upoly_zero_eq_one, eval_add, eval_X,
      eval_one]
    ring
  | 2 =>
    rw [coeff_negRec_two]
    simp only [Gneg, PowerSeries.coeff_mk, hy, upoly_two_eq, upoly_one_eq, eval_add, eval_X,
      eval_one, eval_pow]
    ring
  | k + 3 =>
    rw [coeff_negRec_add_three]
    simp only [Gneg, PowerSeries.coeff_mk, hy]
    have h := congrArg (eval (-(j : ℚ))) (upoly_sub_comp_succ_three k)
    simp only [eval_sub, eval_add, eval_mul, eval_X, eval_comp, eval_one] at h
    linear_combination (-1 : ℚ) * h

/-- `G_{−(n+1)}` 作为多项式：`gnegPoly 0 = 1`，
`gnegPoly (n+1) = (1 − x + (n+1)x³)·gnegPoly n + (n+1)x²`（报告 T5.3(2) 的递推，下标平移一位：
`gnegPoly n` 对应 `G_{−(n+1)}`，见 `coe_gnegPoly`）。 -/
noncomputable def gnegPoly : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => (1 - X + C ((n : ℚ) + 1) * X ^ 3) * gnegPoly n + C ((n : ℚ) + 1) * X ^ 2

/-- 辅助引理（T5.3(2)）：`gnegPoly` 看成幂级数就是 `G_{−(n+1)}`。 -/
theorem coe_gnegPoly (n : ℕ) : (↑(gnegPoly n) : PowerSeries ℚ) = Gneg (n + 1) := by
  induction n with
  | zero => rw [Gneg_one]; simp [gnegPoly]
  | succ n ih =>
    rw [Gneg_succ (n + 1), ← ih, gnegPoly]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_pow, Nat.cast_add, Nat.cast_one]

/-- 辅助引理（T5.3(2)）：`G_{−2} = 1 − x + x² + x³`。 -/
theorem gnegPoly_one : gnegPoly 1 = 1 - X + X ^ 2 + X ^ 3 := by
  simp only [gnegPoly, Nat.cast_zero, zero_add, map_one, one_mul, mul_one]
  ring

/-- 辅助引理（T5.3(2)）：`[x^{r+3}]G_{−(n+2)} = [x^{r+3}]G_{−(n+1)} − [x^{r+2}]G_{−(n+1)}
+ (n+1)·[x^r]G_{−(n+1)}`。 -/
theorem coeff_gnegPoly_succ_add_three (n r : ℕ) :
    (gnegPoly (n + 1)).coeff (r + 3) = (gnegPoly n).coeff (r + 3) - (gnegPoly n).coeff (r + 2)
      + ((n : ℚ) + 1) * (gnegPoly n).coeff r := by
  have e : gnegPoly (n + 1) = gnegPoly n - X * gnegPoly n
      + C ((n : ℚ) + 1) * (X ^ 3 * gnegPoly n) + C ((n : ℚ) + 1) * X ^ 2 := by
    rw [gnegPoly]; ring
  rw [e, coeff_add, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul, coeff_X_pow,
    show r + 3 = (r + 2) + 1 by ring, coeff_X_mul]
  simp

/-- 辅助引理（T5.3(2)）：`r > 3n` 时 `[x^r]G_{−(n+1)} = 0`。 -/
theorem coeff_gnegPoly_of_lt : ∀ (n r : ℕ), 3 * n < r → (gnegPoly n).coeff r = 0
  | 0, r, h => by
    rw [gnegPoly, coeff_one]
    simp [show r ≠ 0 by omega]
  | n + 1, r, h => by
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 3 := ⟨r - 3, by omega⟩
    rw [coeff_gnegPoly_succ_add_three, coeff_gnegPoly_of_lt n (r + 3) (by omega),
      coeff_gnegPoly_of_lt n (r + 2) (by omega), coeff_gnegPoly_of_lt n r (by omega)]
    ring

/-- 辅助引理（T5.3(2)）：`deg G_{−(n+1)} ≤ 3n`。 -/
theorem natDegree_gnegPoly_le (n : ℕ) : (gnegPoly n).natDegree ≤ 3 * n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun r hr => coeff_gnegPoly_of_lt n r hr

/-- **T5.3(2)**（c5a 定理 4.3 的最高项）：`[x^{3n}]G_{−(n+1)} = n!`，即 `g_{j,3j−3} = (j−1)!`。 -/
theorem coeff_gnegPoly_top (n : ℕ) : (gnegPoly n).coeff (3 * n) = (n ! : ℚ) := by
  induction n with
  | zero => simp [gnegPoly]
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 3 by ring, coeff_gnegPoly_succ_add_three, ih,
      coeff_gnegPoly_of_lt n (3 * n + 3) (by omega), coeff_gnegPoly_of_lt n (3 * n + 2) (by omega),
      Nat.factorial_succ]
    push_cast
    ring

/-- **T5.3(2)**：`deg G_{−(n+1)} = 3n`，即 `deg G_{−j} = 3j − 3`（`j ≥ 1`）。 -/
theorem natDegree_gnegPoly (n : ℕ) : (gnegPoly n).natDegree = 3 * n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_gnegPoly_le n)
    (by rw [coeff_gnegPoly_top]; exact_mod_cast Nat.factorial_ne_zero n)

/-- **T5.3(2)**（c5a 定理 4.3 的次高项）：`[x^{3n+2}]G_{−(n+2)} = (n+1)!`，即 `j ≥ 2` 时
`g_{j,3j−4} = (j−1)!`。 -/
theorem coeff_gnegPoly_top_one (n : ℕ) :
    (gnegPoly (n + 1)).coeff (3 * n + 2) = ((n + 1)! : ℚ) := by
  induction n with
  | zero =>
    rw [gnegPoly_one]
    simp [coeff_X, coeff_one, coeff_X_pow]
  | succ n ih =>
    rw [show 3 * (n + 1) + 2 = (3 * n + 2) + 3 by ring, coeff_gnegPoly_succ_add_three, ih,
      coeff_gnegPoly_of_lt (n + 1) (3 * n + 2 + 3) (by omega),
      coeff_gnegPoly_of_lt (n + 1) (3 * n + 2 + 2) (by omega), Nat.factorial_succ (n + 1)]
    push_cast
    ring

/-- 辅助引理（T5.3(2)(3)）：`c(n+2, 2) = (n+1)·c(n+1, 2) + n!`（Mathlib 的无符号第一类 Stirling 数
`Nat.stirlingFirst` 的递推）。 -/
theorem stirlingFirst_two_succ_hs (n : ℕ) :
    Nat.stirlingFirst (n + 2) 2 = (n + 1) * Nat.stirlingFirst (n + 1) 2 + n ! := by
  have h : Nat.stirlingFirst (n + 2) 2
      = (n + 1) * Nat.stirlingFirst (n + 1) 2 + Nat.stirlingFirst (n + 1) 1 :=
    Nat.stirlingFirst_succ_succ (n + 1) 1
  rw [h, Nat.stirlingFirst_one_right]

/-- 辅助引理（T5.3(2)(3)）：`c(n+2, 2) > 0`。 -/
theorem stirlingFirst_two_pos_hs (n : ℕ) : 0 < Nat.stirlingFirst (n + 2) 2 := by
  rw [stirlingFirst_two_succ_hs]
  have := Nat.factorial_pos n
  omega

/-- **T5.3(2)**（c5a 定理 4.3 的第三高项）：`[x^{3n+1}]G_{−(n+2)} = −c(n+2, 2)`，即 `j ≥ 2` 时
`g_{j,3j−5} = −c(j,2)`（`c` 为无符号第一类 Stirling 数 `Nat.stirlingFirst`）。 -/
theorem coeff_gnegPoly_top_two (n : ℕ) :
    (gnegPoly (n + 1)).coeff (3 * n + 1) = -(Nat.stirlingFirst (n + 2) 2 : ℚ) := by
  induction n with
  | zero =>
    rw [gnegPoly_one]
    simp [coeff_X, coeff_one, coeff_X_pow, Nat.stirlingFirst_self]
  | succ n ih =>
    rw [show 3 * (n + 1) + 1 = (3 * n + 1) + 3 by ring, coeff_gnegPoly_succ_add_three, ih,
      coeff_gnegPoly_of_lt (n + 1) (3 * n + 1 + 3) (by omega),
      show 3 * n + 1 + 2 = 3 * (n + 1) by ring, coeff_gnegPoly_top,
      stirlingFirst_two_succ_hs (n + 1)]
    rw [show n + 1 + 1 = n + 2 by ring]
    push_cast
    ring

/-- 辅助引理（T5.3(2)）：`u_k(−(n+1)) = [x^k]G_{−(n+1)}`。 -/
theorem upoly_eval_neg_succ (k n : ℕ) :
    (upoly k).eval (-((n : ℚ) + 1)) = (gnegPoly n).coeff k := by
  have h := congrArg (PowerSeries.coeff k) (coe_gnegPoly n)
  rw [Polynomial.coeff_coe, Gneg, PowerSeries.coeff_mk] at h
  rw [h, Nat.cast_add, Nat.cast_one]

/-- **T5.3(2)**：对 `j ≥ 1`，`G_{−j}` 是多项式，次数为 `3j − 3`。 -/
theorem Gneg_isPoly {j : ℕ} (hj : 1 ≤ j) :
    ∃ p : ℚ[X], (↑p : PowerSeries ℚ) = Gneg j ∧ p.natDegree = 3 * j - 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  exact ⟨gnegPoly n, coe_gnegPoly n, by rw [natDegree_gnegPoly]; omega⟩

/-- **T5.3(2)**：`1 ≤ j ≤ s_k := ⌊(k+2)/3⌋` 时 `u_k(−j) = 0`。 -/
theorem upoly_eval_neg_eq_zero {k j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ (k + 2) / 3) :
    (upoly k).eval (-(j : ℚ)) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  rw [Nat.cast_add, Nat.cast_one, upoly_eval_neg_succ]
  exact coeff_gnegPoly_of_lt n k (by omega)

/-- **T5.3(2)**（推论）：`u_{3j}(−j−1) = j!`。 -/
theorem upoly_three_mul_eval (j : ℕ) : (upoly (3 * j)).eval (-((j : ℚ) + 1)) = (j ! : ℚ) := by
  rw [upoly_eval_neg_succ, coeff_gnegPoly_top]

/-- 辅助引理（T5.3(2)(3)）：`u_{3a+1}(−a−2) = −c(a+2, 2)`。 -/
theorem upoly_three_mul_add_one_eval (a : ℕ) :
    (upoly (3 * a + 1)).eval (-((a : ℚ) + 2)) = -(Nat.stirlingFirst (a + 2) 2 : ℚ) := by
  have h := upoly_eval_neg_succ (3 * a + 1) (a + 1)
  rw [coeff_gnegPoly_top_two] at h
  rw [← h]
  congr 2
  push_cast
  ring

/-- 辅助引理（T5.3(2)(3)）：`u_{3a+2}(−a−2) = (a+1)!`。 -/
theorem upoly_three_mul_add_two_eval (a : ℕ) :
    (upoly (3 * a + 2)).eval (-((a : ℚ) + 2)) = ((a + 1)! : ℚ) := by
  have h := upoly_eval_neg_succ (3 * a + 2) (a + 1)
  rw [coeff_gnegPoly_top_one] at h
  rw [← h]
  congr 2
  push_cast
  ring

/-- **T5.3(2)**：`u_k(−s_k−1) ≠ 0`，`s_k = ⌊(k+2)/3⌋`（对一切 `k ≥ 0`）。 -/
theorem upoly_eval_neg_ne_zero (k : ℕ) :
    (upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 1)) ≠ 0 := by
  obtain ⟨a, ha | ha | ha⟩ : ∃ a, k = 3 * a ∨ k = 3 * a + 1 ∨ k = 3 * a + 2 := ⟨k / 3, by omega⟩
  · subst ha
    rw [show (3 * a + 2) / 3 = a by omega, upoly_three_mul_eval]
    exact_mod_cast Nat.factorial_ne_zero a
  · subst ha
    rw [show (3 * a + 1 + 2) / 3 = a + 1 by omega,
      show -(((a + 1 : ℕ) : ℚ) + 1) = -((a : ℚ) + 2) by push_cast; ring,
      upoly_three_mul_add_one_eval]
    have := stirlingFirst_two_pos_hs a
    have h : (0 : ℚ) < Nat.stirlingFirst (a + 2) 2 := by exact_mod_cast this
    linarith
  · subst ha
    rw [show (3 * a + 2 + 2) / 3 = a + 1 by omega,
      show -(((a + 1 : ℕ) : ℚ) + 1) = -((a : ℚ) + 2) by push_cast; ring,
      upoly_three_mul_add_two_eval]
    exact_mod_cast Nat.factorial_ne_zero (a + 1)

/-- **T5.3(2)**（推论）：`(y+1)(y+2)⋯(y+s_k)` 在 `ℚ[y]` 中整除 `u_k(y)`。 -/
theorem prod_dvd_upoly (k : ℕ) : (∏ i ∈ Icc 1 ((k + 2) / 3), (X + C (i : ℚ))) ∣ upoly k := by
  have e : ∀ i : ℕ, (X + C (i : ℚ)) = X - C (-(i : ℚ)) := fun i => by
    rw [map_neg, sub_neg_eq_add]
  simp_rw [e]
  have hinj : Function.Injective (fun i : ℕ => -(i : ℚ)) := by
    intro a b h
    simpa using h
  refine Finset.prod_dvd_of_coprime
    (fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C hinj hab) fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  rw [dvd_iff_isRoot]
  exact upoly_eval_neg_eq_zero hi.1 hi.2

end Neg

/-! ## 3. T5.3(3)：互反引理，`deg h_k = ⌊2k/3⌋` 与首项系数 -/

section Recip

/-- 辅助引理（T5.3(3)）：`desc_k(−1) = (−1)·(−2)⋯(−k) = (−1)^k·k!`。 -/
theorem descPochhammer_eval_neg_one_hs (k : ℕ) :
    (descPochhammer ℚ k).eval (-1) = (-1) ^ k * (k ! : ℚ) := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℚ) (-1) k
  rw [neg_neg, ascPochhammer_eval_one] at h
  have h2 : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination -((-1 : ℚ) ^ k) * h - (descPochhammer ℚ k).eval (-1) * h2

/-- 互反引理中的多项式 `B_{k,i}(y) = C(y − i + k, k) = (y−i+k)(y−i+k−1)⋯(y−i+1)/k!`
（`descPochhammer ℚ k = y(y−1)⋯(y−k+1)` 复合 `y ↦ y + k − i`，再乘 `1/k!`）。 -/
noncomputable def recipPoly (k i : ℕ) : ℚ[X] :=
  C ((k ! : ℚ)⁻¹) * (descPochhammer ℚ k).comp (X + C ((k : ℚ) - i))

/-- 辅助引理（T5.3(3)）：`B_{k,i}(y) = desc_k(y + k − i)/k!`。 -/
theorem recipPoly_eval (k i : ℕ) (y : ℚ) :
    (recipPoly k i).eval y = (k ! : ℚ)⁻¹ * (descPochhammer ℚ k).eval (y + k - i) := by
  rw [recipPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C, add_sub_assoc]

/-- 辅助引理（T5.3(3)）：`i ≤ m` 时 `B_{k,i}(m) = C(m − i + k, k)`。 -/
theorem recipPoly_eval_nat_of_le {k i m : ℕ} (h : i ≤ m) :
    (recipPoly k i).eval (m : ℚ) = ((m - i + k).choose k : ℚ) := by
  have hc : ((m - i + k : ℕ) : ℚ) = (m : ℚ) + k - i := by
    rw [Nat.cast_add, Nat.cast_sub h]; ring
  rw [recipPoly_eval, Nat.cast_choose_eq_descPochhammer_div ℚ (m - i + k) k, hc]
  ring

/-- 辅助引理（T5.3(3)）：`m < i ≤ k` 时 `B_{k,i}(m) = 0`。 -/
theorem recipPoly_eval_nat_of_lt {k i m : ℕ} (h1 : m < i) (h2 : i ≤ k) :
    (recipPoly k i).eval (m : ℚ) = 0 := by
  have hc : (m : ℚ) + k - i = ((m + k - i : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  rw [recipPoly_eval, hc, descPochhammer_eval_coe_nat_of_lt (by omega), mul_zero]

/-- 辅助引理（T5.3(3)）：`j ≥ 1`、`i + j ≤ k` 时 `B_{k,i}(−j) = 0`。 -/
theorem recipPoly_eval_neg_of_le {k i j : ℕ} (hj : 1 ≤ j) (h : i + j ≤ k) :
    (recipPoly k i).eval (-(j : ℚ)) = 0 := by
  have hc : -(j : ℚ) + k - i = ((k - i - j : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  rw [recipPoly_eval, hc, descPochhammer_eval_coe_nat_of_lt (by omega), mul_zero]

/-- 辅助引理（T5.3(3)）：`i + j = k + 1` 时 `B_{k,i}(−j) = (−1)^k`。 -/
theorem recipPoly_eval_neg_of_eq {k i j : ℕ} (h : i + j = k + 1) :
    (recipPoly k i).eval (-(j : ℚ)) = (-1) ^ k := by
  have hc : -(j : ℚ) + k - i = -1 := by
    have : (i : ℚ) + j = k + 1 := by exact_mod_cast h
    linarith
  have hk : (k ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [recipPoly_eval, hc, descPochhammer_eval_neg_one_hs, mul_comm ((-1 : ℚ) ^ k), ← mul_assoc,
    inv_mul_cancel₀ hk, one_mul]

/-- 辅助引理（T5.3(3)）：`U_k(m) = Σ_{i=0}^{m} h_{k,i}·C(m − i + k, k)`（由
`Σ_m U_k(m)t^m = h_k(t)/(1−t)^{k+1}` 与 `1/(1−t)^{k+1} = Σ_n C(n+k,k)t^n`）。 -/
theorem U_eq_sum_hcoeff (k m : ℕ) :
    (U k m : ℚ) = ∑ i ∈ range (m + 1), (hpoly k).coeff i * ((m - i + k).choose k : ℚ) := by
  have hs := hpoly_spec k
  have hm := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℚ k
  have hf : fser k = ↑(hpoly k) * PowerSeries.mk (fun n => ((k + n).choose k : ℚ)) := by
    linear_combination (PowerSeries.mk (fun n => ((k + n).choose k : ℚ))) * hs - fser k * hm
  have h := congrArg (PowerSeries.coeff m) hf
  rw [fser, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (↑(hpoly k) : PowerSeries ℚ)
        * PowerSeries.coeff b (PowerSeries.mk fun n => ((k + n).choose k : ℚ)))] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_coe, PowerSeries.coeff_mk, add_comm k]

/-- 辅助引理（T5.3(3)(5)）：`U_k(m) = Σ_{i=0}^{k} h_{k,i}·[i ≤ m]·C(m − i + k, k)`（求和范围与 `m` 无关）。 -/
theorem U_eq_sum_hcoeff_ite (k m : ℕ) :
    (U k m : ℚ) = ∑ i ∈ range (k + 1),
      (hpoly k).coeff i * (if i ≤ m then ((m - i + k).choose k : ℚ) else 0) := by
  rw [U_eq_sum_hcoeff]
  have h2 : ∑ i ∈ range (m + 1), (hpoly k).coeff i * ((m - i + k).choose k : ℚ)
      = ∑ i ∈ range (m + 1),
          (hpoly k).coeff i * (if i ≤ m then ((m - i + k).choose k : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [show i ≤ m by omega]
  rw [h2]
  apply sum_range_eq_of_zero_hs
  · intro i hi
    simp [show ¬ i ≤ m by omega]
  · intro i hi
    rw [coeff_hpoly_eq_zero (by omega) (by omega), zero_mul]

/-- 辅助引理（T5.3(3)，互反引理的多项式形式，c5a 引理 4.2 的证明第一步）：
`u_k(y) = Σ_{i=0}^{k} h_{k,i}·C(y − i + k, k)`（`ℚ[y]` 中的恒等式）。 -/
theorem upoly_eq_sum_recip (k : ℕ) :
    upoly k = ∑ i ∈ range (k + 1), C ((hpoly k).coeff i) * recipPoly k i := by
  refine (eq_upoly_of_eval fun m => ?_).symm
  rw [eval_finsetSum, U_eq_sum_hcoeff_ite]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [eval_mul, eval_C]
  split_ifs with him
  · rw [recipPoly_eval_nat_of_le him]
  · rw [recipPoly_eval_nat_of_lt (by omega) (by omega)]

/-- 辅助引理（T5.3(3)，互反引理在 `−j` 处）：若 `1 ≤ j ≤ k+1`，且 `i > k+1−j` 时 `h_{k,i} = 0`，
则 `u_k(−j) = (−1)^k·h_{k,k+1−j}`。 -/
theorem upoly_eval_neg_eq_hcoeff {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k + 1)
    (hvan : ∀ i, k + 1 - j < i → (hpoly k).coeff i = 0) :
    (upoly k).eval (-(j : ℚ)) = (-1) ^ k * (hpoly k).coeff (k + 1 - j) := by
  rw [upoly_eq_sum_recip, eval_finsetSum, Finset.sum_eq_single (k + 1 - j)]
  · rw [eval_mul, eval_C, recipPoly_eval_neg_of_eq (by omega), mul_comm]
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rw [eval_mul, eval_C]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [recipPoly_eval_neg_of_le hj (by omega), mul_zero]
    · rw [hvan i hgt, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- 辅助引理（T5.3(3)）：`i + j > k` 时 `B_{k,i}(−j) = (−1)^k·C(i+j−1, k)`（`desc_k(−n) = (−1)^k·asc_k(n)`，
`n = i + j − k ≥ 1`）。 -/
theorem recipPoly_eval_neg_of_gt {k i j : ℕ} (h : k < i + j) :
    (recipPoly k i).eval (-(j : ℚ)) = (-1) ^ k * ((i + j - 1).choose k : ℚ) := by
  have hc : -(j : ℚ) + k - i = -((i + j - k : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]; ring
  have hasc := ascPochhammer_eval_neg_eq_descPochhammer (R := ℚ) (-((i + j - k : ℕ) : ℚ)) k
  rw [neg_neg, ascPochhammer_nat_eq_natCast_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose',
    show i + j - k + k - 1 = i + j - 1 by omega, Nat.cast_mul] at hasc
  have h2 : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have hd : (descPochhammer ℚ k).eval (-((i + j - k : ℕ) : ℚ))
      = (-1) ^ k * ((k ! : ℚ) * ((i + j - 1).choose k : ℚ)) := by
    linear_combination -((-1 : ℚ) ^ k) * hasc
      - (descPochhammer ℚ k).eval (-((i + j - k : ℕ) : ℚ)) * h2
  have hkf : (k ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [recipPoly_eval, hc, hd, mul_left_comm ((-1 : ℚ) ^ k), ← mul_assoc, inv_mul_cancel₀ hkf,
    one_mul]

/-- **T5.3(3)**（c5a 引理 4.2，互反引理，`f = u_k`、`d = k`、`h = h_k` 的情形）：对 `j ≥ 1`，
`u_k(−j) = (−1)^k·Σ_{i = k−j+1}^{k} h_{k,i}·C(i+j−1, k)`（这里写成对 `0 ≤ i ≤ k` 中满足 `i + j > k`
的项求和；`i > deg h_k` 的项为 0）。 -/
theorem upoly_eval_neg_recip (k j : ℕ) (hj : 1 ≤ j) :
    (upoly k).eval (-(j : ℚ)) = (-1) ^ k * ∑ i ∈ range (k + 1),
      (if k < i + j then (hpoly k).coeff i * ((i + j - 1).choose k : ℚ) else 0) := by
  rw [upoly_eq_sum_recip, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]
  split_ifs with h
  · rw [recipPoly_eval_neg_of_gt h]; ring
  · rw [recipPoly_eval_neg_of_le hj (by omega), mul_zero, mul_zero]

/-- 辅助引理（T5.3(3)）：对 `j ≤ s_k`，`i > k − j` 时 `h_{k,i} = 0`（对 `j` 归纳，每一步用
`u_k(−j) = 0`（T5.3(2)）与互反引理）。 -/
theorem hpoly_coeff_vanish (k : ℕ) :
    ∀ j, j ≤ (k + 2) / 3 → ∀ i, k - j < i → (hpoly k).coeff i = 0 := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    exact coeff_hpoly_eq_zero (by omega) (by omega)
  | succ j ih =>
    intro hj i hi
    rcases Nat.lt_or_ge (k - j) i with h | h
    · exact ih (by omega) i h
    · have hi' : i = k - j := by omega
      subst hi'
      have h1 := upoly_eval_neg_eq_hcoeff (k := k) (j := j + 1) (by omega) (by omega)
        (fun i hi => ih (by omega) i (by omega))
      rw [upoly_eval_neg_eq_zero (by omega) hj, show k + 1 - (j + 1) = k - j by omega] at h1
      rcases mul_eq_zero.mp h1.symm with h2 | h2
      · exact absurd h2 (pow_ne_zero _ (by norm_num))
      · exact h2

/-- 辅助引理（T5.3(3)）：`h_{k,k−s_k} = (−1)^k·u_k(−s_k−1)`。 -/
theorem hpoly_coeff_top (k : ℕ) :
    (hpoly k).coeff (k - (k + 2) / 3)
      = (-1) ^ k * (upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 1)) := by
  have h := upoly_eval_neg_eq_hcoeff (k := k) (j := (k + 2) / 3 + 1) (by omega) (by omega)
    (fun i hi => hpoly_coeff_vanish k ((k + 2) / 3) le_rfl i (by omega))
  rw [show k + 1 - ((k + 2) / 3 + 1) = k - (k + 2) / 3 by omega] at h
  rw [show -((((k + 2) / 3 : ℕ) : ℚ) + 1) = -((((k + 2) / 3 + 1 : ℕ) : ℚ)) by push_cast; ring, h,
    ← mul_assoc, ← mul_pow]
  norm_num

/-- **T5.3(3)**：`deg h_k = ⌊2k/3⌋`（对一切 `k ≥ 0`；ℕ 的除法即向下取整）。证明：互反引理 +
T5.3(2)：`h_{k,i} = 0`（`i > k − s_k`），`h_{k,k−s_k} = (−1)^k·u_k(−s_k−1) ≠ 0`，而 `k − s_k = ⌊2k/3⌋`。 -/
theorem natDegree_hpoly (k : ℕ) : (hpoly k).natDegree = 2 * k / 3 := by
  rw [show 2 * k / 3 = k - (k + 2) / 3 by omega]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    exact hpoly_coeff_vanish k _ le_rfl i hi
  · rw [hpoly_coeff_top]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (upoly_eval_neg_ne_zero k)

/-- 辅助引理（T5.3(3)）：`lc(h_k) = (−1)^k·u_k(−s_k−1)`（c5a 引理 4.2 的 `f(−(d−g+1)) = (−1)^d h_g`）。 -/
theorem leadingCoeff_hpoly_eq (k : ℕ) :
    (hpoly k).leadingCoeff = (-1) ^ k * (upoly k).eval (-((((k + 2) / 3 : ℕ) : ℚ) + 1)) := by
  rw [leadingCoeff, natDegree_hpoly, show 2 * k / 3 = k - (k + 2) / 3 by omega, hpoly_coeff_top]

/-- **T5.3(3)**：`k = 3a` 时 `h_k` 的首项系数为 `(−1)^a·a!`。 -/
theorem leadingCoeff_hpoly_three_mul (a : ℕ) :
    (hpoly (3 * a)).leadingCoeff = (-1) ^ a * (a ! : ℚ) := by
  rw [leadingCoeff_hpoly_eq, show (3 * a + 2) / 3 = a by omega, upoly_three_mul_eval]
  have h3 : ((-1 : ℚ)) ^ (3 * a) = (-1) ^ a := by
    rw [pow_mul]; norm_num
  rw [h3]

/-- **T5.3(3)**：`k = 3a+1` 时 `h_k` 的首项系数为 `(−1)^a·c(a+2, 2)`（`c` 为无符号第一类 Stirling 数，
Mathlib 的 `Nat.stirlingFirst`）。 -/
theorem leadingCoeff_hpoly_three_mul_add_one (a : ℕ) :
    (hpoly (3 * a + 1)).leadingCoeff = (-1) ^ a * (Nat.stirlingFirst (a + 2) 2 : ℚ) := by
  rw [leadingCoeff_hpoly_eq, show (3 * a + 1 + 2) / 3 = a + 1 by omega,
    show -(((a + 1 : ℕ) : ℚ) + 1) = -((a : ℚ) + 2) by push_cast; ring,
    upoly_three_mul_add_one_eval]
  have h3 : ((-1 : ℚ)) ^ (3 * a + 1) = -(-1) ^ a := by
    rw [pow_succ, pow_mul]; norm_num
  rw [h3]
  ring

/-- **T5.3(3)**：`k = 3a+2` 时 `h_k` 的首项系数为 `(−1)^a·(a+1)!`。 -/
theorem leadingCoeff_hpoly_three_mul_add_two (a : ℕ) :
    (hpoly (3 * a + 2)).leadingCoeff = (-1) ^ a * ((a + 1)! : ℚ) := by
  rw [leadingCoeff_hpoly_eq, show (3 * a + 2 + 2) / 3 = a + 1 by omega,
    show -(((a + 1 : ℕ) : ℚ) + 1) = -((a : ℚ) + 2) by push_cast; ring,
    upoly_three_mul_add_two_eval]
  have h3 : ((-1 : ℚ)) ^ (3 * a + 2) = (-1) ^ a := by
    rw [pow_add, pow_mul]; norm_num
  rw [h3]

/-- **T5.3(3)**：`h_k` 首项系数的符号为 `(−1)^{⌊k/3⌋}`，即 `(−1)^{⌊k/3⌋}·lc(h_k) > 0`。 -/
theorem leadingCoeff_hpoly_sign (k : ℕ) : 0 < (-1) ^ (k / 3) * (hpoly k).leadingCoeff := by
  have h2 : ∀ a : ℕ, ((-1 : ℚ) ^ a) * (-1) ^ a = 1 := fun a => by
    rw [← mul_pow]; norm_num
  obtain ⟨a, ha | ha | ha⟩ : ∃ a, k = 3 * a ∨ k = 3 * a + 1 ∨ k = 3 * a + 2 := ⟨k / 3, by omega⟩
  · subst ha
    rw [leadingCoeff_hpoly_three_mul, show 3 * a / 3 = a by omega, ← mul_assoc, h2, one_mul]
    exact_mod_cast Nat.factorial_pos a
  · subst ha
    rw [leadingCoeff_hpoly_three_mul_add_one, show (3 * a + 1) / 3 = a by omega, ← mul_assoc, h2,
      one_mul]
    exact_mod_cast stirlingFirst_two_pos_hs a
  · subst ha
    rw [leadingCoeff_hpoly_three_mul_add_two, show (3 * a + 2) / 3 = a by omega, ← mul_assoc, h2,
      one_mul]
    exact_mod_cast Nat.factorial_pos (a + 1)

end Recip

/-! ## 4. T5.3(4)：`Σ_q (−1)^q N(k,q) = u_k(−2)` 与 `n_k` 在 `−1` 处的重根 -/

section Mobius

/-- 辅助引理（T5.3(4)）：`C(y+1, q)` 在 `y = −2` 处取值 `C(−1, q) = (−1)^q`。 -/
theorem binomPoly_eval_neg_two (q : ℕ) : (binomPoly q).eval (-2) = (-1) ^ q := by
  have hq : (q ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one,
    show (-2 : ℚ) + 1 = -1 by norm_num, descPochhammer_eval_neg_one_hs, mul_comm ((-1 : ℚ) ^ q),
    ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- **T5.3(4)**：`Σ_q (−1)^q·N(k,q) = u_k(−2)`（对一切 `k ≥ 0`；由二项式基 `u_k(y) = Σ_q N(k,q)·C(y+1,q)`
与 `C(−1,q) = (−1)^q`）。 -/
theorem sum_neg_one_pow_N (k : ℕ) :
    ∑ q ∈ range (k + 1), (-1 : ℚ) ^ q * (N k q : ℚ) = (upoly k).eval (-2) := by
  rw [upoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, binomPoly_eval_neg_two, mul_comm]

/-- **T5.3(4)**：`k ≥ 4` 时 `Σ_q (−1)^q·N(k,q) = u_k(−2) = 0`。 -/
theorem sum_neg_one_pow_N_eq_zero {k : ℕ} (hk : 4 ≤ k) :
    ∑ q ∈ range (k + 1), (-1 : ℚ) ^ q * (N k q : ℚ) = 0 := by
  rw [sum_neg_one_pow_N]
  have h := upoly_eval_neg_eq_zero (k := k) (j := 2) (by norm_num) (by omega)
  simpa using h

/-- **T5.3(4)**：`k = 1, 2, 3` 时 `Σ_q (−1)^q·N(k,q) = u_k(−2)` 分别为 `−1, 1, 1`。 -/
theorem sum_neg_one_pow_N_small :
    ∑ q ∈ range (1 + 1), (-1 : ℚ) ^ q * (N 1 q : ℚ) = -1 ∧
    ∑ q ∈ range (2 + 1), (-1 : ℚ) ^ q * (N 2 q : ℚ) = 1 ∧
    ∑ q ∈ range (3 + 1), (-1 : ℚ) ^ q * (N 3 q : ℚ) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_neg_one_pow_N, upoly_one_eq]; norm_num
  · rw [sum_neg_one_pow_N, upoly_two_eq]; norm_num
  · rw [sum_neg_one_pow_N, show (-2 : ℚ) = -((1 : ℕ) + 1) by norm_num, upoly_eval_neg_succ,
      gnegPoly_one]
    simp [coeff_X, coeff_one, coeff_X_pow]

/-- **T5.3(4)**：`k ≥ 1` 时 `n_k(z) = Σ_q N(k,q)·z^{q−1}` 以 `z = −1` 为根，重数恰为 `s_k − 1`，
`s_k = ⌊(k+2)/3⌋ = ⌈k/3⌉`（`natCeil_div_three`），即报告的 `⌈k/3⌉ − 1`。证明：由 `nrowPoly_eq`，
`n_k = (1+z)^{s_k−1}·R(z)`，`R(z) = Σ_{i≤g} h_{k,i} z^i (1+z)^{g−i}`（`g = deg h_k = k − s_k`），
`R(−1) = (−1)^g·h_{k,g} ≠ 0`。 -/
theorem rootMultiplicity_nrowPoly {k : ℕ} (hk : 1 ≤ k) :
    (nrowPoly k).rootMultiplicity (-1) = (k + 2) / 3 - 1 := by
  set s := (k + 2) / 3 with hs
  set g := k - s with hg
  set R : ℚ[X] := ∑ i ∈ range (g + 1), C ((hpoly k).coeff i) * X ^ i * (1 + X) ^ (g - i) with hR
  have hfac : nrowPoly k = (X - C (-1)) ^ (s - 1) * R := by
    rw [nrowPoly_eq hk, hR, Finset.mul_sum, map_neg, map_one, sub_neg_eq_add, add_comm X 1]
    symm
    rw [Finset.sum_subset (s₁ := range (g + 1)) (s₂ := range k)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases hig : i ≤ g
      · have hp : (1 + X : ℚ[X]) ^ (k - 1 - i) = (1 + X) ^ (s - 1) * (1 + X) ^ (g - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hp]; ring
      · rw [hpoly_coeff_vanish k s le_rfl i (by omega)]; simp
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intro i hi hni
      rw [Finset.mem_range] at hi hni
      rw [hpoly_coeff_vanish k s le_rfl i (by omega)]; simp
  have hR1 : R.eval (-1) = (-1) ^ g * (hpoly k).coeff g := by
    rw [hR, eval_finsetSum, Finset.sum_eq_single g]
    · simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.sub_self, pow_zero, mul_one]
      ring
    · intro i hi hne
      rw [Finset.mem_range] at hi
      simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
      rw [show (1 : ℚ) + -1 = 0 by norm_num, zero_pow (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hcg : (hpoly k).coeff g ≠ 0 := by
    rw [hg, hs, hpoly_coeff_top]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (upoly_eval_neg_ne_zero k)
  have hRne : R.eval (-1) ≠ 0 := by
    rw [hR1]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcg
  have hR0 : R ≠ 0 := fun h => hRne (by rw [h, eval_zero])
  rw [hfac, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) hR0),
    rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero (by simpa [IsRoot] using hRne),
    add_zero]

/-- 辅助引理（T5.3(4)）：`⌈k/3⌉ = ⌊(k+2)/3⌋`。 -/
theorem natCeil_div_three (k : ℕ) : ⌈(k : ℚ) / 3⌉₊ = (k + 2) / 3 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0 : ℚ) < 3)]
    have : ((k + 2) / 3 - 1) * 3 < k := by omega
    exact_mod_cast this
  · rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 3)]
    have : k ≤ (k + 2) / 3 * 3 := by omega
    exact_mod_cast this

/-- **T5.3(4)**（报告的写法）：`k ≥ 1` 时 `n_k` 在 `z = −1` 处的根重数恰为 `⌈k/3⌉ − 1`。 -/
theorem rootMultiplicity_nrowPoly_ceil {k : ℕ} (hk : 1 ≤ k) :
    (nrowPoly k).rootMultiplicity (-1) = ⌈(k : ℚ) / 3⌉₊ - 1 := by
  rw [rootMultiplicity_nrowPoly hk, natCeil_div_three]

end Mobius

/-! ## 5. T5.3(5)：`h_k` 在 `[0,1]` 上没有根 -/

section Pos

/-- 辅助引理（T5.3(5)）：实数 `|t| < 1` 时 `Σ_m U_k(m)·t^m` 收敛到 `h_k(t)/(1−t)^{k+1}`
（`h_k(t)` 写成 `aeval t (hpoly k)`）。 -/
theorem hasSum_U_mul_pow (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun m => (U k m : ℝ) * t ^ m) (aeval t (hpoly k) / (1 - t) ^ (k + 1)) := by
  have hU : ∀ m, (U k m : ℝ) * t ^ m = ∑ i ∈ range (k + 1),
      ((hpoly k).coeff i : ℝ) * (if i ≤ m then ((m - i + k).choose k : ℝ) * t ^ m else 0) := by
    intro m
    have h := congrArg (fun q : ℚ => (q : ℝ)) (U_eq_sum_hcoeff_ite k m)
    simp only [Rat.cast_natCast, Rat.cast_sum, Rat.cast_mul, apply_ite (fun q : ℚ => (q : ℝ)),
      Rat.cast_zero] at h
    rw [h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hnorm : ‖t‖ < 1 := by rwa [Real.norm_eq_abs]
  have hi : ∀ i ∈ range (k + 1), HasSum
      (fun m => ((hpoly k).coeff i : ℝ) * (if i ≤ m then ((m - i + k).choose k : ℝ) * t ^ m else 0))
      (((hpoly k).coeff i : ℝ) * (t ^ i * (1 / (1 - t) ^ (k + 1)))) := by
    intro i _
    apply HasSum.mul_left
    rw [← hasSum_nat_add_iff' i]
    have h0 : ∑ j ∈ range i, (if i ≤ j then ((j - i + k).choose k : ℝ) * t ^ j else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp [show ¬ i ≤ j by omega]
    rw [h0, sub_zero]
    have h1 : (fun n => if i ≤ n + i then ((n + i - i + k).choose k : ℝ) * t ^ (n + i) else 0)
        = fun n => t ^ i * (((n + k).choose k : ℝ) * t ^ n) := by
      funext n
      simp only [show i ≤ n + i by omega, ↓reduceIte, Nat.add_sub_cancel]
      ring
    rw [h1]
    exact (hasSum_choose_mul_geometric_of_norm_lt_one k hnorm).mul_left (t ^ i)
  have hsum := hasSum_sum hi
  simp only [← hU] at hsum
  convert hsum using 1
  have hdeg : (hpoly k).natDegree < k + 1 := by rw [natDegree_hpoly]; omega
  rw [aeval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, eq_ratCast]
  ring

/-- **T5.3(5)**：`t ∈ [0,1)` 时 `h_k(t) = (1−t)^{k+1}·Σ_m U_k(m)·t^m`（实数级数收敛）。 -/
theorem hpoly_aeval_eq_tsum (k : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    aeval t (hpoly k) = (1 - t) ^ (k + 1) * ∑' m, (U k m : ℝ) * t ^ m := by
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, h1⟩
  have hd : (1 - t) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [(hasSum_U_mul_pow k ht).tsum_eq]
  field_simp

/-- **T5.3(5)**：对 `t ∈ [0,1]`，`h_k(t) > 0`；所以 `h_k` 在 `[0,1]` 上没有实根。证明（照报告）：
`t ∈ [0,1)` 时 `h_k(t) = (1−t)^{k+1}·Σ_m U_k(m)t^m ≥ (1−t)^{k+1}·U_k(0) > 0`；`h_k(1) = N(k,k) > 0`
（`k = 0` 时 `h_0 = 1`）。 -/
theorem hpoly_pos_of_mem_Icc (k : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < aeval t (hpoly k) := by
  rcases lt_or_eq_of_le h1 with h1 | rfl
  · have hs := hasSum_U_mul_pow k (t := t) (abs_lt.mpr ⟨by linarith, h1⟩)
    have h00 : (U k 0 : ℝ) * t ^ 0 ≤ aeval t (hpoly k) / (1 - t) ^ (k + 1) :=
      le_hasSum hs 0 (fun j _ => by positivity)
    rw [U_zero_right] at h00
    have hd : 0 < (1 - t) ^ (k + 1) := pow_pos (by linarith) _
    have hpos : 0 < aeval t (hpoly k) / (1 - t) ^ (k + 1) := by
      simp at h00; linarith
    have := mul_pos hpos hd
    rwa [div_mul_cancel₀ _ hd.ne'] at this
  · have e : aeval (1 : ℝ) (hpoly k) = (((hpoly k).eval 1 : ℚ) : ℝ) := by
      rw [← map_one (algebraMap ℚ ℝ), aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]
    rw [e]
    have hq : 0 < (hpoly k).eval 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [hpoly_zero]
      · rw [hpoly_eval_one hk]; exact_mod_cast N_self_pos k
    exact_mod_cast hq

/-- **T5.3(5)**：`h_k` 在 `[0,1]` 上没有（实）根。 -/
theorem hpoly_ne_zero_of_mem_Icc (k : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    aeval t (hpoly k) ≠ 0 :=
  (hpoly_pos_of_mem_Icc k h0 h1).ne'

end Pos

end A207123
