import A207123.Pick
import A207123.RootLocation

/-!
# 论文推论 8.14：不同取值个数的中心极限定理

论文推论 8.14：在 `n_k(1)` 个「长 `k`、值域恰为某个 `{1,…,q}`」的合法词中均匀随机地取一个，记 `X_k` 为它的不同取值
个数，则 `(X_k − E X_k)/√Var X_k` 依分布收敛到标准正态分布。

形式化：`cltWords k`（这些词）、`numValues w`（不同取值的个数）、`cltMean k`、`cltVar k`（`cltWords k` 上均匀分布时
`X_k` 的期望与方差，按定义写成有限和）、`cltLaw k`（`(X_k − E X_k)/√Var X_k` 的分布：每个词的质量为
`1/|cltWords k|`）。主定理 `cor_clt`：`cltLaw k` 作为概率测度弱收敛到 `gaussianReal 0 1`（Mathlib 的依分布收敛
`TendstoInDistribution` 就定义为分布的这种收敛）。

证明按论文的思路，但不引用 Lindeberg–Feller 定理，直接估计特征函数：
* `n_k = N(k,k)·∏_r (z + r)`（`r` 取 `−(n_k 的根)`，都是正数），所以 `X_k − 1` 的特征函数是
  `∏_r (p_r e^{iτ} + q_r)`，`p_r = 1/(1+r)`、`q_r = r/(1+r)`（`charFun_cltLaw_eq_prod`；这就是论文说的「`X_k − 1`
  是独立 Bernoulli 变量之和」）；
* 期望 `1 + Σ_r p_r`、方差 `Σ_r p_r q_r`（`cltMean_eq`、`cltVar_eq_sum`；由 `∏(z + r)` 在 `1` 处的一阶、二阶导数，
  `linProd_moments`）；
* 每个因子与 `exp(−τ² p q/2)` 相差至多 `p q (|τ|³ + τ⁴)`（三阶泰勒展开，Mathlib 的 `Complex.exp_bound`；
  `bernoulli_factor_bound`），所以特征函数与 `exp(−t²/2)` 相差至多 `|t|³/σ_k + t⁴/σ_k²`（`charFun_cltLaw_bound`）；
* `−1` 是 `n_k` 的 `⌈k/3⌉ − 1` 重根，每个贡献 `p q = 1/4`，所以 `σ_k² ≥ (⌈k/3⌉ − 1)/4 → ∞`（`cltVar_ge`、
  `tendsto_cltVar`；论文证明里的同一句）；
* Lévy 连续性定理（Mathlib 的 `ProbabilityMeasure.tendsto_of_tendsto_charFun`）。
-/

namespace A207123

open Polynomial Filter Topology Complex MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. 定义 -/

/-- 长 `k`、值域恰为某个 `{1,…,q}`（`0 ≤ q ≤ k`）的合法词全体。`k ≥ 1` 时 `q = 0` 不出现，共 `n_k(1)` 个词。 -/
def cltWords (k : ℕ) : Finset (List ℕ) := (Finset.range (k + 1)).biUnion (NW k)

/-- 词 `w` 的不同取值的个数（论文推论 8.14 的 `X_k`）。 -/
def numValues (w : List ℕ) : ℕ := w.toFinset.card

/-- `cltWords k` 上均匀分布时 `X_k` 的期望。 -/
def cltMean (k : ℕ) : ℝ := (∑ w ∈ cltWords k, (numValues w : ℝ)) / (cltWords k).card

/-- `cltWords k` 上均匀分布时 `X_k` 的方差。 -/
def cltVar (k : ℕ) : ℝ :=
  (∑ w ∈ cltWords k, ((numValues w : ℝ) - cltMean k) ^ 2) / (cltWords k).card

/-- `(X_k − E X_k)/√Var X_k` 的分布：`cltWords k` 上的均匀分布在这个函数下的像。 -/
def cltLaw (k : ℕ) : Measure ℝ :=
  ((cltWords k).card : ℝ≥0∞)⁻¹ •
    ∑ w ∈ cltWords k, Measure.dirac (((numValues w : ℝ) - cltMean k) / Real.sqrt (cltVar k))

/-! ## 2. 按取值个数分组 -/

theorem numValues_of_mem_NW {k q : ℕ} {w : List ℕ} (hw : w ∈ NW k q) : numValues w = q := by
  rw [numValues, (mem_NW.1 hw).2.2, Nat.card_Icc]
  omega

theorem NW_pairwiseDisjoint (k : ℕ) (s : Finset ℕ) : (s : Set ℕ).PairwiseDisjoint (NW k) := by
  intro q _ q' _ hqq'
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  exact hqq' ((numValues_of_mem_NW hw).symm.trans (numValues_of_mem_NW hw'))

theorem sum_cltWords {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ w ∈ cltWords k, f (numValues w) = ∑ q ∈ Finset.range (k + 1), N k q • f q := by
  rw [cltWords, Finset.sum_biUnion (NW_pairwiseDisjoint k _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : ∑ w ∈ NW k q, f (numValues w) = ∑ _w ∈ NW k q, f q :=
    Finset.sum_congr rfl fun w hw => by rw [numValues_of_mem_NW hw]
  rw [h, Finset.sum_const]
  rfl

theorem card_cltWords (k : ℕ) : (cltWords k).card = ∑ q ∈ Finset.range (k + 1), N k q := by
  rw [cltWords, Finset.card_biUnion (NW_pairwiseDisjoint k _)]
  rfl

theorem card_cltWords_pos (k : ℕ) : 0 < (cltWords k).card := by
  rw [card_cltWords]
  exact lt_of_lt_of_le (N_self_pos k)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega)))

instance isProbabilityMeasure_cltLaw (k : ℕ) : IsProbabilityMeasure (cltLaw k) := by
  constructor
  have hc : ((cltWords k).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (card_cltWords_pos k).ne'
  rw [cltLaw, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _)

theorem sum_range_N_eq {M : Type*} [AddCommMonoid M] {k : ℕ} (hk : 1 ≤ k) (g : ℕ → M) :
    ∑ q ∈ Finset.range (k + 1), N k q • g q = ∑ q ∈ Finset.Icc 1 k, N k q • g q := by
  symm
  refine Finset.sum_subset (fun q hq => ?_) (fun q hq hq' => ?_)
  · rw [Finset.mem_Icc] at hq
    rw [Finset.mem_range]
    omega
  · have hq0 : q = 0 := by
      rw [Finset.mem_range] at hq
      rw [Finset.mem_Icc] at hq'
      omega
    subst hq0
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [N_succ_zero, zero_smul]

/-! ## 3. `∏(z + r)` 在 `1` 处的值与导数；`n_k` 在 `1` 处的导数 -/

/-- `∏_{r ∈ s} (X + r)`。 -/
def linProd (s : Multiset ℝ) : ℝ[X] := (s.map fun r => X + C r).prod

/-- `P = ∏_{r ∈ s}(X + r)`（`r > 0`）：`P(1) = ∏(1 + r)`，`P'(1) = P(1)·Σ 1/(1+r)`，
`P''(1) = P(1)·((Σ 1/(1+r))² − Σ 1/(1+r)²)`。 -/
theorem linProd_moments (s : Multiset ℝ) (hs : ∀ r ∈ s, 0 < r) :
    (linProd s).eval 1 = (s.map fun r => 1 + r).prod ∧
    (derivative (linProd s)).eval 1 = (linProd s).eval 1 * (s.map fun r => (1 + r)⁻¹).sum ∧
    (derivative (derivative (linProd s))).eval 1 = (linProd s).eval 1 *
      ((s.map fun r => (1 + r)⁻¹).sum ^ 2 - (s.map fun r => ((1 + r)⁻¹) ^ 2).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp [linProd]
  | cons r s ih =>
    have hr : 0 < r := hs r (Multiset.mem_cons_self r s)
    obtain ⟨h0, h1, h2⟩ := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hP : linProd (r ::ₘ s) = (X + C r) * linProd s := by
      rw [linProd, linProd, Multiset.map_cons, Multiset.prod_cons]
    have hne : (1 + r : ℝ) ≠ 0 := by positivity
    have e1 : derivative ((X + C r) * linProd s) = linProd s + (X + C r) * derivative (linProd s) := by
      rw [derivative_mul, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
    have e2 : derivative (derivative ((X + C r) * linProd s)) =
        2 * derivative (linProd s) + (X + C r) * derivative (derivative (linProd s)) := by
      rw [e1, derivative_add, derivative_mul, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
      ring
    simp only [hP, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp only [eval_mul, eval_add, eval_X, eval_C]
      rw [h0]
    · rw [e1]
      simp only [eval_mul, eval_add, eval_X, eval_C]
      rw [h1]
      field_simp
    · rw [e2]
      simp only [eval_mul, eval_add, eval_X, eval_C, eval_ofNat]
      rw [h1, h2]
      field_simp
      ring

theorem eval_one_nR (k : ℕ) : (nR k).eval 1 = ∑ q ∈ Finset.Icc 1 k, (N k q : ℝ) := by
  simp [nR, eval_finsetSum]

theorem eval_one_derivative_nR (k : ℕ) :
    (derivative (nR k)).eval 1 = ∑ q ∈ Finset.Icc 1 k, (N k q : ℝ) * ((q : ℝ) - 1) := by
  rw [nR, derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  rw [derivative_C_mul_X_pow]
  simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  rw [Nat.cast_sub hq1, Nat.cast_one]

theorem eval_one_derivative2_nR (k : ℕ) :
    (derivative (derivative (nR k))).eval 1 =
      ∑ q ∈ Finset.Icc 1 k, (N k q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) - 2) := by
  rw [nR, derivative_sum, derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  rw [derivative_C_mul_X_pow, derivative_C_mul_X_pow]
  simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  rcases Nat.lt_or_ge q 2 with h | h
  · obtain rfl : q = 1 := by omega
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, q = j + 2 := ⟨q - 2, by omega⟩
    rw [show j + 2 - 1 = j + 1 by omega, show j + 1 - 1 = j by omega]
    push_cast
    ring

/-! ## 4. 期望与方差 -/

/-- `n_k` 的根取负（都是正数）。 -/
def negRoots (k : ℕ) : Multiset ℝ := (nR k).roots.map Neg.neg

theorem negRoots_pos {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : r ∈ negRoots k) : 0 < r := by
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr
  exact neg_pos.2 (root_neg_nR hk ha)

theorem nR_eq_C_mul_linProd {k : ℕ} (hk : 1 ≤ k) : nR k = C (N k k : ℝ) * linProd (negRoots k) :=
  nR_eq_prod hk

theorem card_cltWords_eq {k : ℕ} (hk : 1 ≤ k) : ((cltWords k).card : ℝ) = (nR k).eval 1 := by
  rw [card_cltWords, Nat.cast_sum, eval_one_nR]
  have h := sum_range_N_eq (M := ℝ) hk (fun _ => 1)
  simp only [nsmul_eq_mul, mul_one] at h
  exact h

theorem eval_one_nR_pos {k : ℕ} (hk : 1 ≤ k) : 0 < (nR k).eval 1 := by
  rw [← card_cltWords_eq hk]
  exact_mod_cast card_cltWords_pos k

/-- `Σ_r 1/(1+r)`（`r` 取 `negRoots k`）。 -/
def momS (k : ℕ) : ℝ := ((negRoots k).map fun r => (1 + r)⁻¹).sum

/-- `Σ_r 1/(1+r)²`。 -/
def momQ (k : ℕ) : ℝ := ((negRoots k).map fun r => ((1 + r)⁻¹) ^ 2).sum

theorem nR_moments {k : ℕ} (hk : 1 ≤ k) :
    (derivative (nR k)).eval 1 = (nR k).eval 1 * momS k ∧
    (derivative (derivative (nR k))).eval 1 = (nR k).eval 1 * (momS k ^ 2 - momQ k) := by
  obtain ⟨-, h1, h2⟩ := linProd_moments (negRoots k) fun r hr => negRoots_pos hk hr
  rw [nR_eq_C_mul_linProd hk, derivative_C_mul, derivative_C_mul]
  simp only [eval_mul, eval_C]
  refine ⟨?_, ?_⟩
  · rw [h1, momS]
    ring
  · rw [h2, momS, momQ]
    ring

/-- `E X_k = 1 + Σ_r 1/(1+r)`。 -/
theorem cltMean_eq {k : ℕ} (hk : 1 ≤ k) : cltMean k = 1 + momS k := by
  have hA := card_cltWords_eq hk
  have hApos := eval_one_nR_pos hk
  have hsum : ∑ w ∈ cltWords k, (numValues w : ℝ) =
      (derivative (nR k)).eval 1 + (nR k).eval 1 := by
    have h : ∑ w ∈ cltWords k, (numValues w : ℝ) = ∑ q ∈ Finset.range (k + 1), N k q • (q : ℝ) :=
      sum_cltWords k (fun q => (q : ℝ))
    rw [h, sum_range_N_eq hk, eval_one_derivative_nR, eval_one_nR, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [nsmul_eq_mul]; ring
  rw [cltMean, hsum, hA, (nR_moments hk).1]
  field_simp
  ring

/-- `Var X_k = Σ_r 1/(1+r) − Σ_r 1/(1+r)²`。 -/
theorem cltVar_eq {k : ℕ} (hk : 1 ≤ k) : cltVar k = momS k - momQ k := by
  have hA := card_cltWords_eq hk
  have hApos := eval_one_nR_pos hk
  have hm := cltMean_eq hk
  obtain ⟨hB, hC⟩ := nR_moments hk
  have hsum : ∑ w ∈ cltWords k, ((numValues w : ℝ) - cltMean k) ^ 2 =
      (derivative (derivative (nR k))).eval 1 + (3 - 2 * cltMean k) * (derivative (nR k)).eval 1 +
        (1 - cltMean k) ^ 2 * (nR k).eval 1 := by
    have h : ∑ w ∈ cltWords k, ((numValues w : ℝ) - cltMean k) ^ 2 =
        ∑ q ∈ Finset.range (k + 1), N k q • ((q : ℝ) - cltMean k) ^ 2 :=
      sum_cltWords k (fun q => ((q : ℝ) - cltMean k) ^ 2)
    rw [h, sum_range_N_eq hk, eval_one_derivative2_nR, eval_one_derivative_nR, eval_one_nR,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [nsmul_eq_mul]; ring
  rw [cltVar, hsum, hA, hB, hC, hm]
  field_simp
  ring

/-- `Var X_k = Σ_r p_r (1 − p_r)`，`p_r = 1/(1+r)`。 -/
theorem cltVar_eq_sum {k : ℕ} (hk : 1 ≤ k) :
    cltVar k = ((negRoots k).map fun r => (1 + r)⁻¹ * (1 - (1 + r)⁻¹)).sum := by
  rw [cltVar_eq hk, momS, momQ, ← Multiset.sum_map_sub]
  congr 1
  exact Multiset.map_congr rfl fun r _ => by ring

/-- 非负项之和不小于其中值为 `a` 的那些项。 -/
theorem count_mul_le_sum_map {s : Multiset ℝ} {f : ℝ → ℝ} (hf : ∀ r ∈ s, 0 ≤ f r) (a : ℝ) :
    (s.count a : ℝ) * f a ≤ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    have ih := ih fun r hr => hf r (Multiset.mem_cons_of_mem hr)
    have hb := hf b (Multiset.mem_cons_self b s)
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases hab : b = a
    · subst hab
      rw [Multiset.count_cons_self]
      push_cast
      linarith
    · rw [Multiset.count_cons_of_ne (Ne.symm hab)]
      linarith

/-- 论文推论 8.14 证明中的一句：`Var X_k ≥ (⌈k/3⌉ − 1)/4`（`−1` 是 `⌈k/3⌉ − 1` 重根，每个贡献 `1/4`）。 -/
theorem cltVar_ge {k : ℕ} (hk : 1 ≤ k) : (((k + 2) / 3 - 1 : ℕ) : ℝ) / 4 ≤ cltVar k := by
  rw [cltVar_eq_sum hk]
  have hcount : (negRoots k).count 1 = (k + 2) / 3 - 1 := by
    rw [negRoots, ← count_neg_one_nR hk]
    have := Multiset.count_map_eq_count' Neg.neg (nR k).roots neg_injective (-1)
    rwa [neg_neg] at this
  have hf : ∀ r ∈ negRoots k, 0 ≤ (1 + r)⁻¹ * (1 - (1 + r)⁻¹) := by
    intro r hr
    have hr0 := negRoots_pos hk hr
    have e : (1 + r)⁻¹ * (1 - (1 + r)⁻¹) = r / (1 + r) ^ 2 := by
      field_simp
      ring
    rw [e]
    positivity
  have h := count_mul_le_sum_map hf 1
  rw [hcount] at h
  norm_num at h
  linarith

theorem tendsto_cltVar : Tendsto cltVar atTop atTop := by
  have hlow : ∀ k : ℕ, 1 ≤ k → (k : ℝ) / 12 + (-1 / 4) ≤ cltVar k := by
    intro k hk
    have h1 := cltVar_ge hk
    have h3 : k ≤ 3 * ((k + 2) / 3) := by omega
    have h4 : 1 ≤ (k + 2) / 3 := by omega
    rw [Nat.cast_sub h4, Nat.cast_one] at h1
    have h5 : (k : ℝ) ≤ 3 * (((k + 2) / 3 : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  refine tendsto_atTop_mono' atTop (f₁ := fun k : ℕ => (k : ℝ) / 12 + (-1 / 4)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk using hlow k hk
  · exact tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 12))

/-! ## 5. 特征函数 -/

theorem charFun_cltLaw (k : ℕ) (t : ℝ) :
    charFun (cltLaw k) t = ((cltWords k).card : ℂ)⁻¹ *
      ∑ w ∈ cltWords k,
        Complex.exp ((t : ℂ) * ((((numValues w : ℝ) - cltMean k) / Real.sqrt (cltVar k) : ℝ) : ℂ) * I) := by
  rw [charFun_apply_real, cltLaw, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro w _
    exact integrable_dirac (by simp)

theorem aeval_nR (k : ℕ) (z : ℂ) :
    aeval z (nR k) = ∑ q ∈ Finset.Icc 1 k, (N k q : ℂ) * z ^ (q - 1) := by
  rw [nR, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, aeval_C, map_pow, aeval_X, Complex.coe_algebraMap, Complex.ofReal_natCast]

theorem aeval_linProd (s : Multiset ℝ) (z : ℂ) :
    aeval z (linProd s) = (s.map fun r : ℝ => z + (r : ℂ)).prod := by
  rw [linProd, map_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun r _ => by
    simp only [Function.comp_apply, map_add, aeval_X, aeval_C, Complex.coe_algebraMap]

theorem exp_neg_sum_eq_prod (s : Multiset ℝ) (τ : ℝ) :
    Complex.exp (((-(τ * (s.map fun r => (1 + r)⁻¹).sum)) : ℝ) * I) =
      (s.map fun r : ℝ => Complex.exp (((-(τ * (1 + r)⁻¹)) : ℝ) * I)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, ← ih,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem div_algebra_aux {A B D M : ℂ} (hM : M ≠ 0) :
    (M * D)⁻¹ * (A * (M * B)) = A * (B / D) := by
  calc (M * D)⁻¹ * (A * (M * B)) = A * B * D⁻¹ * (M * M⁻¹) := by ring
    _ = A * (B / D) := by rw [mul_inv_cancel₀ hM, div_eq_mul_inv]; ring

/-- 特征函数的乘积形式：`τ = t/σ_k`，`charFun = ∏_r e^{−iτ/(1+r)}·(e^{iτ} + r)/(1 + r)`。 -/
theorem charFun_cltLaw_eq_prod {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    charFun (cltLaw k) t = ((negRoots k).map fun r : ℝ =>
      Complex.exp (((-((t / Real.sqrt (cltVar k)) * (1 + r)⁻¹)) : ℝ) * I) *
        ((Complex.exp (((t / Real.sqrt (cltVar k) : ℝ) : ℂ) * I) + (r : ℂ)) / (1 + (r : ℂ)))).prod := by
  have hm := cltMean_eq hk
  have hNkk : (N k k : ℂ) ≠ 0 := by exact_mod_cast (N_self_pos k).ne'
  have haeval : ∀ z : ℂ, aeval z (nR k) = (N k k : ℂ) * ((negRoots k).map fun r : ℝ => z + (r : ℂ)).prod := by
    intro z
    rw [nR_eq_C_mul_linProd hk, map_mul, aeval_C, Complex.coe_algebraMap, Complex.ofReal_natCast,
      aeval_linProd]
  have hcard : ((cltWords k).card : ℂ) = (N k k : ℂ) * ((negRoots k).map fun r : ℝ => (1 : ℂ) + (r : ℂ)).prod := by
    rw [← haeval 1, ← Complex.ofReal_one, aeval_ofReal, ← card_cltWords_eq hk, Complex.ofReal_natCast]
  have hgroup : ∑ w ∈ cltWords k,
        Complex.exp ((t : ℂ) * ((((numValues w : ℝ) - cltMean k) / Real.sqrt (cltVar k) : ℝ) : ℂ) * I) =
      Complex.exp (((t / Real.sqrt (cltVar k) * (1 - cltMean k)) : ℝ) * I) *
        aeval (Complex.exp (((t / Real.sqrt (cltVar k) : ℝ) : ℂ) * I)) (nR k) := by
    have h : ∑ w ∈ cltWords k,
          Complex.exp ((t : ℂ) * ((((numValues w : ℝ) - cltMean k) / Real.sqrt (cltVar k) : ℝ) : ℂ) * I) =
        ∑ q ∈ Finset.range (k + 1),
          N k q • Complex.exp ((t : ℂ) * ((((q : ℝ) - cltMean k) / Real.sqrt (cltVar k) : ℝ) : ℂ) * I) :=
      sum_cltWords k (fun q => Complex.exp ((t : ℂ) * ((((q : ℝ) - cltMean k) / Real.sqrt (cltVar k) : ℝ) : ℂ) * I))
    rw [h, sum_range_N_eq hk, aeval_nR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
    rw [nsmul_eq_mul, mul_left_comm]
    congr 1
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hq1]
    push_cast
    ring
  have hc : Complex.exp (((t / Real.sqrt (cltVar k) * (1 - cltMean k)) : ℝ) * I) =
      ((negRoots k).map fun r : ℝ => Complex.exp (((-((t / Real.sqrt (cltVar k)) * (1 + r)⁻¹)) : ℝ) * I)).prod := by
    rw [← exp_neg_sum_eq_prod, hm, momS]
    congr 2
    push_cast
    ring
  rw [charFun_cltLaw, hgroup, haeval, hcard, hc, Multiset.prod_map_mul, Multiset.prod_map_div]
  exact div_algebra_aux hNkk

/-! ## 6. 估计 -/

theorem norm_multiset_prod_le_one (s : Multiset ℝ) (f : ℝ → ℂ) (hf : ∀ r ∈ s, ‖f r‖ ≤ 1) :
    ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have h1 := hf r (Multiset.mem_cons_self r s)
    have h2 := ih fun x hx => hf x (Multiset.mem_cons_of_mem hx)
    calc ‖f r‖ * ‖(s.map f).prod‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- 各因子模长 `≤ 1` 时 `‖∏ a − ∏ b‖ ≤ Σ ‖a − b‖`。 -/
theorem norm_multiset_prod_sub_prod_le (s : Multiset ℝ) (a b : ℝ → ℂ)
    (ha : ∀ r ∈ s, ‖a r‖ ≤ 1) (hb : ∀ r ∈ s, ‖b r‖ ≤ 1) :
    ‖(s.map a).prod - (s.map b).prod‖ ≤ (s.map fun r => ‖a r - b r‖).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have ih := ih (fun x hx => ha x (Multiset.mem_cons_of_mem hx))
      (fun x hx => hb x (Multiset.mem_cons_of_mem hx))
    have har := ha r (Multiset.mem_cons_self r s)
    have hB := norm_multiset_prod_le_one s b fun x hx => hb x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have e : a r * (s.map a).prod - b r * (s.map b).prod =
        a r * ((s.map a).prod - (s.map b).prod) + (a r - b r) * (s.map b).prod := by ring
    rw [e]
    calc ‖a r * ((s.map a).prod - (s.map b).prod) + (a r - b r) * (s.map b).prod‖
        ≤ ‖a r‖ * ‖(s.map a).prod - (s.map b).prod‖ + ‖a r - b r‖ * ‖(s.map b).prod‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * (s.map fun r => ‖a r - b r‖).sum + ‖a r - b r‖ * 1 := by
          gcongr
      _ = ‖a r - b r‖ + (s.map fun r => ‖a r - b r‖).sum := by ring

/-- `|x| ≤ 1` 时 `‖e^{ix} − (1 + ix − x²/2)‖ ≤ |x|³`（Mathlib 的 `Complex.exp_bound`，常数是 `2/9`）。 -/
theorem exp_I_taylor_bound {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h := Complex.exp_bound (x := (x : ℂ) * I) (by rw [hnorm]; exact hx) (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) = 1 + x * I - x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one,
      Nat.cast_one, zero_add, pow_zero, pow_one, div_one, mul_pow, I_sq]
    push_cast
    ring
  rw [hs, hnorm] at h
  refine h.trans ?_
  have h3 : 0 ≤ |x| ^ 3 := by positivity
  norm_num [Nat.factorial]
  nlinarith [h3]

/-- 单个因子：`p, q ≥ 0`、`p + q = 1`、`|τ| ≤ 1` 时
`‖q e^{−iτp} + p e^{iτq} − e^{−τ²pq/2}‖ ≤ pq(|τ|³ + τ⁴)`。 -/
theorem bernoulli_factor_bound {p q τ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hτ : |τ| ≤ 1) :
    ‖(q : ℂ) * Complex.exp (((-(τ * p) : ℝ) : ℂ) * I) + (p : ℂ) * Complex.exp (((τ * q : ℝ) : ℂ) * I) -
        ((Real.exp (-(τ ^ 2 * (p * q) / 2)) : ℝ) : ℂ)‖ ≤ p * q * (|τ| ^ 3 + τ ^ 4) := by
  have hp1 : p ≤ 1 := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hx1 : |(-(τ * p))| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_nonneg hp]
    nlinarith [abs_nonneg τ]
  have hx2 : |τ * q| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hq]
    nlinarith [abs_nonneg τ]
  have h1 := exp_I_taylor_bound hx1
  have h2 := exp_I_taylor_bound hx2
  have hy0 : 0 ≤ τ ^ 2 * (p * q) / 2 := by positivity
  have hpq0 : 0 ≤ p * q := mul_nonneg hp hq
  have hpq4 : p * q ≤ 1 / 4 := by nlinarith [sq_nonneg (p - q)]
  have hτ2 : τ ^ 2 ≤ 1 := by
    have := sq_abs τ
    nlinarith [abs_nonneg τ]
  have hy1 : |(-(τ ^ 2 * (p * q) / 2))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hy0]
    nlinarith
  have h3 := Real.abs_exp_sub_one_sub_id_le hy1
  have hpqC : (p : ℂ) + q = 1 := by exact_mod_cast hpq
  have key : (q : ℂ) * Complex.exp (((-(τ * p) : ℝ) : ℂ) * I) + (p : ℂ) * Complex.exp (((τ * q : ℝ) : ℂ) * I) -
        ((Real.exp (-(τ ^ 2 * (p * q) / 2)) : ℝ) : ℂ) =
      (q : ℂ) * (Complex.exp (((-(τ * p) : ℝ) : ℂ) * I) -
          (1 + ((-(τ * p) : ℝ) : ℂ) * I - ((-(τ * p) : ℝ) : ℂ) ^ 2 / 2)) +
        (p : ℂ) * (Complex.exp (((τ * q : ℝ) : ℂ) * I) -
          (1 + ((τ * q : ℝ) : ℂ) * I - ((τ * q : ℝ) : ℂ) ^ 2 / 2)) -
        ((Real.exp (-(τ ^ 2 * (p * q) / 2)) - 1 - (-(τ ^ 2 * (p * q) / 2)) : ℝ) : ℂ) := by
    push_cast
    linear_combination (1 - (τ : ℂ) ^ 2 * ((p : ℂ) * q) / 2) * hpqC
  rw [key]
  have n1 : ‖(q : ℂ) * (Complex.exp (((-(τ * p) : ℝ) : ℂ) * I) -
      (1 + ((-(τ * p) : ℝ) : ℂ) * I - ((-(τ * p) : ℝ) : ℂ) ^ 2 / 2))‖ ≤ q * (|τ| * p) ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    have e : |(-(τ * p))| = |τ| * p := by rw [abs_neg, abs_mul, abs_of_nonneg hp]
    rw [e] at h1
    exact mul_le_mul_of_nonneg_left h1 hq
  have n2 : ‖(p : ℂ) * (Complex.exp (((τ * q : ℝ) : ℂ) * I) -
      (1 + ((τ * q : ℝ) : ℂ) * I - ((τ * q : ℝ) : ℂ) ^ 2 / 2))‖ ≤ p * (|τ| * q) ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    have e : |τ * q| = |τ| * q := by rw [abs_mul, abs_of_nonneg hq]
    rw [e] at h2
    exact mul_le_mul_of_nonneg_left h2 hp
  have n3 : ‖((Real.exp (-(τ ^ 2 * (p * q) / 2)) - 1 - (-(τ ^ 2 * (p * q) / 2)) : ℝ) : ℂ)‖ ≤
      (τ ^ 2 * (p * q) / 2) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [neg_sq] at h3
    exact h3
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  have hA : q * (|τ| * p) ^ 3 + p * (|τ| * q) ^ 3 = p * q * |τ| ^ 3 * (p ^ 2 + q ^ 2) := by ring
  have hB : (τ ^ 2 * (p * q) / 2) ^ 2 = p * q * τ ^ 4 * (p * q / 4) := by ring
  have hpq2 : p ^ 2 + q ^ 2 ≤ 1 := by nlinarith
  have hτ3 : 0 ≤ |τ| ^ 3 := by positivity
  have hτ4 : 0 ≤ τ ^ 4 := by positivity
  have e1 : p * q * |τ| ^ 3 * (p ^ 2 + q ^ 2) ≤ p * q * |τ| ^ 3 := by
    have := mul_nonneg hpq0 hτ3
    nlinarith
  have e2 : p * q * τ ^ 4 * (p * q / 4) ≤ p * q * τ ^ 4 := by
    have := mul_nonneg hpq0 hτ4
    nlinarith
  nlinarith [n1, n2, n3]

theorem factor_norm_le_one {p q x y : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ‖(q : ℂ) * Complex.exp ((x : ℂ) * I) + (p : ℂ) * Complex.exp ((y : ℂ) * I)‖ ≤ 1 := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg hq]
  linarith

/-- 把因子写成 `q e^{−iτp} + p e^{iτq}`，`p = 1/(1+r)`、`q = 1 − p`。 -/
theorem factor_eq (τ r : ℝ) (hr : 0 < r) :
    Complex.exp (((-(τ * (1 + r)⁻¹)) : ℝ) * I) * ((Complex.exp ((τ : ℂ) * I) + r) / (1 + r)) =
      ((1 - (1 + r)⁻¹ : ℝ) : ℂ) * Complex.exp (((-(τ * (1 + r)⁻¹)) : ℝ) * I) +
        (((1 + r)⁻¹ : ℝ) : ℂ) * Complex.exp (((τ * (1 - (1 + r)⁻¹)) : ℝ) * I) := by
  have hr1 : (1 + (r : ℂ)) ≠ 0 := by
    have : (1 + r : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have e : Complex.exp (((τ * (1 - (1 + r)⁻¹)) : ℝ) * I) =
      Complex.exp (((-(τ * (1 + r)⁻¹)) : ℝ) * I) * Complex.exp ((τ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  generalize Complex.exp (((-(τ * (1 + r)⁻¹)) : ℝ) * I) = A
  generalize Complex.exp ((τ : ℂ) * I) = B
  push_cast
  field_simp
  ring

theorem ofReal_exp_sum_eq_prod (s : Multiset ℝ) (f : ℝ → ℝ) :
    ((Real.exp (s.map f).sum : ℝ) : ℂ) = (s.map fun r => ((Real.exp (f r) : ℝ) : ℂ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Real.exp_add, Complex.ofReal_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

theorem bound_algebra {s t v : ℝ} (hs : 0 < s) (hv : s ^ 2 = v) :
    v * (|t / s| ^ 3 + (t / s) ^ 4) = |t| ^ 3 / s + t ^ 4 / v := by
  subst hv
  rw [abs_div, abs_of_pos hs]
  field_simp

/-- 特征函数与 `exp(−t²/2)` 之差：`σ_k > 0`、`|t| ≤ σ_k` 时至多 `|t|³/σ_k + t⁴/σ_k²`。 -/
theorem charFun_cltLaw_bound {k : ℕ} (hk : 1 ≤ k) (t : ℝ) (hv : 0 < cltVar k)
    (ht : |t| ≤ Real.sqrt (cltVar k)) :
    ‖charFun (cltLaw k) t - ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      |t| ^ 3 / Real.sqrt (cltVar k) + t ^ 4 / cltVar k := by
  have hs : 0 < Real.sqrt (cltVar k) := Real.sqrt_pos.2 hv
  have hss : Real.sqrt (cltVar k) ^ 2 = cltVar k := Real.sq_sqrt hv.le
  have hτ : |t / Real.sqrt (cltVar k)| ≤ 1 := by
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    exact ht
  have hprod : ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) = ((negRoots k).map fun r : ℝ =>
      ((Real.exp (-((t / Real.sqrt (cltVar k)) ^ 2 * ((1 + r)⁻¹ * (1 - (1 + r)⁻¹)) / 2)) : ℝ) : ℂ)).prod := by
    rw [← ofReal_exp_sum_eq_prod]
    congr 2
    have e : ∀ r : ℝ, -((t / Real.sqrt (cltVar k)) ^ 2 * ((1 + r)⁻¹ * (1 - (1 + r)⁻¹)) / 2) =
        -((t / Real.sqrt (cltVar k)) ^ 2 / 2) * ((1 + r)⁻¹ * (1 - (1 + r)⁻¹)) := fun r => by ring
    simp_rw [e]
    rw [Multiset.sum_map_mul_left, ← cltVar_eq_sum hk, div_pow, hss]
    field_simp
  rw [charFun_cltLaw_eq_prod hk t, hprod]
  have hfac : ∀ r ∈ negRoots k,
      Complex.exp (((-((t / Real.sqrt (cltVar k)) * (1 + r)⁻¹)) : ℝ) * I) *
          ((Complex.exp (((t / Real.sqrt (cltVar k) : ℝ) : ℂ) * I) + r) / (1 + r)) =
        ((1 - (1 + r)⁻¹ : ℝ) : ℂ) * Complex.exp (((-((t / Real.sqrt (cltVar k)) * (1 + r)⁻¹)) : ℝ) * I) +
          (((1 + r)⁻¹ : ℝ) : ℂ) *
            Complex.exp ((((t / Real.sqrt (cltVar k)) * (1 - (1 + r)⁻¹)) : ℝ) * I) :=
    fun r hr => factor_eq _ r (negRoots_pos hk hr)
  have hp : ∀ r ∈ negRoots k, 0 ≤ (1 + r)⁻¹ ∧ 0 ≤ 1 - (1 + r)⁻¹ := by
    intro r hr
    have hr0 := negRoots_pos hk hr
    have : (1 + r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact ⟨by positivity, by linarith⟩
  refine (norm_multiset_prod_sub_prod_le _ _ _ (fun r hr => ?_) (fun r hr => ?_)).trans ?_
  · rw [hfac r hr]
    exact factor_norm_le_one (hp r hr).1 (hp r hr).2 (by ring)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := (hp r hr).1
    have := (hp r hr).2
    have : 0 ≤ (t / Real.sqrt (cltVar k)) ^ 2 * ((1 + r)⁻¹ * (1 - (1 + r)⁻¹)) / 2 := by positivity
    linarith
  · calc _ ≤ ((negRoots k).map fun r : ℝ =>
            ((1 + r)⁻¹ * (1 - (1 + r)⁻¹)) * (|t / Real.sqrt (cltVar k)| ^ 3 +
              (t / Real.sqrt (cltVar k)) ^ 4)).sum := by
          refine Multiset.sum_map_le_sum_map _ _ fun r hr => ?_
          rw [hfac r hr]
          exact bernoulli_factor_bound (hp r hr).1 (hp r hr).2 (by ring) hτ
      _ = cltVar k * (|t / Real.sqrt (cltVar k)| ^ 3 + (t / Real.sqrt (cltVar k)) ^ 4) := by
          rw [Multiset.sum_map_mul_right, ← cltVar_eq_sum hk]
      _ = |t| ^ 3 / Real.sqrt (cltVar k) + t ^ 4 / cltVar k := bound_algebra hs hss

theorem tendsto_charFun_cltLaw (t : ℝ) :
    Tendsto (fun k => charFun (cltLaw k) t) atTop (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) := by
  have hv := tendsto_cltVar
  have hs : Tendsto (fun k => Real.sqrt (cltVar k)) atTop atTop := Real.tendsto_sqrt_atTop.comp hv
  have hbound : Tendsto (fun k => |t| ^ 3 / Real.sqrt (cltVar k) + t ^ 4 / cltVar k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |t| ^ 3 / Real.sqrt (cltVar k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hs
    have h2 : Tendsto (fun k => t ^ 4 / cltVar k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hv
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hbound
  have hev2 : ∀ᶠ k in atTop, 0 < cltVar k := hv.eventually (eventually_gt_atTop 0)
  have hev3 : ∀ᶠ k in atTop, |t| ≤ Real.sqrt (cltVar k) := hs.eventually (eventually_ge_atTop |t|)
  filter_upwards [eventually_ge_atTop 1, hev2, hev3] with k h1 h2 h3
  exact charFun_cltLaw_bound h1 t h2 h3

/-! ## 7. 论文推论 8.14 -/

/-- 论文推论 8.14：在 `n_k(1)` 个「长 `k`、值域恰为某个 `{1,…,q}`」的合法词中均匀随机地取一个，它的不同取值个数
`X_k` 标准化后的分布 `cltLaw k` 弱收敛（依分布收敛）到标准正态分布 `gaussianReal 0 1`。 -/
theorem cor_clt :
    Tendsto (β := ProbabilityMeasure ℝ) (fun k => ⟨cltLaw k, inferInstance⟩) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  have h : ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) = charFun (gaussianReal 0 1) t := by
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simpa only [ProbabilityMeasure.coe_mk, h] using tendsto_charFun_cltLaw t

end

end A207123
