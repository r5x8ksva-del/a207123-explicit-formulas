import A207123.EndAscent

/-!
# 报告 T3.1 的 Kummer 形式与下不完全 Gamma 形式、T3.3(1) 的整表 `₁F₁` 和式（猜想总表 A8 的一部分）

`λ = (1 − x)/x³`，`a = −t/x³`，`b_i = 1 − x − i·x³ = x³(λ − i)`。注记 5.2（报告 T3.1 的主式，`remark_1F1`）已形式化：
`Σ_m tᵐ/P_m = ₁F₁(1; 1 − λ; a)/(1 − x)`。报告 T3.1 还说下面两个形式在 `ℚ(x)[[t]]` 中成立，T3.3(1) 给出整张表：

* `kummer_1F1`（Kummer 形式）：`₁F₁(1; 1 − λ; a) = e^a·₁F₁(−λ; 1 − λ; −a)`。这里对任意特征 0 的域 `K` 与不是自然数的
  `λ ∈ K` 证明（`e^{zt}` 记作 `expSer z`）；`remark_kummer` 取 `K = ℚ(x)`、`λ = (1 − x)/x³`。
* `sum_inv_P_eq_lowerGamma`（下不完全 Gamma 形式）：`Σ_m tᵐ/P_m = −x^{−3}·e^a·a^λγ(−λ, a)`，其中
  `a^λγ(−λ, a) := Σ_n (−a)ⁿ/(n!(n − λ))` 是报告的形式定义（`lowerGammaSer`）；`remark_lowerGamma` 取 `K = ℚ(x)`。
* `T3_3_one`（整表的 `₁F₁` 和式）：`F = Σ_m G_m tᵐ = Σ_{j≥0} κ_j·(t^j/b_j)·₁F₁(1; j + 1 − λ; a)`，`κ_0 = 1`、`κ_j = j·x²`，
  和在 `t` 进拓扑下收敛：陈述成 `F` 的每个 `tᵐ` 系数等于各项 `tᵐ` 系数之和（`j > m` 的项没有 `tᵐ`）；`G_m = W_m/P_m`
  （`P_mul_G`）。`remark_T3_3_one` 取 `K = ℚ(x)`。

三者都归结为部分分式恒等式 `sum_choose_div_sub`：`Σ_{q=0}^{n} (−1)^q C(n,q)/(λ − q) = (−1)ⁿ n!/∏_{q=0}^{n}(λ − q)`，
以及 `(j + 1 − λ)_n = (−1)ⁿ x^{−3n} ∏_{i=j+1}^{j+n} b_i`（`ascPochhammer_shift_lambda`）。
-/

namespace A207123

open Finset

open scoped Nat

/-- `e^{zt} = Σ_n zⁿ tⁿ/n!`（`t` 的形式幂级数）。 -/
noncomputable def expSer {K : Type*} [Field K] (z : K) : PowerSeries K :=
  PowerSeries.mk fun n => z ^ n / (n ! : K)

/-- 报告 T3.1 对 `a^λ·γ(−λ, a)` 的形式定义（`a = z·t`）：`Σ_n (−z)ⁿ/(n!·(n − λ))·tⁿ`。 -/
noncomputable def lowerGammaSer {K : Type*} [Field K] (lam z : K) : PowerSeries K :=
  PowerSeries.mk fun n => (-z) ^ n / ((n ! : K) * ((n : K) - lam))

/-! ## 1. 部分分式恒等式 -/

/-- 辅助引理：`S(n+1, λ) = S(n, λ) − S(n, λ − 1)`，`S(n, λ) = Σ_{q≤n} (−1)^q C(n,q)/(λ − q)`（Pascal 恒等式）。 -/
theorem sum_choose_div_sub_succ {K : Type*} [Field K] (n : ℕ) (lam : K) :
    ∑ q ∈ range (n + 1 + 1), (-1 : K) ^ q * ((n + 1).choose q : K) / (lam - q) =
      ∑ q ∈ range (n + 1), (-1 : K) ^ q * (n.choose q : K) / (lam - q)
        - ∑ q ∈ range (n + 1), (-1 : K) ^ q * (n.choose q : K) / (lam - 1 - q) := by
  have hφ := Finset.sum_range_succ' (fun r => (-1 : K) ^ r * (n.choose r : K) / (lam - r)) (n + 1)
  beta_reduce at hφ
  rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_div, add_zero] at hφ
  rw [sum_range_succ']
  simp only [Nat.choose_succ_succ', Nat.cast_add, mul_add, add_div, sum_add_distrib]
  have e : ∑ q ∈ range (n + 1), (-1 : K) ^ (q + 1) * (n.choose q : K) / (lam - ((q : K) + (1 : ℕ))) =
      -∑ q ∈ range (n + 1), (-1 : K) ^ q * (n.choose q : K) / (lam - 1 - q) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [pow_succ, Nat.cast_one, show lam - ((q : K) + 1) = lam - 1 - q by ring]
    ring
  have e2 : ∑ q ∈ range (n + 1), (-1 : K) ^ (q + 1) * (n.choose (q + 1) : K) / (lam - ((q : K) + (1 : ℕ))) =
      ∑ q ∈ range (n + 1), (-1 : K) ^ (q + 1) * (n.choose (q + 1) : K) / (lam - ((q + 1 : ℕ) : K)) := by
    refine sum_congr rfl fun q _ => ?_
    push_cast
    ring
  rw [e, e2]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, sub_zero, one_mul] at hφ ⊢
  linear_combination -hφ

/-- **部分分式恒等式**：`λ ∉ {0, …, n}` 时 `Σ_{q=0}^{n} (−1)^q C(n,q)/(λ − q) = (−1)ⁿ n!/∏_{q=0}^{n}(λ − q)`。 -/
theorem sum_choose_div_sub {K : Type*} [Field K] [CharZero K] :
    ∀ (n : ℕ) (lam : K), (∀ q : ℕ, q ≤ n → lam ≠ q) →
      ∑ q ∈ range (n + 1), (-1 : K) ^ q * (n.choose q : K) / (lam - q) =
        (-1) ^ n * (n ! : K) / ∏ q ∈ range (n + 1), (lam - q)
  | 0, lam, h => by
    simp
  | n + 1, lam, h => by
    have hA : ∏ q ∈ range (n + 1), (lam - q) ≠ 0 :=
      prod_ne_zero_iff.2 fun q hq => sub_ne_zero.2 (h q (by have := mem_range.1 hq; omega))
    have hB : ∏ q ∈ range (n + 1), (lam - 1 - q) ≠ 0 := prod_ne_zero_iff.2 fun q hq => by
      have := mem_range.1 hq
      intro e
      exact h (q + 1) (by omega) (by push_cast; linear_combination e)
    have hD : ∏ q ∈ range (n + 1 + 1), (lam - q) ≠ 0 :=
      prod_ne_zero_iff.2 fun q hq => sub_ne_zero.2 (h q (by have := mem_range.1 hq; omega))
    have ih1 := sum_choose_div_sub n lam fun q hq => h q (by omega)
    have ih2 := sum_choose_div_sub n (lam - 1) fun q hq e => h (q + 1) (by omega) (by push_cast; linear_combination e)
    have hD1 : ∏ q ∈ range (n + 1 + 1), (lam - q) = (∏ q ∈ range (n + 1), (lam - q)) * (lam - ((n : K) + 1)) := by
      rw [prod_range_succ, Nat.cast_add, Nat.cast_one]
    have hD2 : ∏ q ∈ range (n + 1 + 1), (lam - q) = (∏ q ∈ range (n + 1), (lam - 1 - q)) * lam := by
      rw [prod_range_succ']
      push_cast
      simp only [sub_zero]
      congr 1
      refine prod_congr rfl fun q _ => ?_
      ring
    rw [sum_choose_div_sub_succ, ih1, ih2, div_sub_div _ _ hA hB, div_eq_div_iff (mul_ne_zero hA hB) hD,
      Nat.factorial_succ]
    push_cast
    linear_combination ((-1 : K) ^ n * (n ! : K) * ∏ q ∈ range (n + 1), (lam - 1 - q)) * hD1
      - ((-1 : K) ^ n * (n ! : K) * ∏ q ∈ range (n + 1), (lam - q)) * hD2

/-! ## 2. Kummer 形式 -/

/-- 辅助引理：`(−λ)_q·(q − λ) = (−λ)·(1 − λ)_q`。 -/
theorem ascPochhammer_neg_mul {K : Type*} [Field K] (lam : K) (q : ℕ) :
    (ascPochhammer K q).eval (-lam) * ((q : K) - lam) = (-lam) * (ascPochhammer K q).eval (1 - lam) := by
  have h1 := ascPochhammer_succ_eval q (-lam)
  have h2 : (ascPochhammer K (q + 1)).eval (-lam) = (-lam) * (ascPochhammer K q).eval (1 - lam) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, show -lam + 1 = 1 - lam by ring]
  rw [← h2, h1]
  ring

/-- 辅助引理：`(1 − λ)_n·(−1)ⁿ = ∏_{q<n}(λ − (q + 1))`。 -/
theorem ascPochhammer_one_sub_mul {K : Type*} [Field K] (lam : K) :
    ∀ n : ℕ, (ascPochhammer K n).eval (1 - lam) * (-1) ^ n = ∏ q ∈ range n, (lam - ((q : K) + 1))
  | 0 => by simp
  | n + 1 => by
    rw [ascPochhammer_succ_eval, prod_range_succ, ← ascPochhammer_one_sub_mul lam n, pow_succ]
    ring

/-- **报告 T3.1**（Kummer 形式）：`λ` 不是自然数时，`₁F₁(1; 1 − λ; z t) = e^{zt}·₁F₁(−λ; 1 − λ; −z t)`。 -/
theorem kummer_1F1 {K : Type*} [Field K] [CharZero K] (lam z : K) (hlam : ∀ q : ℕ, lam ≠ q) :
    hyp1F1 1 (1 - lam) z = expSer z * hyp1F1 (-lam) (1 - lam) (-z) := by
  ext n
  have hsub : ∀ q : ℕ, lam - q ≠ 0 := fun q => sub_ne_zero.2 (hlam q)
  have hasc : ∀ q : ℕ, (ascPochhammer K q).eval (1 - lam) ≠ 0 := fun q h => by
    have := ascPochhammer_one_sub_mul lam q
    rw [h, zero_mul] at this
    exact (prod_ne_zero_iff.2 fun i _ => by
      rw [show (i : K) + 1 = ((i + 1 : ℕ) : K) by push_cast; ring]; exact hsub (i + 1)) this.symm
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.swap_prod_mk, expSer, hyp1F1, PowerSeries.coeff_mk]
  -- 每一项化成 `zⁿ/n!·(−1)^q C(n,q)·λ/(λ − q)`
  have hterm : ∀ q ∈ range (n.succ), z ^ (n - q) / ((n - q)! : K) *
      ((ascPochhammer K q).eval (-lam) / (ascPochhammer K q).eval (1 - lam) * (-z) ^ q / (q ! : K)) =
      z ^ n / (n ! : K) * lam * ((-1 : K) ^ q * (n.choose q : K) / (lam - q)) := by
    intro q hq
    have hqn : q ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hq)
    obtain ⟨p, rfl⟩ : ∃ p, n = p + q := ⟨n - q, by omega⟩
    have hpq : p + q - q = p := by omega
    rw [hpq]
    have hc : ((p + q).choose q : K) * (p ! : K) * (q ! : K) = ((p + q)! : K) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial p q
    have hneg := ascPochhammer_neg_mul lam q
    have hp : (p ! : K) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    have hq' : (q ! : K) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    have hpq' : ((p + q)! : K) ≠ 0 := by exact_mod_cast (p + q).factorial_ne_zero
    have hs := hsub q
    have ha := hasc q
    have hC : ((p + q).choose q : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos (Nat.le_add_left q p)).ne'
    have hratio : (ascPochhammer K q).eval (-lam) / (ascPochhammer K q).eval (1 - lam) = lam / (lam - q) := by
      rw [div_eq_div_iff ha hs]
      linear_combination -hneg
    rw [hratio, ← hc, pow_add, neg_pow]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, sum_choose_div_sub n lam fun q _ => hlam q, ascPochhammer_eval_one]
  have hP := ascPochhammer_one_sub_mul lam n
  have hprod : ∏ q ∈ range (n + 1), (lam - q) = (∏ q ∈ range n, (lam - ((q : K) + 1))) * lam := by
    rw [prod_range_succ']
    push_cast
    simp only [sub_zero]
  have hn : (n ! : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hpr : ∏ q ∈ range n, (lam - ((q : K) + 1)) ≠ 0 := by
    rw [← hP]
    exact mul_ne_zero (hasc n) (pow_ne_zero _ (by norm_num))
  have hl : lam ≠ 0 := by have := hlam 0; rwa [Nat.cast_zero] at this
  rw [hprod, ← hP]
  field_simp

/-- **报告 T3.1**（Kummer 形式）：在 `ℚ(x)[[t]]` 中 `₁F₁(1; 1 − λ; −t/x³) = e^{−t/x³}·₁F₁(−λ; 1 − λ; t/x³)`，
`λ = (1 − x)/x³`。 -/
theorem remark_kummer :
    hyp1F1 1 (1 - (1 - RatFunc.X) / RatFunc.X ^ 3) (-1 / RatFunc.X ^ 3) =
      expSer (-1 / RatFunc.X ^ 3 : RatFunc ℚ) *
        hyp1F1 (-((1 - RatFunc.X) / RatFunc.X ^ 3)) (1 - (1 - RatFunc.X) / RatFunc.X ^ 3)
          (-(-1 / RatFunc.X ^ 3)) := by
  refine kummer_1F1 _ _ fun q h => ?_
  have hb := bpoly_ne_zero q
  apply hb
  apply RatFunc.algebraMap_injective ℚ
  rw [← eval_bpoly_ratFunc, map_zero, eval_bpoly]
  have hx : (RatFunc.X : RatFunc ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 RatFunc.X_ne_zero
  rw [div_eq_iff hx] at h
  linear_combination h

/-! ## 3. 下不完全 Gamma 形式 -/

/-- 辅助引理：`b_i(x) = x³·(λ − i)`，`λ = (1 − x)/x³`。 -/
theorem eval_bpoly_eq_lambda {K : Type*} [Field K] {x : K} (hx : x ≠ 0) (i : ℕ) :
    (bpoly K i).eval x = x ^ 3 * ((1 - x) / x ^ 3 - i) := by
  rw [eval_bpoly]
  field_simp

/-- **报告 T3.1**（下不完全 Gamma 形式）：域 `K` 中 `x ≠ 0`、各 `b_i(x) ≠ 0` 时
`Σ_m tᵐ/P_m(x) = −x^{−3}·e^{a}·a^λγ(−λ, a)`，`a = −t/x³`，`a^λγ(−λ, a) := Σ_n (−a)ⁿ/(n!(n − λ))`（`lowerGammaSer`）。 -/
theorem sum_inv_P_eq_lowerGamma {K : Type*} [Field K] [CharZero K] {x : K} (hx : x ≠ 0)
    (hb : ∀ i : ℕ, (bpoly K i).eval x ≠ 0) :
    PowerSeries.mk (fun m => ((Ppoly K m).eval x)⁻¹) =
      PowerSeries.C (-(x ^ 3)⁻¹) * (expSer (-1 / x ^ 3) * lowerGammaSer ((1 - x) / x ^ 3) (-1 / x ^ 3)) := by
  obtain ⟨lam, hlam⟩ : ∃ lam : K, lam = (1 - x) / x ^ 3 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : K, w = 1 / x ^ 3 := ⟨_, rfl⟩
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  have hsub : ∀ q : ℕ, lam - q ≠ 0 := fun q h => hb q (by rw [eval_bpoly_eq_lambda hx, ← hlam, h, mul_zero])
  have hsub' : ∀ q : ℕ, (q : K) - lam ≠ 0 := fun q h => hsub q (by linear_combination -h)
  ext m
  rw [← hlam, show -1 / x ^ 3 = -w by rw [hw]; ring, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.swap_prod_mk, expSer, lowerGammaSer, PowerSeries.coeff_mk, neg_neg]
  have hterm : ∀ q ∈ range m.succ, (-w) ^ (m - q) / ((m - q)! : K) * (w ^ q / ((q ! : K) * ((q : K) - lam))) =
      -(w ^ m / (m ! : K)) * (-1) ^ m * ((-1 : K) ^ q * (m.choose q : K) / (lam - q)) := by
    intro q hq
    have hqm : q ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hq)
    have hsign : (-1 : K) ^ (m - q) = (-1) ^ m * (-1) ^ q := by
      rw [pow_sub₀ _ (by norm_num) hqm, ← inv_pow, inv_neg, inv_one]
    have hm : (m ! : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hq' : (q ! : K) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    have hmq : ((m - q)! : K) ≠ 0 := by exact_mod_cast (m - q).factorial_ne_zero
    have hs := hsub q
    have hs' := hsub' q
    rw [neg_pow, hsign, Nat.cast_choose K hqm, ← pow_sub_mul_pow w hqm]
    field_simp
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_choose_div_sub m lam fun q _ h => hsub q (by rw [h]; ring)]
  have hprod : (Ppoly K m).eval x = (x ^ 3) ^ (m + 1) * ∏ q ∈ range (m + 1), (lam - (q : K)) := by
    rw [Ppoly, Polynomial.eval_prod, prod_congr rfl fun i _ => eval_bpoly_eq_lambda hx i, prod_mul_distrib,
      prod_const, card_range, ← hlam]
  have hsq : ((-1 : K) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hm : (m ! : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hPi : ∏ q ∈ range (m + 1), (lam - (q : K)) ≠ 0 := prod_ne_zero_iff.2 fun q _ => hsub q
  have hpow : (1 / x ^ 3) ^ m * (x ^ 3) ^ m = 1 := by rw [← mul_pow, one_div_mul_cancel hx3, one_pow]
  rw [hprod, hw]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  calc _ = ((-1 : K) ^ m * (-1) ^ m) * ((x ^ 3)⁻¹ * x ^ 3) * ((1 / x ^ 3) ^ m * (x ^ 3) ^ m) *
          ((m ! : K) * (m ! : K)⁻¹) * ((∏ q ∈ range (m + 1), (lam - (q : K))) *
            (∏ q ∈ range (m + 1), (lam - (q : K)))⁻¹) := by ring
    _ = 1 := by rw [hsq, inv_mul_cancel₀ hx3, hpow, mul_inv_cancel₀ hm, mul_inv_cancel₀ hPi]; ring

/-- **报告 T3.1**（下不完全 Gamma 形式）：在 `ℚ(x)[[t]]` 中 `Σ_m tᵐ/P_m = −x^{−3}·e^{a}·a^λγ(−λ, a)`。 -/
theorem remark_lowerGamma :
    PowerSeries.mk (fun m => ((Ppoly (RatFunc ℚ) m).eval RatFunc.X)⁻¹) =
      PowerSeries.C (-(RatFunc.X ^ 3)⁻¹) * (expSer (-1 / RatFunc.X ^ 3 : RatFunc ℚ) *
        lowerGammaSer ((1 - RatFunc.X) / RatFunc.X ^ 3) (-1 / RatFunc.X ^ 3)) := by
  refine sum_inv_P_eq_lowerGamma RatFunc.X_ne_zero fun i h => bpoly_ne_zero i ?_
  rw [eval_bpoly_ratFunc] at h
  exact RatFunc.algebraMap_injective ℚ (h.trans (map_zero _).symm)

/-! ## 4. T3.3(1)：整表的 `₁F₁` 和式 -/

/-- `κ_0 = 1`，`κ_j = j·x²`（`j ≥ 1`）。 -/
def kappa {K : Type*} [Field K] (x : K) (j : ℕ) : K := if j = 0 then 1 else (j : K) * x ^ 2

/-- 辅助引理：`G_m(x) = W_m(x)/P_m(x) = Σ_{j=0}^{m} κ_j/∏_{i=j}^{m} b_i(x)`（论文定理 4.4 在 `y = 1` 时的形式）。 -/
theorem W_div_P_eq_sum {K : Type*} [Field K] {x : K} (hb : ∀ i : ℕ, (bpoly K i).eval x ≠ 0) :
    ∀ m : ℕ, (Wpoly K m).eval x / (Ppoly K m).eval x =
      ∑ j ∈ range (m + 1), kappa x j / ∏ i ∈ Ico j (m + 1), (bpoly K i).eval x
  | 0 => by simp [Wpoly_zero, Ppoly_zero, kappa]
  | m + 1 => by
    have ih := W_div_P_eq_sum hb m
    have hP : (Ppoly K m).eval x ≠ 0 := by
      rw [Ppoly, Polynomial.eval_prod]
      exact prod_ne_zero_iff.2 fun i _ => hb i
    have hbm := hb (m + 1)
    have e : ∀ j ∈ range (m + 1), kappa x j / ∏ i ∈ Ico j (m + 1 + 1), (bpoly K i).eval x =
        kappa x j / (∏ i ∈ Ico j (m + 1), (bpoly K i).eval x) / (bpoly K (m + 1)).eval x := by
      intro j hj
      rw [prod_Ico_succ_top (by have := mem_range.1 hj; omega), div_div]
    rw [sum_range_succ, sum_congr rfl e, ← sum_div, ← ih, Nat.Ico_succ_singleton, prod_singleton, kappa,
      ite_eq_right (Nat.succ_ne_zero m), Wpoly_succ, Ppoly_succ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    field_simp
    push_cast
    ring

/-- 辅助引理：`(j + 1 − λ)_n = (−1)ⁿ·(x³)^{−n}·∏_{i=1}^{n} b_{j+i}(x)`。 -/
theorem ascPochhammer_shift_lambda {K : Type*} [Field K] {x : K} (hx : x ≠ 0) (j : ℕ) :
    ∀ n : ℕ, (ascPochhammer K n).eval ((j : K) + 1 - (1 - x) / x ^ 3) =
      (-1) ^ n * (x ^ 3)⁻¹ ^ n * ∏ i ∈ range n, (bpoly K (j + 1 + i)).eval x
  | 0 => by simp
  | n + 1 => by
    have h3 : x ^ 3 * (x ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 3 hx)
    rw [ascPochhammer_succ_eval, ascPochhammer_shift_lambda hx j n, prod_range_succ, eval_bpoly]
    push_cast
    linear_combination (-((-1) ^ n * (x ^ 3)⁻¹ ^ n * (∏ i ∈ range n, (bpoly K (j + 1 + i)).eval x) *
      ((j : K) + 1 + n))) * h3

/-- 辅助引理：`[tⁿ]₁F₁(1; j + 1 − λ; −t/x³) = 1/∏_{i=1}^{n} b_{j+i}(x)`。 -/
theorem coeff_hyp1F1_shift {K : Type*} [Field K] [CharZero K] {x : K} (hx : x ≠ 0)
    (hb : ∀ i : ℕ, (bpoly K i).eval x ≠ 0) (j n : ℕ) :
    PowerSeries.coeff n (hyp1F1 1 ((j : K) + 1 - (1 - x) / x ^ 3) (-1 / x ^ 3)) =
      (∏ i ∈ range n, (bpoly K (j + 1 + i)).eval x)⁻¹ := by
  have hP : ∏ i ∈ range n, (bpoly K (j + 1 + i)).eval x ≠ 0 := prod_ne_zero_iff.2 fun i _ => hb _
  have hn : (n ! : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  rw [hyp1F1, PowerSeries.coeff_mk, ascPochhammer_eval_one, ascPochhammer_shift_lambda hx j n]
  have hsq : ((-1 : K) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hpow : (x ^ 3)⁻¹ ^ n * (x ^ 3) ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hx3, one_pow]
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [div_pow, neg_pow, one_pow]
  field_simp
  linear_combination -hpow

/-- **报告 T3.3(1)**（逐系数）：`G_m(x) = W_m(x)/P_m(x) = Σ_{j=0}^{m} (κ_j/b_j(x))·[t^{m−j}]₁F₁(1; j + 1 − λ; −t/x³)`。 -/
theorem T3_3_one_coeff {K : Type*} [Field K] [CharZero K] {x : K} (hx : x ≠ 0)
    (hb : ∀ i : ℕ, (bpoly K i).eval x ≠ 0) (m : ℕ) :
    (Wpoly K m).eval x / (Ppoly K m).eval x =
      ∑ j ∈ range (m + 1), kappa x j / (bpoly K j).eval x *
        PowerSeries.coeff (m - j) (hyp1F1 1 ((j : K) + 1 - (1 - x) / x ^ 3) (-1 / x ^ 3)) := by
  rw [W_div_P_eq_sum hb m]
  refine sum_congr rfl fun j hj => ?_
  have hjm : j < m + 1 := mem_range.1 hj
  rw [coeff_hyp1F1_shift hx hb, prod_eq_prod_Ico_succ_bot hjm, prod_Ico_eq_prod_range,
    show m + 1 - (j + 1) = m - j by omega]
  ring

/-- **报告 T3.3(1)**：在 `K[[t]]` 中 `F = Σ_m G_m(x) tᵐ = Σ_{j≥0} κ_j·(t^j/b_j(x))·₁F₁(1; j + 1 − λ; −t/x³)`，
和按 `t` 进拓扑收敛：`F` 的 `tᵐ` 系数是各项 `tᵐ` 系数之和（`j > m` 的项没有 `tᵐ`，故只到 `j = m`）。 -/
theorem T3_3_one {K : Type*} [Field K] [CharZero K] {x : K} (hx : x ≠ 0)
    (hb : ∀ i : ℕ, (bpoly K i).eval x ≠ 0) :
    PowerSeries.mk (fun m => (Wpoly K m).eval x / (Ppoly K m).eval x) =
      PowerSeries.mk fun m => ∑ j ∈ range (m + 1), PowerSeries.coeff m
        (PowerSeries.X ^ j * PowerSeries.C (kappa x j / (bpoly K j).eval x) *
          hyp1F1 1 ((j : K) + 1 - (1 - x) / x ^ 3) (-1 / x ^ 3)) := by
  ext m
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, T3_3_one_coeff hx hb m]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hj)),
    PowerSeries.coeff_C_mul]

/-- **报告 T3.3(1)**：取 `K = ℚ(x)`（`x = X`）：在 `ℚ(x)[[t]]` 中
`F = Σ_{j≥0} κ_j·(t^j/b_j)·₁F₁(1; j + 1 − λ; −t/x³)`，`κ_0 = 1`、`κ_j = j·x²`。 -/
theorem remark_T3_3_one :
    PowerSeries.mk (fun m => (Wpoly (RatFunc ℚ) m).eval RatFunc.X / (Ppoly (RatFunc ℚ) m).eval RatFunc.X) =
      PowerSeries.mk fun m => ∑ j ∈ range (m + 1), PowerSeries.coeff m
        (PowerSeries.X ^ j * PowerSeries.C (kappa RatFunc.X j / (bpoly (RatFunc ℚ) j).eval RatFunc.X) *
          hyp1F1 1 ((j : RatFunc ℚ) + 1 - (1 - RatFunc.X) / RatFunc.X ^ 3) (-1 / RatFunc.X ^ 3)) := by
  refine T3_3_one RatFunc.X_ne_zero fun i h => bpoly_ne_zero i ?_
  rw [eval_bpoly_ratFunc] at h
  exact RatFunc.algebraMap_injective ℚ (h.trans (map_zero _).symm)

end A207123
