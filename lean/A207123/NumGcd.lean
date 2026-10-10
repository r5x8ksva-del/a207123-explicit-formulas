import A207123.NumStruct
import A207123.Laguerre

/-!
# 报告 T4.3(8)：对一切 `q ≥ 1`，`gcd(Num_q, P_{q−1}) = 1`

报告的证明（第二轮复核者 r-c4ii 的定理 R1）：只需对每个 `0 ≤ i ≤ q−1` 证明 `Num_q` 与 `b_i` 互素。

* `numS q i = Σ_{t≤q} C(q,t)·(q−1−i)^{\underline t}·x^{3t}`（报告的 `S_{q,i}`）；`numS_eq_comp`：它等于
  `s_n(x³)`，`s_n = lagS (i+1) n`、`n = q−1−i`（`Laguerre.lean`）。
* `Numq_modEq`（报告的同余引理）：`b_i ∣ Num_q − W_i·S_{q,i}`。由容斥闭式（`Numq` 就按它定义），模 `b_i` 时
  `b_v ≡ (i−v)·x³`（`bpoly_eq_add`），`j ≤ i` 的项含因子 `b_i`，`j ≥ i+1` 时 `W_{j−1} ≡ W_i`（`bpoly_dvd_W_sub`），
  两处符号 `(−1)^{q−j}` 恰好抵消（`prod_Ico_sub_eq`）；逐项的同余是 `term_modEq`，在 `AdjoinRoot b_i` 中计算。
* `numS_aeval_ne_zero`：`S_{q,i}` 在 `b_i` 的每个复根 `z` 处不为零：`z³` 虚部非零时用 `lagS_aeval_ne_zero`（首一 Laguerre
  多项式只有实根）；`z³` 为实数时 `z` 也是实数（`z = 1 − i z³`），且 `z > 0`，`S` 是正项和（`lagS_aeval_ofReal_ne_zero`）。
  这里对每个 `i` 统一处理，不用分 `b_i` 是否可约（报告的证明在 `b_i` 不可约时用共轭根，可约时用 Laguerre）。
* **`Numq_isCoprime_Ppoly`**（T4.3(8)）：`q ≥ 1` 时 `IsCoprime (Num_q) (P_{q−1})`。`W_i` 与 `b_i` 互素已有
  （`isCoprime_W_b`，T1.3(2)），`S_{q,i}` 与 `b_i` 互素由上一条与 `isCoprime_iff_aeval_ne_zero_of_isAlgClosed`。
* **`Nser_denom_dvd`**（推论：最简分母恰为 `P_{q−1}`）：若 `B·Σ_k N(k,q)x^k` 是多项式，则 `P_{q−1} ∣ B`。
-/

namespace A207123

open Polynomial Finset
open scoped Nat

noncomputable section

/-- 报告的 `S_{q,i} = Σ_{t≤q} C(q,t)·(q−1−i)^{\underline t}·x^{3t}`（`t > q−1−i` 的项为 0）。 -/
def numS (q i : ℕ) : ℚ[X] :=
  ∑ t ∈ range (q + 1), C ((q.choose t : ℚ) * ((q - 1 - i).descFactorial t : ℚ)) * X ^ (3 * t)

/-- `S_{q,i}(x) = s_n(x³)`，`n = q−1−i`、`α = i+1`。 -/
theorem numS_eq_comp {q i : ℕ} (hi : i < q) : numS q i = (lagS (i + 1) (q - 1 - i)).comp (X ^ 3) := by
  rw [numS, lagS, show q - 1 - i + (i + 1) = q by omega, Polynomial.sum_comp]
  simp only [mul_comp, C_comp, X_pow_comp, ← pow_mul]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
  intro t _ hnt
  rw [Finset.mem_range, not_lt] at hnt
  rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
  simp

/-! ## 1. 同余引理 -/

/-- `b_v = b_i + (i − v)·x³`。 -/
theorem bpoly_eq_add (i v : ℕ) : bpoly ℚ v = bpoly ℚ i + C ((i : ℚ) - v) * X ^ 3 := by
  simp only [bpoly, map_sub]
  ring

/-- `(−1)^t·∏_{v=q−t}^{q−1}(i − v) = (q−1−i)^{\underline t}`（写成 `descPochhammer` 在 `q−1−i` 处的值；`t ≤ q`）。 -/
theorem prod_Ico_sub_eq (q i : ℕ) : ∀ t, t ≤ q →
    (-1 : ℚ) ^ t * ∏ v ∈ Ico (q - t) q, ((i : ℚ) - v) = (descPochhammer ℚ t).eval ((q : ℚ) - 1 - i)
  | 0, _ => by simp
  | t + 1, ht => by
    rw [prod_eq_prod_Ico_succ_bot (by omega), show q - (t + 1) + 1 = q - t by omega, pow_succ,
      descPochhammer_succ_eval, ← prod_Ico_sub_eq q i t (by omega),
      show ((q - (t + 1) : ℕ) : ℚ) = (q : ℚ) - t - 1 by rw [Nat.cast_sub ht]; push_cast; ring]
    ring

/-- 逐项的同余：容斥式中 `j = q − t` 的项模 `b_i` 等于 `W_i·C(q,t)·(q−1−i)^{\underline t}·x^{3t}`。 -/
theorem term_modEq {q i t : ℕ} (hi : i < q) (htq : t ≤ q) :
    AdjoinRoot.mk (bpoly ℚ i)
        (C ((-1 : ℚ) ^ (q - (q - t)) * (q.choose (q - t) : ℚ)) * Wprev (q - t)
          * ∏ v ∈ Ico (q - t) q, bpoly ℚ v)
      = AdjoinRoot.mk (bpoly ℚ i)
          (Wpoly ℚ i * (C ((q.choose t : ℚ) * ((q - 1 - i).descFactorial t : ℚ)) * X ^ (3 * t))) := by
  have hb : ∀ v, AdjoinRoot.mk (bpoly ℚ i) (bpoly ℚ v)
      = AdjoinRoot.mk (bpoly ℚ i) (C ((i : ℚ) - v) * X ^ 3) := by
    intro v
    rw [bpoly_eq_add i v, map_add, AdjoinRoot.mk_self, zero_add]
  have hprod : AdjoinRoot.mk (bpoly ℚ i) (∏ v ∈ Ico (q - t) q, bpoly ℚ v)
      = AdjoinRoot.mk (bpoly ℚ i) (C (∏ v ∈ Ico (q - t) q, ((i : ℚ) - v)) * X ^ (3 * t)) := by
    rw [map_prod, Finset.prod_congr rfl fun v _ => hb v, ← map_prod, Finset.prod_mul_distrib,
      Finset.prod_const, Nat.card_Ico, show q - (q - t) = t by omega, ← pow_mul, ← map_prod C]
  rw [map_mul, map_mul, hprod, show q - (q - t) = t by omega, Nat.choose_symm htq]
  by_cases h : t ≤ q - 1 - i
  · have hW : AdjoinRoot.mk (bpoly ℚ i) (Wprev (q - t)) = AdjoinRoot.mk (bpoly ℚ i) (Wpoly ℚ i) := by
      obtain ⟨m, hm⟩ : ∃ m, q - t = m + 1 := ⟨q - t - 1, by omega⟩
      rw [hm, Wprev, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
      exact bpoly_dvd_W_sub (by omega)
    have hc : ((q - 1 - i : ℕ) : ℚ) = (q : ℚ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    have hD : (descPochhammer ℚ t).eval ((q : ℚ) - 1 - i) = ((q - 1 - i).descFactorial t : ℚ) := by
      rw [← descPochhammer_eval_eq_descFactorial, hc]
    have hconst : (-1 : ℚ) ^ t * (q.choose t : ℚ) * ∏ v ∈ Ico (q - t) q, ((i : ℚ) - v)
        = (q.choose t : ℚ) * ((q - 1 - i).descFactorial t : ℚ) := by
      rw [← hD, ← prod_Ico_sub_eq q i t htq]
      ring
    rw [hW, ← map_mul, ← map_mul]
    congr 1
    rw [← hconst]
    simp only [C_mul]
    ring
  · have hz : ∏ v ∈ Ico (q - t) q, ((i : ℚ) - v) = 0 :=
      Finset.prod_eq_zero (Finset.mem_Ico.2 ⟨by omega, hi⟩) (by simp)
    have hD0 : (q - 1 - i).descFactorial t = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    rw [hz, hD0]
    simp

/-- **报告的同余引理**：`i < q` 时 `b_i ∣ Num_q − W_i·S_{q,i}`。 -/
theorem Numq_modEq {q i : ℕ} (hi : i < q) : bpoly ℚ i ∣ Numq q - Wpoly ℚ i * numS q i := by
  rw [← AdjoinRoot.mk_eq_zero, map_sub, sub_eq_zero, Numq, numS, Finset.mul_sum, map_sum, map_sum]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htq : t ≤ q := by
    rw [Finset.mem_range] at ht
    omega
  rw [show q + 1 - 1 - t = q - t by omega]
  exact term_modEq hi htq

/-! ## 2. `S_{q,i}` 在 `b_i` 的复根处不为零 -/

/-- `S_{q,i}` 在 `b_i` 的每个复根处不为零（`i < q`）。 -/
theorem numS_aeval_ne_zero {q i : ℕ} (hi : i < q) {z : ℂ} (hz : aeval z (bpoly ℚ i) = 0) :
    aeval z (numS q i) ≠ 0 := by
  rw [numS_eq_comp hi, aeval_comp, map_pow, aeval_X]
  have hb : 1 - z - (i : ℂ) * z ^ 3 = 0 := by
    rw [← hz]
    simp [bpoly]
  by_cases him : (z ^ 3).im = 0
  · have h1 : z = 1 - (i : ℂ) * z ^ 3 := by linear_combination -hb
    have hzim : z.im = 0 := by
      have h2 := congrArg Complex.im h1
      simp [Complex.mul_im, him] at h2
      exact h2
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
    have hreal : (1 : ℝ) - z.re - (i : ℝ) * z.re ^ 3 = 0 := by
      rw [hzr] at hb
      exact_mod_cast hb
    have hr : 0 < z.re := by
      by_contra hneg0
      have hneg : z.re ≤ 0 := not_lt.1 hneg0
      have h3 : z.re ^ 3 ≤ 0 := by
        have e : z.re ^ 3 = z.re * z.re ^ 2 := by ring
        rw [e]
        exact mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg _)
      have h4 : (i : ℝ) * z.re ^ 3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg i) h3
      linarith
    rw [hzr, ← Complex.ofReal_pow]
    exact lagS_aeval_ofReal_ne_zero _ _ (by positivity)
  · exact lagS_aeval_ne_zero _ _ him

/-! ## 3. T4.3(8) -/

/-- **报告 T4.3(8)**：对一切 `q ≥ 1`，`Num_q` 与 `P_{q−1}` 互素，即 `gcd(Num_q, P_{q−1}) = 1`。 -/
theorem Numq_isCoprime_Ppoly {q : ℕ} (hq : 1 ≤ q) : IsCoprime (Numq q) (Ppoly ℚ (q - 1)) := by
  have hP : Ppoly ℚ (q - 1) = ∏ i ∈ range q, bpoly ℚ i := by
    rw [Ppoly, Nat.sub_add_cancel hq]
  rw [hP]
  refine IsCoprime.prod_right fun i hi => ?_
  have hi' : i < q := Finset.mem_range.1 hi
  obtain ⟨K, hK⟩ := Numq_modEq hi'
  have e : Numq q = Wpoly ℚ i * numS q i + bpoly ℚ i * K := by linear_combination hK
  rw [e]
  refine IsCoprime.add_mul_left_left (IsCoprime.mul_left (isCoprime_W_b le_rfl) ?_) K
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ (numS q i) (bpoly ℚ i)).2 fun z => ?_
  by_cases hz : aeval z (bpoly ℚ i) = 0
  · exact Or.inl (numS_aeval_ne_zero hi' hz)
  · exact Or.inr hz

/-- **报告 T4.3(8)**（推论）：`Σ_k N(k,q)x^k` 的最简分母恰为 `P_{q−1}`：若 `B·Σ_k N(k,q)x^k` 是多项式 `A`，
则 `P_{q−1} ∣ B`（`q ≥ 1`）。 -/
theorem Nser_denom_dvd {q : ℕ} (hq : 1 ≤ q) {A B : ℚ[X]}
    (h : (↑B : PowerSeries ℚ) * Nser q = ↑A) : Ppoly ℚ (q - 1) ∣ B := by
  have hP := P_mul_Nser hq
  have e : B * Numq q = Ppoly ℚ (q - 1) * A := by
    apply Polynomial.coe_injective ℚ
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hP, ← h]
    ring
  exact (Numq_isCoprime_Ppoly hq).symm.dvd_of_dvd_mul_right ⟨A, e⟩

end

end A207123
