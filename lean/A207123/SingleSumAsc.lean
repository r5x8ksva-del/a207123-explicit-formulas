import A207123.SingleSum
import A207123.EndAscent

/-!
# 论文定理 6.2：以上升结尾的那部分也没有 `(2,1)` 形状的单族和

论文定理 6.2：设 `U^↑_k(m)` 是 `H_k(m)` 中以上升结尾（`h_{k−1} < h_k`）的序列个数（`NUp`）。`m ≥ 2` 时不存在整数
`c, d, k₀ ≥ 0` 与复数 `A(s)`（与 `k` 无关），使对所有 `k ≥ k₀` 有 `U^↑_k(m) = Σ_s A(s)·C(k+c−2s, m+s+d)`（二项式与求和的
约定同定理 6.1，主定理 `thm_Spart`）。

* `single_sum_cross`：定理 6.1 证明的前两步对任意满足 `P_m·G = V`（`V` 是多项式）的幂级数 `G` 都成立：若 `G` 的系数
  在 `k ≥ k₀` 时是这种单族和，则对 `D(u₀) = 0` 的每个 `u₀`（`D = ∏_{v≤m}(1 − vu)`），`T³ + u₀T − u₀` 的任意两个根
  `ξ, η` 满足 `F₁(ξ)F₂(η) = F₁(η)F₂(ξ)`，其中 `F₁ = x^{K₁}V`、`F₂ = x^{K₂}(1−x)^m`。
* `P_mul_GUp`：`P_m·Σ_k U^↑_k(m)x^k = W_m − 1`（由 `P_mul_Gc` 与注记 5.2 的 `P_mul_NAser`：不以上升结尾的部分是 `1/P_m`）。
* 论文取纤维 `u = 1/2`，即 `b_2 = 1 − x − 2x³` 的根 `η`（要 `m ≥ 2` 才有 `D(1/2) = 0`）：`W_m(η) − 1 = η⁵(4 − 2η)`、
  `1 − η = 2η³`，于是三个根上 `η^p(2 − η) = λη^r`。论文用 `ℚ(η)` 中的范数与 `17` 进赋值；这里用 `2X³ + X − 1` 的韦达
  关系：`λ³ = 17·2^{r−p−1}`，而 `3λ` 是根的幂和的有理组合、是有理数，`17` 进赋值给出 `3·v(λ) = 1`（`no_common_value_b2`）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 定理 6.1 证明的前两步，对一般的 `P_m·G = V` -/

/-- 在 `u = u₀` 处：`F(ξ) = Σ_i r_i(u₀) ξ^i`（`ξ` 是 `T³ + u₀T − u₀` 的根）。 -/
theorem eval_eq_coords_at {u₀ ξ : ℂ} (hξ : ξ ^ 3 + u₀ * ξ - u₀ = 0) (F : ℂ[X]) :
    F.eval ξ = ∑ i ∈ Finset.range 3, (coordU F i).eval u₀ * ξ ^ i := by
  let ev1 : Polynomial (Polynomial ℂ) →+* ℂ := Polynomial.eval₂RingHom (Polynomial.evalRingHom u₀) ξ
  have hq : ev1 qU = 0 := by
    simp only [ev1, Polynomial.coe_eval₂RingHom, qU, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.coe_evalRingHom, Polynomial.eval_X]
    linear_combination hξ
  have hmap : ev1 (F.map Polynomial.C) = F.eval ξ := by
    simp only [ev1, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
    rw [show (Polynomial.evalRingHom u₀).comp Polynomial.C = RingHom.id ℂ by ext; simp]
    rfl
  have hmod : ev1 (F.map Polynomial.C) = ev1 ((F.map Polynomial.C) %ₘ qU) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div (F.map Polynomial.C) qU]
    rw [map_add, map_mul, hq, zero_mul, add_zero]
  rw [← hmap, hmod]
  simp only [ev1, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_eq_sum_range' _ (natDegree_mod_qU_lt _)]
  rfl

/-- 定理 6.1、6.2 证明的公共部分：`P_m·G = V`，`G` 的系数在 `k ≥ k₀` 时是 `Σ_s A(s)·C(k+c−2s, m+s+d)`，`D(u₀) = 0`，
则有自然数 `K₁, K₂`，使 `T³ + u₀T − u₀` 的任意两个根 `ξ, η` 满足 `F₁(ξ)F₂(η) = F₁(η)F₂(ξ)`
（`F₁ = x^{K₁}V`、`F₂ = x^{K₂}(1−x)^m`；证明同 `thm_S` 的第一、二步）。 -/
theorem single_sum_cross {m : ℕ} {Gs : PowerSeries ℂ} {V : ℂ[X]}
    (hPG : (Ppoly ℂ m : PowerSeries ℂ) * Gs = (V : PowerSeries ℂ))
    {c d : ℤ} {k₀ : ℕ} {A : ℤ → ℂ}
    (hA : ∀ k : ℕ, k₀ ≤ k →
      PowerSeries.coeff k Gs = ∑ᶠ s : ℤ, A s * (binomZ (k + c - 2 * s) (m + s + d) : ℂ))
    {u₀ : ℂ} (hD : (Dpoly m).eval u₀ = 0) :
    ∃ K₁ K₂ : ℕ, ∀ ξ η : ℂ, ξ ^ 3 + u₀ * ξ - u₀ = 0 → η ^ 3 + u₀ * η - u₀ = 0 →
      (Polynomial.X ^ K₁ * V).eval ξ * ((Polynomial.X ^ K₂ * (1 - Polynomial.X) ^ m : ℂ[X])).eval η =
        (Polynomial.X ^ K₁ * V).eval η * ((Polynomial.X ^ K₂ * (1 - Polynomial.X) ^ m : ℂ[X])).eval ξ := by
  -- 第一步：令 `t = s + m + d`，`a_t = A(t − m − d)`，`K = c + 2(m + d)`
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = m + d := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = c + 2 * e := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, ∀ t, a t = A (t - e) := ⟨_, fun _ => rfl⟩
  have hcoef : ∀ k : ℕ, k₀ ≤ k → 0 ≤ (k : ℤ) + K →
      PowerSeries.coeff k Gs =
        PowerSeries.coeff ((k : ℤ) + K).toNat (substU (PowerSeries.mk a) * PowerSeries.mk 1) := by
    intro k hk hkK
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k + K := ⟨((k : ℤ) + K).toNat, by omega⟩
    rw [show ((k : ℤ) + K).toNat = n by omega, hA k hk, coeff_substU_mk_mul_mk_one]
    rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (n + 1)).map
      ⟨fun t : ℕ => (t : ℤ) - e, fun x y h => by simpa using h⟩) ?_]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun t _ => ?_
      show A ((t : ℤ) - e) * (binomZ ((k : ℤ) + c - 2 * ((t : ℤ) - e)) ((m : ℤ) + ((t : ℤ) - e) + d) : ℂ) =
        a t * (if 3 * t ≤ n then ((n - 2 * t).choose t : ℂ) else 0)
      rw [show (k : ℤ) + c - 2 * ((t : ℤ) - e) = (n : ℤ) - 2 * t by omega,
        show (m : ℤ) + ((t : ℤ) - e) + d = t by omega, binomZ_sub_two_mul, Nat.cast_ite, Nat.cast_zero,
        ha t]
    · intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      have hb : binomZ ((k : ℤ) + c - 2 * s) ((m : ℤ) + s + d) ≠ 0 := by
        intro h0
        apply hs
        rw [h0, Nat.cast_zero, mul_zero]
      unfold binomZ at hb
      have hcond : 0 ≤ (m : ℤ) + s + d ∧ (m : ℤ) + s + d ≤ (k : ℤ) + c - 2 * s := by
        by_contra hc
        exact hb (ite_eq_right hc)
      rw [Finset.mem_coe, Finset.mem_map]
      refine ⟨((m : ℤ) + s + d).toNat, Finset.mem_range.2 (by omega), ?_⟩
      show ((((m : ℤ) + s + d).toNat : ℕ) : ℤ) - e = s
      omega
  -- 两边的母函数只差有限项：`x^{K₁}G − x^{K₂}ã(u)/(1−x)` 是多项式 `E`
  obtain ⟨K₁, K₂, hK12⟩ : ∃ K₁ K₂ : ℕ, K = (K₁ : ℤ) - K₂ := ⟨K.toNat, (-K).toNat, by omega⟩
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries ℂ, S = substU (PowerSeries.mk a) * PowerSeries.mk 1 := ⟨_, rfl⟩
  have hlarge : ∀ j, k₀ + K₁ + K₂ ≤ j →
      PowerSeries.coeff j (PowerSeries.X ^ K₁ * Gs) = PowerSeries.coeff j (PowerSeries.X ^ K₂ * S) := by
    intro j hj
    rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
      ite_eq_left (by omega), hS]
    have h1 := hcoef (j - K₁) (by omega) (by omega)
    rw [show (((j - K₁ : ℕ) : ℤ) + K).toNat = j - K₂ by omega] at h1
    exact h1
  obtain ⟨Epoly, hE⟩ : ∃ Epoly : ℂ[X],
      PowerSeries.X ^ K₁ * Gs - PowerSeries.X ^ K₂ * S = (Epoly : PowerSeries ℂ) := by
    refine ⟨PowerSeries.trunc (k₀ + K₁ + K₂) (PowerSeries.X ^ K₁ * Gs - PowerSeries.X ^ K₂ * S), ?_⟩
    ext j
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hj
    · rfl
    · rw [map_sub, hlarge j (by omega), sub_self]
  -- 乘以 `P_m = (1−x)^{m+1} D(u)`：`x^{K₁} V = x^{K₂}(1−x)^m·(Dã)(u) + D(u)·(1−x)^{m+1} E`
  obtain ⟨bS, hbS⟩ : ∃ bS : PowerSeries ℂ, bS = (Dpoly m : PowerSeries ℂ) * PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁⟩ : ∃ F : ℂ[X], F = Polynomial.X ^ K₁ * V := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F : ℂ[X], F = Polynomial.X ^ K₂ * (1 - Polynomial.X) ^ m := ⟨_, rfl⟩
  obtain ⟨F₃, hF₃⟩ : ∃ F : ℂ[X], F = (1 - Polynomial.X) ^ (m + 1) * Epoly := ⟨_, rfl⟩
  have hmain : (F₁ : PowerSeries ℂ) =
      (F₂ : PowerSeries ℂ) * substU bS + substU (Dpoly m : PowerSeries ℂ) * (F₃ : PowerSeries ℂ) := by
    have hP := coe_Ppoly_uS m
    have hmk : PowerSeries.mk (1 : ℕ → ℂ) * (1 - PowerSeries.X) = 1 :=
      PowerSeries.mk_one_mul_one_sub_eq_one ℂ
    rw [hS] at hE
    rw [hF₁, hF₂, hF₃, hbS]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_sub,
      Polynomial.coe_one, map_mul substU]
    linear_combination (substU (Dpoly m : PowerSeries ℂ) * (1 - PowerSeries.X) ^ (m + 1)) * hE -
      PowerSeries.X ^ K₁ * hPG + (PowerSeries.X ^ K₁ * Gs) * hP +
      (substU (Dpoly m : PowerSeries ℂ) * PowerSeries.X ^ K₂ * substU (PowerSeries.mk a) *
        (1 - PowerSeries.X) ^ m) * hmk
  -- 第二步：比较坐标，`r_i(F₁) = r_i(F₂)·Dã + D·r_i(F₃)`（`i = 0, 1, 2`）
  have c1 := coe_eq_coords F₁
  have c2 := coe_eq_coords F₂
  have c3 := coe_eq_coords F₃
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
    at c1 c2 c3
  have hzero := substU_coords_unique
    (α := (coordU F₁ 0 : PowerSeries ℂ) - coordU F₂ 0 * bS - Dpoly m * coordU F₃ 0)
    (β := (coordU F₁ 1 : PowerSeries ℂ) - coordU F₂ 1 * bS - Dpoly m * coordU F₃ 1)
    (γ := (coordU F₁ 2 : PowerSeries ℂ) - coordU F₂ 2 * bS - Dpoly m * coordU F₃ 2) (by
      simp only [map_sub substU, map_mul substU]
      linear_combination hmain - c1 + substU bS * c2 + substU (Dpoly m : PowerSeries ℂ) * c3)
  have hrel : ∀ i, i < 3 →
      (coordU F₁ i : PowerSeries ℂ) = coordU F₂ i * bS + Dpoly m * coordU F₃ i := by
    intro i hi
    interval_cases i
    · linear_combination hzero.1
    · linear_combination hzero.2.1
    · linear_combination hzero.2.2
  -- 消去 `ã`，在 `u = u₀`（`D(u₀) = 0`）处坐标向量成比例
  have hminor : ∀ i j, i < 3 → j < 3 →
      (coordU F₁ i).eval u₀ * (coordU F₂ j).eval u₀ = (coordU F₁ j).eval u₀ * (coordU F₂ i).eval u₀ := by
    intro i j hi hj
    have hp : coordU F₁ i * coordU F₂ j - coordU F₁ j * coordU F₂ i =
        Dpoly m * (coordU F₃ i * coordU F₂ j - coordU F₃ j * coordU F₂ i) := by
      apply Polynomial.coe_injective
      simp only [Polynomial.coe_sub, Polynomial.coe_mul]
      linear_combination (coordU F₂ j : PowerSeries ℂ) * hrel i hi -
        (coordU F₂ i : PowerSeries ℂ) * hrel j hj
    have h1 := congrArg (Polynomial.eval u₀) hp
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, hD, zero_mul] at h1
    linear_combination h1
  -- 在 `T³ + u₀T − u₀` 的两个根处取值
  refine ⟨K₁, K₂, fun ξ η hξ hη => ?_⟩
  rw [← hF₁, ← hF₂, eval_eq_coords_at hξ F₁, eval_eq_coords_at hη F₂, eval_eq_coords_at hη F₁,
    eval_eq_coords_at hξ F₂]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  have m01 := hminor 0 1 (by norm_num) (by norm_num)
  have m02 := hminor 0 2 (by norm_num) (by norm_num)
  have m12 := hminor 1 2 (by norm_num) (by norm_num)
  linear_combination (η - ξ) * m01 + (η ^ 2 - ξ ^ 2) * m02 + (ξ * η ^ 2 - ξ ^ 2 * η) * m12

/-! ## 2. 以上升结尾的序列 -/

/-- `U^↑_k(m)`：`H_k(m)` 中以上升结尾（最后两项 `h_{k−1} < h_k`）的序列个数。 -/
def NUp (k m : ℕ) : ℕ := ((L k m).filter fun l => endsAsc l = true).card

theorem NUp_add_NA (k m : ℕ) : NUp k m + NA k m = U k m := by
  have h := Finset.card_filter_add_card_filter_not (s := L k m) (fun l => endsAsc l = true)
  have e : (L k m).filter (fun l => ¬ endsAsc l = true) = (L k m).filter (fun l => endsAsc l = false) :=
    Finset.filter_congr fun l _ => by simp
  rw [e] at h
  exact h

/-- `G^↑_m = Σ_k U^↑_k(m) x^k`。 -/
noncomputable def GUp (m : ℕ) : PowerSeries ℂ := PowerSeries.mk fun k => (NUp k m : ℂ)

/-- `P_m·G^↑_m = W_m − 1`，即 `G^↑_m = (W_m − 1)/P_m`（论文定理 6.2 证明的第一句）。 -/
theorem P_mul_GUp (m : ℕ) :
    (Ppoly ℂ m : PowerSeries ℂ) * GUp m = ((Wpoly ℂ m - 1 : ℂ[X]) : PowerSeries ℂ) := by
  have hNA : (Ppoly ℂ m : PowerSeries ℂ) * PowerSeries.mk (fun k => (NA k m : ℂ)) = 1 := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) (P_mul_NAser m)
    rw [map_mul, ← Polynomial.polynomial_map_coe, Ppoly_map, map_one] at h
    have hN : PowerSeries.map (algebraMap ℚ ℂ) (NAser m) = PowerSeries.mk (fun k => (NA k m : ℂ)) := by
      ext k
      simp [NAser, PowerSeries.coeff_map]
    rwa [hN] at h
  have hsplit : GUp m = Gc m - PowerSeries.mk (fun k => (NA k m : ℂ)) := by
    ext k
    simp only [GUp, Gc, map_sub, PowerSeries.coeff_mk]
    rw [← NUp_add_NA k m]
    push_cast
    ring
  rw [hsplit, mul_sub, P_mul_Gc, hNA, Polynomial.coe_sub, Polynomial.coe_one]

/-! ## 3. 纤维 `u = 1/2`：`b_2 = 1 − x − 2x³` 的根 -/

theorem Dpoly_eval_half {m : ℕ} (hm : 2 ≤ m) : (Dpoly m).eval (1 / 2) = 0 := by
  rw [Dpoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (i := 2) (Finset.mem_range.2 (by omega)) (by norm_num)

/-- `b_2(η) = 0`（写成 `η³ + η/2 − 1/2 = 0`）且 `m ≥ 2` 时 `W_m(η) − 1 = η⁵(4 − 2η)`。 -/
theorem eval_Wpoly_sub_one_root {m : ℕ} (hm : 2 ≤ m) {η : ℂ} (hη : η ^ 3 + 1 / 2 * η - 1 / 2 = 0) :
    (Wpoly ℂ m - 1).eval η = η ^ 5 * (4 - 2 * η) := by
  have hb2 : (bpoly ℂ 2).eval η = 0 := by
    simp only [bpoly, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow]
    push_cast
    linear_combination -2 * hη
  rw [Wpoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum, Finset.sum_eq_add 1 2 (by norm_num)]
  · have h0 : (Ppoly ℂ (1 - 1)).eval η = 1 - η := by
      rw [Nat.sub_self, Ppoly, zero_add, Finset.prod_range_one, bpoly]
      simp
    have h1 : (Ppoly ℂ (2 - 1)).eval η = (1 - η) * (1 - η - η ^ 3) := by
      rw [show 2 - 1 = 1 from rfl, Ppoly, Polynomial.eval_prod, Finset.prod_range_succ, Finset.prod_range_one]
      simp only [bpoly]
      simp
    rw [Polynomial.eval_mul, Polynomial.eval_C, h0, Polynomial.eval_mul, Polynomial.eval_C, h1]
    push_cast
    linear_combination (4 * η ^ 3 - 6 * η ^ 2) * hη
  · intro j hj hj12
    obtain ⟨hj1, hj2⟩ := hj12
    rw [Finset.mem_Icc] at hj
    rw [Polynomial.eval_mul, Ppoly, Polynomial.eval_prod,
      Finset.prod_eq_zero (i := 2) (Finset.mem_range.2 (by omega)) hb2, mul_zero]
  · intro h1
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h1
  · intro h2
    exact absurd (Finset.mem_Icc.2 ⟨by norm_num, hm⟩) h2

/-! ## 4. `2X³ + X − 1` 的三个根与 `17` 进赋值 -/

theorem cubic_roots_half :
    ∃ a b c : ℂ, ∀ z : ℂ, z ^ 3 + 1 / 2 * z - 1 / 2 = (z - a) * (z - b) * (z - c) := by
  set f : ℂ[X] := Polynomial.X ^ 3 +
    (Polynomial.C (1 / 2 : ℂ) * Polynomial.X - Polynomial.C (1 / 2 : ℂ)) with hf
  have hlow : (Polynomial.C (1 / 2 : ℂ) * Polynomial.X - Polynomial.C (1 / 2 : ℂ)).degree < 3 := by
    have h1 : (Polynomial.C (1 / 2 : ℂ) * Polynomial.X - Polynomial.C (1 / 2 : ℂ)).degree ≤ 1 :=
      (Polynomial.degree_sub_le _ _).trans
        (max_le (Polynomial.degree_C_mul_X_le _) (Polynomial.degree_C_le.trans zero_le_one))
    exact h1.trans_lt (by norm_num)
  have hmonic : f.Monic := Polynomial.monic_X_pow_add hlow
  have hdeg : f.natDegree = 3 := by
    rw [hf, Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact hlow),
      Polynomial.natDegree_X_pow]
  have hcard : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.1 (IsAlgClosed.splits f)
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.1 (hcard.trans hdeg)
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul, habc] at hprod
  refine ⟨a, b, c, fun z => ?_⟩
  have := congrArg (Polynomial.eval z) hprod
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, hf, Polynomial.eval_add, Polynomial.eval_pow] at this
  linear_combination -this

theorem powsum_rat_half {a b c : ℂ} (ha : a ^ 3 + 1 / 2 * a - 1 / 2 = 0) (hb : b ^ 3 + 1 / 2 * b - 1 / 2 = 0)
    (hc : c ^ 3 + 1 / 2 * c - 1 / 2 = 0) (h1 : a + b + c = 0) (h2 : a * b + b * c + c * a = 1 / 2) :
    ∀ n : ℕ, ∃ q : ℚ, a ^ n + b ^ n + c ^ n = q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · exact ⟨3, by norm_num⟩
    · exact ⟨0, by push_cast; linear_combination h1⟩
    · exact ⟨-1, by push_cast; linear_combination (a + b + c) * h1 - 2 * h2⟩
    · obtain ⟨q1, hq1⟩ := ih n (by omega)
      obtain ⟨q2, hq2⟩ := ih (n + 1) (by omega)
      refine ⟨q1 / 2 - q2 / 2, ?_⟩
      push_cast
      linear_combination a ^ n * ha + b ^ n * hb + c ^ n * hc + 1 / 2 * hq1 - 1 / 2 * hq2

/-- `q³·2^a = 459·2^b` 没有有理解（`459 = 27·17`，两边的 `17` 进赋值是 `3·v(q)` 与 `1`）。 -/
theorem not_rat_cube_17 (q : ℚ) (a b : ℕ) : q ^ 3 * 2 ^ a ≠ 459 * 2 ^ b := by
  intro h
  have hq : q ≠ 0 := by
    rintro rfl
    have h0 : (459 : ℚ) * 2 ^ b ≠ 0 := by positivity
    exact h0 (by rw [← h]; ring)
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have h2 : padicValRat 17 2 = 0 := by
    have e := padicValRat.of_nat (p := 17) (n := 2)
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 17 ∣ 2)] at e
    exact_mod_cast e
  have h27 : padicValRat 17 27 = 0 := by
    have e := padicValRat.of_nat (p := 17) (n := 27)
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 17 ∣ 27)] at e
    exact_mod_cast e
  have h17 : padicValRat 17 17 = 1 := by
    have e := padicValRat.self (p := 17) (by norm_num)
    exact_mod_cast e
  have hL : padicValRat 17 (q ^ 3 * 2 ^ a) = 3 * padicValRat 17 q := by
    rw [padicValRat.mul (q := q ^ 3) (r := 2 ^ a) (pow_ne_zero 3 hq) (pow_ne_zero a two_ne_zero),
      padicValRat.pow, padicValRat.pow, h2]
    push_cast
    ring
  have hR : padicValRat 17 (459 * 2 ^ b) = 1 := by
    rw [padicValRat.mul (q := 459) (r := 2 ^ b) (by norm_num) (pow_ne_zero b two_ne_zero), padicValRat.pow, h2,
      show (459 : ℚ) = 17 * 27 by norm_num, padicValRat.mul (q := 17) (r := 27) (by norm_num) (by norm_num),
      h17, h27]
    ring
  have hv := congrArg (padicValRat 17) h
  rw [hL, hR] at hv
  omega

/-- `2X³ + X − 1` 的根上 `η^p(2 − η) = λ·η^r` 不可能对所有根成立：三个根相乘得 `λ³ = 17·2^{r−p−1}`，而 `λ` 是某个
有理系数多项式在每个根处的值，`3λ` 是有理数。 -/
theorem no_common_value_b2 (p r : ℕ) (lam : ℂ) :
    ¬ ∀ η : ℂ, η ^ 3 + 1 / 2 * η - 1 / 2 = 0 → η ^ p * (2 - η) = lam * η ^ r := by
  intro H
  obtain ⟨a, b, c, hz⟩ := cubic_roots_half
  have ha : a ^ 3 + 1 / 2 * a - 1 / 2 = 0 := by rw [hz a]; ring
  have hb : b ^ 3 + 1 / 2 * b - 1 / 2 = 0 := by rw [hz b]; ring
  have hc : c ^ 3 + 1 / 2 * c - 1 / 2 = 0 := by rw [hz c]; ring
  have z0 := hz 0
  have z1 := hz 1
  have zm := hz (-1)
  have z2 := hz 2
  have e1 : a + b + c = 0 := by linear_combination (1 / 2 : ℂ) * z1 + (1 / 2 : ℂ) * zm - z0
  have e2 : a * b + b * c + c * a = 1 / 2 := by linear_combination (-1 / 2 : ℂ) * z1 + (1 / 2 : ℂ) * zm
  have e3 : a * b * c = 1 / 2 := by linear_combination z0
  have e4 : (2 - a) * (2 - b) * (2 - c) = 17 / 2 := by linear_combination -z2
  have hs := powsum_rat_half ha hb hc e1 e2
  have Ha := H a ha
  have Hb := H b hb
  have Hc := H c hc
  have hlam3 : (a * b * c) ^ p * ((2 - a) * (2 - b) * (2 - c)) = lam ^ 3 * (a * b * c) ^ r := by
    calc _ = (a ^ p * (2 - a)) * (b ^ p * (2 - b)) * (c ^ p * (2 - c)) := by ring
      _ = (lam * a ^ r) * (lam * b ^ r) * (lam * c ^ r) := by rw [Ha, Hb, Hc]
      _ = _ := by ring
  rw [e3, e4] at hlam3
  -- `λ` 是某个有理系数多项式在每个根处的值（`η⁻¹ = 2η² + 1`）
  obtain ⟨h, hh⟩ : ∃ h : ℚ[X], ∀ x : ℂ, x ^ 3 + 1 / 2 * x - 1 / 2 = 0 → x ^ p * (2 - x) = lam * x ^ r →
      h.eval₂ (algebraMap ℚ ℂ) x = lam := by
    rcases le_or_gt r p with hrp | hrp
    · refine ⟨Polynomial.X ^ (p - r) * (Polynomial.C 2 - Polynomial.X), fun x hx Hx => ?_⟩
      have hx0 : x ≠ 0 := fun h => by rw [h] at hx; norm_num at hx
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub,
        map_ofNat, Polynomial.eval₂_ofNat]
      have e : x ^ p = x ^ (p - r) * x ^ r := by rw [← pow_add, Nat.sub_add_cancel hrp]
      rw [e] at Hx
      have hxr : x ^ r ≠ 0 := pow_ne_zero _ hx0
      apply mul_right_cancel₀ hxr
      linear_combination Hx
    · refine ⟨(Polynomial.C 2 * Polynomial.X ^ 2 + 1) ^ (r - p) * (Polynomial.C 2 - Polynomial.X),
        fun x hx Hx => ?_⟩
      have hx0 : x ≠ 0 := fun h => by rw [h] at hx; norm_num at hx
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_one, map_ofNat, Polynomial.eval₂_ofNat]
      have e : x ^ r = x ^ p * x ^ (r - p) := by rw [← pow_add, Nat.add_sub_cancel' hrp.le]
      rw [e] at Hx
      have hxp : x ^ p ≠ 0 := pow_ne_zero _ hx0
      have H1 : 2 - x = lam * x ^ (r - p) := by
        apply mul_left_cancel₀ hxp
        linear_combination Hx
      have H2 : (x * (2 * x ^ 2 + 1)) ^ (r - p) = 1 := by
        rw [show x * (2 * x ^ 2 + 1) = 1 by linear_combination 2 * hx, one_pow]
      calc (2 * x ^ 2 + 1) ^ (r - p) * (2 - x) = (2 * x ^ 2 + 1) ^ (r - p) * (lam * x ^ (r - p)) := by
            rw [H1]
        _ = lam * (x * (2 * x ^ 2 + 1)) ^ (r - p) := by rw [mul_pow]; ring
        _ = lam := by rw [H2, mul_one]
  obtain ⟨q, hq⟩ := sum_eval_rat hs h
  rw [hh a ha Ha, hh b hb Hb, hh c hc Hc] at hq
  have e1' : ((1 : ℂ) / 2) ^ p * 2 ^ p = 1 := by rw [← mul_pow]; norm_num
  have e2' : ((1 : ℂ) / 2) ^ r * 2 ^ r = 1 := by rw [← mul_pow]; norm_num
  have key : (q : ℂ) ^ 3 * 2 ^ (p + 1) = 459 * 2 ^ r := by
    rw [← hq]
    linear_combination (-27 * 2 ^ (p + 1) * 2 ^ r : ℂ) * hlam3 + (27 * 17 * 2 ^ r : ℂ) * e1' -
      (27 * lam ^ 3 * 2 ^ (p + 1)) * e2'
  exact not_rat_cube_17 q (p + 1) r (by exact_mod_cast key)

/-! ## 5. 定理 6.2 -/

/-- **论文定理 6.2**：`m ≥ 2` 时 `U^↑_k(m)`（以上升结尾的序列个数）不能对所有 `k ≥ k₀` 写成
`Σ_s A(s)·C(k+c−2s, m+s+d)`（整数 `c, d`，复数 `A(s)` 与 `k` 无关，约定同 `thm_S`）。 -/
theorem thm_Spart {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ (c d : ℤ) (k₀ : ℕ) (A : ℤ → ℂ), ∀ k : ℕ, k₀ ≤ k →
      (NUp k m : ℂ) = ∑ᶠ s : ℤ, A s * (binomZ (k + c - 2 * s) (m + s + d) : ℂ) := by
  rintro ⟨c, d, k₀, A, hA⟩
  obtain ⟨K₁, K₂, hcross⟩ := single_sum_cross (c := c) (d := d) (k₀ := k₀) (A := A) (P_mul_GUp m)
    (fun k hk => by simp only [GUp, PowerSeries.coeff_mk]; exact hA k hk) (Dpoly_eval_half hm)
  obtain ⟨a, b, c', hz⟩ := cubic_roots_half
  have ha : a ^ 3 + 1 / 2 * a - 1 / 2 = 0 := by rw [hz a]; ring
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; norm_num at ha
  -- 在 `b_2` 的根 `η` 处：`F₁(η) = 2η^{K₁+5}(2 − η)`，`F₂(η) = 2^m η^{K₂+3m}`
  have hF₁ : ∀ η : ℂ, η ^ 3 + 1 / 2 * η - 1 / 2 = 0 →
      (Polynomial.X ^ K₁ * (Wpoly ℂ m - 1)).eval η = 2 * (η ^ (K₁ + 5) * (2 - η)) := by
    intro η hη
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_Wpoly_sub_one_root hm hη]
    ring
  have hF₂ : ∀ η : ℂ, η ^ 3 + 1 / 2 * η - 1 / 2 = 0 →
      ((Polynomial.X ^ K₂ * (1 - Polynomial.X) ^ m : ℂ[X])).eval η = 2 ^ m * η ^ (K₂ + 3 * m) := by
    intro η hη
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_one]
    rw [show 1 - η = 2 * η ^ 3 by linear_combination -2 * hη, mul_pow, ← pow_mul, pow_add]
    ring
  obtain ⟨F1a, hF1a⟩ : ∃ x : ℂ, x = (Polynomial.X ^ K₁ * (Wpoly ℂ m - 1)).eval a := ⟨_, rfl⟩
  obtain ⟨F2a, hF2a⟩ : ∃ x : ℂ, x = ((Polynomial.X ^ K₂ * (1 - Polynomial.X) ^ m : ℂ[X])).eval a := ⟨_, rfl⟩
  have hF2a0 : (2 : ℂ) * F2a ≠ 0 := by
    rw [hF2a, hF₂ a ha]
    exact mul_ne_zero two_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ ha0))
  apply no_common_value_b2 (K₁ + 5) (K₂ + 3 * m) (F1a * 2 ^ m / (2 * F2a))
  intro η hη
  have h := hcross η a hη ha
  rw [hF₁ η hη, hF₂ η hη, ← hF1a, ← hF2a] at h
  rw [div_mul_eq_mul_div, eq_div_iff hF2a0]
  linear_combination h

end

end A207123
