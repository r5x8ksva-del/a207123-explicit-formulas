import A207123.NonDFinite
import A207123.Poly

/-!
# 论文定理 3.2(2)：`U_k(m)` 按 `(y − 1)·∏_{i=1}^{m}(y³ − y² − i)` 的根展开

论文定理 3.2(2)：对每个 `m ≥ 0`，有非零的数 `α_m(σ)`，使 `U_k(m) = Σ_σ α_m(σ)·σ^k` 对一切 `k ≥ 0` 成立，`σ` 取遍
`(y − 1)·∏_{i=1}^{m}(y³ − y² − i)` 的 `3m + 1` 个根；若 `σ` 是 `y³ − y² − j` 的根（`1 ≤ j < m`），或 `σ = 1`、`j = 0`，
则 `α_m(σ) = α_j(σ)·(−σ³)^{m−j}/(m − j)!`。

* `Qpoly m`：`(X − 1)·∏_{i=1}^{m}(X³ − X² − i)`（ℂ 上）；`sig m`：它的根的集合（`Finset`）。
* `card_sig`：`sig m` 有 `3m + 1` 个元素，即这些根两两不同。
* `Ppoly_eq_prod_sig`：`P_m(x) = ∏_σ (1 − σx)`（`P_m` 是 `Q_m` 的反转）。
* `alpha m σ = W_m(1/σ) / ∏_{τ ≠ σ}(1 − τ/σ)`：`G_m = W_m/P_m` 的部分分式系数。
* `thm_asym_two`（`U_eq_sum_alpha`、`alpha_ne_zero`）：展开式与系数非零；`alpha_unique`：系数由 `U` 唯一确定。
* `alpha_eq`：第二句（条件写成 `σ ≠ 0`、`σ³ − σ² = j`；`j = 0` 时就是 `σ = 1`）。

证明：`W_m` 与 `Σ_σ α_m(σ)·∏_{τ≠σ}(1 − τx)` 的次数都 ≤ 3m，在 `P_m` 的 `3m + 1` 个根 `1/σ` 处取值相同，所以相等；
`P_m = (1 − σx)·∏_{τ≠σ}(1 − τx)`，`(1 − σx)·Σ_k σ^k x^k = 1`，于是在幂级数里 `P_m·G_m = W_m = P_m·Σ_σ α_m(σ)/(1 − σx)`，
约去 `P_m`。`α_m(σ) ≠ 0` 因为 `W_m`、`P_m` 互素（`simple_root_Ppoly`）。第二句：`W_{m+1} = W_m + (m+1)x²P_m`
在 `1/σ` 处等于 `W_m`，余因子多乘一个 `b_{m+1}(1/σ) = (j − m − 1)/σ³`。
-/

open Polynomial Finset

namespace A207123

/-- `Q_m(y) = (y − 1)·∏_{i=1}^{m}(y³ − y² − i)`（ℂ 上）。 -/
noncomputable def Qpoly (m : ℕ) : ℂ[X] := (X - 1) * ∏ i ∈ Icc 1 m, (X ^ 3 - X ^ 2 - C (i : ℂ))

/-- `Q_m` 的根的集合。 -/
noncomputable def sig (m : ℕ) : Finset ℂ := (Qpoly m).roots.toFinset

/-- 辅助引理（定理 3.2(2)）：`Q_{m+1} = Q_m·(X³ − X² − (m + 1))`。 -/
theorem Qpoly_succ (m : ℕ) :
    Qpoly (m + 1) = Qpoly m * (X ^ 3 - X ^ 2 - C ((m + 1 : ℕ) : ℂ)) := by
  rw [Qpoly, Qpoly, prod_Icc_succ_top (by omega : 1 ≤ m + 1), mul_assoc]

/-- 辅助引理（定理 3.2(2)）：`σ ≠ 0` 时 `b_i(1/σ)·σ³ = σ³ − σ² − i`。 -/
theorem eval_bpoly_inv (i : ℕ) {σ : ℂ} (hσ : σ ≠ 0) :
    (bpoly ℂ i).eval σ⁻¹ * σ ^ 3 = σ ^ 3 - σ ^ 2 - i := by
  have h : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  rw [eval_bpoly]
  linear_combination (-(σ ^ 2 + (i : ℂ) * (σ⁻¹ ^ 2 * σ ^ 2 + σ⁻¹ * σ + 1))) * h

/-- 辅助引理（定理 3.2(2)）：`σ ≠ 0` 时 `P_m(1/σ)·σ^{3m+1} = Q_m(σ)`（`P_m` 是 `Q_m` 的反转）。 -/
theorem eval_Ppoly_inv (m : ℕ) {σ : ℂ} (hσ : σ ≠ 0) :
    (Ppoly ℂ m).eval σ⁻¹ * σ ^ (3 * m + 1) = (Qpoly m).eval σ := by
  induction m with
  | zero =>
    rw [Ppoly_zero, eval_bpoly, Qpoly, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), prod_empty,
      mul_one]
    simp only [eval_sub, eval_X, eval_one, Nat.cast_zero, zero_mul, sub_zero, mul_zero, zero_add, pow_one]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hσ]
  | succ m ih =>
    rw [Ppoly_succ, Qpoly_succ, eval_mul, eval_mul, ← ih]
    simp only [eval_sub, eval_pow, eval_X, eval_C]
    rw [← eval_bpoly_inv (m + 1) hσ]
    ring

/-- 辅助引理（定理 3.2(2)）：`Q_m(0) ≠ 0`。 -/
theorem eval_zero_Qpoly_ne (m : ℕ) : (Qpoly m).eval 0 ≠ 0 := by
  rw [Qpoly, eval_mul, eval_prod]
  simp only [eval_sub, eval_X, eval_one, eval_pow, eval_C]
  refine mul_ne_zero (by norm_num) (prod_ne_zero_iff.mpr fun i hi => ?_)
  rw [mem_Icc] at hi
  have hi0 : (i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro h
  exact hi0 (by linear_combination -h)

/-- 辅助引理（定理 3.2(2)）：`Q_m ≠ 0`。 -/
theorem Qpoly_ne_zero (m : ℕ) : Qpoly m ≠ 0 := fun h => eval_zero_Qpoly_ne m (by rw [h, eval_zero])

/-- 辅助引理（定理 3.2(2)）：`P_m(0) = 1`。 -/
theorem eval_zero_Ppoly (m : ℕ) : (Ppoly ℂ m).eval 0 = 1 := by
  rw [Ppoly, eval_prod]
  exact prod_eq_one fun i _ => by rw [eval_bpoly]; ring

/-- 辅助引理（定理 3.2(2)）：`σ` 是 `Q_m` 的根，当且仅当 `σ ≠ 0` 且 `1/σ` 是 `P_m` 的根。 -/
theorem mem_sig {m : ℕ} {σ : ℂ} : σ ∈ sig m ↔ σ ≠ 0 ∧ (Ppoly ℂ m).eval σ⁻¹ = 0 := by
  rw [sig, Multiset.mem_toFinset, mem_roots (Qpoly_ne_zero m), IsRoot.def]
  constructor
  · intro h
    have hσ : σ ≠ 0 := by
      rintro rfl
      exact eval_zero_Qpoly_ne m h
    refine ⟨hσ, ?_⟩
    have h2 := eval_Ppoly_inv m hσ
    rw [h] at h2
    exact (mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ hσ)
  · rintro ⟨hσ, h⟩
    rw [← eval_Ppoly_inv m hσ, h, zero_mul]

/-- 辅助引理（定理 3.2(2)）：`sig m` 就是 `Q_m` 的根（定义的改写）。 -/
theorem mem_sig_iff_isRoot {m : ℕ} {σ : ℂ} : σ ∈ sig m ↔ (Qpoly m).IsRoot σ := by
  rw [sig, Multiset.mem_toFinset, mem_roots (Qpoly_ne_zero m)]

/-- 辅助引理（定理 3.2(2)）：`σ ≠ 0`、`σ³ − σ² = j` 时 `σ` 是 `j ≤ m` 的每个 `Q_m` 的根。 -/
theorem mem_sig_of_cubic {j m : ℕ} (hjm : j ≤ m) {σ : ℂ} (hσ : σ ≠ 0) (hσj : σ ^ 3 - σ ^ 2 = j) :
    σ ∈ sig m := by
  refine mem_sig.mpr ⟨hσ, ?_⟩
  rw [Ppoly, eval_prod]
  refine prod_eq_zero (mem_range.mpr (by omega : j < m + 1)) ?_
  have h := eval_bpoly_inv j hσ
  rw [hσj, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hσ)

/-- 辅助引理（定理 3.2(2)）：`P_m` 在 ℂ 上可分。 -/
theorem separable_Ppoly_C (m : ℕ) : (Ppoly ℂ m).Separable := by
  rw [← Ppoly_map ℚ (algebraMap ℚ ℂ) m]
  exact (separable_Ppoly m).map

/-- 辅助引理（定理 3.2(2)）：`P_m` 在 ℂ 上的次数是 `3m + 1`。 -/
theorem natDegree_Ppoly_C (m : ℕ) : (Ppoly ℂ m).natDegree = 3 * m + 1 := by
  rw [← Ppoly_map ℚ (algebraMap ℚ ℂ) m, natDegree_map, natDegree_P]

/-- 辅助引理（定理 3.2(2)）：`P_m` 在 ℂ 上有 `3m + 1` 个两两不同的根。 -/
theorem card_roots_toFinset_Ppoly (m : ℕ) : #((Ppoly ℂ m).roots.toFinset) = 3 * m + 1 := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (separable_Ppoly_C m)),
    IsAlgClosed.card_roots_eq_natDegree, natDegree_Ppoly_C]

/-- 辅助引理（定理 3.2(2)）：`sig m` 是 `P_m` 的根的倒数的集合。 -/
theorem sig_eq_image (m : ℕ) : sig m = (Ppoly ℂ m).roots.toFinset.image (·⁻¹) := by
  have hP : Ppoly ℂ m ≠ 0 := (separable_Ppoly_C m).ne_zero
  ext σ
  rw [mem_sig, mem_image]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨σ⁻¹, ?_, inv_inv σ⟩
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def]
    exact h
  · rintro ⟨z, hz, rfl⟩
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def] at hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [eval_zero_Ppoly] at hz
      exact one_ne_zero hz
    refine ⟨inv_ne_zero hz0, ?_⟩
    simpa only [inv_inv] using hz

/-- **定理 3.2(2) 的一部分**：`Q_m` 有 `3m + 1` 个两两不同的根。 -/
theorem card_sig (m : ℕ) : #(sig m) = 3 * m + 1 := by
  rw [sig_eq_image, card_image_of_injective _ inv_injective, card_roots_toFinset_Ppoly]

/-- 辅助引理（定理 3.2(2)）：`1 − τx` 的次数 ≤ 1。 -/
theorem natDegree_one_sub_C_mul_X_le (τ : ℂ) : (1 - C τ * X : ℂ[X]).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans
    (max_le (by rw [natDegree_one]; omega) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

/-- 辅助引理（定理 3.2(2)）：`P_m(x) = ∏_σ (1 − σx)`，`σ` 取遍 `Q_m` 的根。 -/
theorem Ppoly_eq_prod_sig (m : ℕ) : Ppoly ℂ m = ∏ σ ∈ sig m, (1 - C σ * X) := by
  have hP : Ppoly ℂ m ≠ 0 := (separable_Ppoly_C m).ne_zero
  have h0 : (0 : ℂ) ∉ (Ppoly ℂ m).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_zero_Ppoly]
    exact one_ne_zero
  have hcard : #(insert (0 : ℂ) (Ppoly ℂ m).roots.toFinset) = 3 * m + 2 := by
    rw [card_insert_of_notMem h0, card_roots_toFinset_Ppoly]
  have hdeg : (∏ σ ∈ sig m, (1 - C σ * X) : ℂ[X]).natDegree ≤ 3 * m + 1 := by
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ σ ∈ sig m, (1 - C σ * X : ℂ[X]).natDegree ≤ ∑ _σ ∈ sig m, 1 :=
          sum_le_sum fun σ _ => natDegree_one_sub_C_mul_X_le σ
      _ = 3 * m + 1 := by rw [sum_const, smul_eq_mul, mul_one, card_sig]
  refine eq_of_degrees_lt_of_eval_finset_eq (insert (0 : ℂ) (Ppoly ℂ m).roots.toFinset) ?_ ?_ ?_
  · rw [hcard]
    refine degree_le_natDegree.trans_lt ?_
    rw [natDegree_Ppoly_C]
    exact_mod_cast (by omega : 3 * m + 1 < 3 * m + 2)
  · rw [hcard]
    refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast (by omega : (∏ σ ∈ sig m, (1 - C σ * X) : ℂ[X]).natDegree < 3 * m + 2)
  · intro x hx
    rw [mem_insert] at hx
    rw [eval_prod]
    rcases hx with rfl | hx
    · rw [eval_zero_Ppoly]
      symm
      exact prod_eq_one fun σ _ => by simp
    · rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def] at hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [eval_zero_Ppoly] at hx
        exact one_ne_zero hx
      have hmem : x⁻¹ ∈ sig m := mem_sig.mpr ⟨inv_ne_zero hx0, by rw [inv_inv]; exact hx⟩
      rw [hx]
      symm
      exact prod_eq_zero hmem (by simp [inv_mul_cancel₀ hx0])

/-- 余因子 `∏_{τ ≠ σ}(1 − τx)`（`τ` 取遍 `Q_m` 的其余根）。 -/
noncomputable def cof (m : ℕ) (σ : ℂ) : ℂ[X] := ∏ τ ∈ (sig m).erase σ, (1 - C τ * X)

/-- 定理 3.2(2) 的系数：`α_m(σ) = W_m(1/σ) / ∏_{τ ≠ σ}(1 − τ/σ)`。 -/
noncomputable def alpha (m : ℕ) (σ : ℂ) : ℂ := (Wpoly ℂ m).eval σ⁻¹ / (cof m σ).eval σ⁻¹

/-- 辅助引理（定理 3.2(2)）：`σ` 是 `Q_m` 的根时 `P_m = (1 − σx)·∏_{τ≠σ}(1 − τx)`。 -/
theorem Ppoly_eq_mul_cof {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) : Ppoly ℂ m = (1 - C σ * X) * cof m σ := by
  rw [Ppoly_eq_prod_sig, cof, mul_prod_erase (sig m) (fun τ => (1 - C τ * X : ℂ[X])) hσ]

/-- 辅助引理（定理 3.2(2)）：余因子的次数不超过其余根的个数。 -/
theorem natDegree_cof_le (m : ℕ) (σ : ℂ) : (cof m σ).natDegree ≤ #((sig m).erase σ) := by
  rw [cof]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ τ ∈ (sig m).erase σ, (1 - C τ * X : ℂ[X]).natDegree ≤ ∑ _τ ∈ (sig m).erase σ, 1 :=
        sum_le_sum fun τ _ => natDegree_one_sub_C_mul_X_le τ
    _ = #((sig m).erase σ) := by rw [sum_const, smul_eq_mul, mul_one]

/-- 辅助引理（定理 3.2(2)）：`∏_{τ ≠ σ}(1 − τ/σ) ≠ 0`。 -/
theorem eval_cof_ne_zero {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) : (cof m σ).eval σ⁻¹ ≠ 0 := by
  have hσ0 : σ ≠ 0 := (mem_sig.mp hσ).1
  rw [cof, eval_prod]
  refine prod_ne_zero_iff.mpr fun τ hτ => ?_
  rw [mem_erase] at hτ
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
  intro h
  apply hτ.1
  have h1 : τ * σ⁻¹ = 1 := by linear_combination -h
  calc τ = τ * σ⁻¹ * σ := by rw [mul_assoc, inv_mul_cancel₀ hσ0, mul_one]
    _ = σ := by rw [h1, one_mul]

/-- 辅助引理（定理 3.2(2)）：`Σ_σ a(σ)·∏_{τ≠σ}(1 − τx)` 在 `x = 1/σ₀` 处只剩 `σ = σ₀` 一项。 -/
theorem eval_sum_cof (m : ℕ) (a : ℂ → ℂ) {σ₀ : ℂ} (h0 : σ₀ ∈ sig m) :
    (∑ σ ∈ sig m, C (a σ) * cof m σ).eval σ₀⁻¹ = a σ₀ * (cof m σ₀).eval σ₀⁻¹ := by
  have hσ0 : σ₀ ≠ 0 := (mem_sig.mp h0).1
  rw [eval_finsetSum, sum_eq_single σ₀]
  · rw [eval_mul, eval_C]
  · intro σ _ hne
    rw [eval_mul, cof, eval_prod]
    refine mul_eq_zero_of_right _ (prod_eq_zero (mem_erase.mpr ⟨Ne.symm hne, h0⟩) ?_)
    simp [mul_inv_cancel₀ hσ0]
  · intro h
    exact absurd h0 h

/-- 辅助引理（定理 3.2(2)，部分分式）：`W_m = Σ_σ α_m(σ)·∏_{τ≠σ}(1 − τx)`。 -/
theorem W_eq_sum_alpha (m : ℕ) : Wpoly ℂ m = ∑ σ ∈ sig m, C (alpha m σ) * cof m σ := by
  have hcard : #((sig m).image (·⁻¹)) = 3 * m + 1 := by
    rw [card_image_of_injective _ inv_injective, card_sig]
  have hW : (Wpoly ℂ m).natDegree ≤ 3 * m := by
    rw [← Wpoly_map ℚ (algebraMap ℚ ℂ) m, natDegree_map]
    exact natDegree_W_le m
  have hS : (∑ σ ∈ sig m, C (alpha m σ) * cof m σ).natDegree ≤ 3 * m := by
    refine natDegree_sum_le_of_forall_le _ _ fun σ hσ => (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_cof_le m σ).trans ?_
    rw [card_erase_of_mem hσ, card_sig]
    omega
  refine eq_of_degrees_lt_of_eval_finset_eq ((sig m).image (·⁻¹)) ?_ ?_ ?_
  · rw [hcard]
    refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast (by omega : (Wpoly ℂ m).natDegree < 3 * m + 1)
  · rw [hcard]
    refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast (by omega : (∑ σ ∈ sig m, C (alpha m σ) * cof m σ).natDegree < 3 * m + 1)
  · intro x hx
    obtain ⟨σ₀, h0, rfl⟩ := mem_image.mp hx
    rw [eval_sum_cof m (alpha m) h0, alpha, div_mul_cancel₀ _ (eval_cof_ne_zero h0)]

/-- 几何级数 `Σ_k σ^k x^k`，即 `1/(1 − σx)`。 -/
noncomputable def geom (σ : ℂ) : PowerSeries ℂ := PowerSeries.mk fun k => σ ^ k

/-- 辅助引理（定理 3.2(2)）：`(1 − σx)·Σ_k σ^k x^k = 1`。 -/
theorem one_sub_mul_geom (σ : ℂ) : ((1 - C σ * X : ℂ[X]) : PowerSeries ℂ) * geom σ = 1 := by
  rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
    sub_mul, one_mul, mul_assoc]
  ext k
  rw [map_sub, PowerSeries.coeff_C_mul]
  rcases k with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, geom, PowerSeries.coeff_mk, pow_zero, mul_zero, sub_zero]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, geom, PowerSeries.coeff_mk, PowerSeries.coeff_mk, pow_succ]
    have h1 : PowerSeries.coeff (k + 1) (1 : PowerSeries ℂ) = 0 := by simp [PowerSeries.coeff_one]
    rw [h1]
    ring

/-- 辅助引理（定理 3.2(2)）：多项式 `Σ_σ C(a σ)·f σ` 作为幂级数。 -/
theorem coe_sum_C_mul (s : Finset ℂ) (a : ℂ → ℂ) (f : ℂ → ℂ[X]) :
    ((∑ σ ∈ s, C (a σ) * f σ : ℂ[X]) : PowerSeries ℂ) =
      ∑ σ ∈ s, PowerSeries.C (a σ) * (f σ : PowerSeries ℂ) := by
  have h := map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) (fun σ => C (a σ) * f σ) s
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C] at h
  exact h

/-- 辅助引理（定理 3.2(2)）：`Σ_σ a(σ)·∏_{τ≠σ}(1 − τx) = P_m·Σ_σ a(σ)/(1 − σx)`（幂级数）。 -/
theorem coe_sum_cof (m : ℕ) (a : ℂ → ℂ) :
    ((∑ σ ∈ sig m, C (a σ) * cof m σ : ℂ[X]) : PowerSeries ℂ) =
      (Ppoly ℂ m : PowerSeries ℂ) * ∑ σ ∈ sig m, PowerSeries.C (a σ) * geom σ := by
  rw [coe_sum_C_mul, mul_sum]
  refine sum_congr rfl fun σ hσ => ?_
  rw [Ppoly_eq_mul_cof hσ, Polynomial.coe_mul]
  calc PowerSeries.C (a σ) * (cof m σ : PowerSeries ℂ)
      = PowerSeries.C (a σ) * (cof m σ : PowerSeries ℂ) *
          (((1 - C σ * X : ℂ[X]) : PowerSeries ℂ) * geom σ) := by
        rw [one_sub_mul_geom, mul_one]
    _ = _ := by ring

/-- 辅助引理（定理 3.2(2)）：`G_m = Σ_σ α_m(σ)/(1 − σx)`（幂级数）。 -/
theorem Gc_eq_sum_geom (m : ℕ) : Gc m = ∑ σ ∈ sig m, PowerSeries.C (alpha m σ) * geom σ := by
  have hP : ((Ppoly ℂ m : ℂ[X]) : PowerSeries ℂ) ≠ 0 := by
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact (separable_Ppoly_C m).ne_zero
  refine mul_left_cancel₀ hP ?_
  rw [P_mul_Gc, ← coe_sum_cof m (alpha m), ← W_eq_sum_alpha m]

/-- **定理 3.2(2)**（展开式）：对一切 `k ≥ 0`，`U_k(m) = Σ_σ α_m(σ)·σ^k`。 -/
theorem U_eq_sum_alpha (m k : ℕ) : (U k m : ℂ) = ∑ σ ∈ sig m, alpha m σ * σ ^ k := by
  have h := congrArg (PowerSeries.coeff k) (Gc_eq_sum_geom m)
  rw [Gc, PowerSeries.coeff_mk, map_sum] at h
  rw [h]
  refine sum_congr rfl fun σ _ => ?_
  rw [PowerSeries.coeff_C_mul, geom, PowerSeries.coeff_mk]

/-- **定理 3.2(2)**（系数非零）：`α_m(σ) ≠ 0`，因为 `W_m`、`P_m` 互素。 -/
theorem alpha_ne_zero {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) : alpha m σ ≠ 0 :=
  div_ne_zero (simple_root_Ppoly m σ⁻¹ (mem_sig.mp hσ).2).2 (eval_cof_ne_zero hσ)

/-- **定理 3.2(2)**（系数唯一）：若对一切 `k ≥ 0` 都有 `U_k(m) = Σ_σ β(σ)·σ^k`，则 `β = α_m`（在 `Q_m` 的根上）。 -/
theorem alpha_unique {m : ℕ} (β : ℂ → ℂ) (h : ∀ k : ℕ, (U k m : ℂ) = ∑ σ ∈ sig m, β σ * σ ^ k) :
    ∀ σ ∈ sig m, β σ = alpha m σ := by
  have hser : ∑ σ ∈ sig m, PowerSeries.C (β σ - alpha m σ) * geom σ = 0 := by
    ext k
    rw [map_sum, map_zero]
    simp only [PowerSeries.coeff_C_mul, geom, PowerSeries.coeff_mk, sub_mul, sum_sub_distrib]
    rw [← h k, ← U_eq_sum_alpha m k, sub_self]
  have hpoly : (∑ σ ∈ sig m, C (β σ - alpha m σ) * cof m σ : ℂ[X]) = 0 := by
    rw [← Polynomial.coe_eq_zero_iff, coe_sum_cof m (fun σ => β σ - alpha m σ), hser, mul_zero]
  intro σ hσ
  have h2 := congrArg (eval σ⁻¹) hpoly
  rw [eval_sum_cof m (fun σ => β σ - alpha m σ) hσ, eval_zero] at h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (eval_cof_ne_zero hσ))

/-- **定理 3.2(2)**（第一句）：`σ` 取遍 `Q_m` 的 `3m + 1` 个两两不同的根，系数 `α_m(σ)` 都不为 0，且对一切 `k ≥ 0`
有 `U_k(m) = Σ_σ α_m(σ)·σ^k`（系数由此唯一确定，见 `alpha_unique`）。 -/
theorem thm_asym_two (m : ℕ) :
    #(sig m) = 3 * m + 1 ∧ (∀ σ ∈ sig m, alpha m σ ≠ 0) ∧
      ∀ k : ℕ, (U k m : ℂ) = ∑ σ ∈ sig m, alpha m σ * σ ^ k :=
  ⟨card_sig m, fun _ hσ => alpha_ne_zero hσ, U_eq_sum_alpha m⟩

/-- 辅助引理（定理 3.2(2)）：`σ` 同为 `Q_m`、`Q_{m+1}` 的根时，余因子多乘一个 `b_{m+1}`。 -/
theorem cof_succ {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) (hσ' : σ ∈ sig (m + 1)) :
    cof (m + 1) σ = cof m σ * bpoly ℂ (m + 1) := by
  have hne : (1 - C σ * X : ℂ[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (eval 0) h
    simp at h2
  refine mul_left_cancel₀ hne ?_
  rw [← Ppoly_eq_mul_cof hσ', ← mul_assoc, ← Ppoly_eq_mul_cof hσ, Ppoly_succ]

/-- 辅助引理（定理 3.2(2) 第二句）：`σ ≠ 0`、`σ³ − σ² = j ≤ m` 时 `α_{m+1}(σ)·(m + 1 − j) = α_m(σ)·(−σ³)`。 -/
theorem alpha_succ {j m : ℕ} (hjm : j ≤ m) {σ : ℂ} (hσ0 : σ ≠ 0) (hσj : σ ^ 3 - σ ^ 2 = j) :
    alpha (m + 1) σ * ((m + 1 - j : ℕ) : ℂ) = alpha m σ * (-σ ^ 3) := by
  have hσm : σ ∈ sig m := mem_sig_of_cubic hjm hσ0 hσj
  have hσm1 : σ ∈ sig (m + 1) := mem_sig_of_cubic (by omega) hσ0 hσj
  have hW : (Wpoly ℂ (m + 1)).eval σ⁻¹ = (Wpoly ℂ m).eval σ⁻¹ := by
    simp only [Wpoly_succ, eval_add, eval_mul, (mem_sig.mp hσm).2, mul_zero, add_zero]
  have hB : ((m + 1 - j : ℕ) : ℂ) = -((bpoly ℂ (m + 1)).eval σ⁻¹ * σ ^ 3) := by
    rw [eval_bpoly_inv (m + 1) hσ0, hσj, Nat.cast_sub (by omega : j ≤ m + 1)]
    ring
  have hC : (cof m σ).eval σ⁻¹ ≠ 0 := eval_cof_ne_zero hσm
  have hB0 : (bpoly ℂ (m + 1)).eval σ⁻¹ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, neg_zero, Nat.cast_eq_zero] at hB
    omega
  rw [alpha, alpha, hW, cof_succ hσm hσm1, eval_mul, hB, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (mul_ne_zero hC hB0) hC]
  ring

/-- **定理 3.2(2)**（第二句）：若 `σ ≠ 0`、`σ³ − σ² = j`（`j ≥ 1` 时即 `σ` 是 `y³ − y² − j` 的根，`j = 0` 时即 `σ = 1`），
则对 `m ≥ j`，`α_m(σ) = α_j(σ)·(−σ³)^{m−j}/(m − j)!`。 -/
theorem alpha_eq {j m : ℕ} (hjm : j ≤ m) {σ : ℂ} (hσ0 : σ ≠ 0) (hσj : σ ^ 3 - σ ^ 2 = j) :
    alpha m σ = alpha j σ * (-σ ^ 3) ^ (m - j) / ((m - j).factorial : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjm
  clear hjm
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := alpha_succ (m := j + n) (by omega) hσ0 hσj
    have e1 : j + n + 1 - j = n + 1 := by omega
    have e2 : j + (n + 1) - j = n + 1 := by omega
    have e3 : j + n - j = n := by omega
    rw [e1] at h1
    rw [e3] at ih
    have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [e2, ← add_assoc, eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), Nat.factorial_succ,
      Nat.cast_mul, ← mul_assoc, h1, ih, div_mul_eq_mul_div, div_mul_cancel₀ _ hf]
    ring

end A207123
