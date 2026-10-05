import A207123.Recurrence

/-!
# `F` 的两条「非 D-finite」型结论（报告 T3.7(1) 的 ODE 部分、T3.7(2)）

**T3.7(2)**（`no_k_only_recurrence`）：设 `p_{ab} ∈ ℂ[k]`（`0 ≤ a ≤ A`，`0 ≤ b ≤ B`）不全为 0，则不存在
`k0, m0` 使 `Σ_{a,b} p_{ab}(k)·U_{k−a}(m−b) = 0` 对象限 `k ≥ k0, m ≥ m0` 中的一切 `(k, m)` 成立
（另要求 `k ≥ A`、`m ≥ B` 使下标非负；把象限缩小不影响结论，所以这不减弱结论）。

**T3.7(1) 的 ODE 部分**（`no_x_ODE`、`no_x_ODE_poly`）：`F(x,t) = Σ U_k(m)x^k t^m`（写成
`ℂ[[x]][[t]]` 的元素 `Fxt`）不满足任何系数在 `ℂ[x][[t]]`（特别地 `ℂ[x,t]`）、不全为 0 的
`x` 方向线性 ODE `Σ_j p_j·∂_x^j F = 0`。

D-finite 的定义（Lipshitz）、引理 D1（D-finite ⇒ 每个变量方向都有多项式系数 ODE）与「所以 `F`
不是 D-finite」这最后一步在 `DFinite.lean`。T3.7(3)（`𝒩` 的对应结论）在 `DFiniteN.lean`（`𝒩` 不是 D-finite）与 `NoKOnlyN.lean`（`N` 没有只依赖 `k` 的象限递推）。

**证明路线**（`notes/c3b.md` §5 证明一的代数化，不用复分析）：
* 先把 `b` 方向平移，使 `b = 0` 那一列不全为 0（`no_k_only_recurrence`）。
* 固定 `m = n + 1`。递推说明 `S = Σ_{a,b} p_{ab}(θ)(x^a·G_{m−b})` 是多项式（`θ = x·d/dx`，
  `polyTheta`）。由 `P_m·G_m = W_m`（`P_mul_Gc`），`P^{j+1}·θ^j(B/P)` 是多项式 `Bseq`
  （`pow_mul_theta_iter`），且 `Bseq ≡ (−1)^j j!·(x P')^j·B (mod P)`（`Bseq_mod`）。
* 乘以 `L = b_m^{D0+1}·P_{m−1}^{D+1}` 后逐项都是多项式（`HasPolyVal`），在 `b_m` 的实根
  `x_m ∈ (0,1)` 处取值：`b ≥ 1` 的项与 `b = 0, e < D0` 的项为 0，只剩
  `P_{m−1}(x_m)^{D−D0}·(−1)^{D0} D0!·(x_m P_m'(x_m))^{D0}·W_m(x_m)·C(x_m)`，
  其中 `C(x) = Σ_a [k^{D0}]p_{a0}·x^a` 与 `m` 无关（`key_eval`）。
* 公因子都非零：`b_v(x_m) = (m−v)x_m³ ≠ 0`（`v < m`），`b_m'(x_m) = −1−3m x_m² < 0`，
  `W_m(x_m) ≥ 1`（正性，`W_pos_of_root`，不需要 T1.3(2) 的互素性）。于是 `C(x_m) = 0`。
* 不同的 `m` 给出不同的根 `x_m`，`C` 有无穷多个根，`C = 0`，与 `D0` 的取法矛盾（`no_rec_col0`）。
* T3.7(1) 同理（`notes/c3b.md` §4）：取所有 `p_j` 中最低的 `t` 次数 `l0` 与该次系数非零的最大 `j = J`，
  比较 `t^{m+l0}` 系数，把 `θ` 换成 `d/dx`（`Dseq`、`pow_mul_deriv_iter`），在 `x_m` 处得到
  `[t^{l0}]p_J(x_m) = 0` 对一切 `m` 成立，于是 `[t^{l0}]p_J = 0`，矛盾。
-/

open Polynomial Finset

namespace A207123

/-! ### 实根与正性 -/

/-- 辅助引理（T3.7，引理 C）：`m ≥ 1` 时 `b_m = 1 − x − m·x³` 在 `(0,1)` 中有实根（介值定理）。 -/
theorem exists_root_b (m : ℕ) (hm : 1 ≤ m) : ∃ x : ℝ, 0 < x ∧ (bpoly ℝ m).eval x = 0 := by
  have hcont : ContinuousOn (fun x => (bpoly ℝ m).eval x) (Set.Icc 0 1) :=
    (Polynomial.continuous _).continuousOn
  have h0 : (bpoly ℝ m).eval 0 = 1 := by simp [eval_bpoly]
  have h1 : (bpoly ℝ m).eval 1 = -(m : ℝ) := by rw [eval_bpoly]; ring
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmem : (0 : ℝ) ∈ Set.Icc ((bpoly ℝ m).eval 1) ((bpoly ℝ m).eval 0) := by
    rw [h0, h1]; constructor <;> linarith
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  have hx0' : (bpoly ℝ m).eval x = 0 := hx0
  refine ⟨x, ?_, hx0'⟩
  rcases hx.1.lt_or_eq with h | h
  · exact h
  · rw [← h, h0] at hx0'; norm_num at hx0'

/-- 辅助引理（T3.7，引理 C(d)）：若 `b_m(x) = 0`，则 `b_v(x) = (m − v)·x³`。 -/
theorem eval_b_sub_of_root {R : Type*} [CommRing R] {m : ℕ} {x : R}
    (hr : (bpoly R m).eval x = 0) (v : ℕ) :
    (bpoly R v).eval x = ((m : R) - v) * x ^ 3 := by
  have h := hr
  rw [eval_bpoly] at h
  rw [eval_bpoly]
  linear_combination h

/-- 辅助引理（T3.7，引理 P(b)）：若 `x > 0` 是 `b_m` 的实根，则 `W_m(x) ≥ 1`（各 `P_{j−1}(x) ≥ 0`）。 -/
theorem W_pos_of_root (m : ℕ) (x : ℝ) (hx : 0 < x) (hr : (bpoly ℝ m).eval x = 0) :
    1 ≤ (Wpoly ℝ m).eval x := by
  have hb : ∀ v, v ≤ m → 0 ≤ (bpoly ℝ v).eval x := by
    intro v hv
    rw [eval_b_sub_of_root hr]
    have h1 : (0 : ℝ) ≤ (m : ℝ) - v := by
      have : (v : ℝ) ≤ m := by exact_mod_cast hv
      linarith
    exact mul_nonneg h1 (pow_nonneg hx.le 3)
  have hP : ∀ j ∈ Icc 1 m, 0 ≤ (Ppoly ℝ (j - 1)).eval x := by
    intro j hj
    rw [mem_Icc] at hj
    rw [Ppoly, eval_prod]
    apply prod_nonneg
    intro v hv
    rw [mem_range] at hv
    exact hb v (by omega)
  have hsum : 0 ≤ ∑ j ∈ Icc 1 m, (C (j : ℝ) * Ppoly ℝ (j - 1)).eval x := by
    apply sum_nonneg
    intro j hj
    rw [eval_mul, eval_C]
    exact mul_nonneg (Nat.cast_nonneg _) (hP j hj)
  rw [Wpoly, eval_add, eval_one, eval_mul, eval_pow, eval_X, eval_finsetSum]
  nlinarith [sq_nonneg x]

/-- 辅助引理（T3.7）：实数 `x` 处 `W_m` 的复值等于实值。 -/
theorem eval_Wpoly_ofReal (m : ℕ) (x : ℝ) :
    (Wpoly ℂ m).eval (x : ℂ) = (((Wpoly ℝ m).eval x : ℝ) : ℂ) := by
  rw [← Wpoly_map ℝ Complex.ofRealHom, eval_map, ← Complex.ofRealHom_eq_coe, eval₂_at_apply]
  rfl

/-! ### θ 算子 -/

variable {K : Type*} [Field K]

/-- `θ = x·d/dx` 作用在形式幂级数上。 -/
noncomputable def theta (f : PowerSeries K) : PowerSeries K := PowerSeries.X * PowerSeries.derivative (R := K) f

/-- 辅助引理（T3.7(2)）：`θ f = x·f′` 的定义式。 -/
theorem theta_def (f : PowerSeries K) : theta f = PowerSeries.X * PowerSeries.derivative (R := K) f := rfl

/-- 辅助引理（T3.7(2)）：`[x^k] θ f = k·[x^k] f`。 -/
theorem coeff_theta (f : PowerSeries K) (k : ℕ) :
    PowerSeries.coeff k (theta f) = (k : K) * PowerSeries.coeff k f := by
  unfold theta
  cases k with
  | zero => simp
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

/-- 辅助引理（T3.7(2)）：`[x^k] θ^e f = k^e·[x^k] f`。 -/
theorem coeff_theta_iter (f : PowerSeries K) (e k : ℕ) :
    PowerSeries.coeff k (theta^[e] f) = (k : K) ^ e * PowerSeries.coeff k f := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', coeff_theta, ih]
    ring

/-- `θ^j(B₀/P)` 的分子（分母为 `P^{j+1}`）。 -/
noncomputable def Bseq (P B0 : K[X]) : ℕ → K[X]
  | 0 => B0
  | j + 1 => Polynomial.X * (P * Polynomial.derivative (Bseq P B0 j)
      - Polynomial.C ((j : K) + 1) * Polynomial.derivative P * Bseq P B0 j)

/-- 辅助引理（T3.7(2)）：若 `P·g = B₀`，则 `P^{j+1}·θ^j g = Bseq P B₀ j`（多项式）。 -/
theorem pow_mul_theta_iter (P B0 : K[X]) (g : PowerSeries K) (h : (P : PowerSeries K) * g = B0) (j : ℕ) :
    (P : PowerSeries K) ^ (j + 1) * theta^[j] g = (Bseq P B0 j : PowerSeries K) := by
  induction j with
  | zero => simpa [Bseq] using h
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hD := congrArg (PowerSeries.derivative (R := K)) ih
    rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_coe,
      PowerSeries.derivative_coe] at hD
    simp only [Bseq, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
    rw [theta_def]
    simp only [smul_eq_mul] at hD
    have e1 : ((j + 1 : ℕ) : PowerSeries K) = PowerSeries.C ((j : K) + 1) := by
      simp [map_add, map_natCast]
    rw [← ih]
    rw [show j + 1 - 1 = j by omega] at hD
    rw [e1] at hD
    linear_combination (PowerSeries.X * (P : PowerSeries K)) * hD

/-- 辅助引理（T3.7(2)）：`Bseq P B₀ j ≡ (−1)^j j!·(x P′)^j·B₀ (mod P)`（最高阶极点系数）。 -/
theorem Bseq_mod (P B0 : K[X]) (j : ℕ) :
    P ∣ Bseq P B0 j - Polynomial.C ((-1) ^ j * (j.factorial : K))
      * (Polynomial.X * Polynomial.derivative P) ^ j * B0 := by
  induction j with
  | zero => simp [Bseq]
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨Polynomial.X * Polynomial.derivative (Bseq P B0 j)
      - Polynomial.C ((j : K) + 1) * Polynomial.derivative P * Polynomial.X * q, ?_⟩
    have hB : Bseq P B0 j = P * q + Polynomial.C ((-1) ^ j * (j.factorial : K))
      * (Polynomial.X * Polynomial.derivative P) ^ j * B0 := by rw [← hq]; ring
    simp only [Bseq]
    rw [Nat.factorial_succ]
    push_cast
    rw [hB]
    simp only [map_mul, map_pow, map_neg, map_one, map_add, map_natCast]
    ring

/-- 在 `P` 的根 `z` 处：`Bseq(z) = (−1)^j j!·(z P'(z))^j·B₀(z)`。 -/
theorem eval_Bseq_of_root (P B0 : K[X]) (j : ℕ) {z : K} (hz : P.eval z = 0) :
    (Bseq P B0 j).eval z = (-1) ^ j * (j.factorial : K)
      * (z * (Polynomial.derivative P).eval z) ^ j * B0.eval z := by
  obtain ⟨q, hq⟩ := Bseq_mod P B0 j
  have h := congrArg (Polynomial.eval z) hq
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, hz, zero_mul] at h
  linear_combination h

/-! ### 多项式系数的逐项乘法与「多项式值」 -/

/-- `polyTheta q f = Σ_k q(k)·f_k·x^k`（`q(θ) f`）。 -/
noncomputable def polyTheta (q : K[X]) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun k => q.eval (k : K) * PowerSeries.coeff k f

/-- 辅助引理（T3.7(2)）：`q(θ) f = Σ_e [k^e]q · θ^e f`（`deg q ≤ N`）。 -/
theorem polyTheta_eq_sum (q : K[X]) (f : PowerSeries K) (N : ℕ) (hN : q.natDegree ≤ N) :
    polyTheta q f = ∑ e ∈ range (N + 1), PowerSeries.C (q.coeff e) * theta^[e] f := by
  ext k
  rw [polyTheta, PowerSeries.coeff_mk, map_sum]
  simp only [PowerSeries.coeff_C_mul, coeff_theta_iter]
  rw [Polynomial.eval_eq_sum_range' (n := N + 1) (by omega), sum_mul]
  apply sum_congr rfl
  intro e _
  ring

/-- `f` 是多项式 `T`（作为幂级数），且 `T(z) = v`。 -/
def HasPolyVal (f : PowerSeries K) (z v : K) : Prop := ∃ T : K[X], f = (T : PowerSeries K) ∧ T.eval z = v

/-- 辅助引理（T3.7）：「是多项式且在 `z` 处取值」对加法封闭。 -/
theorem HasPolyVal.add {f g : PowerSeries K} {z v w : K} (hf : HasPolyVal f z v) (hg : HasPolyVal g z w) :
    HasPolyVal (f + g) z (v + w) := by
  obtain ⟨T, rfl, hT⟩ := hf
  obtain ⟨T', rfl, hT'⟩ := hg
  exact ⟨T + T', by rw [Polynomial.coe_add], by rw [eval_add, hT, hT']⟩

/-- 辅助引理（T3.7）：「是多项式且在 `z` 处取值」对常数倍封闭。 -/
theorem HasPolyVal.const_mul {f : PowerSeries K} {z v : K} (c : K) (hf : HasPolyVal f z v) :
    HasPolyVal (PowerSeries.C c * f) z (c * v) := by
  obtain ⟨T, rfl, hT⟩ := hf
  exact ⟨Polynomial.C c * T, by rw [Polynomial.coe_mul, Polynomial.coe_C], by rw [eval_mul, eval_C, hT]⟩

/-- 辅助引理（T3.7）：0 是取值为 0 的多项式。 -/
theorem HasPolyVal.zero (z : K) : HasPolyVal (0 : PowerSeries K) z 0 :=
  ⟨0, by simp, by simp⟩

/-- 辅助引理（T3.7）：「是多项式且在 `z` 处取值」对有限和封闭。 -/
theorem HasPolyVal.sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries K) (v : ι → K) {z : K}
    (h : ∀ i ∈ s, HasPolyVal (f i) z (v i)) : HasPolyVal (∑ i ∈ s, f i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasPolyVal.zero z
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- 辅助引理（T3.7）：同一幂级数作为多项式在 `z` 处的值唯一（多项式到幂级数的嵌入是单射）。 -/
theorem HasPolyVal.unique {f : PowerSeries K} {z v w : K} (hv : HasPolyVal f z v) (hw : HasPolyVal f z w) :
    v = w := by
  obtain ⟨T, rfl, hT⟩ := hv
  obtain ⟨T', hTT', hT'⟩ := hw
  have : T = T' := Polynomial.coe_inj.mp hTT'
  rw [← hT, ← hT', this]

/-- 辅助引理（T3.7）：改写取值。 -/
theorem HasPolyVal.congr_val {f : PowerSeries K} {z v w : K} (h : HasPolyVal f z v) (hv : v = w) :
    HasPolyVal f z w := hv ▸ h

/-! ### 关键计算：在 `b_{n+1}` 的根处比较「最高阶极点」系数 -/

/-- `G_m` 的复系数版本。 -/
noncomputable def Gc (m : ℕ) : PowerSeries ℂ := PowerSeries.mk fun k => (U k m : ℂ)

/-- `P_m·G_m = W_m` 在 `ℂ` 上（由 `ℚ` 上的 `P_mul_G`（报告 T1.3(1)）经系数映射得到）。 -/
theorem P_mul_Gc (m : ℕ) : (Ppoly ℂ m : PowerSeries ℂ) * Gc m = (Wpoly ℂ m : PowerSeries ℂ) := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) (P_mul_G m)
  rw [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, Ppoly_map,
    Wpoly_map] at h
  have hG : PowerSeries.map (algebraMap ℚ ℂ) (Gser m) = Gc m := by
    ext k
    simp [Gser, Gc, PowerSeries.coeff_map]
  rwa [hG] at h

section Key


/-- 辅助引理（T3.7(2)）：`P_m·(x^a G_m) = x^a W_m`。 -/
theorem P_mul_XG (m a : ℕ) :
    (Ppoly ℂ m : PowerSeries ℂ) * (PowerSeries.X ^ a * Gc m)
      = ((Polynomial.X ^ a * Wpoly ℂ m : ℂ[X]) : PowerSeries ℂ) := by
  rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, ← P_mul_Gc m]
  ring

/-- `b ≥ 1` 的项：`L·θ^e(x^a G_{m'})`（`m' ≤ n`）是 `b_{n+1}^{D0+1}` 的倍式，在根处为 0。 -/
theorem term_lower (n m' D0 D e a : ℕ) (hm' : m' ≤ n) (he : e ≤ D) (z : ℂ)
    (hz : (bpoly ℂ (n + 1)).eval z = 0) :
    HasPolyVal (((bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ n ^ (D + 1) : ℂ[X]) : PowerSeries ℂ)
      * theta^[e] (PowerSeries.X ^ a * Gc m')) z 0 := by
  have hdvd : Ppoly ℂ m' ∣ Ppoly ℂ n := by
    apply prod_dvd_prod_of_subset
    intro v hv
    rw [mem_range] at hv ⊢
    omega
  obtain ⟨R, hR⟩ := hdvd
  have hsplit : bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ n ^ (D + 1)
      = (bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ m' ^ (D - e) * R ^ (D + 1)) * Ppoly ℂ m' ^ (e + 1) := by
    rw [hR, mul_pow]
    have : Ppoly ℂ m' ^ (D + 1) = Ppoly ℂ m' ^ (D - e) * Ppoly ℂ m' ^ (e + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  refine ⟨bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ m' ^ (D - e) * R ^ (D + 1)
    * Bseq (Ppoly ℂ m') (Polynomial.X ^ a * Wpoly ℂ m') e, ?_, ?_⟩
  · rw [hsplit, Polynomial.coe_mul, Polynomial.coe_pow, mul_assoc,
      pow_mul_theta_iter _ _ _ (P_mul_XG m' a) e, ← Polynomial.coe_mul]
  · simp [eval_mul, eval_pow, hz]

/-- `b = 0` 的项：`e < D0` 时在根处为 0；`e = D0` 时给出最高阶极点系数。 -/
theorem term_top (n D0 D e a : ℕ) (hD : D0 ≤ D) (he : e ≤ D0) (z : ℂ)
    (hz : (bpoly ℂ (n + 1)).eval z = 0) :
    HasPolyVal (((bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ n ^ (D + 1) : ℂ[X]) : PowerSeries ℂ)
      * theta^[e] (PowerSeries.X ^ a * Gc (n + 1))) z
      (if e = D0 then (Ppoly ℂ n).eval z ^ (D - D0)
        * ((-1) ^ D0 * (D0.factorial : ℂ) * (z * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval z) ^ D0
          * (z ^ a * (Wpoly ℂ (n + 1)).eval z)) else 0) := by
  have hsplit : bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ n ^ (D + 1)
      = (bpoly ℂ (n + 1) ^ (D0 - e) * Ppoly ℂ n ^ (D - e)) * Ppoly ℂ (n + 1) ^ (e + 1) := by
    rw [Ppoly_succ, mul_pow]
    have h1 : bpoly ℂ (n + 1) ^ (D0 + 1) = bpoly ℂ (n + 1) ^ (D0 - e) * bpoly ℂ (n + 1) ^ (e + 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : Ppoly ℂ n ^ (D + 1) = Ppoly ℂ n ^ (D - e) * Ppoly ℂ n ^ (e + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h1, h2]
    ring
  have hPz : (Ppoly ℂ (n + 1)).eval z = 0 := by rw [Ppoly_succ, eval_mul, hz, mul_zero]
  refine ⟨bpoly ℂ (n + 1) ^ (D0 - e) * Ppoly ℂ n ^ (D - e)
    * Bseq (Ppoly ℂ (n + 1)) (Polynomial.X ^ a * Wpoly ℂ (n + 1)) e, ?_, ?_⟩
  · rw [hsplit, Polynomial.coe_mul, mul_assoc, Polynomial.coe_pow (φ := Ppoly ℂ (n + 1)),
      pow_mul_theta_iter _ _ _ (P_mul_XG (n + 1) a) e, ← Polynomial.coe_mul]
  · rw [eval_mul, eval_mul, eval_pow, eval_pow, hz, eval_Bseq_of_root _ _ _ hPz]
    split_ifs with h
    · subst h
      simp only [Nat.sub_self, pow_zero, one_mul, eval_mul, eval_pow, eval_X]
    · have : 0 < D0 - e := by omega
      rw [zero_pow (by omega), zero_mul, zero_mul]

/-- 关键等式：若 `S = Σ_{a,b} q_{ab}(θ)(x^a G_{n+1−b})` 是多项式，则在 `b_{n+1}` 的根 `z` 处，
`b = 0` 列最高次系数组成的组合 `Σ_a [k^{D0}]p_{a0} · (…)·z^a` 为 0。 -/
theorem key_eval (A B n D0 D : ℕ) (hBn : B ≤ n + 1) (hD : D0 ≤ D) (p : ℕ → ℕ → ℂ[X])
    (hdeg0 : ∀ a ∈ range (A + 1), (p a 0).natDegree ≤ D0)
    (hdeg : ∀ a ∈ range (A + 1), ∀ b ∈ range (B + 1), (p a b).natDegree ≤ D)
    (z : ℂ) (hz : (bpoly ℂ (n + 1)).eval z = 0) (Q : ℂ[X])
    (hS : ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
        polyTheta (p a b) (PowerSeries.X ^ a * Gc (n + 1 - b)) = (Q : PowerSeries ℂ)) :
    ∑ a ∈ range (A + 1), (p a 0).coeff D0 * ((Ppoly ℂ n).eval z ^ (D - D0)
      * ((-1) ^ D0 * (D0.factorial : ℂ) * (z * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval z) ^ D0
        * (z ^ a * (Wpoly ℂ (n + 1)).eval z))) = 0 := by
  set L : ℂ[X] := bpoly ℂ (n + 1) ^ (D0 + 1) * Ppoly ℂ n ^ (D + 1) with hL
  have hLz : L.eval z = 0 := by
    rw [hL, eval_mul, eval_pow, hz, zero_pow (by omega), zero_mul]
  have h1 : HasPolyVal ((L : PowerSeries ℂ) * ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
      polyTheta (p a b) (PowerSeries.X ^ a * Gc (n + 1 - b))) z 0 :=
    ⟨L * Q, by rw [hS, ← Polynomial.coe_mul], by rw [eval_mul, hLz, zero_mul]⟩
  have h2 : HasPolyVal ((L : PowerSeries ℂ) * ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
      polyTheta (p a b) (PowerSeries.X ^ a * Gc (n + 1 - b))) z
      (∑ a ∈ range (A + 1), (p a 0).coeff D0 * ((Ppoly ℂ n).eval z ^ (D - D0)
        * ((-1) ^ D0 * (D0.factorial : ℂ) * (z * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval z) ^ D0
          * (z ^ a * (Wpoly ℂ (n + 1)).eval z)))) := by
    rw [mul_sum]
    apply HasPolyVal.sum
    intro a ha
    rw [sum_range_succ', mul_add, mul_sum]
    apply HasPolyVal.congr_val (v := (∑ b ∈ range B, (0 : ℂ)) + (p a 0).coeff D0 *
      ((Ppoly ℂ n).eval z ^ (D - D0) * ((-1) ^ D0 * (D0.factorial : ℂ)
        * (z * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval z) ^ D0
        * (z ^ a * (Wpoly ℂ (n + 1)).eval z))))
    · apply HasPolyVal.add
      · apply HasPolyVal.sum
        intro b hb
        rw [mem_range] at hb
        rw [polyTheta_eq_sum _ _ D (hdeg a ha (b + 1) (by rw [mem_range]; omega)), mul_sum]
        apply HasPolyVal.congr_val (v := ∑ e ∈ range (D + 1), (p a (b + 1)).coeff e * 0)
        · apply HasPolyVal.sum
          intro e he
          rw [mem_range] at he
          rw [mul_left_comm]
          apply HasPolyVal.const_mul
          rw [show n + 1 - (b + 1) = n - b by omega]
          exact term_lower n (n - b) D0 D e a (by omega) (by omega) z hz
        · simp
      · rw [Nat.sub_zero, polyTheta_eq_sum _ _ D0 (hdeg0 a ha), mul_sum]
        apply HasPolyVal.congr_val (v := ∑ e ∈ range (D0 + 1), (p a 0).coeff e *
          (if e = D0 then (Ppoly ℂ n).eval z ^ (D - D0)
            * ((-1) ^ D0 * (D0.factorial : ℂ)
              * (z * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval z) ^ D0
              * (z ^ a * (Wpoly ℂ (n + 1)).eval z)) else 0))
        · apply HasPolyVal.sum
          intro e he
          rw [mem_range] at he
          rw [mul_left_comm]
          apply HasPolyVal.const_mul
          exact term_top n D0 D e a hD (by omega) z hz
        · simp only [mul_ite, mul_zero]
          rw [sum_ite_eq']
          simp
    · simp
  exact (h2.unique h1)

end Key

/-! ### 主定理 -/

/-- 辅助引理（T3.7）：实系数多项式在实数处的复值等于实值。 -/
theorem eval_ofReal_map (q : ℝ[X]) (x : ℝ) :
    (q.map Complex.ofRealHom).eval (x : ℂ) = ((q.eval x : ℝ) : ℂ) := by
  rw [eval_map, ← Complex.ofRealHom_eq_coe, eval₂_at_apply]
  rfl

/-- 辅助引理（T3.7）：实数 `x` 处 `b_i` 的复值等于实值。 -/
theorem eval_b_ofReal (i : ℕ) (x : ℝ) :
    (bpoly ℂ i).eval (x : ℂ) = (((bpoly ℝ i).eval x : ℝ) : ℂ) := by
  rw [← bpoly_map ℝ Complex.ofRealHom, eval_ofReal_map]

/-- 辅助引理（T3.7，引理 P(b)）：`b_i′(z) = −(1 + 3i·z²)`。 -/
theorem eval_deriv_b (i : ℕ) (z : ℂ) :
    (Polynomial.derivative (bpoly ℂ i)).eval z = -(1 + 3 * (i : ℂ) * z ^ 2) := by
  simp only [bpoly, derivative_sub, derivative_one, derivative_X, derivative_mul, derivative_C,
    derivative_X_pow, zero_mul, zero_add, eval_sub, eval_one, eval_zero,
    eval_mul, eval_C, eval_pow, eval_X]
  push_cast
  ring

section Main


/-- 情形「`b = 0` 那一列不全为 0」：矛盾。 -/
theorem no_rec_col0 (A B k0 m0 : ℕ) (p : ℕ → ℕ → ℂ[X]) (hp0 : ∃ a ≤ A, p a 0 ≠ 0)
    (hrel : ∀ k m, k0 ≤ k → m0 ≤ m → A ≤ k → B ≤ m →
      ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1), (p a b).eval (k : ℂ) * (U (k - a) (m - b) : ℂ) = 0) :
    False := by
  classical
  -- D0：b = 0 列中非零多项式的最高次数
  have hne : ((range (A + 1)).filter (fun a => p a 0 ≠ 0)).Nonempty := by
    obtain ⟨a, ha, hpa⟩ := hp0
    exact ⟨a, mem_filter.mpr ⟨mem_range.mpr (by omega), hpa⟩⟩
  obtain ⟨a', ha', hmax⟩ := ((range (A + 1)).filter (fun a => p a 0 ≠ 0)).exists_max_image
    (fun a => (p a 0).natDegree) hne
  rw [mem_filter] at ha'
  set D0 := (p a' 0).natDegree with hD0
  have hdeg0 : ∀ a ∈ range (A + 1), (p a 0).natDegree ≤ D0 := by
    intro a ha
    by_cases hpa : p a 0 = 0
    · rw [hpa, natDegree_zero]; exact Nat.zero_le _
    · exact hmax a (mem_filter.mpr ⟨ha, hpa⟩)
  set D := max D0 (((range (A + 1)) ×ˢ (range (B + 1))).sup
    (fun ab : ℕ × ℕ => (p ab.1 ab.2).natDegree)) with hDdef
  have hD : D0 ≤ D := le_max_left _ _
  have hdeg : ∀ a ∈ range (A + 1), ∀ b ∈ range (B + 1), (p a b).natDegree ≤ D := by
    intro a ha b hb
    exact le_max_of_le_right (Finset.le_sup (f := fun ab : ℕ × ℕ => (p ab.1 ab.2).natDegree)
      (b := (a, b)) (mem_product.mpr ⟨ha, hb⟩))
  -- 与 m 无关的多项式 C(x) = Σ_a [k^{D0}] p_{a0} · x^a
  set Cp : ℂ[X] := ∑ a ∈ range (A + 1), Polynomial.C ((p a 0).coeff D0) * Polynomial.X ^ a
    with hCp
  have hCp0 : Cp ≠ 0 := by
    intro h
    have hc := congrArg (fun q => q.coeff a') h
    simp only [hCp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      coeff_zero, sum_ite_eq, ha'.1, ↓reduceIte] at hc
    exact (leadingCoeff_ne_zero.mpr ha'.2) hc
  have hCpeval : ∀ z : ℂ, Cp.eval z = ∑ a ∈ range (A + 1), (p a 0).coeff D0 * z ^ a := by
    intro z
    simp [hCp, eval_finsetSum]
  -- 对每个足够大的 n，b_{n+1} 的实根是 C 的根
  have hroot : ∀ n, max m0 B ≤ n + 1 →
      ∃ z : ℂ, z ≠ 0 ∧ (bpoly ℂ (n + 1)).eval z = 0 ∧ Cp.eval z = 0 := by
    intro n hn
    obtain ⟨x, hx, hr⟩ := exists_root_b (n + 1) (by omega)
    have hzb : (bpoly ℂ (n + 1)).eval (x : ℂ) = 0 := by rw [eval_b_ofReal, hr]; simp
    have hz0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    set N := max k0 A with hN
    set S := ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
      polyTheta (p a b) (PowerSeries.X ^ a * Gc (n + 1 - b)) with hSdef
    have hS : S = ((PowerSeries.trunc N S : ℂ[X]) : PowerSeries ℂ) := by
      ext k
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hk
      · rfl
      · have hk' : N ≤ k := by omega
        rw [hSdef, ← hrel k (n + 1) (by omega) (by omega) (by omega) (by omega)]
        simp only [map_sum, polyTheta, PowerSeries.coeff_mk]
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b _
        rw [mem_range] at ha
        rw [PowerSeries.coeff_X_pow_mul']
        simp only [show a ≤ k by omega, ↓reduceIte, Gc, PowerSeries.coeff_mk]
    have hkey := key_eval A B n D0 D (by omega) hD p hdeg0 hdeg (x : ℂ) hzb _ hS
    refine ⟨(x : ℂ), hz0, hzb, ?_⟩
    -- 公因子非零
    have hPn : (Ppoly ℂ n).eval (x : ℂ) ≠ 0 := by
      rw [Ppoly, eval_prod, prod_ne_zero_iff]
      intro v hv
      rw [mem_range] at hv
      rw [eval_b_sub_of_root hzb v]
      refine mul_ne_zero ?_ (pow_ne_zero 3 hz0)
      rw [sub_ne_zero]
      exact_mod_cast (show n + 1 ≠ v by omega)
    have hPd : (Polynomial.derivative (Ppoly ℂ (n + 1))).eval (x : ℂ) ≠ 0 := by
      rw [Ppoly_succ, derivative_mul, eval_add, eval_mul, eval_mul, hzb, mul_zero, zero_add]
      refine mul_ne_zero hPn ?_
      rw [eval_deriv_b]
      have hpos : (0 : ℝ) < 1 + 3 * ((n + 1 : ℕ) : ℝ) * x ^ 2 := by positivity
      have hcast : (1 + 3 * ((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ 2)
          = ((1 + 3 * ((n + 1 : ℕ) : ℝ) * x ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, neg_ne_zero]
      exact_mod_cast hpos.ne'
    have hW : (Wpoly ℂ (n + 1)).eval (x : ℂ) ≠ 0 := by
      rw [eval_Wpoly_ofReal]
      have := W_pos_of_root (n + 1) x hx hr
      exact_mod_cast (show (Wpoly ℝ (n + 1)).eval x ≠ 0 by linarith)
    have hfac : (Ppoly ℂ n).eval (x : ℂ) ^ (D - D0) * ((-1) ^ D0 * (D0.factorial : ℂ)
        * ((x : ℂ) * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval (x : ℂ)) ^ D0)
        * (Wpoly ℂ (n + 1)).eval (x : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hPn) (mul_ne_zero (mul_ne_zero
        (pow_ne_zero _ (by norm_num)) ?_) (pow_ne_zero _ (mul_ne_zero hz0 hPd)))) hW
      exact_mod_cast D0.factorial_ne_zero
    rw [hCpeval]
    have hsum : ∑ a ∈ range (A + 1), (p a 0).coeff D0 * ((Ppoly ℂ n).eval (x : ℂ) ^ (D - D0)
        * ((-1) ^ D0 * (D0.factorial : ℂ)
          * ((x : ℂ) * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval (x : ℂ)) ^ D0
          * ((x : ℂ) ^ a * (Wpoly ℂ (n + 1)).eval (x : ℂ))))
        = ((Ppoly ℂ n).eval (x : ℂ) ^ (D - D0) * ((-1) ^ D0 * (D0.factorial : ℂ)
          * ((x : ℂ) * (Polynomial.derivative (Ppoly ℂ (n + 1))).eval (x : ℂ)) ^ D0)
          * (Wpoly ℂ (n + 1)).eval (x : ℂ))
          * ∑ a ∈ range (A + 1), (p a 0).coeff D0 * (x : ℂ) ^ a := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum] at hkey
    exact (mul_eq_zero.mp hkey).resolve_left hfac
  -- 无穷多个两两不同的根 ⇒ C = 0，矛盾
  choose! zf hzf using hroot
  set M := max m0 B with hM
  have hinj : Function.Injective (fun j : ℕ => zf (j + M)) := by
    intro i j hij
    simp only at hij
    obtain ⟨hz0, hb, -⟩ := hzf (i + M) (by omega)
    obtain ⟨-, hb2, -⟩ := hzf (j + M) (by omega)
    rw [hij] at hz0 hb
    have h := eval_b_sub_of_root hb (j + M + 1)
    rw [hb2] at h
    have h3 : (zf (j + M)) ^ 3 ≠ 0 := pow_ne_zero 3 hz0
    have h4 : ((i + M + 1 : ℕ) : ℂ) - ((j + M + 1 : ℕ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp h.symm with h5 | h5
      · exact h5
      · exact absurd h5 h3
    have h6 : (i + M + 1 : ℕ) = j + M + 1 := by exact_mod_cast sub_eq_zero.mp h4
    omega
  have hinf : {z : ℂ | Cp.IsRoot z}.Infinite :=
    Set.infinite_of_injective_forall_mem hinj (fun j => (hzf (j + M) (by omega)).2.2)
  exact hCp0 (Polynomial.eq_zero_of_infinite_isRoot Cp hinf)

/-- **T3.7(2)**：不存在系数只依赖 `k`（复系数多项式 `p_{ab}(k)`，不全为 0）、在某个象限
`k ≥ k0, m ≥ m0` 上成立的递推 `Σ_{a≤A, b≤B} p_{ab}(k)·U_{k−a}(m−b) = 0`
（象限内另要求 `k ≥ A`、`m ≥ B`，使下标非负；把象限缩小不影响结论）。 -/
theorem no_k_only_recurrence (A B k0 m0 : ℕ) (p : ℕ → ℕ → ℂ[X])
    (hp : ∃ a ≤ A, ∃ b ≤ B, p a b ≠ 0) :
    ¬ ∀ k m, k0 ≤ k → m0 ≤ m → A ≤ k → B ≤ m →
      ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1), (p a b).eval (k : ℂ) * (U (k - a) (m - b) : ℂ) = 0 := by
  classical
  intro hrel
  have hex : ∃ b, b ≤ B ∧ ∃ a ≤ A, p a b ≠ 0 := by
    obtain ⟨a, ha, b, hb, h⟩ := hp
    exact ⟨b, hb, a, ha, h⟩
  obtain ⟨hb0B, a0, ha0, hpa0⟩ := Nat.find_spec hex
  have hzero : ∀ b < Nat.find hex, ∀ a ≤ A, p a b = 0 := by
    intro b hb a ha
    by_contra h
    exact Nat.find_min hex hb ⟨by omega, a, ha, h⟩
  apply no_rec_col0 A (B - Nat.find hex) k0 m0 (fun a b => p a (b + Nat.find hex))
    ⟨a0, ha0, by simpa using hpa0⟩
  intro k m hk hm hAk hBm
  have h := hrel k (m + Nat.find hex) hk (by omega) hAk (by omega)
  rw [← h]
  apply sum_congr rfl
  intro a ha
  rw [mem_range] at ha
  have hlow : ∑ b ∈ range (Nat.find hex),
      (p a b).eval (k : ℂ) * (U (k - a) (m + Nat.find hex - b) : ℂ) = 0 := by
    apply sum_eq_zero
    intro b hb
    rw [hzero b (mem_range.mp hb) a (by omega), eval_zero, zero_mul]
  conv_rhs => rw [show B + 1 = Nat.find hex + (B - Nat.find hex + 1) by omega, sum_range_add, hlow,
    zero_add]
  apply sum_congr rfl
  intro b _
  rw [show Nat.find hex + b = b + Nat.find hex by omega,
    show m + Nat.find hex - (b + Nat.find hex) = m - b by omega]

end Main

/-! ### `d/dx` 版本的分子递推 -/

section Dx

variable {K : Type*} [Field K]

/-- `D^j(B₀/P)` 的分子（分母为 `P^{j+1}`），`D = d/dx`。 -/
noncomputable def Dseq (P B0 : K[X]) : ℕ → K[X]
  | 0 => B0
  | j + 1 => P * Polynomial.derivative (Dseq P B0 j)
      - Polynomial.C ((j : K) + 1) * Polynomial.derivative P * Dseq P B0 j

/-- 辅助引理（T3.7(1)）：若 `P·g = B₀`，则 `P^{j+1}·g^{(j)} = Dseq P B₀ j`（多项式）。 -/
theorem pow_mul_deriv_iter (P B0 : K[X]) (g : PowerSeries K) (h : (P : PowerSeries K) * g = B0)
    (j : ℕ) :
    (P : PowerSeries K) ^ (j + 1) * (PowerSeries.derivative (R := K))^[j] g
      = (Dseq P B0 j : PowerSeries K) := by
  induction j with
  | zero => simpa [Dseq] using h
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hD := congrArg (PowerSeries.derivative (R := K)) ih
    rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_coe,
      PowerSeries.derivative_coe] at hD
    simp only [Dseq, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C]
    simp only [smul_eq_mul] at hD
    have e1 : ((j + 1 : ℕ) : PowerSeries K) = PowerSeries.C ((j : K) + 1) := by
      simp [map_add, map_natCast]
    rw [← ih]
    rw [show j + 1 - 1 = j by omega] at hD
    rw [e1] at hD
    linear_combination (P : PowerSeries K) * hD

/-- 辅助引理（T3.7(1)）：`Dseq P B₀ j ≡ (−1)^j j!·(P′)^j·B₀ (mod P)`（最高阶极点系数）。 -/
theorem Dseq_mod (P B0 : K[X]) (j : ℕ) :
    P ∣ Dseq P B0 j - Polynomial.C ((-1) ^ j * (j.factorial : K))
      * (Polynomial.derivative P) ^ j * B0 := by
  induction j with
  | zero => simp [Dseq]
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨Polynomial.derivative (Dseq P B0 j)
      - Polynomial.C ((j : K) + 1) * Polynomial.derivative P * q, ?_⟩
    have hB : Dseq P B0 j = P * q + Polynomial.C ((-1) ^ j * (j.factorial : K))
      * (Polynomial.derivative P) ^ j * B0 := by rw [← hq]; ring
    simp only [Dseq]
    rw [Nat.factorial_succ]
    push_cast
    rw [hB]
    simp only [map_mul, map_pow, map_neg, map_one, map_add, map_natCast]
    ring

/-- 辅助引理（T3.7(1)）：在 `P` 的根 `z` 处 `Dseq(z) = (−1)^j j!·P′(z)^j·B₀(z)`。 -/
theorem eval_Dseq_of_root (P B0 : K[X]) (j : ℕ) {z : K} (hz : P.eval z = 0) :
    (Dseq P B0 j).eval z = (-1) ^ j * (j.factorial : K)
      * ((Polynomial.derivative P).eval z) ^ j * B0.eval z := by
  obtain ⟨q, hq⟩ := Dseq_mod P B0 j
  have h := congrArg (Polynomial.eval z) hq
  simp only [eval_sub, eval_mul, eval_C, eval_pow, hz, zero_mul] at h
  linear_combination h

/-- 辅助引理（T3.7(1)）：「是多项式且在 `z` 处取值」对乘多项式封闭。 -/
theorem HasPolyVal.poly_mul {f : PowerSeries K} {z v : K} (q : K[X]) (hf : HasPolyVal f z v) :
    HasPolyVal ((q : PowerSeries K) * f) z (q.eval z * v) := by
  obtain ⟨T, rfl, hT⟩ := hf
  exact ⟨q * T, by rw [Polynomial.coe_mul], by rw [eval_mul, hT]⟩

end Dx

/-! ### 逐项多项式值 -/

/-- 辅助引理（T3.7(1)）：`m′ ≤ n` 时 `L·G_{m′}^{(j)}` 是 `b_{n+1}^{J+1}` 的倍式，在 `b_{n+1}` 的根处为 0。 -/
theorem dterm_lower (n m' J r j : ℕ) (hm' : m' ≤ n) (hj : j ≤ r) (z : ℂ)
    (hz : (bpoly ℂ (n + 1)).eval z = 0) :
    HasPolyVal (((bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ n ^ (r + 1) : ℂ[X]) : PowerSeries ℂ)
      * (PowerSeries.derivative (R := ℂ))^[j] (Gc m')) z 0 := by
  have hdvd : Ppoly ℂ m' ∣ Ppoly ℂ n := by
    apply prod_dvd_prod_of_subset
    intro v hv
    rw [mem_range] at hv ⊢
    omega
  obtain ⟨R, hR⟩ := hdvd
  have hsplit : bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ n ^ (r + 1)
      = (bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ m' ^ (r - j) * R ^ (r + 1)) * Ppoly ℂ m' ^ (j + 1) := by
    rw [hR, mul_pow]
    have : Ppoly ℂ m' ^ (r + 1) = Ppoly ℂ m' ^ (r - j) * Ppoly ℂ m' ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  refine ⟨bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ m' ^ (r - j) * R ^ (r + 1)
    * Dseq (Ppoly ℂ m') (Wpoly ℂ m') j, ?_, ?_⟩
  · rw [hsplit, Polynomial.coe_mul, Polynomial.coe_pow, mul_assoc,
      pow_mul_deriv_iter _ _ _ (P_mul_Gc m') j, ← Polynomial.coe_mul]
  · simp [eval_mul, eval_pow, hz]

/-- 辅助引理（T3.7(1)）：`L·G_{n+1}^{(j)}`（`j ≤ J`）在 `b_{n+1}` 的根处，`j < J` 时为 0，`j = J` 时给出最高阶极点系数。 -/
theorem dterm_top (n J r j : ℕ) (hJ : J ≤ r) (hj : j ≤ J) (z : ℂ)
    (hz : (bpoly ℂ (n + 1)).eval z = 0) :
    HasPolyVal (((bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ n ^ (r + 1) : ℂ[X]) : PowerSeries ℂ)
      * (PowerSeries.derivative (R := ℂ))^[j] (Gc (n + 1))) z
      (if j = J then (Ppoly ℂ n).eval z ^ (r - J)
        * ((-1) ^ J * (J.factorial : ℂ) * ((Polynomial.derivative (Ppoly ℂ (n + 1))).eval z) ^ J
          * (Wpoly ℂ (n + 1)).eval z) else 0) := by
  have hsplit : bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ n ^ (r + 1)
      = (bpoly ℂ (n + 1) ^ (J - j) * Ppoly ℂ n ^ (r - j)) * Ppoly ℂ (n + 1) ^ (j + 1) := by
    rw [Ppoly_succ, mul_pow]
    have h1 : bpoly ℂ (n + 1) ^ (J + 1) = bpoly ℂ (n + 1) ^ (J - j) * bpoly ℂ (n + 1) ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : Ppoly ℂ n ^ (r + 1) = Ppoly ℂ n ^ (r - j) * Ppoly ℂ n ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h1, h2]
    ring
  have hPz : (Ppoly ℂ (n + 1)).eval z = 0 := by rw [Ppoly_succ, eval_mul, hz, mul_zero]
  refine ⟨bpoly ℂ (n + 1) ^ (J - j) * Ppoly ℂ n ^ (r - j)
    * Dseq (Ppoly ℂ (n + 1)) (Wpoly ℂ (n + 1)) j, ?_, ?_⟩
  · rw [hsplit, Polynomial.coe_mul, mul_assoc, Polynomial.coe_pow (φ := Ppoly ℂ (n + 1)),
      pow_mul_deriv_iter _ _ _ (P_mul_Gc (n + 1)) j, ← Polynomial.coe_mul]
  · rw [eval_mul, eval_mul, eval_pow, eval_pow, hz, eval_Dseq_of_root _ _ _ hPz]
    split_ifs with h
    · subst h
      simp only [Nat.sub_self, pow_zero, one_mul]
    · have : 0 < J - j := by omega
      rw [zero_pow (by omega), zero_mul, zero_mul]

/-! ### T3.7(1)：`F` 关于 `x` 没有多项式系数 ODE -/

/-- 二元母函数 `F(x,t) = Σ_{k,m} U_k(m)·x^k·t^m`，写成以 `t` 为外层变量的幂级数
（`ℂ[[x,t]] = ℂ[[x]][[t]]`），`[t^m]F = G_m(x)`。 -/
noncomputable def Fxt : PowerSeries (PowerSeries ℂ) := PowerSeries.mk fun m => Gc m

/-- `∂_x`：对每个 `t^m` 系数求 `x` 导数。 -/
noncomputable def dX (f : PowerSeries (PowerSeries ℂ)) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun m => PowerSeries.derivative (R := ℂ) (PowerSeries.coeff m f)

/-- 辅助引理（T3.7(1)）：`[t^m] ∂_x^j F = (d/dx)^j [t^m] F`。 -/
theorem coeff_dX_iter (f : PowerSeries (PowerSeries ℂ)) (j m : ℕ) :
    PowerSeries.coeff m (dX^[j] f)
      = (PowerSeries.derivative (R := ℂ))^[j] (PowerSeries.coeff m f) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dX, PowerSeries.coeff_mk, ih]

/-- 系数嵌入 `ℂ[x][[t]] → ℂ[[x]][[t]]`。 -/
noncomputable def embedC (p : PowerSeries ℂ[X]) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.map (Polynomial.coeToPowerSeries.ringHom) p

/-- 辅助引理（T3.7(1)）：系数嵌入 `ℂ[x][[t]] → ℂ[[x]][[t]]` 逐 `t^l` 系数就是多项式到幂级数的嵌入。 -/
theorem coeff_embedC (p : PowerSeries ℂ[X]) (l : ℕ) :
    PowerSeries.coeff l (embedC p) = ((PowerSeries.coeff l p : ℂ[X]) : PowerSeries ℂ) := by
  rw [embedC, PowerSeries.coeff_map]
  rfl

/-- **T3.7(1)**（ODE 部分）：不存在不全为 0 的 `p_0, …, p_r ∈ ℂ[x][[t]]`（`t` 的幂级数、`x` 的
多项式系数；特别地包括 `p_j ∈ ℂ[x,t]`，见 `no_x_ODE_poly`）使 `Σ_j p_j·∂_x^j F = 0`。
报告接着由引理 D1（D-finite ⇒ 每个变量方向都有多项式系数 ODE）推出 `F` 不是 D-finite；
D-finite 的定义、引理 D1 与这一步在 `DFinite.lean`（`not_isDFinite_FK`）。 -/
theorem no_x_ODE (r : ℕ) (p : ℕ → PowerSeries ℂ[X]) (hp : ∃ j ≤ r, p j ≠ 0) :
    ∑ j ∈ range (r + 1), embedC (p j) * dX^[j] Fxt ≠ 0 := by
  classical
  intro hode
  -- 所有 `p_j` 中出现的最低 `t` 次数 `l0`
  have hex : ∃ l, ∃ j ≤ r, PowerSeries.coeff l (p j) ≠ 0 := by
    obtain ⟨j, hj, hpj⟩ := hp
    by_contra h
    push Not at h
    exact hpj (PowerSeries.ext fun l => by rw [map_zero]; exact h l j hj)
  have hmin : ∀ l < Nat.find hex, ∀ j ≤ r, PowerSeries.coeff l (p j) = 0 := by
    intro l hl j hj
    by_contra h
    exact Nat.find_min hex hl ⟨j, hj, h⟩
  obtain ⟨j1, hj1, hj1ne⟩ := Nat.find_spec hex
  set l0 := Nat.find hex with hl0
  -- `J`：在 `t^{l0}` 系数非零的 `p_j` 中最大的 `j`
  set Sj := (range (r + 1)).filter (fun j => PowerSeries.coeff l0 (p j) ≠ 0) with hSj
  have hSne : Sj.Nonempty := ⟨j1, mem_filter.mpr ⟨mem_range.mpr (by omega), hj1ne⟩⟩
  set J := Sj.max' hSne with hJdef
  have hJS : J ∈ Sj := Sj.max'_mem hSne
  rw [hSj, mem_filter, mem_range] at hJS
  have hJr : J ≤ r := by omega
  have hJmax : ∀ j ≤ r, J < j → PowerSeries.coeff l0 (p j) = 0 := by
    intro j hj hJj
    by_contra h
    have hmem : j ∈ Sj := mem_filter.mpr ⟨mem_range.mpr (by omega), h⟩
    have := Sj.le_max' j hmem
    omega
  set q := PowerSeries.coeff l0 (p J) with hq
  have hq0 : q ≠ 0 := hJS.2
  -- 每个 `n`：`b_{n+1}` 的实根是 `q` 的根
  have hroot : ∀ n : ℕ, ∃ z : ℂ, z ≠ 0 ∧ (bpoly ℂ (n + 1)).eval z = 0 ∧ q.eval z = 0 := by
    intro n
    obtain ⟨x, hx, hr⟩ := exists_root_b (n + 1) (by omega)
    have hzb : (bpoly ℂ (n + 1)).eval (x : ℂ) = 0 := by rw [eval_b_ofReal, hr]; simp
    have hz0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    refine ⟨(x : ℂ), hz0, hzb, ?_⟩
    set N := n + 1 + l0 with hN
    have hc := congrArg (PowerSeries.coeff N) hode
    rw [map_sum, map_zero] at hc
    simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      coeff_embedC, coeff_dX_iter, Fxt, PowerSeries.coeff_mk] at hc
    set L : ℂ[X] := bpoly ℂ (n + 1) ^ (J + 1) * Ppoly ℂ n ^ (r + 1) with hL
    set V : ℂ := (Ppoly ℂ n).eval (x : ℂ) ^ (r - J)
      * ((-1) ^ J * (J.factorial : ℂ) * ((Polynomial.derivative (Ppoly ℂ (n + 1))).eval (x : ℂ)) ^ J
        * (Wpoly ℂ (n + 1)).eval (x : ℂ)) with hV
    have h1 : HasPolyVal ((L : PowerSeries ℂ) * ∑ j ∈ range (r + 1), ∑ l ∈ range (N + 1),
        ((PowerSeries.coeff l (p j) : ℂ[X]) : PowerSeries ℂ)
          * (PowerSeries.derivative (R := ℂ))^[j] (Gc (N - l))) (x : ℂ) 0 := by
      rw [hc, mul_zero]
      exact HasPolyVal.zero _
    have h2 : HasPolyVal ((L : PowerSeries ℂ) * ∑ j ∈ range (r + 1), ∑ l ∈ range (N + 1),
        ((PowerSeries.coeff l (p j) : ℂ[X]) : PowerSeries ℂ)
          * (PowerSeries.derivative (R := ℂ))^[j] (Gc (N - l))) (x : ℂ)
        (∑ j ∈ range (r + 1), ∑ l ∈ range (N + 1),
          if l = l0 ∧ j = J then q.eval (x : ℂ) * V else 0) := by
      rw [mul_sum]
      apply HasPolyVal.sum
      intro j hj
      rw [mem_range] at hj
      rw [mul_sum]
      apply HasPolyVal.sum
      intro l hl
      rw [mem_range] at hl
      rw [mul_left_comm]
      rcases lt_trichotomy l l0 with hlt | heq | hgt
      · -- `l < l0`：系数为 0
        rw [hmin l hlt j (by omega), Polynomial.coe_zero, zero_mul]
        exact HasPolyVal.congr_val (HasPolyVal.zero _) (by rw [ite_eq_right (by omega)])
      · rw [heq, show N - l0 = n + 1 by omega]
        by_cases hjJ : j ≤ J
        · apply HasPolyVal.congr_val (HasPolyVal.poly_mul _ (dterm_top n J r j hJr hjJ _ hzb))
          by_cases h : j = J
          · subst h
            rw [ite_eq_left rfl, ite_eq_left ⟨rfl, rfl⟩]
          · simp [h]
        · rw [hJmax j (by omega) (by omega), Polynomial.coe_zero, zero_mul]
          exact HasPolyVal.congr_val (HasPolyVal.zero _) (by rw [ite_eq_right (by omega)])
      · -- `l > l0`：`G_{N−l}` 的分母与 `b_{n+1}` 互素，乘 `L` 后在根处为 0
        apply HasPolyVal.congr_val (HasPolyVal.poly_mul _
          (dterm_lower n (N - l) J r j (by omega) (by omega) _ hzb))
        rw [mul_zero, ite_eq_right (by omega)]
    have hval := h2.unique h1
    rw [sum_eq_single J (fun j _ hj => sum_eq_zero fun l _ => by rw [ite_eq_right (by tauto)])
      (fun h => absurd (mem_range.mpr (by omega)) h),
      sum_eq_single l0 (fun l _ hl => by rw [ite_eq_right (by tauto)])
        (fun h => absurd (mem_range.mpr (by omega)) h), ite_eq_left ⟨rfl, rfl⟩] at hval
    -- `V ≠ 0`
    have hPn : (Ppoly ℂ n).eval (x : ℂ) ≠ 0 := by
      rw [Ppoly, eval_prod, prod_ne_zero_iff]
      intro v hv
      rw [mem_range] at hv
      rw [eval_b_sub_of_root hzb v]
      refine mul_ne_zero ?_ (pow_ne_zero 3 hz0)
      rw [sub_ne_zero]
      exact_mod_cast (show n + 1 ≠ v by omega)
    have hPd : (Polynomial.derivative (Ppoly ℂ (n + 1))).eval (x : ℂ) ≠ 0 := by
      rw [Ppoly_succ, derivative_mul, eval_add, eval_mul, eval_mul, hzb, mul_zero, zero_add]
      refine mul_ne_zero hPn ?_
      rw [eval_deriv_b]
      have hpos : (0 : ℝ) < 1 + 3 * ((n + 1 : ℕ) : ℝ) * x ^ 2 := by positivity
      have hcast : (1 + 3 * ((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ 2)
          = ((1 + 3 * ((n + 1 : ℕ) : ℝ) * x ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, neg_ne_zero]
      exact_mod_cast hpos.ne'
    have hW : (Wpoly ℂ (n + 1)).eval (x : ℂ) ≠ 0 := by
      rw [eval_Wpoly_ofReal]
      have := W_pos_of_root (n + 1) x hx hr
      exact_mod_cast (show (Wpoly ℝ (n + 1)).eval x ≠ 0 by linarith)
    have hV0 : V ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ hPn) (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (pow_ne_zero _ (by norm_num)) ?_) (pow_ne_zero _ hPd)) hW)
      exact_mod_cast J.factorial_ne_zero
    exact (mul_eq_zero.mp hval).resolve_right hV0
  -- 无穷多个两两不同的根 ⇒ `q = 0`，矛盾
  choose zf hzf using hroot
  have hinj : Function.Injective zf := by
    intro i j hij
    obtain ⟨hz0, hb, -⟩ := hzf i
    obtain ⟨-, hb2, -⟩ := hzf j
    rw [hij] at hz0 hb
    have h := eval_b_sub_of_root hb (j + 1)
    rw [hb2] at h
    have h3 : (zf j) ^ 3 ≠ 0 := pow_ne_zero 3 hz0
    have h4 : ((i + 1 : ℕ) : ℂ) - ((j + 1 : ℕ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp h.symm with h5 | h5
      · exact h5
      · exact absurd h5 h3
    have h6 : (i + 1 : ℕ) = j + 1 := by exact_mod_cast sub_eq_zero.mp h4
    omega
  have hinf : {z : ℂ | q.IsRoot z}.Infinite :=
    Set.infinite_of_injective_forall_mem hinj (fun n => (hzf n).2.2)
  exact hq0 (Polynomial.eq_zero_of_infinite_isRoot q hinf)

/-- **T3.7(1)**（ODE 部分，系数取 `ℂ[x,t]`）：不存在不全为 0 的 `p_0, …, p_r ∈ ℂ[x,t]`
（这里写成 `t` 的多项式、系数为 `x` 的多项式）使 `Σ_j p_j·∂_x^j F = 0`。 -/
theorem no_x_ODE_poly (r : ℕ) (p : ℕ → Polynomial ℂ[X]) (hp : ∃ j ≤ r, p j ≠ 0) :
    ∑ j ∈ range (r + 1), embedC (p j : PowerSeries ℂ[X]) * dX^[j] Fxt ≠ 0 :=
  no_x_ODE r (fun j => (p j : PowerSeries ℂ[X]))
    (by
      obtain ⟨j, hj, h⟩ := hp
      exact ⟨j, hj, by rwa [Ne, Polynomial.coe_eq_zero_iff]⟩)

end A207123
