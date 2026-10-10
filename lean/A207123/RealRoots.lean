import A207123.Interlace
import A207123.HStruct

/-!
# 论文 §8：三角形的行多项式只有实根（命题 8.10）

`nR k` 是论文 §8 的行多项式 `n_k(z) = Σ_{q=1}^{k} N(k,q)·z^{q−1}`（实系数；`nR_eq_map`：它就是 `HStruct.lean`
的 `nrowPoly k` 映射到 `ℝ[X]`）。交错 `g ≪ f` 见 `Interlace.lean`（`Interlaces g f`）。

* 算子（论文 §8.1）：`opDz p = (1+z)p' + 2p`、`opTz p = z·opDz p`、`opPsiz p = (1+z)·opTz p`。
  论文引理 8.8：`lemma_il_T_one`（(1)）、`opDz_interlaces`（`𝒟p ≪ (1+z)p`，即 (3) 的中间一步）、`Interlaces.opDz`、`Interlaces.opTz`、
  `Interlaces.opPsiz`（(2)：`g ≪ f` 推出 `𝒟g ≪ 𝒟f`、`𝒯g ≪ 𝒯f`、`Ψg ≪ Ψf`）、`interlaces_one_add_X_mul_opTz`
  （(3)：根都 `≤ 0` 时 `(1+z)p ≪ 𝒯p`）、`opTz_one_add_X_mul`（(4)）。论文用上半平面虚部与 Gauss–Lucas 定理
  证 (2)；这里改用锥的表示：`g = c·f + Σ w_a·f/(z−a)`，而 `𝒟(f/(z−a)) ≪ 𝒟f` 由
  `𝒟f = (z−a)·𝒟(f/(z−a)) + (1+z)·f/(z−a)` 与引理 8.6 得到。
* 论文引理 8.9：`nR_rec`（`n_{k+3} = (1+z)·n_{k+2} + Ψn_k`，`k ≥ 1`），由 `N_tri` 逐个系数比较。
* 论文命题 8.10：`prop_four_relations`（对每个 `k ≥ 3`：(α_k) `n_{k−1} ≪ n_k`、(β_k) `n_k ≪ 𝒯n_{k−1}`、
  (δ_k) `n_k ≪ Ψn_{k−2}`、(ε_k) `Ψn_{k−2} ≪ 𝒯n_k`，这里写成 `k + 3`）与 `alpha_two`、`beta_two`；
  初值 `k ≤ 3` 按显式的根逐点数根（`n_3` 的根是 `−1 ± √2/2`）。
* 推论：`realRooted_nR`（`k ≥ 1` 时 `n_k` 的实根计重数个数等于次数）、`nrowPoly_root_im_eq_zero`
  （`nrowPoly k` 的每个复根都是实数）。
-/

namespace A207123

open Polynomial

noncomputable section

/-! ## 1. 行多项式 -/

/-- 论文 §8 的行多项式 `n_k(z) = Σ_{q=1}^{k} N(k,q)·z^{q−1}`（实系数）。 -/
def nR (k : ℕ) : ℝ[X] := ∑ q ∈ Finset.Icc 1 k, C (N k q : ℝ) * X ^ (q - 1)

theorem nR_eq_map (k : ℕ) : nR k = (nrowPoly k).map (algebraMap ℚ ℝ) := by
  simp [nR, nrowPoly, Polynomial.map_sum]

theorem coeff_nR (k j : ℕ) : (nR k).coeff j = (N k (j + 1) : ℝ) := by
  rw [nR, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hj : j + 1 ≤ k
  · rw [Finset.sum_eq_single (j + 1)]
    · simp
    · intro q hq hne
      rw [Finset.mem_Icc] at hq
      rw [ite_eq_right (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨by omega, hj⟩) h
  · rw [N_eq_zero_of_lt (by omega), Nat.cast_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    rw [ite_eq_right (by omega), mul_zero]

theorem natDegree_nR {k : ℕ} (hk : 1 ≤ k) : (nR k).natDegree = k - 1 := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_nR, N_eq_zero_of_lt (by omega), Nat.cast_zero]
  · apply le_natDegree_of_ne_zero
    rw [coeff_nR, Nat.sub_add_cancel hk]
    exact_mod_cast (N_self_pos k).ne'

theorem leadingCoeff_nR {k : ℕ} (hk : 1 ≤ k) : (nR k).leadingCoeff = N k k := by
  rw [leadingCoeff, natDegree_nR hk, coeff_nR, Nat.sub_add_cancel hk]

theorem leadingCoeff_nR_pos {k : ℕ} (hk : 1 ≤ k) : 0 < (nR k).leadingCoeff := by
  rw [leadingCoeff_nR hk]
  exact_mod_cast N_self_pos k

theorem nR_ne_zero {k : ℕ} (hk : 1 ≤ k) : nR k ≠ 0 :=
  leadingCoeff_ne_zero.1 (leadingCoeff_nR_pos hk).ne'

/-- `n_k` 的系数非负，所以没有正根。 -/
theorem nAbove_nR_zero {k : ℕ} (hk : 1 ≤ k) : nAbove (nR k) 0 = 0 :=
  nAbove_zero_of_coeff_nonneg (nR_ne_zero hk) fun i => by rw [coeff_nR]; positivity

/-! ## 2. 算子 `𝒟`、`𝒯`、`Ψ` -/

/-- 论文 §8.1 的 `𝒟p = (1+z)p' + 2p`。 -/
def opDz (p : ℝ[X]) : ℝ[X] := (1 + X) * derivative p + C 2 * p

/-- 论文 §8.1 的 `𝒯p = z·𝒟p`。 -/
def opTz (p : ℝ[X]) : ℝ[X] := X * opDz p

/-- 论文 §8.1 的 `Ψp = (1+z)·𝒯p`。 -/
def opPsiz (p : ℝ[X]) : ℝ[X] := (1 + X) * opTz p

theorem one_add_X_eq : (1 + X : ℝ[X]) = X - C (-1) := by
  rw [C_neg, C_1, sub_neg_eq_add, add_comm]

theorem realRooted_one_add_X : RealRooted (1 + X : ℝ[X]) := by
  rw [one_add_X_eq]
  exact realRooted_X_sub_C _

theorem nAbove_one_add_X_zero : nAbove (1 + X) 0 = 0 := by
  rw [one_add_X_eq, nAbove_X_sub_C, ite_eq_right (by norm_num)]

theorem leadingCoeff_one_add_X : (1 + X : ℝ[X]).leadingCoeff = 1 := by
  rw [add_comm, ← C_1, leadingCoeff_X_add_C]

theorem leadingCoeff_mul_pos {p q : ℝ[X]} (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff) :
    0 < (p * q).leadingCoeff := by
  rw [leadingCoeff_mul]
  exact mul_pos hp hq

theorem leadingCoeff_X_pos : 0 < (X : ℝ[X]).leadingCoeff := by
  rw [leadingCoeff_X]
  exact zero_lt_one

theorem leadingCoeff_one_add_X_pos : 0 < (1 + X : ℝ[X]).leadingCoeff := by
  rw [leadingCoeff_one_add_X]
  exact zero_lt_one

theorem leadingCoeff_X_sub_C_pos (a : ℝ) : 0 < (X - C a).leadingCoeff := by
  rw [leadingCoeff_X_sub_C]
  exact zero_lt_one

theorem leadingCoeff_C_mul_pos {r : ℝ} (hr : 0 < r) {p : ℝ[X]} (hp : 0 < p.leadingCoeff) :
    0 < (C r * p).leadingCoeff := by
  rw [leadingCoeff_mul, leadingCoeff_C]
  exact mul_pos hr hp

theorem coeff_opDz (p : ℝ[X]) (m : ℕ) :
    (opDz p).coeff m = (m + 1) * p.coeff (m + 1) + (m + 2) * p.coeff m := by
  have e : opDz p = derivative p + X * derivative p + C 2 * p := by
    rw [opDz]
    ring
  rw [e, coeff_add, coeff_add, coeff_derivative, coeff_C_mul]
  rcases m with _ | m
  · rw [coeff_X_mul_zero]
    push_cast
    ring
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem coeff_opTz_zero (p : ℝ[X]) : (opTz p).coeff 0 = 0 := coeff_X_mul_zero _

theorem coeff_opTz_succ (p : ℝ[X]) (m : ℕ) : (opTz p).coeff (m + 1) = (opDz p).coeff m :=
  coeff_X_mul _ _

theorem coeff_one_add_X_mul_zero (p : ℝ[X]) : ((1 + X) * p).coeff 0 = p.coeff 0 := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul_zero, add_zero]

theorem coeff_one_add_X_mul_succ (p : ℝ[X]) (m : ℕ) :
    ((1 + X) * p).coeff (m + 1) = p.coeff (m + 1) + p.coeff m := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul]

/-- `𝒟` 不改变次数，首项系数乘以 `deg p + 2`。 -/
theorem opDz_lc {p : ℝ[X]} (hlc : 0 < p.leadingCoeff) :
    (opDz p).natDegree = p.natDegree ∧ 0 < (opDz p).leadingCoeff := by
  have h : (opDz p).coeff p.natDegree = (p.natDegree + 2) * p.leadingCoeff := by
    rw [coeff_opDz, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), leadingCoeff]
    ring
  have hle : (opDz p).natDegree ≤ p.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_opDz, coeff_eq_zero_of_natDegree_lt hm, coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  have hpos : 0 < (opDz p).coeff p.natDegree := by
    rw [h]
    exact mul_pos (by positivity) hlc
  have hdeg : (opDz p).natDegree = p.natDegree :=
    le_antisymm hle (le_natDegree_of_ne_zero hpos.ne')
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg]
  exact hpos

theorem opTz_lc {p : ℝ[X]} (hlc : 0 < p.leadingCoeff) : 0 < (opTz p).leadingCoeff :=
  leadingCoeff_mul_pos leadingCoeff_X_pos (opDz_lc hlc).2

theorem opPsiz_lc {p : ℝ[X]} (hlc : 0 < p.leadingCoeff) : 0 < (opPsiz p).leadingCoeff :=
  leadingCoeff_mul_pos leadingCoeff_one_add_X_pos (opTz_lc hlc)

theorem opDz_add (p q : ℝ[X]) : opDz (p + q) = opDz p + opDz q := by
  simp only [opDz, derivative_add]
  ring

theorem opDz_C_mul (r : ℝ) (p : ℝ[X]) : opDz (C r * p) = C r * opDz p := by
  simp only [opDz, derivative_C_mul]
  ring

theorem opDz_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    opDz (∑ i ∈ s, f i) = ∑ i ∈ s, opDz (f i) := by
  simp only [opDz, derivative_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

theorem opTz_add (p q : ℝ[X]) : opTz (p + q) = opTz p + opTz q := by
  rw [opTz, opTz, opTz, opDz_add, mul_add]

theorem opDz_X_sub_C_mul (q : ℝ[X]) (a : ℝ) :
    opDz ((X - C a) * q) = (X - C a) * opDz q + (1 + X) * q := by
  simp only [opDz, derivative_mul, derivative_sub, derivative_X, derivative_C]
  ring

/-- 论文引理 8.8(4)：`𝒯((1+z)p) = (1+z)(𝒯p + zp)`。 -/
theorem opTz_one_add_X_mul (p : ℝ[X]) : opTz ((1 + X) * p) = (1 + X) * (opTz p + X * p) := by
  simp only [opTz, opDz, derivative_mul, derivative_add, derivative_one, derivative_X]
  ring

/-! ## 3. 论文引理 8.8 -/

/-- 论文引理 8.8 证明 (3) 的中间一步：`𝒟p ≪ (1+z)p`（`p` 实根、首项系数为正）。特别地 `𝒟p` 实根。 -/
theorem opDz_interlaces {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff) :
    Interlaces (opDz p) ((1 + X) * p) := by
  have h1 : Interlaces p ((1 + X) * p) := by
    rw [one_add_X_eq]
    exact interlaces_X_sub_C_mul hp _
  have h2 : Interlaces (C 2 * p) ((1 + X) * p) := h1.C_mul_left (by norm_num)
  by_cases hd : p.natDegree = 0
  · have hd' : derivative p = 0 := derivative_eq_zero.2 hd
    rw [opDz, hd', mul_zero, zero_add]
    exact h2
  · have h3 : Interlaces ((1 + X) * derivative p) ((1 + X) * p) :=
      (interlaces_mul_iff realRooted_one_add_X).2 (interlaces_derivative hp hlc (by omega))
    rw [opDz]
    exact h3.add_left h2 (leadingCoeff_mul_pos leadingCoeff_one_add_X_pos hlc)
      (leadingCoeff_mul_pos leadingCoeff_one_add_X_pos (leadingCoeff_derivative_pos hlc (by omega)))
      (leadingCoeff_C_mul_pos (by norm_num) hlc)

theorem RealRooted.opDz {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff) :
    RealRooted (opDz p) :=
  (opDz_interlaces hp hlc).2.1

/-- 论文引理 8.8(2) 的核心：`g ≪ f`（首项系数都为正）推出 `𝒟g ≪ 𝒟f`。 -/
theorem Interlaces.opDz {g f : ℝ[X]} (h : Interlaces g f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) : Interlaces (opDz g) (opDz f) := by
  have hf := h.1
  have hgen : ∀ a ∈ f.roots, Interlaces (A207123.opDz (f /ₘ (X - C a))) (A207123.opDz f) := by
    intro a ha
    have hr := isRoot_of_mem_roots ha
    have hq : RealRooted (f /ₘ (X - C a)) := realRooted_divByMonic hf hr
    have hlcq : 0 < (f /ₘ (X - C a)).leadingCoeff := by
      rw [leadingCoeff_divByMonic' hr]
      exact hlcf
    have hDq := opDz_interlaces hq hlcq
    have hlcDq := (opDz_lc hlcq).2
    have e : A207123.opDz f = (X - C a) * A207123.opDz (f /ₘ (X - C a)) + (1 + X) * (f /ₘ (X - C a)) := by
      conv_lhs => rw [← divByMonic_spec hr]
      exact opDz_X_sub_C_mul _ a
    rw [e]
    exact Interlaces.add_right (interlaces_X_sub_C_mul hDq.2.1 a) hDq hlcDq
      (leadingCoeff_mul_pos (leadingCoeff_X_sub_C_pos a) hlcDq)
      (leadingCoeff_mul_pos leadingCoeff_one_add_X_pos hlcq)
  obtain ⟨c, hc, w, hw, rfl⟩ := cone_of_interlaces h hlcf hlcg
  have hcone : InCone (A207123.opDz (coneSum f c w)) (A207123.opDz f) := by
    have e : A207123.opDz (coneSum f c w) = C c * A207123.opDz f +
        ∑ a ∈ f.roots.toFinset, C (w a) * A207123.opDz (f /ₘ (X - C a)) := by
      rw [coneSum, opDz_add, opDz_C_mul, opDz_sum]
      simp only [opDz_C_mul]
    rw [e]
    refine (InCone.C_mul (InCone.self _) hc).add
      (InCone.sum _ (fun a ha => hw a (Multiset.mem_toFinset.1 ha)) fun a ha => ?_)
    have hm := Multiset.mem_toFinset.1 ha
    exact (hgen a hm).inCone (opDz_lc hlcf).2
      (opDz_lc (by rw [leadingCoeff_divByMonic' (isRoot_of_mem_roots hm)]; exact hlcf)).2
  exact hcone.interlaces (hf.opDz hlcf) (opDz_lc hlcf).2
    (leadingCoeff_ne_zero.1 (opDz_lc hlcg).2.ne')

/-- 论文引理 8.8(2)：`g ≪ f` 推出 `𝒯g ≪ 𝒯f`。 -/
theorem Interlaces.opTz {g f : ℝ[X]} (h : Interlaces g f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) : Interlaces (opTz g) (opTz f) :=
  (interlaces_mul_iff realRooted_X).2 (h.opDz hlcf hlcg)

/-- 论文引理 8.8(2)：`g ≪ f` 推出 `Ψg ≪ Ψf`。 -/
theorem Interlaces.opPsiz {g f : ℝ[X]} (h : Interlaces g f) (hlcf : 0 < f.leadingCoeff)
    (hlcg : 0 < g.leadingCoeff) : Interlaces (opPsiz g) (opPsiz f) :=
  (interlaces_mul_iff realRooted_one_add_X).2 (h.opTz hlcf hlcg)

theorem nAbove_one_add_X_mul_zero {p : ℝ[X]} (hp : p ≠ 0) (h0 : nAbove p 0 = 0) :
    nAbove ((1 + X) * p) 0 = 0 := by
  rw [nAbove_mul realRooted_one_add_X.1 hp, nAbove_one_add_X_zero, h0]

theorem nAbove_opDz_zero {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff)
    (h0 : nAbove p 0 = 0) : nAbove (opDz p) 0 = 0 := by
  have h := ((opDz_interlaces hp hlc).2.2 0).1
  rw [nAbove_one_add_X_mul_zero hp.1 h0] at h
  omega

theorem nAbove_opTz_zero {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff)
    (h0 : nAbove p 0 = 0) : nAbove (opTz p) 0 = 0 := by
  rw [opTz, nAbove_mul realRooted_X.1 (hp.opDz hlc).1, nAbove_X, ite_eq_right (lt_irrefl 0),
    nAbove_opDz_zero hp hlc h0]

/-- 论文引理 8.8(3)：根都 `≤ 0` 时 `(1+z)p ≪ 𝒯p`。 -/
theorem interlaces_one_add_X_mul_opTz {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff)
    (h0 : nAbove p 0 = 0) : Interlaces ((1 + X) * p) (opTz p) :=
  (opDz_interlaces hp hlc).X_mul (nAbove_one_add_X_mul_zero hp.1 h0)

theorem RealRooted.opTz {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff) :
    RealRooted (opTz p) :=
  realRooted_mul realRooted_X (hp.opDz hlc)

theorem RealRooted.opPsiz {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff) :
    RealRooted (opPsiz p) :=
  realRooted_mul realRooted_one_add_X (hp.opTz hlc)

/-- 论文引理 8.8(1)：`𝒟p`、`𝒯p`、`Ψp` 实根，次数分别为 `deg p`、`deg p + 1`、`deg p + 2`
（`p` 实根、首项系数为正）。 -/
theorem lemma_il_T_one {p : ℝ[X]} (hp : RealRooted p) (hlc : 0 < p.leadingCoeff) :
    RealRooted (opDz p) ∧ RealRooted (opTz p) ∧ RealRooted (opPsiz p) ∧
      (opDz p).natDegree = p.natDegree ∧ (opTz p).natDegree = p.natDegree + 1 ∧
      (opPsiz p).natDegree = p.natDegree + 2 := by
  have hD := opDz_lc hlc
  have hDne : opDz p ≠ 0 := leadingCoeff_ne_zero.1 hD.2.ne'
  have hT : (opTz p).natDegree = p.natDegree + 1 := by
    rw [opTz, natDegree_X_mul hDne, hD.1]
  refine ⟨hp.opDz hlc, hp.opTz hlc, hp.opPsiz hlc, hD.1, hT, ?_⟩
  have h1 : (1 + X : ℝ[X]).natDegree = 1 := by
    rw [one_add_X_eq, natDegree_X_sub_C]
  rw [opPsiz, natDegree_mul realRooted_one_add_X.1 (hp.opTz hlc).1, hT, h1]
  omega

/-! ## 4. 论文引理 8.9：行多项式的递推 -/

/-- 论文引理 8.9：`k ≥ 1` 时 `n_{k+3} = (1+z)·n_{k+2} + Ψn_k`（由三角递推 `N_tri` 逐个系数比较）。 -/
theorem nR_rec {k : ℕ} (hk : 1 ≤ k) : nR (k + 3) = (1 + X) * nR (k + 2) + opPsiz (nR k) := by
  have hk0 : N k 0 = 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact N_succ_zero k'
  have hk2 : N (k + 2) 0 = 0 := N_succ_zero (k + 1)
  ext j
  rw [coeff_add, coeff_nR, opPsiz]
  rcases j with _ | j
  · rw [coeff_one_add_X_mul_zero, coeff_one_add_X_mul_zero, coeff_opTz_zero, coeff_nR]
    have h := N_tri k 0
    rw [hk2, zero_add, Nat.zero_mul, add_zero] at h
    rw [h]
    simp
  · rw [coeff_one_add_X_mul_succ, coeff_one_add_X_mul_succ, coeff_nR, coeff_nR, coeff_opTz_succ]
    rcases j with _ | j
    · rw [coeff_opTz_zero, coeff_opDz, coeff_nR, coeff_nR]
      have h := N_tri k 1
      rw [show 1 - 1 = 0 from rfl, hk0] at h
      rw [h]
      push_cast
      ring
    · rw [coeff_opTz_succ, coeff_opDz, coeff_opDz, coeff_nR, coeff_nR, coeff_nR]
      have h := N_tri k (j + 1 + 1)
      rw [Nat.add_sub_cancel] at h
      rw [h]
      push_cast
      ring

theorem nR_rec' {k : ℕ} (hk : 1 ≤ k) : nR (k + 3) = (1 + X) * (nR (k + 2) + opTz (nR k)) := by
  rw [nR_rec hk, opPsiz]
  ring

/-! ## 5. 初值 `k ≤ 3` -/

theorem N_three : N 3 1 = 1 ∧ N 3 2 = 4 ∧ N 3 3 = 2 := by
  have h0 := N_tri 0 0
  have h1 := N_tri 0 1
  have h01 : N 0 1 = 0 := N_eq_zero_of_lt (by norm_num)
  have h02 : N 0 2 = 0 := N_eq_zero_of_lt (by norm_num)
  have h20 : N 2 0 = 0 := N_succ_zero 1
  norm_num [N_init, h01, h02, h20] at h0 h1
  exact ⟨h0, h1, N_diag 3 (by norm_num)⟩

theorem nR_one : nR 1 = C 1 := by
  ext j
  rw [coeff_nR, coeff_C]
  rcases j with _ | j
  · simp [N_init]
  · rw [N_eq_zero_of_lt (by omega)]
    simp

theorem nR_two : nR 2 = C 2 * (X - C (-1 / 2)) := by
  ext j
  rw [coeff_nR, coeff_C_mul, coeff_sub, coeff_X, coeff_C]
  rcases j with _ | _ | j
  · norm_num [N_init]
  · norm_num [N_init]
  · rw [N_eq_zero_of_lt (by omega)]
    simp

/-- `n_3 = 2z² + 4z + 1` 的两个根 `−1 ∓ √2/2`。 -/
def r31 : ℝ := -1 - Real.sqrt 2 / 2

def r32 : ℝ := -1 + Real.sqrt 2 / 2

theorem sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

theorem nR_three : nR 3 = C 2 * ((X - C r31) * (X - C r32)) := by
  have e1 : nR 3 = C 2 * X ^ 2 + C 4 * X + C 1 := by
    ext j
    rw [coeff_nR, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    obtain ⟨n1, n2, n3⟩ := N_three
    rcases j with _ | _ | _ | j
    · simp [n1]
    · simp [n2]
    · simp [n3]
    · rw [N_eq_zero_of_lt (by omega)]
      simp
  rw [e1]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub, r31, r32]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  linear_combination (1 / 2 : ℝ) * h

theorem opTz_nR_one : opTz (nR 1) = C 2 * (X - C 0) := by
  rw [nR_one]
  apply Polynomial.funext
  intro r
  simp only [opTz, opDz, derivative_C, mul_zero, zero_add, eval_mul, eval_C, eval_X, eval_sub]
  ring

theorem opTz_nR_two : opTz (nR 2) = C 6 * ((X - C 0) * (X - C (-2 / 3))) := by
  rw [nR_two]
  apply Polynomial.funext
  intro r
  simp only [opTz, opDz, derivative_mul, derivative_C, derivative_sub, derivative_X, eval_mul,
    eval_add, eval_C, eval_X, eval_sub, eval_one, zero_mul, zero_add, sub_zero, mul_one]
  ring

theorem opPsiz_nR_one : opPsiz (nR 1) = C 2 * ((X - C 0) * (X - C (-1))) := by
  rw [opPsiz, opTz_nR_one]
  apply Polynomial.funext
  intro r
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_sub, eval_one]
  ring

theorem opTz_nR_three :
    opTz (nR 3) = C 8 * ((X - C 0) * ((X - C (-1 / 2)) * (X - C (-3 / 2)))) := by
  have e1 : nR 3 = C 2 * X ^ 2 + C 4 * X + C 1 := by
    rw [nR_three]
    apply Polynomial.funext
    intro r
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub, r31, r32]
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linear_combination (-1 / 2 : ℝ) * h
  rw [e1]
  apply Polynomial.funext
  intro r
  simp only [opTz, opDz, derivative_add, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, eval_mul, eval_add, eval_C, eval_X, eval_sub, eval_one, eval_pow, zero_mul,
    zero_add, mul_one, add_zero]
  push_cast
  ring

/-- 一次因子乘积的根数。 -/
theorem nAbove_lin1 {a : ℝ} (ha : a ≠ 0) (r x : ℝ) :
    nAbove (C a * (X - C r)) x = if x < r then 1 else 0 := by
  rw [nAbove_C_mul _ ha, nAbove_X_sub_C]

theorem nAbove_lin2 {a : ℝ} (ha : a ≠ 0) (r s x : ℝ) :
    nAbove (C a * ((X - C r) * (X - C s))) x = (if x < r then 1 else 0) + (if x < s then 1 else 0) := by
  rw [nAbove_C_mul _ ha, nAbove_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero s), nAbove_X_sub_C,
    nAbove_X_sub_C]

theorem nAbove_lin3 {a : ℝ} (ha : a ≠ 0) (r s t x : ℝ) :
    nAbove (C a * ((X - C r) * ((X - C s) * (X - C t)))) x =
      (if x < r then 1 else 0) + ((if x < s then 1 else 0) + (if x < t then 1 else 0)) := by
  rw [nAbove_C_mul _ ha, nAbove_mul (X_sub_C_ne_zero r)
    (mul_ne_zero (X_sub_C_ne_zero s) (X_sub_C_ne_zero t)),
    nAbove_mul (X_sub_C_ne_zero s) (X_sub_C_ne_zero t), nAbove_X_sub_C, nAbove_X_sub_C,
    nAbove_X_sub_C]

theorem rr_lin1 {a : ℝ} (ha : a ≠ 0) (r : ℝ) : RealRooted (C a * (X - C r)) :=
  (realRooted_X_sub_C r).C_mul ha

theorem rr_lin2 {a : ℝ} (ha : a ≠ 0) (r s : ℝ) : RealRooted (C a * ((X - C r) * (X - C s))) :=
  (realRooted_mul (realRooted_X_sub_C r) (realRooted_X_sub_C s)).C_mul ha

theorem rr_lin3 {a : ℝ} (ha : a ≠ 0) (r s t : ℝ) :
    RealRooted (C a * ((X - C r) * ((X - C s) * (X - C t)))) :=
  (realRooted_mul (realRooted_X_sub_C r)
    (realRooted_mul (realRooted_X_sub_C s) (realRooted_X_sub_C t))).C_mul ha

/-- 论文命题 8.10 的 (α_2)：`n_1 ≪ n_2`。 -/
theorem alpha_two : Interlaces (nR 1) (nR 2) := by
  rw [nR_one, nR_two]
  refine ⟨rr_lin1 two_ne_zero _, realRooted_C one_ne_zero, fun x => ?_⟩
  rw [nAbove_lin1 two_ne_zero, nAbove, roots_C, Multiset.filter_zero, Multiset.card_zero]
  split_ifs <;> omega

/-- 论文命题 8.10 的 (β_2)：`n_2 ≪ 𝒯n_1`。 -/
theorem beta_two : Interlaces (nR 2) (opTz (nR 1)) := by
  rw [opTz_nR_one, nR_two]
  refine ⟨rr_lin1 two_ne_zero _, rr_lin1 two_ne_zero _, fun x => ?_⟩
  rw [nAbove_lin1 two_ne_zero, nAbove_lin1 two_ne_zero]
  by_cases h1 : x < -1 / 2 <;> by_cases h2 : x < 0 <;> simp only [h1, h2, ↓reduceIte] <;>
    first | omega | (exfalso; linarith)

theorem alpha_three : Interlaces (nR 2) (nR 3) := by
  rw [nR_two, nR_three]
  obtain ⟨s1, s2⟩ := sqrt_two_bounds
  refine ⟨rr_lin2 two_ne_zero _ _, rr_lin1 two_ne_zero _, fun x => ?_⟩
  rw [nAbove_lin1 two_ne_zero, nAbove_lin2 two_ne_zero]
  by_cases h1 : x < -1 / 2 <;> by_cases h2 : x < r31 <;> by_cases h3 : x < r32 <;>
    simp only [h1, h2, h3, ↓reduceIte] <;>
    first | omega | (exfalso; simp only [r31, r32] at h1 h2 h3; linarith)

theorem beta_three : Interlaces (nR 3) (opTz (nR 2)) := by
  rw [opTz_nR_two, nR_three]
  obtain ⟨s1, s2⟩ := sqrt_two_bounds
  refine ⟨rr_lin2 (a := 6) (by norm_num) _ _, rr_lin2 two_ne_zero _ _, fun x => ?_⟩
  rw [nAbove_lin2 (a := 6) (by norm_num), nAbove_lin2 two_ne_zero]
  by_cases h1 : x < 0 <;> by_cases h2 : x < -2 / 3 <;> by_cases h3 : x < r31 <;>
    by_cases h4 : x < r32 <;> simp only [h1, h2, h3, h4, ↓reduceIte] <;>
    first | omega | (exfalso; simp only [r31, r32] at h1 h2 h3 h4; linarith)

theorem delta_three : Interlaces (nR 3) (opPsiz (nR 1)) := by
  rw [opPsiz_nR_one, nR_three]
  obtain ⟨s1, s2⟩ := sqrt_two_bounds
  refine ⟨rr_lin2 two_ne_zero _ _, rr_lin2 two_ne_zero _ _, fun x => ?_⟩
  rw [nAbove_lin2 two_ne_zero, nAbove_lin2 two_ne_zero]
  by_cases h1 : x < 0 <;> by_cases h2 : x < -1 <;> by_cases h3 : x < r31 <;>
    by_cases h4 : x < r32 <;> simp only [h1, h2, h3, h4, ↓reduceIte] <;>
    first | omega | (exfalso; simp only [r31, r32] at h1 h2 h3 h4; linarith)

theorem epsilon_three : Interlaces (opPsiz (nR 1)) (opTz (nR 3)) := by
  rw [opPsiz_nR_one, opTz_nR_three]
  refine ⟨rr_lin3 (a := 8) (by norm_num) _ _ _, rr_lin2 two_ne_zero _ _, fun x => ?_⟩
  rw [nAbove_lin2 two_ne_zero, nAbove_lin3 (a := 8) (by norm_num)]
  by_cases h1 : x < 0 <;> by_cases h2 : x < -1 <;> by_cases h3 : x < -1 / 2 <;>
    by_cases h4 : x < -3 / 2 <;> simp only [h1, h2, h3, h4, ↓reduceIte] <;>
    first | omega | (exfalso; linarith)

/-! ## 6. 论文命题 8.10 -/

/-- 归纳的一步：由 (α_{k−1})、(β_{k−1})、(α_k)、(β_k)、(δ_k)、(ε_k) 推出 `k + 1` 的四个关系
（论文命题 8.10 的证明；这里 `k = j + 3`，`A = n_k`、`B = n_{k−1}`、`C = n_{k−2}`）。 -/
theorem four_step (j : ℕ)
    (ha1 : Interlaces (nR (j + 1)) (nR (j + 2))) (hb1 : Interlaces (nR (j + 2)) (opTz (nR (j + 1))))
    (ha : Interlaces (nR (j + 2)) (nR (j + 3))) (hb : Interlaces (nR (j + 3)) (opTz (nR (j + 2))))
    (hd : Interlaces (nR (j + 3)) (opPsiz (nR (j + 1))))
    (he : Interlaces (opPsiz (nR (j + 1))) (opTz (nR (j + 3)))) :
    Interlaces (nR (j + 3)) (nR (j + 4)) ∧ Interlaces (nR (j + 4)) (opTz (nR (j + 3))) ∧
      Interlaces (nR (j + 4)) (opPsiz (nR (j + 2))) ∧
      Interlaces (opPsiz (nR (j + 2))) (opTz (nR (j + 4))) := by
  set A := nR (j + 3) with hA
  set B := nR (j + 2) with hB
  set Cc := nR (j + 1) with hC
  have hrec : nR (j + 4) = (1 + X) * A + opPsiz Cc := nR_rec (k := j + 1) (by omega)
  have hrec' : nR (j + 4) = (1 + X) * (A + opTz Cc) := nR_rec' (k := j + 1) (by omega)
  have hAr : RealRooted A := ha.1
  have hBr : RealRooted B := ha.2.1
  have hCr : RealRooted Cc := ha1.2.1
  have hlA : 0 < A.leadingCoeff := leadingCoeff_nR_pos (by omega)
  have hlB : 0 < B.leadingCoeff := leadingCoeff_nR_pos (by omega)
  have hlC : 0 < Cc.leadingCoeff := leadingCoeff_nR_pos (by omega)
  have h0A : nAbove A 0 = 0 := nAbove_nR_zero (by omega)
  have h0B : nAbove B 0 = 0 := nAbove_nR_zero (by omega)
  have h0C : nAbove Cc 0 = 0 := nAbove_nR_zero (by omega)
  have hl1A : 0 < ((1 + X) * A).leadingCoeff := leadingCoeff_mul_pos leadingCoeff_one_add_X_pos hlA
  have hTCB : Interlaces (opTz Cc) (opTz B) := ha1.opTz hlB hlC
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (α_{k+1})
    rw [hrec]
    have h1 : Interlaces A ((1 + X) * A) := by
      rw [one_add_X_eq]
      exact interlaces_X_sub_C_mul hAr _
    exact h1.add_right hd hlA hl1A (opPsiz_lc hlC)
  · -- (β_{k+1})
    rw [hrec]
    exact (interlaces_one_add_X_mul_opTz hAr hlA h0A).add_left he (opTz_lc hlA) hl1A (opPsiz_lc hlC)
  · -- (δ_{k+1})
    rw [hrec', opPsiz]
    exact (interlaces_mul_iff realRooted_one_add_X).2
      (hb.add_left hTCB (opTz_lc hlB) hlA (opTz_lc hlC))
  · -- (ε_{k+1})
    have hT : opTz (nR (j + 4)) = opPsiz A + (1 + X) * (X * A) + (1 + X) * opTz (opTz Cc) +
        (1 + X) * (X * opTz Cc) := by
      rw [hrec', opTz_one_add_X_mul, opTz_add, opPsiz]
      ring
    have h0TB : nAbove (opTz B) 0 = 0 := nAbove_opTz_zero hBr hlB h0B
    have hlTB := opTz_lc hlB
    have hlTC := opTz_lc hlC
    have e1 : Interlaces (opPsiz B) (opPsiz A) := ha.opPsiz hlA hlB
    have e2 : Interlaces (opPsiz B) ((1 + X) * (X * A)) := by
      rw [opPsiz]
      exact (interlaces_mul_iff realRooted_one_add_X).2 (hb.X_mul h0TB)
    have e3 : Interlaces (opPsiz B) ((1 + X) * opTz (opTz Cc)) := by
      rw [opPsiz]
      exact (interlaces_mul_iff realRooted_one_add_X).2 (hb1.opTz hlTC hlB)
    have e4 : Interlaces (opPsiz B) ((1 + X) * (X * opTz Cc)) := by
      rw [opPsiz]
      exact (interlaces_mul_iff realRooted_one_add_X).2 (hTCB.X_mul h0TB)
    have l1 := opPsiz_lc hlA
    have l2 : 0 < ((1 + X) * (X * A)).leadingCoeff :=
      leadingCoeff_mul_pos leadingCoeff_one_add_X_pos (leadingCoeff_mul_pos leadingCoeff_X_pos hlA)
    have l3 : 0 < ((1 + X) * opTz (opTz Cc)).leadingCoeff :=
      leadingCoeff_mul_pos leadingCoeff_one_add_X_pos (opTz_lc hlTC)
    have l4 : 0 < ((1 + X) * (X * opTz Cc)).leadingCoeff :=
      leadingCoeff_mul_pos leadingCoeff_one_add_X_pos (leadingCoeff_mul_pos leadingCoeff_X_pos hlTC)
    have lB := opPsiz_lc hlB
    rw [hT]
    exact ((e1.add_right e2 lB l1 l2).add_right e3 lB (leadingCoeff_add_pos l1 l2) l3).add_right e4 lB
      (leadingCoeff_add_pos (leadingCoeff_add_pos l1 l2) l3) l4

/-- 论文命题 8.10：对每个 `k ≥ 3`（这里写成 `k + 3`），(α_k) `n_{k−1} ≪ n_k`、(β_k) `n_k ≪ 𝒯n_{k−1}`、
(δ_k) `n_k ≪ Ψn_{k−2}`、(ε_k) `Ψn_{k−2} ≪ 𝒯n_k`。 -/
theorem prop_four_relations (k : ℕ) :
    Interlaces (nR (k + 2)) (nR (k + 3)) ∧ Interlaces (nR (k + 3)) (opTz (nR (k + 2))) ∧
      Interlaces (nR (k + 3)) (opPsiz (nR (k + 1))) ∧
      Interlaces (opPsiz (nR (k + 1))) (opTz (nR (k + 3))) := by
  have key : ∀ k, (Interlaces (nR (k + 1)) (nR (k + 2)) ∧
      Interlaces (nR (k + 2)) (opTz (nR (k + 1)))) ∧
      (Interlaces (nR (k + 2)) (nR (k + 3)) ∧ Interlaces (nR (k + 3)) (opTz (nR (k + 2))) ∧
      Interlaces (nR (k + 3)) (opPsiz (nR (k + 1))) ∧
      Interlaces (opPsiz (nR (k + 1))) (opTz (nR (k + 3)))) := by
    intro k
    induction k with
    | zero => exact ⟨⟨alpha_two, beta_two⟩, alpha_three, beta_three, delta_three, epsilon_three⟩
    | succ k ih =>
      obtain ⟨⟨ha1, hb1⟩, ha, hb, hd, he⟩ := ih
      exact ⟨⟨ha, hb⟩, four_step k ha1 hb1 ha hb hd he⟩
  exact (key k).2

/-- 论文命题 8.10 的最后一句：每个 `n_k`（`k ≥ 1`）只有实根，即实根（计重数）的个数等于次数 `k − 1`。 -/
theorem realRooted_nR {k : ℕ} (hk : 1 ≤ k) : RealRooted (nR k) := by
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · rw [nR_one]
    exact realRooted_C one_ne_zero
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact (prop_four_relations j).1.2.1

/-- 实根多项式的复根都是实数。 -/
theorem RealRooted.im_eq_zero {p : ℝ[X]} (hp : RealRooted p) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) : z.im = 0 := by
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hp.2
  rw [← hprod, Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, Multiset.map_map, eval_mul,
    eval_C, eval_multiset_prod, Multiset.map_map] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd ((algebraMap ℝ ℂ).injective (by rw [h, map_zero])) (leadingCoeff_ne_zero.2 hp.1)
  · rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
    obtain ⟨a, _, ha⟩ := h
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C] at ha
    rw [sub_eq_zero.1 ha]
    simp

/-- 论文定理 8.1 第一句的「实根」部分（`HStruct.lean` 的有理系数 `nrowPoly k`）：`k ≥ 1` 时 `n_k` 的每个
复根都是实数。 -/
theorem nrowPoly_root_im_eq_zero {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : aeval z (nrowPoly k) = 0) :
    z.im = 0 := by
  apply (realRooted_nR hk).im_eq_zero
  rw [nR_eq_map, Polynomial.map_map]
  convert hz using 1
  rw [aeval_def, eval₂_eq_eval_map]
  congr 2

end

end A207123
