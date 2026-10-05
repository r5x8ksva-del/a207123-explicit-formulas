import A207123.OreRelN

/-!
# 报告 T3.7(3) 的后半：`N` 没有系数只依赖 `k` 的象限递推

**T3.7(3)**（后半，`no_k_only_recurrence_N`）：设 `p_{ab} ∈ ℂ[k]`（`0 ≤ a ≤ A`，`0 ≤ b ≤ B`）不全为 0，
则不存在 `k0, q0` 使 `Σ_{a,b} p_{ab}(k)·N(k−a, q−b) = 0` 对象限 `k ≥ k0, q ≥ q0` 中的一切 `(k, q)` 成立
（与 T3.7(2) 的 `no_k_only_recurrence` 相同，另要求 `k ≥ A`、`q ≥ B` 使下标非负；把象限缩小不影响结论）。
前半「`𝒩` 不是 D-finite」在 `DFiniteN.lean`。

**证明路线**（与 `OreRelN.lean` 同一套搬运，不用极点论证）：
* 把递推写成算子 `R = Σ p_{ab}(k)·X^a·Y^b`，它在象限上零化 `N`。
* 二项式变换 `P`（`V = P·N`）与只依赖 `k` 的系数、`X` 可交换，且 `Δ^b·P·Y^b = Y^b·P`
  （`Δ = 1 − Y`），所以 `Δ^B·P·R = M·P`，`M = Σ p_{ab}(k)·X^a·Δ^{B−b}·Y^b` 的系数仍只依赖 `k`
  （`opD_pow_P_kOp`）。
* `Δ^{q0}` 消去边界部分（`opD_pow_P_vanish`），于是 `M' := Δ^{q0}·M` 在象限上零化 `V = Y·U + e0`，
  从而 `M'·Y` 在象限上零化 `U`。
* `M'·Y` 是系数只依赖 `k` 的算子（`KOnly`，对左乘 `p(k)`、`X`、`Y`、`Δ` 封闭），由 T3.7(2)
  （`no_k_only_recurrence`）它为 0（`kOnly_ann_zero`）。
* 逐步消去：`Y` 可从右边消去（`eq_zero_of_mul_opEinv`），`Δ`、`P` 单射，得 `R = 0`；
  正规形唯一（`normal_form_unique`）给出所有 `p_{ab} = 0`，矛盾。
-/

open Polynomial Finset

namespace A207123

/-! ### 系数只依赖 `k` 的算子 -/

/-- 系数只依赖 `k` 的正规形 `Σ_{(a,b)} s_{ab}(k)·X^a·Y^b`（`s_{ab} ∈ ℂ[k]`）。 -/
noncomputable def kNorm (s : ℕ × ℕ →₀ ℂ[X]) : Module.End ℂ Arr :=
  s.sum fun ab q => mulOp (Polynomial.C q) * opX ^ ab.1 * opEinv ^ ab.2

/-- 辅助引理（T3.7(3)）：`kNorm` 可加。 -/
theorem kNorm_add (s s' : ℕ × ℕ →₀ ℂ[X]) : kNorm (s + s') = kNorm s + kNorm s' :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [C_add, map_add, add_mul, add_mul])

/-- 辅助引理（T3.7(3)）：`kNorm 0 = 0`。 -/
theorem kNorm_zero : kNorm 0 = 0 := Finsupp.sum_zero_index

/-- 辅助引理（T3.7(3)）：`kNorm` 与减法交换。 -/
theorem kNorm_sub (s s' : ℕ × ℕ →₀ ℂ[X]) : kNorm (s - s') = kNorm s - kNorm s' :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [C_sub, map_sub, sub_mul, sub_mul])

/-- 辅助引理（T3.7(3)）：单项的 `kNorm`。 -/
theorem kNorm_single (ab : ℕ × ℕ) (q : ℂ[X]) :
    kNorm (Finsupp.single ab q) = mulOp (Polynomial.C q) * opX ^ ab.1 * opEinv ^ ab.2 :=
  Finsupp.sum_single_index (by simp)

/-- 辅助引理（T3.7(3)）：`kNorm` 的作用。 -/
theorem kNorm_apply (s : ℕ × ℕ →₀ ℂ[X]) (f : Arr) (k m : ℕ) :
    kNorm s f k m = ∑ ab ∈ s.support, (s ab).eval (k : ℂ)
      * (if ab.1 ≤ k then (if ab.2 ≤ m then f (k - ab.1) (m - ab.2) else 0) else 0) := by
  simp only [kNorm, Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply,
    mulOp_apply, opX_pow_apply, opEinv_pow_apply, evalEval_C]

/-- 辅助引理（T3.7(3)）：左乘 `p(k)`。 -/
theorem mulOpC_mul_kNorm (p : ℂ[X]) (s : ℕ × ℕ →₀ ℂ[X]) :
    mulOp (Polynomial.C p) * kNorm s = kNorm (s.mapRange (fun q => p * q) (mul_zero p)) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [Finsupp.mapRange_zero, kNorm_zero, mul_zero]
  | add s s' hs hs' =>
    rw [kNorm_add, mul_add, hs, hs', Finsupp.mapRange_add (fun x y => mul_add p x y), kNorm_add]
  | single ab q =>
    rw [Finsupp.mapRange_single, kNorm_single, kNorm_single, C_mul, map_mul]
    simp only [mul_assoc]

/-- 辅助引理（T3.7(3)）：`k ↦ k − 1` 平移保持「只依赖 `k`」。 -/
theorem shiftK_C (q : ℂ[X]) : shiftK (Polynomial.C q) = Polynomial.C (q.comp (Polynomial.X - 1)) := by
  simp [shiftK]

/-- 辅助引理（T3.7(3)）：`m ↦ m − 1` 平移不改变只依赖 `k` 的系数。 -/
theorem shiftM_C (q : ℂ[X]) : shiftM (Polynomial.C q) = Polynomial.C q := by
  simp [shiftM]

/-- 辅助引理（T3.7(3)）：左乘 `X`。 -/
theorem opX_mul_kNorm (s : ℕ × ℕ →₀ ℂ[X]) :
    opX * kNorm s = kNorm ((s.mapRange (fun q => q.comp (Polynomial.X - 1)) (zero_comp)).mapDomain
      fun ab => (ab.1 + 1, ab.2)) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [Finsupp.mapRange_zero, Finsupp.mapDomain_zero, kNorm_zero, mul_zero]
  | add s s' hs hs' =>
    rw [kNorm_add, mul_add, hs, hs', Finsupp.mapRange_add (fun x y => add_comp),
      Finsupp.mapDomain_add, kNorm_add]
  | single ab q =>
    rw [Finsupp.mapRange_single, Finsupp.mapDomain_single, kNorm_single, kNorm_single,
      ← mul_assoc, ← mul_assoc, opX_mul_mulOp, shiftK_C, pow_succ']
    simp only [mul_assoc]

/-- 辅助引理（T3.7(3)）：左乘 `Y`。 -/
theorem opEinv_mul_kNorm (s : ℕ × ℕ →₀ ℂ[X]) :
    opEinv * kNorm s = kNorm (s.mapDomain fun ab => (ab.1, ab.2 + 1)) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [Finsupp.mapDomain_zero, kNorm_zero, mul_zero]
  | add s s' hs hs' => rw [kNorm_add, mul_add, hs, hs', Finsupp.mapDomain_add, kNorm_add]
  | single ab q =>
    have hE : opEinv * opX ^ ab.1 = opX ^ ab.1 * opEinv := (commute_opX_opEinv.pow_left _).eq.symm
    rw [Finsupp.mapDomain_single, kNorm_single, kNorm_single, ← mul_assoc, ← mul_assoc,
      opEinv_mul_mulOp, shiftM_C, mul_assoc (mulOp _), hE, pow_succ']
    simp only [mul_assoc]

/-- 系数只依赖 `k` 的算子（某个 `kNorm s`）。 -/
def KOnly (T : Module.End ℂ Arr) : Prop := ∃ s : ℕ × ℕ →₀ ℂ[X], T = kNorm s

/-- 辅助引理（T3.7(3)）：`1` 的系数只依赖 `k`。 -/
theorem KOnly.one : KOnly 1 :=
  ⟨Finsupp.single (0, 0) 1, by rw [kNorm_single, C_1, map_one, pow_zero, pow_zero, mul_one, mul_one]⟩

/-- 辅助引理（T3.7(3)）：`KOnly` 对加法封闭。 -/
theorem KOnly.add {T T' : Module.End ℂ Arr} (h : KOnly T) (h' : KOnly T') : KOnly (T + T') := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨s', rfl⟩ := h'
  exact ⟨s + s', (kNorm_add s s').symm⟩

/-- 辅助引理（T3.7(3)）：`KOnly` 对有限和封闭。 -/
theorem KOnly.sum {ι : Type*} (t : Finset ι) (T : ι → Module.End ℂ Arr)
    (h : ∀ i ∈ t, KOnly (T i)) : KOnly (∑ i ∈ t, T i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by rw [sum_empty, kNorm_zero]⟩
  | insert i t hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i t)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- 辅助引理（T3.7(3)）：`KOnly` 对左乘 `p(k)` 封闭。 -/
theorem KOnly.map_mulOpC {T : Module.End ℂ Arr} (p : ℂ[X]) (h : KOnly T) :
    KOnly (mulOp (Polynomial.C p) * T) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨_, mulOpC_mul_kNorm p s⟩

/-- 辅助引理（T3.7(3)）：`KOnly` 对左乘 `X` 封闭。 -/
theorem KOnly.map_opX {T : Module.End ℂ Arr} (h : KOnly T) : KOnly (opX * T) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨_, opX_mul_kNorm s⟩

/-- 辅助引理（T3.7(3)）：`KOnly` 对左乘 `Y` 封闭。 -/
theorem KOnly.map_opEinv {T : Module.End ℂ Arr} (h : KOnly T) : KOnly (opEinv * T) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨_, opEinv_mul_kNorm s⟩

/-- 辅助引理（T3.7(3)）：`KOnly` 对左乘 `Δ = 1 − Y` 封闭。 -/
theorem KOnly.map_opD {T : Module.End ℂ Arr} (h : KOnly T) : KOnly (opD * T) := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨s', hs'⟩ := KOnly.map_opEinv ⟨s, rfl⟩
  refine ⟨s - s', ?_⟩
  rw [kNorm_sub, ← hs', opD, sub_mul, one_mul]

/-- 辅助引理（T3.7(3)）：`KOnly` 对左乘 `g^n` 封闭（`g` 保持 `KOnly`）。 -/
theorem KOnly.pow_mul {g T : Module.End ℂ Arr} (hg : ∀ S, KOnly S → KOnly (g * S)) (n : ℕ)
    (h : KOnly T) : KOnly (g ^ n * T) := by
  induction n with
  | zero => rwa [pow_zero, one_mul]
  | succ n ih => rw [pow_succ', mul_assoc]; exact hg _ ih

/-- 辅助引理（T3.7(3)，由 T3.7(2)）：系数只依赖 `k` 的算子若在象限上零化 `U`，则系数全为 0。 -/
theorem kOnly_ann_zero (s : ℕ × ℕ →₀ ℂ[X]) {k0 m0 : ℕ} (h : VanishOn (kNorm s Uarr) k0 m0) :
    s = 0 := by
  classical
  by_contra hs
  obtain ⟨ab0, hab0⟩ := Finsupp.support_nonempty_iff.mpr hs
  set A' := s.support.sup Prod.fst with hA'
  set B' := s.support.sup Prod.snd with hB'
  have hle : ∀ ab ∈ s.support, ab.1 ≤ A' ∧ ab.2 ≤ B' := fun ab hab =>
    ⟨Finset.le_sup (f := Prod.fst) hab, Finset.le_sup (f := Prod.snd) hab⟩
  apply no_k_only_recurrence A' B' (max k0 A') (max m0 B') (fun a b => s (a, b))
    ⟨ab0.1, (hle ab0 hab0).1, ab0.2, (hle ab0 hab0).2, Finsupp.mem_support_iff.mp hab0⟩
  intro k m hk hm hAk hBm
  have h0 := h k m (le_of_max_le_left hk) (le_of_max_le_left hm)
  rw [kNorm_apply] at h0
  rw [← h0, ← sum_product']
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro ab hab
    rw [mem_product, mem_range, mem_range]
    exact ⟨by have := (hle ab hab).1; omega, by have := (hle ab hab).2; omega⟩
  · intro ab hab
    rw [mem_sdiff, Finsupp.mem_support_iff, not_not] at hab
    rw [hab.2]
    simp
  · intro ab hab
    have h1 : ab.1 ≤ k := le_trans (hle ab hab).1 hAk
    have h2 : ab.2 ≤ m := le_trans (hle ab hab).2 hBm
    simp only [h1, h2, ↓reduceIte, Uarr]

/-! ### 搬运 -/

/-- 辅助引理（T3.7(3)）：二项式变换 `P` 与只依赖 `k` 的乘法算子可交换。 -/
theorem P_mul_mulOpC (q : ℂ[X]) : opP * mulOp (Polynomial.C q) = mulOp (Polynomial.C q) * opP := by
  ext f k m
  simp only [Module.End.mul_apply, opP_apply, mulOp_apply, evalEval_C, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- 辅助引理（T3.7(3)）：`Δ` 与只依赖 `k` 的乘法算子可交换。 -/
theorem opD_mul_mulOpC (q : ℂ[X]) : opD * mulOp (Polynomial.C q) = mulOp (Polynomial.C q) * opD := by
  rw [opD_mul_mulOp, shiftM_C, sub_self, map_zero, zero_add]

/-- 辅助引理（T3.7(3)）：`Δ^b·P·Y^b = Y^b·P`。 -/
theorem opD_pow_P_opEinv_pow (b : ℕ) : opD ^ b * opP * opEinv ^ b = opEinv ^ b * opP := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hc : opD ^ b * opEinv = opEinv * opD ^ b := (commute_opD_opEinv.pow_left b).eq
    calc opD ^ (b + 1) * opP * opEinv ^ (b + 1)
        = opD ^ b * (opD * opP * opEinv) * opEinv ^ b := by
          rw [pow_succ opD b, pow_succ' opEinv b]; simp only [mul_assoc]
      _ = opEinv * (opD ^ b * opP * opEinv ^ b) := by
          rw [opD_P_Y, ← mul_assoc (opD ^ b), hc]; simp only [mul_assoc]
      _ = opEinv ^ (b + 1) * opP := by rw [ih, pow_succ']; simp only [mul_assoc]

/-- 辅助引理（T3.7(3)）：单项的搬运：`b ≤ B` 时 `Δ^B·P·(q(k)·X^a·Y^b) = q(k)·X^a·Δ^{B−b}·Y^b·P`。 -/
theorem opD_pow_P_mono (B a b : ℕ) (hb : b ≤ B) (q : ℂ[X]) :
    opD ^ B * opP * (mulOp (Polynomial.C q) * opX ^ a * opEinv ^ b)
      = mulOp (Polynomial.C q) * opX ^ a * opD ^ (B - b) * opEinv ^ b * opP := by
  have h1 : opD ^ B * mulOp (Polynomial.C q) = mulOp (Polynomial.C q) * opD ^ B :=
    ((show Commute opD (mulOp (Polynomial.C q)) from opD_mul_mulOpC q).pow_left B).eq
  have h2 : opD ^ B * opX ^ a = opX ^ a * opD ^ B := ((commute_opD_opX.pow_left B).pow_right a).eq
  have h3 : opP * opX ^ a = opX ^ a * opP :=
    ((show Commute opP opX from P_mul_opX).pow_right a).eq
  have h4 : opD ^ B = opD ^ (B - b) * opD ^ b := by rw [← pow_add, Nat.sub_add_cancel hb]
  calc opD ^ B * opP * (mulOp (Polynomial.C q) * opX ^ a * opEinv ^ b)
      = opD ^ B * mulOp (Polynomial.C q) * (opP * opX ^ a) * opEinv ^ b := by
        simp only [mul_assoc]
        rw [← mul_assoc opP (mulOp _), P_mul_mulOpC]
        simp only [mul_assoc]
    _ = mulOp (Polynomial.C q) * (opD ^ B * opX ^ a) * opP * opEinv ^ b := by
        rw [h1, h3]; simp only [mul_assoc]
    _ = mulOp (Polynomial.C q) * opX ^ a * opD ^ (B - b) * (opD ^ b * opP * opEinv ^ b) := by
        rw [h2, h4]; simp only [mul_assoc]
    _ = mulOp (Polynomial.C q) * opX ^ a * opD ^ (B - b) * opEinv ^ b * opP := by
        rw [opD_pow_P_opEinv_pow]; simp only [mul_assoc]

/-- 辅助引理（T3.7(3)）：只依赖 `k` 的递推算子 `R = Σ_{a≤A, b≤B} p_{ab}(k)·X^a·Y^b` 的搬运：
`Δ^B·P·R = M·P`，`M = Σ p_{ab}(k)·X^a·Δ^{B−b}·Y^b`。 -/
theorem opD_pow_P_kOp (A B : ℕ) (p : ℕ → ℕ → ℂ[X]) :
    opD ^ B * opP * (∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
        mulOp (Polynomial.C (p a b)) * opX ^ a * opEinv ^ b)
      = (∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
          mulOp (Polynomial.C (p a b)) * opX ^ a * opD ^ (B - b) * opEinv ^ b) * opP := by
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro b hb
  exact opD_pow_P_mono B a b (by rw [mem_range] at hb; omega) (p a b)

/-! ### 主定理 -/

/-- **T3.7(3)**（后半）：`N` 没有系数只依赖 `k` 的象限递推。即设 `p_{ab} ∈ ℂ[k]`（`a ≤ A`、`b ≤ B`）
不全为 0，则不存在 `k0, q0` 使 `Σ_{a≤A, b≤B} p_{ab}(k)·N(k−a, q−b) = 0` 对象限 `k ≥ k0, q ≥ q0` 中的
一切 `(k, q)` 成立（象限内另要求 `k ≥ A`、`q ≥ B`，使下标非负；把象限缩小不影响结论）。 -/
theorem no_k_only_recurrence_N (A B k0 q0 : ℕ) (p : ℕ → ℕ → ℂ[X])
    (hp : ∃ a ≤ A, ∃ b ≤ B, p a b ≠ 0) :
    ¬ ∀ k q, k0 ≤ k → q0 ≤ q → A ≤ k → B ≤ q →
      ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1), (p a b).eval (k : ℂ) * (N (k - a) (q - b) : ℂ) = 0 := by
  classical
  intro hrel
  -- 递推算子 `R`
  set R : Module.End ℂ Arr := ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
    mulOp (Polynomial.C (p a b)) * opX ^ a * opEinv ^ b with hRdef
  have hRmem : R ∈ OU := sum_mem fun a _ => sum_mem fun b _ =>
    mul_mem (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem a)) (pow_mem opEinv_mem b)
  set K0 := max k0 A with hK0
  set Q0 := max q0 B with hQ0
  have hvan : VanishOn (R Narr) K0 Q0 := by
    intro k q hk hq
    rw [← hrel k q (le_of_max_le_left hk) (le_of_max_le_left hq) (le_of_max_le_right hk)
      (le_of_max_le_right hq), hRdef, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply]
    apply sum_congr rfl
    intro a ha
    rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply]
    apply sum_congr rfl
    intro b hb
    rw [mem_range] at ha hb
    have h1 : a ≤ k := by have := le_of_max_le_right hk; omega
    have h2 : b ≤ q := by have := le_of_max_le_right hq; omega
    simp only [Module.End.mul_apply, mulOp_apply, opX_pow_apply, opEinv_pow_apply, evalEval_C,
      h1, h2, ↓reduceIte, Narr]
  -- 搬运：`Δ^B·P·R = M·P`
  set M : Module.End ℂ Arr := ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
    mulOp (Polynomial.C (p a b)) * opX ^ a * opD ^ (B - b) * opEinv ^ b with hMdef
  have hT : opD ^ B * opP * R = M * opP := opD_pow_P_kOp A B p
  have hMmem : M ∈ OU := sum_mem fun a _ => sum_mem fun b _ =>
    mul_mem (mul_mem (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem a)) (pow_mem opD_mem _))
      (pow_mem opEinv_mem b)
  set M' := opD ^ Q0 * M with hM'def
  have hM'mem : M' ∈ OU := mul_mem (pow_mem opD_mem _) hMmem
  -- `M'` 在象限上零化 `V = P·N`
  have hV : VanishOn (M' (opP Narr)) K0 (Q0 + B) := by
    have e : M' (opP Narr) = (opD ^ (Q0 + B) * opP) (R Narr) := by
      have h := LinearMap.congr_fun hT Narr
      simp only [Module.End.mul_apply] at h
      rw [hM'def, Module.End.mul_apply, ← h, pow_add]
      simp only [Module.End.mul_apply]
    rw [e]
    exact opD_pow_P_vanish (Q0 + B) (R Narr) K0 (fun k q hk hq => hvan k q hk (by omega))
  -- `M'·Y` 在象限上零化 `U`
  obtain ⟨A1, B1, hreach⟩ := reach_of_mem hM'mem
  have he0 : VanishOn (M' e0) (1 + A1) (1 + B1) :=
    hreach e0 1 1 (fun k m hk hm => by simp only [e0]; split_ifs with h <;> first | rfl | omega)
  have hU : VanishOn ((M' * opEinv) Uarr) (max K0 (1 + A1)) (max (Q0 + B) (1 + B1)) := by
    intro k m hk hm
    have h1 := hV k m (le_of_max_le_left hk) (le_of_max_le_left hm)
    have h2 := he0 k m (le_of_max_le_right hk) (le_of_max_le_right hm)
    rw [opP_Narr, map_add, Pi.add_apply, Pi.add_apply, h2, add_zero] at h1
    exact h1
  -- `M'·Y` 的系数只依赖 `k`
  have hK : KOnly (M' * opEinv) := by
    rw [hM'def, mul_assoc]
    apply KOnly.pow_mul (fun S hS => hS.map_opD) Q0
    rw [hMdef, sum_mul]
    apply KOnly.sum
    intro a _
    rw [sum_mul]
    apply KOnly.sum
    intro b _
    have e : mulOp (Polynomial.C (p a b)) * opX ^ a * opD ^ (B - b) * opEinv ^ b * opEinv
        = mulOp (Polynomial.C (p a b)) * (opX ^ a * (opD ^ (B - b) * (opEinv ^ (b + 1) * 1))) := by
      rw [mul_one, pow_succ]; simp only [mul_assoc]
    rw [e]
    apply KOnly.map_mulOpC
    apply KOnly.pow_mul (fun S hS => hS.map_opX) a
    apply KOnly.pow_mul (fun S hS => hS.map_opD) (B - b)
    exact KOnly.pow_mul (fun S hS => hS.map_opEinv) (b + 1) KOnly.one
  obtain ⟨s, hs⟩ := hK
  have hs0 : s = 0 := kOnly_ann_zero s (hs ▸ hU)
  -- 逐步消去，得 `R = 0`
  have hMY : M' * opEinv = 0 := by rw [hs, hs0, kNorm_zero]
  have hM'0 : M' = 0 := eq_zero_of_mul_opEinv hM'mem hMY
  have hM0 : M = 0 := by
    have h : opD ^ Q0 * M = opD ^ Q0 * 0 := by rw [mul_zero]; exact hM'0
    exact cancel_left_of_injective (opD_pow_injective Q0) h
  have hR0 : R = 0 := by
    have h1 : opD ^ B * (opP * R) = opD ^ B * (opP * 0) := by
      rw [← mul_assoc, hT, hM0, zero_mul, mul_zero, mul_zero]
    have h2 := cancel_left_of_injective (opD_pow_injective B) h1
    exact cancel_left_of_injective opP_injective (by rw [h2])
  -- `R` 的正规形
  set r : ℕ × ℕ →₀ Coef := ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1),
    Finsupp.single (a, b) (Polynomial.C (p a b)) with hrdef
  have hRr : R = normOp r := by
    rw [hRdef, hrdef]
    have hn : ∀ (t : Finset ℕ) (g : ℕ → ℕ × ℕ →₀ Coef),
        normOp (∑ i ∈ t, g i) = ∑ i ∈ t, normOp (g i) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => rw [sum_empty, sum_empty, normOp_zero]
      | insert i t hi ih => rw [sum_insert hi, sum_insert hi, normOp_add, ih]
    rw [hn]
    apply sum_congr rfl
    intro a _
    rw [hn]
    apply sum_congr rfl
    intro b _
    rw [normOp_single]
  have hr0 : r = 0 := normal_form_unique r (by rw [← hRr, hR0])
  -- 于是一切 `p_{ab} = 0`，矛盾
  obtain ⟨a0, ha0, b0, hb0, hp0⟩ := hp
  apply hp0
  have hval : r (a0, b0) = Polynomial.C (p a0 b0) := by
    rw [hrdef, Finsupp.finsetSum_apply, sum_eq_single a0]
    · rw [Finsupp.finsetSum_apply, sum_eq_single b0]
      · rw [Finsupp.single_eq_same]
      · intro b _ hb
        rw [Finsupp.single_eq_of_ne (by intro h; have := congrArg Prod.snd h; simp only at this; omega)]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    · intro a _ ha
      rw [Finsupp.finsetSum_apply]
      apply sum_eq_zero
      intro b _
      rw [Finsupp.single_eq_of_ne (by intro h; have := congrArg Prod.fst h; simp only at this; omega)]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  have := congrArg (fun t : ℕ × ℕ →₀ Coef => t (a0, b0)) hr0
  simp only [Finsupp.coe_zero, Pi.zero_apply] at this
  rw [hval] at this
  exact Polynomial.C_eq_zero.mp this

end A207123
