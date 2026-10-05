import A207123.NonDFinite

/-!
# 全部多项式系数象限递推 = 引理 1 生成的左理想（报告 T3.8 的 `U` 部分）

**报告的设定**（T3.8）：`O_U = ℂ[k,m]⟨X, E⁻¹⟩`（`X : k ↦ k − 1`，`E⁻¹ : m ↦ m − 1`），
`Rel(U)` 是在某个象限上零化 `U` 的算子全体，`L1 = 1 − E⁻¹ − X − m·X³`。结论 `Rel(U) = O_U·L1`。

**Lean 中的实现**：
* 算子作用在 `ℕ × ℕ` 上的复数组上（`Arr`，负下标处补 0）：乘法算子 `mulOp p`（`p ∈ ℂ[k,m]`）、
  位移 `opX`、`opEinv`。
* `OU`：`End_ℂ(ℂ^{ℕ×ℕ})` 中由 `k`、`m`、`X`、`E⁻¹` 生成的 `ℂ`-子代数。它满足 Ore 交换律
  `X·p(k,m) = p(k−1,m)·X`、`E⁻¹·p(k,m) = p(k,m−1)·E⁻¹`（`opX_mul_mulOp`、`opEinv_mul_mulOp`），
  每个元素都能写成 `Σ r_{ab}(k,m)·X^a·E^{−b}`（`exists_normal_form`），且写法唯一
  （`normal_form_unique`）。所以 `OU` 就是报告中的 Ore 代数 `O_U`（它在 `ℂ^{ℕ×ℕ}` 上的作用是忠实的）。
* `RelU`：`OU` 中在某个象限 `k ≥ k0, m ≥ m0` 上零化 `U` 的算子。

**主定理**：`RelU_eq`（`Rel(U) = {Q·L1 : Q ∈ O_U}`）与 `RelU_iff_mem_span`（在环 `O_U` 中，
`Rel(U)` 恰为 `L1` 生成的左理想 `Ideal.span {L1}`）。

**证明路线**（报告 T3.8 证明要点、`notes/c3b.md` §6）：
* 约化（`red_of_mem`）：用 `E⁻¹ = 1 − X − m·X³ − L1`，把 `O_U` 的任意元素写成
  「纯 `X` 位移算子 `Σ_a r_a(k,m)·X^a`」加上 `Q·L1`（`Q ∈ O_U`）。
* 命题 A（`pure_ann_zero`）：纯 `X` 位移算子若在象限上零化 `U`，则系数全为 0。固定 `m`，
  `S = Σ_a r_a(θ,m)(x^a G_m)` 是多项式（`θ = x·d/dx`）；乘以 `P_m^{D+1}` 后在 `P_m` 的根处
  取值（`col_key`），得到 `C(x) = Σ_a [k^D]r_a(k,m)·x^a` 在 `b_0, …, b_m` 各自的一个根处为 0。
  这 `m + 1` 个根两两不同，而 `deg C < A`，取 `m ≥ A` 得 `C = 0`（`col_zero`）。于是对每个
  `m ≥ max(m0, A)` 都有 `r_a(·, m) = 0`，所以 `r_a = 0`。所用的非零性：`P_m'` 在根处非零
  （各 `b_v` 的根互不相同且是单根），`W_m` 在根处非零（T1.3(2) 的 `isCoprime_W_P`）。
* 反方向：`O_U` 的元素只向下看有限步（`reach_of_mem`），而 `L1·U` 在 `k ≥ 3, m ≥ 1` 上为 0
  （引理 1，`L1_U`）。

`N` 的版本 `Rel(N) = O_N·L_N`（含饱和引理）在 `OreRelN.lean`；T3.8 的维数公式（`U`、`N` 两个版本）在 `OreDim.lean`。
-/

open Polynomial Finset

namespace A207123

/-! ### 作用空间、系数环与生成元 -/

/-- 作用空间：`ℕ × ℕ` 上的复数组 `f(k, m)`（负下标处的值约定为 0）。 -/
abbrev Arr := ℕ → ℕ → ℂ

/-- 系数环 `ℂ[k, m]`，写成 `ℂ[X][Y]`：内层变量是 `k`，外层变量是 `m`；`p` 在 `(k, m)` 处的值是
`p.evalEval k m`。 -/
abbrev Coef := Polynomial (Polynomial ℂ)

/-- 系数 `k`。 -/
noncomputable def cK : Coef := Polynomial.C Polynomial.X

/-- 系数 `m`。 -/
noncomputable def cM : Coef := Polynomial.X

/-- 辅助引理（T3.8）：`k` 在 `(x, y)` 处的值是 `x`。 -/
@[simp] theorem evalEval_cK (x y : ℂ) : cK.evalEval x y = x := by rw [cK, evalEval_C, eval_X]

/-- 辅助引理（T3.8）：`m` 在 `(x, y)` 处的值是 `y`。 -/
@[simp] theorem evalEval_cM (x y : ℂ) : cM.evalEval x y = y := by simp [cM]

/-- 乘法算子 `f ↦ p(k, m)·f`，作为环同态 `ℂ[k,m] → End(ℂ^{ℕ×ℕ})`。 -/
noncomputable def mulOp : Coef →+* Module.End ℂ Arr where
  toFun p :=
    { toFun := fun f k m => p.evalEval (k : ℂ) (m : ℂ) * f k m
      map_add' := fun f g => by funext k m; simp only [Pi.add_apply]; ring
      map_smul' := fun c f => by
        funext k m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by ext f k m; simp
  map_mul' p q := by ext f k m; simp [evalEval_mul]; ring
  map_zero' := by ext f k m; simp
  map_add' p q := by ext f k m; simp [evalEval_add]; ring

/-- 辅助引理（T3.8）：乘法算子的作用。 -/
theorem mulOp_apply (p : Coef) (f : Arr) (k m : ℕ) :
    mulOp p f k m = p.evalEval (k : ℂ) (m : ℂ) * f k m := rfl

/-- `X`：`(X f)(k, m) = f(k − 1, m)`（`k = 0` 时为 0）。 -/
noncomputable def opX : Module.End ℂ Arr where
  toFun f k m := if k = 0 then 0 else f (k - 1) m
  map_add' f g := by funext k m; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext k m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- 辅助引理（T3.8）：`X` 的作用。 -/
theorem opX_apply (f : Arr) (k m : ℕ) : opX f k m = if k = 0 then 0 else f (k - 1) m := rfl

/-- `E⁻¹`：`(E⁻¹ f)(k, m) = f(k, m − 1)`（`m = 0` 时为 0）。 -/
noncomputable def opEinv : Module.End ℂ Arr where
  toFun f k m := if m = 0 then 0 else f k (m - 1)
  map_add' f g := by funext k m; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext k m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- 辅助引理（T3.8）：`E⁻¹` 的作用。 -/
theorem opEinv_apply (f : Arr) (k m : ℕ) : opEinv f k m = if m = 0 then 0 else f k (m - 1) := rfl

/-- 辅助引理（T3.8）：`(X^a f)(k, m) = f(k − a, m)`（`a > k` 时为 0）。 -/
theorem opX_pow_apply (a : ℕ) (f : Arr) (k m : ℕ) :
    (opX ^ a) f k m = if a ≤ k then f (k - a) m else 0 := by
  induction a generalizing k with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, opX_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp only [hk.ne', ↓reduceIte, ih]
      by_cases h : a + 1 ≤ k
      · simp [h, show a ≤ k - 1 by omega, show k - 1 - a = k - (a + 1) by omega]
      · simp [h, show ¬ a ≤ k - 1 by omega]

/-- 辅助引理（T3.8）：`(E^{−b} f)(k, m) = f(k, m − b)`（`b > m` 时为 0）。 -/
theorem opEinv_pow_apply (b : ℕ) (f : Arr) (k m : ℕ) :
    (opEinv ^ b) f k m = if b ≤ m then f k (m - b) else 0 := by
  induction b generalizing m with
  | zero => simp
  | succ b ih =>
    rw [pow_succ', Module.End.mul_apply, opEinv_apply]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp only [hm.ne', ↓reduceIte, ih]
      by_cases h : b + 1 ≤ m
      · simp [h, show b ≤ m - 1 by omega, show m - 1 - b = m - (b + 1) by omega]
      · simp [h, show ¬ b ≤ m - 1 by omega]

/-- 辅助引理（T3.8）：常数 `c` 的乘法算子就是 `c` 在代数 `End(ℂ^{ℕ×ℕ})` 中的像。 -/
theorem mulOp_CC (c : ℂ) :
    mulOp (Polynomial.C (Polynomial.C c)) = algebraMap ℂ (Module.End ℂ Arr) c := by
  ext f k m
  simp [mulOp_apply, Module.algebraMap_end_apply]

/-! ### Ore 交换律 -/

/-- 系数的平移 `p(k, m) ↦ p(k − 1, m)`。 -/
noncomputable def shiftK (p : Coef) : Coef := p.map (Polynomial.compRingHom (Polynomial.X - 1))

/-- 系数的平移 `p(k, m) ↦ p(k, m − 1)`。 -/
noncomputable def shiftM (p : Coef) : Coef := p.comp (Polynomial.X - 1)

/-- 辅助引理（T3.8）：`shiftK` 的取值。 -/
theorem evalEval_shiftK (p : Coef) (x y : ℂ) :
    (shiftK p).evalEval x y = p.evalEval (x - 1) y := by
  induction p using Polynomial.induction_on with
  | C a => simp [shiftK, evalEval_C, eval_comp]
  | add p q hp hq => simp only [shiftK, Polynomial.map_add, evalEval_add] at hp hq ⊢; rw [hp, hq]
  | monomial n a _ => simp [shiftK, evalEval_mul, evalEval_pow, evalEval_C, eval_comp]

/-- 辅助引理（T3.8）：`shiftM` 的取值。 -/
theorem evalEval_shiftM (p : Coef) (x y : ℂ) :
    (shiftM p).evalEval x y = p.evalEval x (y - 1) := by
  show eval x (eval (C y) (p.comp (X - 1))) = eval x (eval (C (y - 1)) p)
  rw [eval_comp, eval_sub, eval_X, eval_one, C_sub, C_1]

/-- 辅助引理（T3.8）：`k` 方向的平移不改变系数 `m`。 -/
theorem shiftK_cM : shiftK cM = cM := by simp [shiftK, cM]

/-- 辅助引理（T3.8，Ore 交换律）：`X·p(k,m) = p(k−1,m)·X`。 -/
theorem opX_mul_mulOp (p : Coef) : opX * mulOp p = mulOp (shiftK p) * opX := by
  ext f k m
  simp only [Module.End.mul_apply, opX_apply, mulOp_apply, evalEval_shiftK]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp only [hk.ne', ↓reduceIte]
    rw [Nat.cast_pred hk]

/-- 辅助引理（T3.8，Ore 交换律）：`E⁻¹·p(k,m) = p(k,m−1)·E⁻¹`。 -/
theorem opEinv_mul_mulOp (p : Coef) : opEinv * mulOp p = mulOp (shiftM p) * opEinv := by
  ext f k m
  simp only [Module.End.mul_apply, opEinv_apply, mulOp_apply, evalEval_shiftM]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · simp only [hm.ne', ↓reduceIte]
    rw [Nat.cast_pred hm]

/-- 辅助引理（T3.8，Ore 交换律）：`X` 与 `E⁻¹` 可交换。 -/
theorem commute_opX_opEinv : Commute opX opEinv := by
  show opX * opEinv = opEinv * opX
  ext f k m
  simp only [Module.End.mul_apply, opX_apply, opEinv_apply]
  split_ifs <;> rfl

/-- 辅助引理（T3.8，Ore 交换律）：`X` 与乘以 `m` 可交换。 -/
theorem commute_opX_cM : Commute opX (mulOp cM) := by
  show opX * mulOp cM = mulOp cM * opX
  rw [opX_mul_mulOp, shiftK_cM]

/-! ### `O_U`、`L1`、`Rel(U)` -/

/-- `O_U = ℂ[k,m]⟨X, E⁻¹⟩`：`End_ℂ(ℂ^{ℕ×ℕ})` 中由乘法算子 `k`、`m` 与位移 `X`、`E⁻¹` 生成的
`ℂ`-子代数（报告 T3.8；与 Ore 代数的对应见文件头）。 -/
noncomputable def OU : Subalgebra ℂ (Module.End ℂ Arr) :=
  Algebra.adjoin ℂ {mulOp cK, mulOp cM, opX, opEinv}

/-- `L1 = 1 − E⁻¹ − X − m·X³`（报告 T3.8；`L1·U = 0` 即引理 1）。 -/
noncomputable def L1 : Module.End ℂ Arr := 1 - opEinv - opX - mulOp cM * opX ^ 3

/-- `U` 看成 `ℕ × ℕ` 上的复数组。 -/
noncomputable def Uarr : Arr := fun k m => (U k m : ℂ)

/-- `f` 在象限 `k ≥ k1, m ≥ m1` 上为 0。 -/
def VanishOn (f : Arr) (k1 m1 : ℕ) : Prop := ∀ k m, k1 ≤ k → m1 ≤ m → f k m = 0

/-- `Rel(U)`（报告 T3.8）：`O_U` 中在某个象限 `k ≥ k0, m ≥ m0` 上零化 `U` 的算子全体。 -/
def RelU : Set (Module.End ℂ Arr) :=
  {R | R ∈ OU ∧ ∃ k0 m0 : ℕ, VanishOn (R Uarr) k0 m0}

/-- 辅助引理（T3.8）：生成元 `k` 属于 `O_U`。 -/
theorem cK_mem : mulOp cK ∈ OU := Algebra.subset_adjoin (by simp)

/-- 辅助引理（T3.8）：生成元 `m` 属于 `O_U`。 -/
theorem cM_mem : mulOp cM ∈ OU := Algebra.subset_adjoin (by simp)

/-- 辅助引理（T3.8）：生成元 `X` 属于 `O_U`。 -/
theorem opX_mem : opX ∈ OU := Algebra.subset_adjoin (by simp)

/-- 辅助引理（T3.8）：生成元 `E⁻¹` 属于 `O_U`。 -/
theorem opEinv_mem : opEinv ∈ OU := Algebra.subset_adjoin (by simp)

/-- 辅助引理（T3.8）：任何多项式系数 `p(k, m)` 的乘法算子属于 `O_U`。 -/
theorem mulOp_mem_OU (p : Coef) : mulOp p ∈ OU := by
  have hC : ∀ a : ℂ[X], mulOp (Polynomial.C a) ∈ OU := by
    intro a
    induction a using Polynomial.induction_on with
    | C c => rw [mulOp_CC]; exact Subalgebra.algebraMap_mem _ c
    | add a b ha hb => rw [Polynomial.C_add, map_add]; exact add_mem ha hb
    | monomial n c _ =>
      rw [Polynomial.C_mul, map_mul, mulOp_CC, Polynomial.C_pow, map_pow]
      exact mul_mem (Subalgebra.algebraMap_mem _ c) (pow_mem cK_mem _)
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ => rw [map_mul, map_pow]; exact mul_mem (hC a) (pow_mem cM_mem _)

/-- 辅助引理（T3.8）：`L1 ∈ O_U`。 -/
theorem L1_mem : L1 ∈ OU :=
  sub_mem (sub_mem (sub_mem (one_mem _) opEinv_mem) opX_mem)
    (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem 3))

/-- 辅助引理（T3.8）：`E⁻¹ = 1 − X − m·X³ − L1`。 -/
theorem opEinv_eq : opEinv = 1 - opX - mulOp cM * opX ^ 3 - L1 := by
  unfold L1; abel

/-- 辅助引理（T3.8，引理 1）：`L1·U` 在象限 `k ≥ 3, m ≥ 1` 上为 0。 -/
theorem L1_U : VanishOn (L1 Uarr) 3 1 := by
  intro k m hk hm
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h := lemma1 k' m'
  simp only [L1, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, opX_pow_apply,
    opX_apply, opEinv_apply, mulOp_apply, evalEval_cM, Pi.sub_apply, Uarr]
  simp only [show k' + 3 ≠ 0 by omega, show m' + 1 ≠ 0 by omega, show 3 ≤ k' + 3 by omega,
    ↓reduceIte, show k' + 3 - 1 = k' + 2 by omega, show k' + 3 - 3 = k' by omega,
    show m' + 1 - 1 = m' by omega]
  rw [h]
  push_cast
  ring

/-! ### 反方向：`O_U·L1 ⊆ Rel(U)` -/

/-- `T` 只向下看有限步：存在 `A, B`，使 `f` 在象限 `(k1, m1)` 上为 0 时 `T f` 在象限
`(k1 + A, m1 + B)` 上为 0。 -/
def Reach (T : Module.End ℂ Arr) : Prop :=
  ∃ A B : ℕ, ∀ f k1 m1, VanishOn f k1 m1 → VanishOn (T f) (k1 + A) (m1 + B)

/-- 辅助引理（T3.8）：`O_U` 的元素都只向下看有限步。 -/
theorem reach_of_mem {T : Module.End ℂ Arr} (hT : T ∈ OU) : Reach T := by
  have hmul : ∀ p : Coef, Reach (mulOp p) := fun p =>
    ⟨0, 0, fun f k1 m1 hf k m hk hm => by
      rw [mulOp_apply, hf k m (by omega) (by omega), mul_zero]⟩
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hmul _
    · exact hmul _
    · refine ⟨1, 0, fun f k1 m1 hf k m hk hm => ?_⟩
      rw [opX_apply]
      split_ifs with h
      · rfl
      · exact hf _ _ (by omega) (by omega)
    · refine ⟨0, 1, fun f k1 m1 hf k m hk hm => ?_⟩
      rw [opEinv_apply]
      split_ifs with h
      · rfl
      · exact hf _ _ (by omega) (by omega)
  | algebraMap c =>
    refine ⟨0, 0, fun f k1 m1 hf k m hk hm => ?_⟩
    rw [Module.algebraMap_end_apply, Pi.smul_apply, Pi.smul_apply, hf k m (by omega) (by omega),
      smul_zero]
  | add x y _ _ hx hy =>
    obtain ⟨A, B, h⟩ := hx
    obtain ⟨A', B', h'⟩ := hy
    refine ⟨A + A', B + B', fun f k1 m1 hf k m hk hm => ?_⟩
    rw [LinearMap.add_apply, Pi.add_apply, Pi.add_apply, h f k1 m1 hf k m (by omega) (by omega),
      h' f k1 m1 hf k m (by omega) (by omega), add_zero]
  | mul x y _ _ hx hy =>
    obtain ⟨A, B, h⟩ := hx
    obtain ⟨A', B', h'⟩ := hy
    refine ⟨A' + A, B' + B, fun f k1 m1 hf k m hk hm => ?_⟩
    rw [Module.End.mul_apply]
    exact h _ _ _ (h' f k1 m1 hf) k m (by omega) (by omega)

/-! ### 约化：`O_U` 的元素 ≡ 纯 `X` 位移算子 (mod `O_U·L1`) -/

/-- 纯 `X` 位移算子 `Σ_a r_a(k, m)·X^a`（`r` 是有限支撑的系数族）。 -/
noncomputable def pureOp (r : ℕ →₀ Coef) : Module.End ℂ Arr := r.sum fun a p => mulOp p * opX ^ a

/-- 辅助引理（T3.8）：`pureOp 0 = 0`。 -/
theorem pureOp_zero : pureOp 0 = 0 := Finsupp.sum_zero_index

/-- 辅助引理（T3.8）：`pureOp` 可加。 -/
theorem pureOp_add (r s : ℕ →₀ Coef) : pureOp (r + s) = pureOp r + pureOp s :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])

/-- 辅助引理（T3.8）：`pureOp` 与减法交换。 -/
theorem pureOp_sub (r s : ℕ →₀ Coef) : pureOp (r - s) = pureOp r - pureOp s :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul])

/-- 辅助引理（T3.8）：单项的 `pureOp`。 -/
theorem pureOp_single (a : ℕ) (p : Coef) : pureOp (Finsupp.single a p) = mulOp p * opX ^ a :=
  Finsupp.sum_single_index (by simp)

/-- 辅助引理（T3.8）：纯 `X` 位移算子的作用。 -/
theorem pureOp_apply (r : ℕ →₀ Coef) (f : Arr) (k m : ℕ) :
    pureOp r f k m = ∑ a ∈ r.support,
      (r a).evalEval (k : ℂ) (m : ℂ) * (if a ≤ k then f (k - a) m else 0) := by
  simp only [pureOp, Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply,
    mulOp_apply, opX_pow_apply]

/-- `T ≡ 某个纯 X 位移算子 (mod O_U·L1)`。 -/
def Red (T : Module.End ℂ Arr) : Prop := ∃ r : ℕ →₀ Coef, ∃ Q ∈ OU, T = pureOp r + Q * L1

/-- 辅助引理（T3.8）：`Red 0`。 -/
theorem red_zero : Red 0 := ⟨0, 0, zero_mem _, by rw [pureOp_zero, zero_mul, add_zero]⟩

/-- 辅助引理（T3.8）：纯 `X` 位移算子满足 `Red`。 -/
theorem red_pure (r : ℕ →₀ Coef) : Red (pureOp r) := ⟨r, 0, zero_mem _, by rw [zero_mul, add_zero]⟩

/-- 辅助引理（T3.8）：`Red` 对加法封闭。 -/
theorem red_add {S T : Module.End ℂ Arr} (hS : Red S) (hT : Red T) : Red (S + T) := by
  obtain ⟨r, Q, hQ, rfl⟩ := hS
  obtain ⟨r', Q', hQ', rfl⟩ := hT
  exact ⟨r + r', Q + Q', add_mem hQ hQ', by rw [pureOp_add, add_mul]; abel⟩

/-- 辅助引理（T3.8）：`Red` 对加上 `O_U·L1` 的元素封闭。 -/
theorem red_add_mul {S Q' : Module.End ℂ Arr} (hS : Red S) (hQ' : Q' ∈ OU) : Red (S + Q' * L1) := by
  obtain ⟨r, Q, hQ, rfl⟩ := hS
  exact ⟨r, Q + Q', add_mem hQ hQ', by rw [add_mul]; abel⟩

/-- 辅助引理（T3.8）：`Red` 对减去 `O_U·L1` 的元素封闭。 -/
theorem red_sub_mul {S Q' : Module.End ℂ Arr} (hS : Red S) (hQ' : Q' ∈ OU) : Red (S - Q' * L1) := by
  obtain ⟨r, Q, hQ, rfl⟩ := hS
  exact ⟨r, Q - Q', sub_mem hQ hQ', by rw [sub_mul]; abel⟩

/-- 辅助引理（T3.8）：`Red 1`。 -/
theorem red_one : Red 1 := by
  have h := red_pure (Finsupp.single 0 1)
  rwa [pureOp_single, map_one, pow_zero, one_mul] at h

/-- 辅助引理（T3.8）：左乘乘法算子保持 `Red`。 -/
theorem red_mulOp {T : Module.End ℂ Arr} (q : Coef) (hT : Red T) : Red (mulOp q * T) := by
  obtain ⟨r, Q, hQ, rfl⟩ := hT
  rw [mul_add, ← mul_assoc]
  refine red_add_mul ?_ (mul_mem (mulOp_mem_OU q) hQ)
  induction r using Finsupp.induction_linear with
  | zero => rw [pureOp_zero, mul_zero]; exact red_zero
  | add r s hr hs => rw [pureOp_add, mul_add]; exact red_add hr hs
  | single a p =>
    have h := red_pure (Finsupp.single a (q * p))
    rwa [pureOp_single, map_mul, mul_assoc, ← pureOp_single] at h

/-- 辅助引理（T3.8）：左乘 `X` 保持 `Red`。 -/
theorem red_opX {T : Module.End ℂ Arr} (hT : Red T) : Red (opX * T) := by
  obtain ⟨r, Q, hQ, rfl⟩ := hT
  rw [mul_add, ← mul_assoc]
  refine red_add_mul ?_ (mul_mem opX_mem hQ)
  induction r using Finsupp.induction_linear with
  | zero => rw [pureOp_zero, mul_zero]; exact red_zero
  | add r s hr hs => rw [pureOp_add, mul_add]; exact red_add hr hs
  | single a p =>
    have h := red_pure (Finsupp.single (a + 1) (shiftK p))
    rwa [pureOp_single, pow_succ', ← mul_assoc, ← opX_mul_mulOp, mul_assoc, ← pureOp_single] at h

/-- 辅助引理（T3.8）：左乘 `E⁻¹` 保持 `Red`（用 `E⁻¹ = 1 − X − m·X³ − L1`）。 -/
theorem red_opEinv {T : Module.End ℂ Arr} (hT : Red T) : Red (opEinv * T) := by
  obtain ⟨r, Q, hQ, rfl⟩ := hT
  rw [mul_add, ← mul_assoc]
  refine red_add_mul ?_ (mul_mem opEinv_mem hQ)
  induction r using Finsupp.induction_linear with
  | zero => rw [pureOp_zero, mul_zero]; exact red_zero
  | add r s hr hs => rw [pureOp_add, mul_add]; exact red_add hr hs
  | single a p =>
    have hcomm : opX ^ a * mulOp cM = mulOp cM * opX ^ a := (commute_opX_cM.pow_left a).eq
    have hE : opEinv * opX ^ a = opX ^ a * opEinv := (commute_opX_opEinv.pow_left a).eq.symm
    have hL : opEinv * pureOp (Finsupp.single a p) = mulOp (shiftM p) * (opX ^ a * opEinv) := by
      rw [pureOp_single, ← mul_assoc, opEinv_mul_mulOp, mul_assoc, hE]
    have key : opEinv * pureOp (Finsupp.single a p)
        = pureOp (Finsupp.single a (shiftM p) - Finsupp.single (a + 1) (shiftM p)
            - Finsupp.single (a + 3) (shiftM p * cM))
          - (mulOp (shiftM p) * opX ^ a) * L1 := by
      rw [hL, opEinv_eq, pureOp_sub, pureOp_sub, pureOp_single, pureOp_single, pureOp_single,
        map_mul, pow_succ opX a, pow_add opX a 3]
      simp only [mul_sub, mul_one]
      rw [← mul_assoc (opX ^ a) (mulOp cM), hcomm]
      simp only [mul_assoc]
    rw [key]
    exact red_sub_mul (red_pure _) (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem a))

/-- 辅助引理（T3.8）：`T ∈ O_U` 时，左乘 `T` 保持 `Red`。 -/
theorem red_mul_of_mem {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∀ S, Red S → Red (T * S) := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    intro S hS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact red_mulOp _ hS
    · exact red_mulOp _ hS
    · exact red_opX hS
    · exact red_opEinv hS
  | algebraMap c =>
    intro S hS
    rw [← mulOp_CC]
    exact red_mulOp _ hS
  | add x y _ _ hx hy =>
    intro S hS
    rw [add_mul]
    exact red_add (hx S hS) (hy S hS)
  | mul x y _ _ hx hy =>
    intro S hS
    rw [mul_assoc]
    exact hx _ (hy S hS)

/-- 辅助引理（T3.8，约化）：`O_U` 的每个元素都可写成「纯 `X` 位移算子 + `Q·L1`」（`Q ∈ O_U`）。 -/
theorem red_of_mem {T : Module.End ℂ Arr} (hT : T ∈ OU) : Red T := by
  simpa using red_mul_of_mem hT 1 red_one

/-! ### 命题 A：纯 `X` 位移算子不能在象限上零化 `U` -/

/-- 辅助引理（T3.8，命题 A）：`P_m^{D+1}·θ^e(x^a G_m)`（`e ≤ D`）是多项式；在 `P_m` 的根 `z` 处，
`e < D` 时值为 0，`e = D` 时值为 `(−1)^D D!·(z P_m'(z))^D·z^a W_m(z)`。 -/
theorem col_term (m D e a : ℕ) (he : e ≤ D) (z : ℂ) (hz : (Ppoly ℂ m).eval z = 0) :
    HasPolyVal (((Ppoly ℂ m ^ (D + 1) : ℂ[X]) : PowerSeries ℂ)
      * theta^[e] (PowerSeries.X ^ a * Gc m)) z
      (if e = D then (-1) ^ D * (D.factorial : ℂ) * (z * (derivative (Ppoly ℂ m)).eval z) ^ D
        * (z ^ a * (Wpoly ℂ m).eval z) else 0) := by
  have hsplit : Ppoly ℂ m ^ (D + 1) = Ppoly ℂ m ^ (D - e) * Ppoly ℂ m ^ (e + 1) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨Ppoly ℂ m ^ (D - e) * Bseq (Ppoly ℂ m) (Polynomial.X ^ a * Wpoly ℂ m) e, ?_, ?_⟩
  · rw [hsplit, Polynomial.coe_mul, mul_assoc, Polynomial.coe_pow (φ := Ppoly ℂ m) (e + 1),
      pow_mul_theta_iter _ _ _ (P_mul_XG m a) e, ← Polynomial.coe_mul]
  · rw [eval_mul, eval_pow, hz, eval_Bseq_of_root _ _ _ hz]
    split_ifs with h
    · subst h
      simp only [Nat.sub_self, pow_zero, one_mul, eval_mul, eval_pow, eval_X]
    · rw [zero_pow (by omega), zero_mul]

/-- 辅助引理（T3.8，命题 A）：若 `S = Σ_{a<A} q_a(θ)(x^a G_m)` 是多项式（`deg q_a ≤ D`），则在
`P_m` 的根 `z` 处，`Σ_a [k^D]q_a·(−1)^D D!·(z P_m'(z))^D·z^a W_m(z) = 0`。 -/
theorem col_key (m A D : ℕ) (q : ℕ → ℂ[X]) (hdeg : ∀ a ∈ range A, (q a).natDegree ≤ D)
    (z : ℂ) (hz : (Ppoly ℂ m).eval z = 0) (T : ℂ[X])
    (hS : ∑ a ∈ range A, polyTheta (q a) (PowerSeries.X ^ a * Gc m) = (T : PowerSeries ℂ)) :
    ∑ a ∈ range A, (q a).coeff D * ((-1) ^ D * (D.factorial : ℂ)
      * (z * (derivative (Ppoly ℂ m)).eval z) ^ D * (z ^ a * (Wpoly ℂ m).eval z)) = 0 := by
  set L : ℂ[X] := Ppoly ℂ m ^ (D + 1) with hL
  have hLz : L.eval z = 0 := by rw [hL, eval_pow, hz, zero_pow (by omega)]
  have h1 : HasPolyVal ((L : PowerSeries ℂ)
      * ∑ a ∈ range A, polyTheta (q a) (PowerSeries.X ^ a * Gc m)) z 0 :=
    ⟨L * T, by rw [hS, ← Polynomial.coe_mul], by rw [eval_mul, hLz, zero_mul]⟩
  have h2 : HasPolyVal ((L : PowerSeries ℂ)
      * ∑ a ∈ range A, polyTheta (q a) (PowerSeries.X ^ a * Gc m)) z
      (∑ a ∈ range A, (q a).coeff D * ((-1) ^ D * (D.factorial : ℂ)
        * (z * (derivative (Ppoly ℂ m)).eval z) ^ D * (z ^ a * (Wpoly ℂ m).eval z))) := by
    rw [mul_sum]
    apply HasPolyVal.sum
    intro a ha
    rw [polyTheta_eq_sum _ _ D (hdeg a ha), mul_sum]
    apply HasPolyVal.congr_val (v := ∑ e ∈ range (D + 1), (q a).coeff e *
      (if e = D then (-1) ^ D * (D.factorial : ℂ) * (z * (derivative (Ppoly ℂ m)).eval z) ^ D
        * (z ^ a * (Wpoly ℂ m).eval z) else 0))
    · apply HasPolyVal.sum
      intro e he
      rw [mem_range] at he
      rw [mul_left_comm]
      apply HasPolyVal.const_mul
      exact col_term m D e a (by omega) z hz
    · simp only [mul_ite, mul_zero]
      rw [sum_ite_eq']
      simp
  exact h2.unique h1

/-- 辅助引理（T3.8，命题 A）：每个 `b_v` 都有一个非零复单根（`v = 0` 时取 `1`，`v ≥ 1` 时取
`(0,1)` 中的实根）。 -/
theorem exists_simple_root_b (v : ℕ) :
    ∃ z : ℂ, z ≠ 0 ∧ (bpoly ℂ v).eval z = 0 ∧ (derivative (bpoly ℂ v)).eval z ≠ 0 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · refine ⟨1, one_ne_zero, by simp [eval_bpoly], ?_⟩
    rw [eval_deriv_b]; norm_num
  · obtain ⟨x, hx, hr⟩ := exists_root_b v hv
    refine ⟨(x : ℂ), by exact_mod_cast hx.ne', by rw [eval_b_ofReal, hr]; simp, ?_⟩
    rw [eval_deriv_b]
    have hpos : (0 : ℝ) < 1 + 3 * (v : ℝ) * x ^ 2 := by positivity
    have hcast : (1 + 3 * (v : ℂ) * (x : ℂ) ^ 2) = ((1 + 3 * (v : ℝ) * x ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, neg_ne_zero]
    exact_mod_cast hpos.ne'

/-- 辅助引理（T3.8，命题 A 的单列情形）：固定 `m`。若 `q_a ∈ ℂ[k]`（`a < A`，`A ≤ m + 1`）使
`Σ_{a<A} q_a(k)·U_{k−a}(m) = 0` 对一切 `k ≥ k0`（且 `k ≥ A`）成立，则所有 `q_a = 0`。 -/
theorem col_zero (m A k0 : ℕ) (hA : A ≤ m + 1) (q : ℕ → ℂ[X])
    (hrel : ∀ k, k0 ≤ k → A ≤ k → ∑ a ∈ range A, (q a).eval (k : ℂ) * (U (k - a) m : ℂ) = 0) :
    ∀ a < A, q a = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨a0, ha0, hqa0⟩ := hne
  -- D：非零 `q_a` 的最高次数
  have hne' : ((range A).filter (fun a => q a ≠ 0)).Nonempty :=
    ⟨a0, mem_filter.mpr ⟨mem_range.mpr ha0, hqa0⟩⟩
  obtain ⟨a', ha', hmax⟩ := ((range A).filter (fun a => q a ≠ 0)).exists_max_image
    (fun a => (q a).natDegree) hne'
  rw [mem_filter] at ha'
  set D := (q a').natDegree with hD
  have hdeg : ∀ a ∈ range A, (q a).natDegree ≤ D := by
    intro a ha
    by_cases hqa : q a = 0
    · rw [hqa, natDegree_zero]; exact Nat.zero_le _
    · exact hmax a (mem_filter.mpr ⟨ha, hqa⟩)
  -- `C(x) = Σ_a [k^D]q_a·x^a`：非零，次数 `< m + 1`
  set Cp : ℂ[X] := ∑ a ∈ range A, Polynomial.C ((q a).coeff D) * Polynomial.X ^ a with hCp
  have hCp0 : Cp ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff a') h
    simp only [hCp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      coeff_zero, sum_ite_eq, ha'.1, ↓reduceIte] at hc
    exact (leadingCoeff_ne_zero.mpr ha'.2) hc
  have hCpeval : ∀ z : ℂ, Cp.eval z = ∑ a ∈ range A, (q a).coeff D * z ^ a := by
    intro z
    simp [hCp, eval_finsetSum]
  have hCpdeg : Cp.natDegree < m + 1 := by
    have : Cp.natDegree ≤ m := by
      rw [hCp]
      apply natDegree_sum_le_of_forall_le
      intro a ha
      rw [mem_range] at ha
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    omega
  -- `S = Σ_a q_a(θ)(x^a G_m)` 是多项式
  set N := max k0 A with hN
  set S := ∑ a ∈ range A, polyTheta (q a) (PowerSeries.X ^ a * Gc m) with hSdef
  have hS : S = ((PowerSeries.trunc N S : ℂ[X]) : PowerSeries ℂ) := by
    ext k
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hk
    · rfl
    · rw [hSdef, ← hrel k (by omega) (by omega)]
      simp only [map_sum, polyTheta, PowerSeries.coeff_mk]
      apply sum_congr rfl
      intro a ha
      rw [mem_range] at ha
      rw [PowerSeries.coeff_X_pow_mul']
      simp only [show a ≤ k by omega, ↓reduceIte, Gc, PowerSeries.coeff_mk]
  -- 对每个 `v ≤ m`，`b_v` 的单根 `z_v` 是 `C` 的根
  have hroot : ∀ v ∈ range (m + 1),
      ∃ z : ℂ, z ≠ 0 ∧ (bpoly ℂ v).eval z = 0 ∧ Cp.eval z = 0 := by
    intro v hv
    obtain ⟨z, hz0, hzb, hzd⟩ := exists_simple_root_b v
    have hPz : (Ppoly ℂ m).eval z = 0 := by
      rw [Ppoly, eval_prod]
      exact prod_eq_zero hv hzb
    have hsplitP : Ppoly ℂ m = bpoly ℂ v * ∏ i ∈ (range (m + 1)).erase v, bpoly ℂ i := by
      rw [Ppoly, Finset.mul_prod_erase _ _ hv]
    have hR : (∏ i ∈ (range (m + 1)).erase v, bpoly ℂ i).eval z ≠ 0 := by
      rw [eval_prod, prod_ne_zero_iff]
      intro i hi
      rw [eval_b_sub_of_root hzb i]
      refine mul_ne_zero ?_ (pow_ne_zero 3 hz0)
      rw [sub_ne_zero]
      exact_mod_cast (Finset.ne_of_mem_erase hi).symm
    have hPd : (derivative (Ppoly ℂ m)).eval z ≠ 0 := by
      rw [hsplitP, derivative_mul, eval_add, eval_mul, eval_mul, hzb, zero_mul, add_zero]
      exact mul_ne_zero hzd hR
    have hW : (Wpoly ℂ m).eval z ≠ 0 := by
      have hc := (isCoprime_W_P m).map (Polynomial.mapRingHom (algebraMap ℚ ℂ))
      rw [Polynomial.coe_mapRingHom, Wpoly_map, Ppoly_map] at hc
      obtain ⟨u, w, huw⟩ := hc
      intro h0
      have h1 := congrArg (eval z) huw
      rw [eval_add, eval_mul, eval_mul, h0, hPz, mul_zero, mul_zero, add_zero, eval_one] at h1
      exact zero_ne_one h1
    have hkey := col_key m A D q hdeg z hPz _ hS
    refine ⟨z, hz0, hzb, ?_⟩
    have hfac : (-1) ^ D * (D.factorial : ℂ) * (z * (derivative (Ppoly ℂ m)).eval z) ^ D
        * (Wpoly ℂ m).eval z ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_)
        (pow_ne_zero _ (mul_ne_zero hz0 hPd))) hW
      exact_mod_cast D.factorial_ne_zero
    rw [hCpeval]
    have hsum : ∑ a ∈ range A, (q a).coeff D * ((-1) ^ D * (D.factorial : ℂ)
        * (z * (derivative (Ppoly ℂ m)).eval z) ^ D * (z ^ a * (Wpoly ℂ m).eval z))
        = ((-1) ^ D * (D.factorial : ℂ) * (z * (derivative (Ppoly ℂ m)).eval z) ^ D
          * (Wpoly ℂ m).eval z) * ∑ a ∈ range A, (q a).coeff D * z ^ a := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum] at hkey
    exact (mul_eq_zero.mp hkey).resolve_left hfac
  -- `m + 1` 个两两不同的根，而 `deg C < m + 1`，所以 `C = 0`，矛盾
  choose! zf hzf using hroot
  apply hCp0
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Cp ((range (m + 1)).image zf)
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    exact (hzf v hv).2.2
  · rw [card_image_of_injOn, card_range]
    · exact hCpdeg
    · intro v hv w hw hvw
      obtain ⟨hz0, hb, -⟩ := hzf v (Finset.mem_coe.mp hv)
      obtain ⟨-, hb2, -⟩ := hzf w (Finset.mem_coe.mp hw)
      rw [← hvw] at hb2
      have h := eval_b_sub_of_root hb w
      rw [hb2] at h
      have h4 : ((v : ℂ) - (w : ℂ)) = 0 := by
        rcases mul_eq_zero.mp h.symm with h5 | h5
        · exact h5
        · exact absurd h5 (pow_ne_zero 3 hz0)
      exact_mod_cast sub_eq_zero.mp h4

/-- 辅助引理（T3.8）：两元多项式 `p(k, m)` 若对每个整数 `m ≥ M`，`p(·, m)` 作为 `k` 的多项式为 0，
则 `p = 0`。 -/
theorem coef_eq_zero_of_eval (p : Coef) (M : ℕ)
    (h : ∀ m : ℕ, M ≤ m → p.eval (Polynomial.C (m : ℂ)) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => Polynomial.C ((j + M : ℕ) : ℂ))
  · intro i j hij
    have h1 : ((i + M : ℕ) : ℂ) = ((j + M : ℕ) : ℂ) := Polynomial.C_injective hij
    have h2 := Nat.cast_injective h1
    omega
  · intro j
    exact h (j + M) (by omega)

/-- 辅助引理（T3.8）：两元多项式 `p(k, m)` 若在 `{(k, m) ∈ ℕ² : k ≥ a0, m ≥ b0}` 上为 0，则 `p = 0`。 -/
theorem coef_eq_zero_of_vanish (p : Coef) (a0 b0 : ℕ)
    (h : ∀ k m : ℕ, a0 ≤ k → b0 ≤ m → p.evalEval (k : ℂ) (m : ℂ) = 0) : p = 0 := by
  apply coef_eq_zero_of_eval p b0
  intro m hm
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => ((j + a0 : ℕ) : ℂ))
  · intro i j hij
    have h2 := Nat.cast_injective (R := ℂ) hij
    omega
  · intro j
    exact h (j + a0) m (by omega) hm

/-- **命题 A**（T3.8）：纯 `X` 位移算子 `Σ_a r_a(k, m)·X^a`（`r_a ∈ ℂ[k,m]`）若在某个象限
`k ≥ k0, m ≥ m0` 上零化 `U`，则所有系数 `r_a = 0`。 -/
theorem pure_ann_zero (r : ℕ →₀ Coef) (k0 m0 : ℕ) (h : VanishOn (pureOp r Uarr) k0 m0) :
    r = 0 := by
  classical
  set A := r.support.sup (· + 1) with hA
  have hsupp : ∀ a ∈ r.support, a < A := fun a ha =>
    Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Finset.le_sup (f := (· + 1)) ha)
  have hcol : ∀ m, max m0 A ≤ m → ∀ a < A, (r a).eval (Polynomial.C (m : ℂ)) = 0 := by
    intro m hm
    apply col_zero m A (max k0 A) (by omega) (fun a => (r a).eval (Polynomial.C (m : ℂ)))
    intro k hk hAk
    have h0 := h k m (by omega) (by omega)
    rw [pureOp_apply] at h0
    rw [← h0]
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro a ha
      exact mem_range.mpr (hsupp a ha)
    · intro a ha
      rw [mem_sdiff, Finsupp.mem_support_iff, not_not] at ha
      rw [ha.2]
      simp
    · intro a ha
      have hak : a ≤ k := by have := hsupp a ha; omega
      simp only [hak, ↓reduceIte, Uarr]
  refine Finsupp.ext fun a => ?_
  show r a = 0
  by_cases ha : a ∈ r.support
  · exact coef_eq_zero_of_eval (r a) (max m0 A) (fun m hm => hcol m hm a (hsupp a ha))
  · exact Finsupp.notMem_support_iff.mp ha

/-! ### 主定理 -/

/-- **T3.8（`U` 的部分）**：`Rel(U) = O_U·L1`，即 `O_U = ℂ[k,m]⟨X, E⁻¹⟩` 中在某个象限上零化 `U`
的算子，恰好是 `Q·L1`（`Q ∈ O_U`，`L1 = 1 − E⁻¹ − X − m·X³`）。 -/
theorem RelU_eq : RelU = {R | ∃ Q ∈ OU, R = Q * L1} := by
  ext R
  constructor
  · rintro ⟨hR, k0, m0, hvan⟩
    obtain ⟨r, Q, hQ, rfl⟩ := red_of_mem hR
    obtain ⟨A, B, hreach⟩ := reach_of_mem hQ
    have hQU : VanishOn (Q (L1 Uarr)) (3 + A) (1 + B) := hreach _ 3 1 L1_U
    have hpure : VanishOn (pureOp r Uarr) (max k0 (3 + A)) (max m0 (1 + B)) := by
      intro k m hk hm
      have h1 := hvan k m (by omega) (by omega)
      have h2 := hQU k m (by omega) (by omega)
      rw [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, Pi.add_apply, h2,
        add_zero] at h1
      exact h1
    have hr := pure_ann_zero r _ _ hpure
    exact ⟨Q, hQ, by rw [hr, pureOp_zero, zero_add]⟩
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨mul_mem hQ L1_mem, ?_⟩
    obtain ⟨A, B, hreach⟩ := reach_of_mem hQ
    exact ⟨3 + A, 1 + B, hreach _ 3 1 L1_U⟩

/-- **T3.8（`U` 的部分，左理想形式）**：在环 `O_U` 中，`R` 在某个象限上零化 `U` 当且仅当 `R`
属于 `L1` 生成的左理想 `O_U·L1`（`Ideal.span {L1}`；非交换环中 `Ideal` 指左理想）。 -/
theorem RelU_iff_mem_span (R : OU) :
    (∃ k0 m0 : ℕ, VanishOn ((R : Module.End ℂ Arr) Uarr) k0 m0) ↔
      R ∈ Ideal.span {(⟨L1, L1_mem⟩ : OU)} := by
  rw [Ideal.mem_span_singleton']
  constructor
  · intro h
    have hR : (R : Module.End ℂ Arr) ∈ RelU := ⟨R.2, h⟩
    rw [RelU_eq] at hR
    obtain ⟨Q, hQ, hRQ⟩ := hR
    exact ⟨⟨Q, hQ⟩, Subtype.ext hRQ.symm⟩
  · rintro ⟨Q, rfl⟩
    have hR : ((Q * ⟨L1, L1_mem⟩ : OU) : Module.End ℂ Arr) ∈ RelU := by
      rw [RelU_eq]
      exact ⟨Q, Q.2, rfl⟩
    exact hR.2

/-! ### `O_U` 就是 Ore 代数 `ℂ[k,m]⟨X, E⁻¹⟩`：正规形存在且唯一 -/

/-- 正规形 `Σ_{(a,b)} r_{ab}(k, m)·X^a·E^{−b}`。 -/
noncomputable def normOp (r : ℕ × ℕ →₀ Coef) : Module.End ℂ Arr :=
  r.sum fun ab p => mulOp p * opX ^ ab.1 * opEinv ^ ab.2

/-- 辅助引理（T3.8）：`normOp` 可加。 -/
theorem normOp_add (r s : ℕ × ℕ →₀ Coef) : normOp (r + s) = normOp r + normOp s :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul, add_mul])

/-- 辅助引理（T3.8）：单项的 `normOp`。 -/
theorem normOp_single (ab : ℕ × ℕ) (p : Coef) :
    normOp (Finsupp.single ab p) = mulOp p * opX ^ ab.1 * opEinv ^ ab.2 :=
  Finsupp.sum_single_index (by simp)

/-- 辅助引理（T3.8）：正规形的作用。 -/
theorem normOp_apply (r : ℕ × ℕ →₀ Coef) (f : Arr) (k m : ℕ) :
    normOp r f k m = ∑ ab ∈ r.support, (r ab).evalEval (k : ℂ) (m : ℂ)
      * (if ab.1 ≤ k then (if ab.2 ≤ m then f (k - ab.1) (m - ab.2) else 0) else 0) := by
  simp only [normOp, Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply,
    mulOp_apply, opX_pow_apply, opEinv_pow_apply]

/-- 辅助引理（T3.8）：每个正规形都属于 `O_U`。 -/
theorem normOp_mem (r : ℕ × ℕ →₀ Coef) : normOp r ∈ OU := by
  induction r using Finsupp.induction_linear with
  | zero => rw [show normOp 0 = 0 from Finsupp.sum_zero_index]; exact zero_mem _
  | add r s hr hs => rw [normOp_add]; exact add_mem hr hs
  | single ab p =>
    rw [normOp_single]
    exact mul_mem (mul_mem (mulOp_mem_OU p) (pow_mem opX_mem _)) (pow_mem opEinv_mem _)

/-- 辅助引理（T3.8）：`T ∈ O_U` 时，左乘 `T` 把正规形变成正规形。 -/
theorem normal_mul_of_mem {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∀ S, (∃ r, S = normOp r) → ∃ r, T * S = normOp r := by
  -- 左乘一个生成元
  have gen : ∀ g : Module.End ℂ Arr,
      (∀ ab : ℕ × ℕ, ∀ p : Coef, ∃ r, g * normOp (Finsupp.single ab p) = normOp r) →
      ∀ S, (∃ r, S = normOp r) → ∃ r, g * S = normOp r := by
    intro g hg S hS
    obtain ⟨r, rfl⟩ := hS
    induction r using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [show normOp 0 = 0 from Finsupp.sum_zero_index, mul_zero]⟩
    | add r s hr hs =>
      obtain ⟨r1, h1⟩ := hr
      obtain ⟨s1, h2⟩ := hs
      exact ⟨r1 + s1, by rw [normOp_add, mul_add, h1, h2, normOp_add]⟩
    | single ab p => exact hg ab p
  have hmul : ∀ q : Coef, ∀ S, (∃ r, S = normOp r) → ∃ r, mulOp q * S = normOp r :=
    fun q => gen _ fun ab p => ⟨Finsupp.single ab (q * p), by
      rw [normOp_single, normOp_single, map_mul]; simp only [mul_assoc]⟩
  have hX : ∀ S, (∃ r, S = normOp r) → ∃ r, opX * S = normOp r :=
    gen _ fun ab p => ⟨Finsupp.single (ab.1 + 1, ab.2) (shiftK p), by
      rw [normOp_single, normOp_single, pow_succ', ← mul_assoc, ← mul_assoc, ← mul_assoc,
        opX_mul_mulOp]⟩
  have hE : ∀ S, (∃ r, S = normOp r) → ∃ r, opEinv * S = normOp r :=
    gen _ fun ab p => ⟨Finsupp.single (ab.1, ab.2 + 1) (shiftM p), by
      rw [normOp_single, normOp_single, pow_succ', ← mul_assoc, ← mul_assoc, ← mul_assoc,
        opEinv_mul_mulOp, mul_assoc _ opEinv, (commute_opX_opEinv.pow_left ab.1).eq.symm,
        ← mul_assoc]⟩
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hmul _
    · exact hmul _
    · exact hX
    · exact hE
  | algebraMap c =>
    intro S hS
    rw [← mulOp_CC]
    exact hmul _ S hS
  | add x y _ _ hx hy =>
    intro S hS
    obtain ⟨r1, h1⟩ := hx S hS
    obtain ⟨r2, h2⟩ := hy S hS
    exact ⟨r1 + r2, by rw [add_mul, h1, h2, normOp_add]⟩
  | mul x y _ _ hx hy =>
    intro S hS
    rw [mul_assoc]
    exact hx _ (hy S hS)

/-- 辅助定理（T3.8，`O_U` 的结构）：`O_U` 的每个元素都能写成正规形
`Σ_{(a,b)} r_{ab}(k, m)·X^a·E^{−b}`。 -/
theorem exists_normal_form {T : Module.End ℂ Arr} (hT : T ∈ OU) : ∃ r, T = normOp r := by
  obtain ⟨r, hr⟩ := normal_mul_of_mem hT 1 ⟨Finsupp.single (0, 0) 1, by
    rw [normOp_single, map_one, pow_zero, pow_zero, one_mul, one_mul]⟩
  exact ⟨r, by rw [← hr, mul_one]⟩

/-- 辅助定理（T3.8，`O_U` 的结构）：正规形的写法唯一，即 `X^a·E^{−b}` 在 `ℂ[k,m]` 上左线性无关
（`O_U` 在 `ℂ^{ℕ×ℕ}` 上的作用是忠实的）。 -/
theorem normal_form_unique (r : ℕ × ℕ →₀ Coef) (h : normOp r = 0) : r = 0 := by
  classical
  refine Finsupp.ext fun ab => ?_
  obtain ⟨a0, b0⟩ := ab
  show r (a0, b0) = 0
  apply coef_eq_zero_of_vanish (r (a0, b0)) a0 b0
  intro k m hk hm
  -- 作用在 `(k − a0, m − b0)` 处的点函数上，在 `(k, m)` 处取值
  set δ : Arr := fun i j => if i = k - a0 ∧ j = m - b0 then 1 else 0 with hδ
  have h0 : normOp r δ k m = 0 := by rw [h]; rfl
  rw [normOp_apply, Finset.sum_eq_single (a0, b0)] at h0
  · simpa [hk, hm, hδ] using h0
  · intro ab _ hab
    by_cases h1 : ab.1 ≤ k
    · by_cases h2 : ab.2 ≤ m
      · have : ¬ (k - ab.1 = k - a0 ∧ m - ab.2 = m - b0) := by
          rintro ⟨e1, e2⟩
          exact hab (Prod.ext (by omega) (by omega))
        simp [h1, h2, hδ, this]
      · simp [h1, h2]
    · simp [h1]
  · intro hn
    rw [Finsupp.notMem_support_iff.mp hn]
    simp

end A207123
