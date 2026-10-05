import A207123.OreRel
import A207123.Binomial

/-!
# 报告 T3.8 的 `N` 部分：`Rel(N) = O_N·L_N`

**报告的设定**（T3.8）：`O_N = ℂ[k,q]⟨X, Y⟩`（`X : k ↦ k − 1`，`Y : q ↦ q − 1`），`Rel(N)` 是在某个
象限上零化 `N` 的算子全体，`L_N = 1 − X − XY − (q−1)X³(1+Y)²`。结论 `Rel(N) = O_N·L_N`。

**Lean 中的实现**：`O_N` 与 `O_U` 是同一个 Ore 代数（把第二个变量 `m` 改名为 `q`、`E⁻¹` 改名为 `Y`），
所以这里直接用 `OreRel.lean` 的 `OU`（作用在 `ℕ × ℕ` 上的复数组上，第二个下标此时是 `q`，
`Y = opEinv`，`q = mulOp cM`）。

**主定理**：`RelN_eq`（`Rel(N) = {Q·L_N : Q ∈ O_N}`）与 `RelN_iff_mem_span`（左理想形式）。
另外形式化了报告的**饱和引理**（`notes/c3b.md` §7.2）：`saturation_Y`（`Y·L ∈ O_N L_N ⇒ L ∈ O_N L_N`）
与 `saturation_one_add_Y`（`(1+Y)·L ∈ O_N L_N ⇒ L ∈ O_N L_N`）。

**证明路线**（与报告的「代换 `t = y/(1+y)` 搬回 `U` + 饱和引理」是同一个想法，但全程在数组上、
只用多项式系数的算子表述，不用微分算子环）：
* 二项式变换 `P`：`(P f)(k, m) = Σ_{q ≤ m} C(m, q)·f(k, q)`，`V := P·N`，于是
  `V(k, m+1) = U(k, m)`、`V(k, 0) = N(k, 0)`（`Binomial.lean` 的 `U_eq_Vn`）。记 `Δ = 1 − Y`。
* `P` 与生成元的交换关系（`opD_P_Y`、`P_mul_cM`、`opD_P_one_add`）：
  `Δ·P·Y = Y·P`，`P·q = m·Δ·P`，`Δ·P·(1+Y) = P`。由此得到搬运恒等式（`L1V_P`）
  `L1V·P = Δ·P·L_N`，其中 `L1V = 1 − Y − X − (m−1)X³` 是 `V` 的引理 1 算子（`Y·L1 = L1V·Y`）。
* `Rel(V) = O·L1V`（`relV`）：由 `Rel(U) = O_U·L1`（`RelU_eq`）与 `Y·L1 = L1V·Y` 推出。
* 设 `𝓛 ∈ O_N` 在象限上零化 `N`。存在 `j` 与 `𝓜 ∈ O` 使 `Δ^j·P·𝓛 = 𝓜·P`（`exists_N_to_V`）；
  `Δ^e` 消去「`q < q0` 的边界部分」（`opD_pow_P_vanish`），于是 `Δ^e 𝓜 ∈ Rel(V)`，
  `Δ^e 𝓜 = 𝒬·L1V`；用搬运恒等式与反方向的交换关系（`exists_V_to_N`）回到 `N` 一侧，
  得到 `(1+Y)^d·𝓛 = Z·L_N`（`Z ∈ O_N`）；最后用饱和引理 (ii) 剥掉 `(1+Y)^d`。
* 反方向：`L_N` 在 `k ≥ 3, q ≥ 1` 上零化 `N`（`LN_N`，即 T1.4(2) 的三角递推 `N_tri`）。

T3.8 中 `N` 的维数公式在 `OreDim.lean`（`finrank_relN_tot`、`finrank_relN_gr`）。
-/

open Polynomial Finset

namespace A207123

/-! ### 设定 -/

/-- `N(k, q)` 看成 `ℕ × ℕ` 上的复数组（第二个下标是 `q`）。 -/
noncomputable def Narr : Arr := fun k q => (N k q : ℂ)

/-- `L_N = 1 − X − X·Y − (q − 1)·X³·(1 + Y)²`（报告 T3.8；`Y = opEinv` 是 `q ↦ q − 1`）。 -/
noncomputable def LN : Module.End ℂ Arr :=
  1 - opX - opX * opEinv - mulOp (cM - 1) * opX ^ 3 * (1 + opEinv) ^ 2

/-- `Rel(N)`（报告 T3.8）：`O_N` 中在某个象限 `k ≥ k0, q ≥ q0` 上零化 `N` 的算子全体。 -/
def RelN : Set (Module.End ℂ Arr) :=
  {R | R ∈ OU ∧ ∃ k0 q0 : ℕ, VanishOn (R Narr) k0 q0}

/-- 辅助引理（T3.8）：`L_N ∈ O_N`。 -/
theorem LN_mem : LN ∈ OU :=
  sub_mem (sub_mem (sub_mem (one_mem _) opX_mem) (mul_mem opX_mem opEinv_mem))
    (mul_mem (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem 3))
      (pow_mem (add_mem (one_mem _) opEinv_mem) 2))

/-- 辅助引理（T3.8，T1.4(2)）：`L_N·N` 在象限 `k ≥ 3, q ≥ 1` 上为 0（三角递推 `N_tri`）。 -/
theorem LN_N : VanishOn (LN Narr) 3 1 := by
  intro k q hk hq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h := N_tri k' r
  simp only [LN, sq, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
    Module.End.mul_apply, opX_pow_apply, opX_apply, opEinv_apply, mulOp_apply, Pi.sub_apply,
    Pi.add_apply, evalEval_sub, evalEval_cM, evalEval_one, Narr]
  simp only [show k' + 3 ≠ 0 by omega, show r + 1 ≠ 0 by omega, show 3 ≤ k' + 3 by omega,
    ↓reduceIte, show k' + 3 - 1 = k' + 2 by omega, show k' + 3 - 3 = k' by omega,
    show r + 1 - 1 = r by omega]
  rcases r with _ | r
  · simp only [↓reduceIte, zero_mul, Nat.zero_add] at h ⊢
    rw [h]
    push_cast
    ring
  · simp only [show r + 1 ≠ 0 by omega, ↓reduceIte, show r + 1 - 1 = r by omega,
      show r + 1 + 1 = r + 2 by omega] at h ⊢
    rw [h]
    push_cast
    ring

/-! ### 二项式变换 `P` 与 `Δ = 1 − Y` -/

/-- 第二个下标方向的二项式变换：`(P f)(k, m) = Σ_{q ≤ m} C(m, q)·f(k, q)`。 -/
noncomputable def opP : Module.End ℂ Arr where
  toFun f k m := ∑ q ∈ range (m + 1), (m.choose q : ℂ) * f k q
  map_add' f g := by
    funext k m; simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c f := by
    funext k m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun _ _ => by ring

/-- 辅助引理（T3.8）：`P` 的作用。 -/
theorem opP_apply (f : Arr) (k m : ℕ) :
    opP f k m = ∑ q ∈ range (m + 1), (m.choose q : ℂ) * f k q := rfl

/-- `Δ = 1 − Y`（`m` 或 `q` 方向的后向差分）。 -/
noncomputable def opD : Module.End ℂ Arr := 1 - opEinv

/-- 辅助引理（T3.8）：`Δ ∈ O`。 -/
theorem opD_mem : opD ∈ OU := sub_mem (one_mem _) opEinv_mem

/-- 辅助引理（T3.8）：`(Δ f)(k, m) = f(k, m) − f(k, m − 1)`（`m = 0` 时为 `f(k, 0)`）。 -/
theorem opD_apply (f : Arr) (k m : ℕ) :
    opD f k m = f k m - (if m = 0 then 0 else f k (m - 1)) := rfl

/-- 辅助引理（T3.8）：Pascal 公式的数组形式 `(P f)(k, m+1) = (P f)(k, m) + (P f')(k, m)`，
`f'(k, q) = f(k, q + 1)`。 -/
theorem opP_succ (f : Arr) (k m : ℕ) :
    opP f k (m + 1) = opP f k m + opP (fun k q => f k (q + 1)) k m := by
  simp only [opP_apply]
  rw [sum_range_succ' _ (m + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
    Nat.choose_zero_right]
  rw [sum_range_succ' (fun q => (m.choose q : ℂ) * f k q),
    sum_range_succ (fun q => (m.choose (q + 1) : ℂ) * f k (q + 1))]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  ring

/-- 辅助引理（T3.8）：`Δ·P·Y = Y·P`。 -/
theorem opD_P_Y : opD * opP * opEinv = opEinv * opP := by
  ext f k m
  simp only [Module.End.mul_apply, opD_apply]
  rcases m with _ | m
  · simp [opP_apply, opEinv_apply]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, opEinv_apply (opP f)]
    rw [opP_succ]
    have : (fun k q => opEinv f k (q + 1)) = f := by
      funext k q; simp [opEinv_apply]
    rw [this]
    ring

/-- 辅助引理（T3.8）：`Δ·P·(1 + Y) = P`。 -/
theorem opD_P_one_add : opD * opP * (1 + opEinv) = opP := by
  rw [mul_add, mul_one, opD_P_Y, opD, sub_mul, one_mul, sub_add_cancel]

/-- 辅助引理（T3.8）：`Δ^n·P·(1 + Y)^n = P`。 -/
theorem opD_pow_P_one_add_pow (n : ℕ) : opD ^ n * opP * (1 + opEinv) ^ n = opP := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc opD ^ (n + 1) * opP * (1 + opEinv) ^ (n + 1)
        = opD ^ n * (opD * opP * (1 + opEinv)) * (1 + opEinv) ^ n := by
          rw [pow_succ opD n, pow_succ' (1 + opEinv) n]; simp only [mul_assoc]
      _ = opP := by rw [opD_P_one_add, ih]

/-- 辅助引理（T3.8）：`P·q = m·Δ·P`（`(P(q f))(k, m) = m·((P f)(k, m) − (P f)(k, m − 1))`）。 -/
theorem P_mul_cM : opP * mulOp cM = mulOp cM * opD * opP := by
  ext f k m
  simp only [Module.End.mul_apply, mulOp_apply, evalEval_cM, opD_apply]
  rcases m with _ | m
  · simp [opP_apply, mulOp_apply]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [opP_succ f, add_sub_cancel_left]
    simp only [opP_apply, mulOp_apply, evalEval_cM]
    rw [sum_range_succ' _ (m + 1), mul_sum]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    apply sum_congr rfl
    intro q _
    have h := Nat.add_one_mul_choose_eq m q
    have h' : ((m + 1 : ℕ) : ℂ) * (m.choose q : ℂ) = ((m + 1).choose (q + 1) : ℂ) * ((q + 1 : ℕ) : ℂ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linear_combination (f k (q + 1)) * h'.symm

/-- 辅助引理（T3.8）：`P` 与 `X` 可交换。 -/
theorem P_mul_opX : opP * opX = opX * opP := by
  ext f k m
  simp only [Module.End.mul_apply, opP_apply, opX_apply]
  split_ifs <;> simp

/-- 辅助引理（T3.8）：`P` 与乘以 `k` 可交换。 -/
theorem P_mul_cK : opP * mulOp cK = mulOp cK * opP := by
  ext f k m
  simp only [Module.End.mul_apply, opP_apply, mulOp_apply, evalEval_cK, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- 辅助引理（T3.8）：`shiftM m = m − 1`。 -/
theorem shiftM_cM : shiftM cM = cM - 1 := by simp [shiftM, cM]

/-- 辅助引理（T3.8）：`shiftM k = k`。 -/
theorem shiftM_cK : shiftM cK = cK := by simp [shiftM, cK]

/-- 辅助引理（T3.8）：`Y` 与乘以 `k` 可交换。 -/
theorem commute_opEinv_cK : Commute opEinv (mulOp cK) := by
  show opEinv * mulOp cK = mulOp cK * opEinv
  rw [opEinv_mul_mulOp, shiftM_cK]

/-- 辅助引理（T3.8）：`Δ` 与 `Y` 可交换。 -/
theorem commute_opD_opEinv : Commute opD opEinv := by
  show opD * opEinv = opEinv * opD
  simp only [opD, sub_mul, mul_sub, one_mul, mul_one]

/-- 辅助引理（T3.8）：`Δ` 与 `X` 可交换。 -/
theorem commute_opD_opX : Commute opD opX := by
  show opD * opX = opX * opD
  simp only [opD, sub_mul, mul_sub, one_mul, mul_one, commute_opX_opEinv.eq]

/-- 辅助引理（T3.8）：`Δ` 与乘以 `k` 可交换。 -/
theorem commute_opD_cK : Commute opD (mulOp cK) := by
  show opD * mulOp cK = mulOp cK * opD
  simp only [opD, sub_mul, mul_sub, one_mul, mul_one, commute_opEinv_cK.eq]

/-! ### 单射性 -/

/-- 辅助引理（T3.8）：`P` 单射（下三角、对角线为 1）。 -/
theorem opP_injective : Function.Injective opP := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  funext k m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h := congrFun (congrFun hf k) m
    rw [opP_apply, sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul,
      sum_eq_zero (fun q hq => by rw [ih q (mem_range.mp hq)]; simp), zero_add] at h
    exact h

/-- 辅助引理（T3.8）：`Y` 单射。 -/
theorem opEinv_injective : Function.Injective opEinv := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  funext k m
  have h := congrFun (congrFun hf k) (m + 1)
  simpa [opEinv_apply] using h

/-- 辅助引理（T3.8）：`1 + Y` 单射。 -/
theorem one_add_opEinv_injective : Function.Injective (1 + opEinv : Module.End ℂ Arr) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  funext k m
  induction m with
  | zero =>
    have h := congrFun (congrFun hf k) 0
    simpa [opEinv_apply] using h
  | succ m ih =>
    have h := congrFun (congrFun hf k) (m + 1)
    simp only [LinearMap.add_apply, Module.End.one_apply, Pi.add_apply, opEinv_apply,
      Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ih, Pi.zero_apply, add_zero] at h
    exact h

/-- 辅助引理（T3.8）：`Δ = 1 − Y` 单射。 -/
theorem opD_injective : Function.Injective opD := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  funext k m
  induction m with
  | zero =>
    have h := congrFun (congrFun hf k) 0
    simpa [opD_apply] using h
  | succ m ih =>
    have h := congrFun (congrFun hf k) (m + 1)
    simp only [opD_apply, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ih, Pi.zero_apply,
      sub_zero] at h
    exact h

/-- 辅助引理（T3.8）：单射算子可以从左边消去。 -/
theorem cancel_left_of_injective {T A B : Module.End ℂ Arr} (hT : Function.Injective T)
    (h : T * A = T * B) : A = B :=
  LinearMap.ext fun f => hT (LinearMap.congr_fun h f)

/-! ### `V = P·N` 与它的引理 1 算子 `L1V` -/

/-- 单点数组 `e0 = [k = 0 ∧ m = 0]`。 -/
def e0 : Arr := fun k m => if k = 0 ∧ m = 0 then 1 else 0

/-- 辅助引理（T3.8）：`V = P·N = Y·U + e0`，即 `V(k, m+1) = U(k, m)`、`V(k, 0) = N(k, 0) = [k = 0]`
（`U_eq_Vn`、`Vn_succ_zero`）。 -/
theorem opP_Narr : opP Narr = opEinv Uarr + e0 := by
  funext k m
  have hV : opP Narr k m = (Vn k m : ℂ) := by
    simp only [opP_apply, Narr, Vn]
    push_cast
    exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [hV, Pi.add_apply, Pi.add_apply, opEinv_apply]
  rcases m with _ | m
  · rcases k with _ | k
    · simp [Vn, e0, N_init.1]
    · simp [Vn_succ_zero, e0]
  · simp [e0, Uarr, U_eq_Vn]

/-- `L1V = 1 − Y − X − (m − 1)·X³`（`V` 的引理 1 算子）。 -/
noncomputable def L1V : Module.End ℂ Arr := 1 - opEinv - opX - mulOp (cM - 1) * opX ^ 3

/-- 辅助引理（T3.8）：`L1V ∈ O`。 -/
theorem L1V_mem : L1V ∈ OU :=
  sub_mem (sub_mem (sub_mem (one_mem _) opEinv_mem) opX_mem)
    (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem 3))

/-- 辅助引理（T3.8）：`Y·L1 = L1V·Y`。 -/
theorem opEinv_mul_L1 : opEinv * L1 = L1V * opEinv := by
  have h1 : opEinv * mulOp cM = mulOp (cM - 1) * opEinv := by rw [opEinv_mul_mulOp, shiftM_cM]
  have h2 : opEinv * opX = opX * opEinv := commute_opX_opEinv.eq.symm
  have h3 : opEinv * opX ^ 3 = opX ^ 3 * opEinv := (commute_opX_opEinv.pow_left 3).eq.symm
  have h4 : opEinv * (mulOp cM * opX ^ 3) = mulOp (cM - 1) * opX ^ 3 * opEinv := by
    rw [← mul_assoc, h1, mul_assoc, h3, ← mul_assoc]
  simp only [L1, L1V, mul_sub, sub_mul, mul_one, one_mul, h2, h4]

/-- 辅助引理（T3.8，搬运恒等式）：`L1V·P = Δ·P·L_N`。 -/
theorem L1V_P : L1V * opP = opD * opP * LN := by
  -- `Δ·m = 1 + (m − 1)·Δ`
  have hDm : opD * mulOp cM = 1 + mulOp (cM - 1) * opD := by
    rw [opD, sub_mul, one_mul, opEinv_mul_mulOp, shiftM_cM, mul_sub, mul_one, map_sub, map_one]
    abel
  -- `Δ·P·(q − 1)·(1+Y)² = (m − 1)·P`
  have hq : opD * opP * (mulOp (cM - 1) * (1 + opEinv) ^ 2) = mulOp (cM - 1) * opP := by
    have e1 : opP * mulOp (cM - 1) = (mulOp cM * opD - 1) * opP := by
      rw [map_sub, map_one, mul_sub, mul_one, P_mul_cM, sub_mul, one_mul]
    have e2 : opD * (mulOp cM * opD - 1) = mulOp (cM - 1) * opD ^ 2 := by
      rw [mul_sub, mul_one, ← mul_assoc, hDm, add_mul, one_mul, sq, mul_assoc]
      abel
    calc opD * opP * (mulOp (cM - 1) * (1 + opEinv) ^ 2)
        = opD * (opP * mulOp (cM - 1)) * (1 + opEinv) ^ 2 := by simp only [mul_assoc]
      _ = opD * ((mulOp cM * opD - 1) * opP) * (1 + opEinv) ^ 2 := by rw [e1]
      _ = (opD * (mulOp cM * opD - 1)) * opP * (1 + opEinv) ^ 2 := by simp only [mul_assoc]
      _ = mulOp (cM - 1) * (opD ^ 2 * opP * (1 + opEinv) ^ 2) := by
          rw [e2]; simp only [mul_assoc]
      _ = mulOp (cM - 1) * opP := by rw [opD_pow_P_one_add_pow]
  have hcX : opX * mulOp (cM - 1) = mulOp (cM - 1) * opX := by
    rw [opX_mul_mulOp]
    congr 2
    simp [shiftK, cM]
  have cPX : Commute opP opX := P_mul_opX
  have hcX3 : mulOp (cM - 1) * opX ^ 3 = opX ^ 3 * mulOp (cM - 1) :=
    ((Commute.pow_left (show Commute opX (mulOp (cM - 1)) from hcX) 3).eq).symm
  have cDPX3 : Commute (opD * opP) (opX ^ 3) :=
    Commute.mul_left (commute_opD_opX.pow_right 3) (cPX.pow_right 3)
  have t1 : opD * opP * opX = opX * (opD * opP) := by
    rw [mul_assoc, P_mul_opX, ← mul_assoc, commute_opD_opX.eq, mul_assoc]
  have t2 : opD * opP * (opX * opEinv) = opX * (opEinv * opP) := by
    rw [← mul_assoc, t1, mul_assoc, opD_P_Y]
  have t3 : opD * opP * (mulOp (cM - 1) * opX ^ 3 * (1 + opEinv) ^ 2)
      = mulOp (cM - 1) * opX ^ 3 * opP := by
    calc opD * opP * (mulOp (cM - 1) * opX ^ 3 * (1 + opEinv) ^ 2)
        = (opD * opP * opX ^ 3) * (mulOp (cM - 1) * (1 + opEinv) ^ 2) := by
          rw [hcX3]; simp only [mul_assoc]
      _ = opX ^ 3 * (opD * opP * (mulOp (cM - 1) * (1 + opEinv) ^ 2)) := by
          rw [cDPX3.eq]; simp only [mul_assoc]
      _ = mulOp (cM - 1) * opX ^ 3 * opP := by rw [hq, ← mul_assoc, ← hcX3]
  have hLN : opD * opP * LN = opD * opP - opX * (opD * opP) - opX * (opEinv * opP)
      - mulOp (cM - 1) * opX ^ 3 * opP := by
    rw [LN, mul_sub, mul_sub, mul_sub, mul_one, t1, t2, t3]
  rw [hLN, L1V]
  simp only [opD, sub_mul, mul_sub, one_mul]
  abel

/-! ### `O` 的元素在第二个下标上的因果性与有界性 -/

/-- 辅助引理（T3.8）：`O` 的元素不把数据移到更小的第二个下标：若 `f` 在第二个下标 `≤ q1` 的行上为 0，
则 `T f` 也是。 -/
theorem causal_of_mem {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∀ f : Arr, ∀ q1 : ℕ, (∀ k q, q ≤ q1 → f k q = 0) → ∀ k q, q ≤ q1 → T f k q = 0 := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · intro f q1 hf k q hq; rw [mulOp_apply, hf k q hq, mul_zero]
    · intro f q1 hf k q hq; rw [mulOp_apply, hf k q hq, mul_zero]
    · intro f q1 hf k q hq
      rw [opX_apply]
      split_ifs
      · rfl
      · exact hf _ _ hq
    · intro f q1 hf k q hq
      rw [opEinv_apply]
      split_ifs
      · rfl
      · exact hf _ _ (by omega)
  | algebraMap c =>
    intro f q1 hf k q hq
    rw [Module.algebraMap_end_apply, Pi.smul_apply, Pi.smul_apply, hf k q hq, smul_zero]
  | add x y _ _ hx hy =>
    intro f q1 hf k q hq
    rw [LinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx f q1 hf k q hq, hy f q1 hf k q hq,
      add_zero]
  | mul x y _ _ hx hy =>
    intro f q1 hf k q hq
    rw [Module.End.mul_apply]
    exact hx _ q1 (hy f q1 hf) k q hq

/-- 辅助引理（T3.8）：`O` 的元素在第二个下标上只向上移有限步：存在 `B`，使 `f` 在 `q > q1` 的行上为 0
时，`T f` 在 `q > q1 + B` 的行上为 0。 -/
theorem band_of_mem {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∃ B : ℕ, ∀ f : Arr, ∀ q1 : ℕ, (∀ k q, q1 < q → f k q = 0) →
      ∀ k q, q1 + B < q → T f k q = 0 := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, fun f q1 hf k q hq => by rw [mulOp_apply, hf k q (by omega), mul_zero]⟩
    · exact ⟨0, fun f q1 hf k q hq => by rw [mulOp_apply, hf k q (by omega), mul_zero]⟩
    · refine ⟨0, fun f q1 hf k q hq => ?_⟩
      rw [opX_apply]
      split_ifs
      · rfl
      · exact hf _ _ (by omega)
    · refine ⟨1, fun f q1 hf k q hq => ?_⟩
      rw [opEinv_apply]
      split_ifs
      · rfl
      · exact hf _ _ (by omega)
  | algebraMap c =>
    exact ⟨0, fun f q1 hf k q hq => by
      rw [Module.algebraMap_end_apply, Pi.smul_apply, Pi.smul_apply, hf k q (by omega), smul_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨B1, h1⟩ := hx
    obtain ⟨B2, h2⟩ := hy
    exact ⟨B1 + B2, fun f q1 hf k q hq => by
      rw [LinearMap.add_apply, Pi.add_apply, Pi.add_apply, h1 f q1 hf k q (by omega),
        h2 f q1 hf k q (by omega), add_zero]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨B1, h1⟩ := hx
    obtain ⟨B2, h2⟩ := hy
    exact ⟨B2 + B1, fun f q1 hf k q hq => by
      rw [Module.End.mul_apply]
      exact h1 _ (q1 + B2) (h2 f q1 hf) k q (by omega)⟩

/-! ### 三种分解 -/

/-- 辅助引理（T3.8）：`normOp 0 = 0`。 -/
theorem normOp_zero : normOp 0 = 0 := Finsupp.sum_zero_index

/-- 系数的平移 `p(k, q) ↦ p(k, q + 1)`（`shiftM` 的逆）。 -/
noncomputable def shiftMinv (p : Coef) : Coef := p.comp (Polynomial.X + 1)

/-- 辅助引理（T3.8）：`shiftM (shiftMinv p) = p`。 -/
theorem shiftM_shiftMinv (p : Coef) : shiftM (shiftMinv p) = p := by
  simp [shiftM, shiftMinv, Polynomial.comp_assoc]

/-- 辅助引理（T3.8）：`p·Y = Y·p(k, q+1)`。 -/
theorem mulOp_mul_opEinv (p : Coef) : mulOp p * opEinv = opEinv * mulOp (shiftMinv p) := by
  rw [opEinv_mul_mulOp, shiftM_shiftMinv]

/-- 辅助引理（T3.8）：右分解：`O` 的每个元素都可写成 `M·Y + R`（`M ∈ O`，`R` 是纯 `X` 位移算子）。 -/
theorem exists_right_decomp {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∃ M ∈ OU, ∃ r : ℕ →₀ Coef, T = M * opEinv + pureOp r := by
  obtain ⟨t, rfl⟩ := exists_normal_form hT
  clear hT
  induction t using Finsupp.induction_linear with
  | zero => exact ⟨0, zero_mem _, 0, by rw [normOp_zero, pureOp_zero, zero_mul, add_zero]⟩
  | add t s ht hs =>
    obtain ⟨M1, hM1, r1, h1⟩ := ht
    obtain ⟨M2, hM2, r2, h2⟩ := hs
    exact ⟨M1 + M2, add_mem hM1 hM2, r1 + r2, by
      rw [normOp_add, h1, h2, pureOp_add, add_mul]; abel⟩
  | single ab p =>
    obtain ⟨a, b⟩ := ab
    rcases b with _ | b
    · exact ⟨0, zero_mem _, Finsupp.single a p, by
        rw [normOp_single, pureOp_single, pow_zero, mul_one, zero_mul, zero_add]⟩
    · refine ⟨mulOp p * opX ^ a * opEinv ^ b,
        mul_mem (mul_mem (mulOp_mem_OU p) (pow_mem opX_mem a)) (pow_mem opEinv_mem b), 0, ?_⟩
      rw [normOp_single, pureOp_zero, add_zero]
      dsimp only
      rw [pow_succ, ← mul_assoc]

/-- 辅助引理（T3.8）：左分解 (A)：`O` 的每个元素都可写成 `Y·M + R`（`R` 是纯 `X` 位移算子）。 -/
theorem exists_left_decomp_Y {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∃ M ∈ OU, ∃ r : ℕ →₀ Coef, T = opEinv * M + pureOp r := by
  obtain ⟨t, rfl⟩ := exists_normal_form hT
  clear hT
  induction t using Finsupp.induction_linear with
  | zero => exact ⟨0, zero_mem _, 0, by rw [normOp_zero, pureOp_zero, mul_zero, add_zero]⟩
  | add t s ht hs =>
    obtain ⟨M1, hM1, r1, h1⟩ := ht
    obtain ⟨M2, hM2, r2, h2⟩ := hs
    exact ⟨M1 + M2, add_mem hM1 hM2, r1 + r2, by
      rw [normOp_add, h1, h2, pureOp_add, mul_add]; abel⟩
  | single ab p =>
    obtain ⟨a, b⟩ := ab
    rcases b with _ | b
    · exact ⟨0, zero_mem _, Finsupp.single a p, by
        rw [normOp_single, pureOp_single, pow_zero, mul_one, mul_zero, zero_add]⟩
    · refine ⟨mulOp (shiftMinv p) * opX ^ a * opEinv ^ b,
        mul_mem (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem a)) (pow_mem opEinv_mem b), 0, ?_⟩
      rw [normOp_single, pureOp_zero, add_zero]
      dsimp only
      have hE : opX ^ a * opEinv = opEinv * opX ^ a := (commute_opX_opEinv.pow_left a).eq
      rw [pow_succ', ← mul_assoc, mul_assoc (mulOp p), hE, ← mul_assoc, mulOp_mul_opEinv]
      simp only [mul_assoc]

/-- 辅助引理（T3.8）：单项式 `p·X^a·Y^b` 可写成 `(1+Y)·M + R`。 -/
theorem mono_left_decomp_one_add_Y (a b : ℕ) :
    ∀ p : Coef, ∃ M ∈ OU, ∃ r : ℕ →₀ Coef,
      mulOp p * opX ^ a * opEinv ^ b = (1 + opEinv) * M + pureOp r := by
  induction b with
  | zero => intro p; exact ⟨0, zero_mem _, Finsupp.single a p, by
      rw [pureOp_single, pow_zero, mul_one, mul_zero, zero_add]⟩
  | succ b ih =>
    intro p
    obtain ⟨M', hM', r', h'⟩ := ih (shiftMinv p)
    have hE : opX ^ a * opEinv = opEinv * opX ^ a := (commute_opX_opEinv.pow_left a).eq
    have hm : mulOp (shiftMinv p) * opX ^ a * opEinv ^ b ∈ OU :=
      mul_mem (mul_mem (mulOp_mem_OU _) (pow_mem opX_mem a)) (pow_mem opEinv_mem b)
    refine ⟨mulOp (shiftMinv p) * opX ^ a * opEinv ^ b - M', sub_mem hm hM', 0 - r', ?_⟩
    have e : mulOp p * opX ^ a * opEinv ^ (b + 1)
        = (1 + opEinv) * (mulOp (shiftMinv p) * opX ^ a * opEinv ^ b)
          - mulOp (shiftMinv p) * opX ^ a * opEinv ^ b := by
      rw [pow_succ', ← mul_assoc, mul_assoc (mulOp p), hE, ← mul_assoc, mulOp_mul_opEinv]
      simp only [add_mul, one_mul, mul_assoc]
      abel
    rw [e, h', pureOp_sub, pureOp_zero, mul_sub]
    abel

/-- 辅助引理（T3.8）：左分解 (B)：`O` 的每个元素都可写成 `(1+Y)·M + R`（`R` 是纯 `X` 位移算子）。 -/
theorem exists_left_decomp_one_add_Y {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∃ M ∈ OU, ∃ r : ℕ →₀ Coef, T = (1 + opEinv) * M + pureOp r := by
  obtain ⟨t, rfl⟩ := exists_normal_form hT
  clear hT
  induction t using Finsupp.induction_linear with
  | zero => exact ⟨0, zero_mem _, 0, by rw [normOp_zero, pureOp_zero, mul_zero, add_zero]⟩
  | add t s ht hs =>
    obtain ⟨M1, hM1, r1, h1⟩ := ht
    obtain ⟨M2, hM2, r2, h2⟩ := hs
    exact ⟨M1 + M2, add_mem hM1 hM2, r1 + r2, by
      rw [normOp_add, h1, h2, pureOp_add, mul_add]; abel⟩
  | single ab p =>
    rw [normOp_single]
    exact mono_left_decomp_one_add_Y ab.1 ab.2 p

/-- 辅助引理（T3.8）：`normOp t·Y = normOp (t 的 Y 次数加 1)`。 -/
theorem normOp_mul_opEinv (t : ℕ × ℕ →₀ Coef) :
    normOp t * opEinv = normOp (t.mapDomain fun ab => (ab.1, ab.2 + 1)) := by
  induction t using Finsupp.induction_linear with
  | zero => rw [normOp_zero, zero_mul, Finsupp.mapDomain_zero, normOp_zero]
  | add t s ht hs => rw [normOp_add, add_mul, ht, hs, Finsupp.mapDomain_add, normOp_add]
  | single ab p =>
    rw [Finsupp.mapDomain_single, normOp_single, normOp_single, mul_assoc, ← pow_succ]

/-- 辅助引理（T3.8）：`O` 的元素可以从右边消去 `Y`：`T·Y = 0 ⇒ T = 0`。 -/
theorem eq_zero_of_mul_opEinv {T : Module.End ℂ Arr} (hT : T ∈ OU) (h : T * opEinv = 0) : T = 0 := by
  obtain ⟨t, rfl⟩ := exists_normal_form hT
  rw [normOp_mul_opEinv] at h
  have h1 := normal_form_unique _ h
  have hinj : Function.Injective fun ab : ℕ × ℕ => (ab.1, ab.2 + 1) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (by omega)
  have h2 : t = 0 := Finsupp.mapDomain_injective hinj (by rw [h1, Finsupp.mapDomain_zero])
  rw [h2, normOp_zero]

/-! ### 行检验 -/

/-- 行函数：只在第二个下标为 `q0` 的那一行取值 `h(k)`。 -/
def rowFun (q0 : ℕ) (h : ℕ → ℂ) : Arr := fun k q => if q = q0 then h k else 0

/-- `k` 方向的单点函数 `[k = k0]`。 -/
def dlt (k0 : ℕ) : ℕ → ℂ := fun k => if k = k0 then 1 else 0

/-- `g` 在 `k < k0` 的列上为 0。 -/
def KSupp (g : Arr) (k0 : ℕ) : Prop := ∀ k q, k < k0 → g k q = 0

/-- 辅助引理（T3.8）：`X` 把 `KSupp` 的下界加 1。 -/
theorem KSupp.map_opX {g : Arr} {k0 : ℕ} (h : KSupp g k0) : KSupp (opX g) (k0 + 1) := by
  intro k q hk
  rw [opX_apply]
  split_ifs
  · rfl
  · exact h _ _ (by omega)

/-- 辅助引理（T3.8）：`X^j` 把 `KSupp` 的下界加 `j`。 -/
theorem KSupp.map_opX_pow {g : Arr} {k0 : ℕ} (h : KSupp g k0) (j : ℕ) :
    KSupp ((opX ^ j) g) (k0 + j) := by
  intro k q hk
  rw [opX_pow_apply]
  split_ifs
  · exact h _ _ (by omega)
  · rfl

/-- 辅助引理（T3.8）：`Y` 保持 `KSupp`。 -/
theorem KSupp.map_opEinv {g : Arr} {k0 : ℕ} (h : KSupp g k0) : KSupp (opEinv g) k0 := by
  intro k q hk
  rw [opEinv_apply]
  split_ifs
  · rfl
  · exact h _ _ hk

/-- 辅助引理（T3.8）：乘法算子保持 `KSupp`。 -/
theorem KSupp.map_mulOp {g : Arr} {k0 : ℕ} (h : KSupp g k0) (p : Coef) : KSupp (mulOp p g) k0 := by
  intro k q hk
  rw [mulOp_apply, h k q hk, mul_zero]

/-- 辅助引理（T3.8）：`KSupp` 对加法封闭。 -/
theorem KSupp.add {g g' : Arr} {k0 : ℕ} (h : KSupp g k0) (h' : KSupp g' k0) :
    KSupp (g + g') k0 := by
  intro k q hk
  rw [Pi.add_apply, Pi.add_apply, h k q hk, h' k q hk, add_zero]

/-- 辅助引理（T3.8）：`(1+Y)^n` 保持 `KSupp`。 -/
theorem KSupp.map_one_add_pow {g : Arr} {k0 : ℕ} (h : KSupp g k0) (n : ℕ) :
    KSupp (((1 + opEinv : Module.End ℂ Arr) ^ n) g) k0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply]
    exact ih.add ih.map_opEinv

/-- 辅助引理（T3.8）：`KSupp` 的下界可以减小。 -/
theorem KSupp.mono {g : Arr} {k0 k1 : ℕ} (h : KSupp g k1) (hk : k0 ≤ k1) : KSupp g k0 :=
  fun k q hq => h k q (by omega)

/-- 辅助引理（T3.8）：行函数 `rowFun q0 (dlt k0)` 在 `k < k0` 的列上为 0。 -/
theorem KSupp_rowFun_dlt (q0 k0 : ℕ) : KSupp (rowFun q0 (dlt k0)) k0 := by
  intro k q hk
  simp only [rowFun, dlt]
  split_ifs <;> first | rfl | omega

/-- 辅助引理（T3.8）：在 `k ≤ k0` 处，`L_N` 作用在 `rowFun q0 (dlt k0)` 上不改变它（含 `X` 的项为 0）。 -/
theorem LN_rowFun_dlt (q0 k0 k q : ℕ) (hk : k ≤ k0) :
    LN (rowFun q0 (dlt k0)) k q = rowFun q0 (dlt k0) k q := by
  have hf := KSupp_rowFun_dlt q0 k0
  have h1 : opX (rowFun q0 (dlt k0)) k q = 0 := hf.map_opX k q (by omega)
  have h2 : opX (opEinv (rowFun q0 (dlt k0))) k q = 0 := hf.map_opEinv.map_opX k q (by omega)
  have h3 : mulOp (cM - 1) ((opX ^ 3) (((1 + opEinv : Module.End ℂ Arr) ^ 2) (rowFun q0 (dlt k0))))
      k q = 0 :=
    ((hf.map_one_add_pow 2).map_opX_pow 3).map_mulOp _ k q (by omega)
  simp only [LN, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, Pi.sub_apply,
    h1, h2, h3, sub_zero]

/-- 辅助引理（T3.8）：在 `k ≤ k0` 处，`L1` 作用在 `rowFun q0 (dlt k0)` 上、第 `q0` 行的值是 `[k = k0]`。 -/
theorem L1_rowFun_dlt (q0 k0 k : ℕ) (hk : k ≤ k0) :
    L1 (rowFun q0 (dlt k0)) k q0 = if k = k0 then 1 else 0 := by
  have hf := KSupp_rowFun_dlt q0 k0
  have h1 : opX (rowFun q0 (dlt k0)) k q0 = 0 := hf.map_opX k q0 (by omega)
  have h3 : mulOp cM ((opX ^ 3) (rowFun q0 (dlt k0))) k q0 = 0 :=
    (hf.map_opX_pow 3).map_mulOp _ k q0 (by omega)
  have h4 : opEinv (rowFun q0 (dlt k0)) k q0 = 0 := by
    simp only [opEinv_apply, rowFun]
    split_ifs <;> first | rfl | omega
  simp only [L1, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, Pi.sub_apply,
    h1, h3, h4, sub_zero]
  simp [rowFun, dlt]

/-- 辅助引理（T3.8）：设 `a₀` 是 `r` 的支撑中最小的下标，`φ(k') = 0`（`k' < k0`）。则纯 `X` 位移算子
在第 `q` 行、`k0 + a₀` 处作用在 `φ` 上的值是 `r_{a₀}(k0 + a₀, q)·φ(k0)`。 -/
theorem row_lowest (r : ℕ →₀ Coef) {a₀ : ℕ} (ha : a₀ ∈ r.support)
    (hmin : ∀ a ∈ r.support, a₀ ≤ a) (k0 q : ℕ) (φ : ℕ → ℂ) (hφ : ∀ k', k' < k0 → φ k' = 0) :
    ∑ a ∈ r.support, (r a).evalEval ((k0 + a₀ : ℕ) : ℂ) (q : ℂ)
      * (if a ≤ k0 + a₀ then φ (k0 + a₀ - a) else 0)
      = (r a₀).evalEval ((k0 + a₀ : ℕ) : ℂ) (q : ℂ) * φ k0 := by
  rw [Finset.sum_eq_single a₀]
  · simp only [show a₀ ≤ k0 + a₀ by omega, ↓reduceIte, Nat.add_sub_cancel]
  · intro a ha' hne
    have := hmin a ha'
    split_ifs with h
    · rw [hφ _ (by omega), mul_zero]
    · rw [mul_zero]
  · intro h
    exact absurd ha h

/-- 辅助引理（T3.8）：若对支撑中最小的下标 `a₀` 与一切 `k0, q` 都有 `r_{a₀}(k0 + a₀, q) = 0`，
则 `r = 0`。 -/
theorem pure_eq_zero_of_lowest (r : ℕ →₀ Coef)
    (h : ∀ a₀ ∈ r.support, (∀ a ∈ r.support, a₀ ≤ a) →
      ∀ k0 q : ℕ, (r a₀).evalEval ((k0 + a₀ : ℕ) : ℂ) (q : ℂ) = 0) : r = 0 := by
  classical
  by_contra hr
  have hne : r.support.Nonempty := Finsupp.support_nonempty_iff.mpr hr
  have ha : r.support.min' hne ∈ r.support := r.support.min'_mem hne
  have hmin : ∀ a ∈ r.support, r.support.min' hne ≤ a := fun a ha => r.support.min'_le a ha
  have hz : r (r.support.min' hne) = 0 :=
    coef_eq_zero_of_vanish _ (r.support.min' hne) 0 (fun k q hk _ => by
      obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + r.support.min' hne := ⟨k - r.support.min' hne, by omega⟩
      exact h _ ha hmin k0 q)
  exact (Finsupp.mem_support_iff.mp ha) hz

/-! ### `Rel(V) = O·L1V` -/

/-- 辅助引理（T3.8）：若 `M ∈ O` 在某个象限上零化 `V = P·N`，则 `M ∈ O·L1V`
（由 `Rel(U) = O_U·L1` 与 `Y·L1 = L1V·Y`）。 -/
theorem relV {M : Module.End ℂ Arr} (hM : M ∈ OU)
    (hvan : ∃ k0 m0 : ℕ, VanishOn (M (opP Narr)) k0 m0) : ∃ Q ∈ OU, M = Q * L1V := by
  obtain ⟨k0, m0, hv⟩ := hvan
  obtain ⟨A, B, hreach⟩ := reach_of_mem hM
  have he0 : VanishOn (M e0) (1 + A) (1 + B) :=
    hreach e0 1 1 (fun k m hk hm => by simp only [e0]; split_ifs with h <;> first | rfl | omega)
  -- `M·Y ∈ Rel(U)`
  have hMY : M * opEinv ∈ RelU := by
    refine ⟨mul_mem hM opEinv_mem, max k0 (1 + A), max m0 (1 + B), fun k m hk hm => ?_⟩
    have h1 := hv k m (by omega) (by omega)
    have h2 := he0 k m (by omega) (by omega)
    rw [opP_Narr, map_add, Pi.add_apply, Pi.add_apply, h2, add_zero] at h1
    exact h1
  rw [RelU_eq] at hMY
  obtain ⟨Q, hQ, hMQ⟩ := hMY
  obtain ⟨Q'', hQ'', r, rfl⟩ := exists_right_decomp hQ
  -- `(M − Q''·L1V)·Y = R·L1`
  have key : (M - Q'' * L1V) * opEinv = pureOp r * L1 := by
    rw [sub_mul, hMQ, add_mul, mul_assoc Q'', opEinv_mul_L1, ← mul_assoc]
    abel
  have hT : M - Q'' * L1V ∈ OU := sub_mem hM (mul_mem hQ'' L1V_mem)
  -- 行检验：`R = 0`
  have hr : r = 0 := by
    apply pure_eq_zero_of_lowest
    intro a₀ ha hmin k1 q0
    have h0 := LinearMap.congr_fun key (rowFun q0 (dlt k1))
    have h0' := congrFun (congrFun h0 (k1 + a₀)) q0
    simp only [Module.End.mul_apply] at h0'
    have hl : (M - Q'' * L1V) (opEinv (rowFun q0 (dlt k1))) (k1 + a₀) q0 = 0 :=
      causal_of_mem hT _ q0 (fun k q hq => by
        simp only [opEinv_apply, rowFun]
        split_ifs <;> first | rfl | omega) _ _ le_rfl
    rw [hl, pureOp_apply, row_lowest r ha hmin k1 q0 (fun k' => L1 (rowFun q0 (dlt k1)) k' q0)
      (fun k' hk' => by rw [L1_rowFun_dlt q0 k1 k' hk'.le]; simp [show k' ≠ k1 by omega])] at h0'
    rw [L1_rowFun_dlt q0 k1 k1 le_rfl] at h0'
    simp only [↓reduceIte, mul_one] at h0'
    exact h0'.symm
  rw [hr, pureOp_zero, zero_mul] at key
  exact ⟨Q'', hQ'', (sub_eq_zero.mp (eq_zero_of_mul_opEinv hT key))⟩

/-! ### 饱和引理（`notes/c3b.md` §7.2） -/

/-- **饱和引理 (i)**（T3.8 的证明要点，`notes/c3b.md` §7.2）：对 `L ∈ O_N`，若 `Y·L ∈ O_N·L_N`，
则 `L ∈ O_N·L_N`。 -/
theorem saturation_Y {L : Module.End ℂ Arr} (hL : L ∈ OU)
    (h : ∃ Λ ∈ OU, opEinv * L = Λ * LN) : ∃ Λ' ∈ OU, L = Λ' * LN := by
  obtain ⟨Λ, hΛ, hYL⟩ := h
  obtain ⟨Λ1, hΛ1, r, rfl⟩ := exists_left_decomp_Y hΛ
  -- `R·L_N = Y·(L − Λ1·L_N)`
  have key : pureOp r * LN = opEinv * (L - Λ1 * LN) := by
    rw [mul_sub, hYL, add_mul, ← mul_assoc]
    abel
  have hT : L - Λ1 * LN ∈ OU := sub_mem hL (mul_mem hΛ1 LN_mem)
  have hr : r = 0 := by
    apply pure_eq_zero_of_lowest
    intro a₀ ha hmin k1 q0
    have h0' := congrFun (congrFun (LinearMap.congr_fun key (rowFun q0 (dlt k1))) (k1 + a₀)) q0
    simp only [Module.End.mul_apply] at h0'
    have hr0 : opEinv ((L - Λ1 * LN) (rowFun q0 (dlt k1))) (k1 + a₀) q0 = 0 := by
      rw [opEinv_apply]
      split_ifs with hq
      · rfl
      · exact causal_of_mem hT _ (q0 - 1) (fun k q hq' => by
          simp only [rowFun]
          split_ifs <;> first | rfl | omega) _ _ le_rfl
    rw [hr0, pureOp_apply, row_lowest r ha hmin k1 q0 (fun k' => LN (rowFun q0 (dlt k1)) k' q0)
      (fun k' hk' => by
        rw [LN_rowFun_dlt q0 k1 k' q0 hk'.le]
        simp [rowFun, dlt, show k' ≠ k1 by omega])] at h0'
    rw [LN_rowFun_dlt q0 k1 k1 q0 le_rfl] at h0'
    simpa [rowFun, dlt] using h0'
  rw [hr, pureOp_zero, add_zero] at hYL
  refine ⟨Λ1, hΛ1, cancel_left_of_injective opEinv_injective ?_⟩
  rw [hYL, mul_assoc]

/-- 辅助引理（T3.8）：交错行和的伸缩：`Σ_{j≤J} (−1)^j ((1+Y) g)(k, q0 + j) = (−1)^J g(k, q0 + J)`
（当 `q0 ≥ 1` 时要求 `g(k, q0 − 1) = 0`）。 -/
theorem alt_sum_one_add_opEinv (g : Arr) (k q0 : ℕ) (hg : q0 ≠ 0 → g k (q0 - 1) = 0) (J : ℕ) :
    ∑ j ∈ range (J + 1), (-1 : ℂ) ^ j * ((1 + opEinv) g) k (q0 + j) = (-1) ^ J * g k (q0 + J) := by
  induction J with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul, add_zero,
      LinearMap.add_apply, Module.End.one_apply, Pi.add_apply, opEinv_apply]
    split_ifs with hq
    · rw [add_zero]
    · rw [hg hq, add_zero]
  | succ J ih =>
    rw [sum_range_succ, ih]
    simp only [LinearMap.add_apply, Module.End.one_apply, Pi.add_apply, opEinv_apply,
      show q0 + (J + 1) ≠ 0 by omega, ↓reduceIte, show q0 + (J + 1) - 1 = q0 + J by omega]
    rw [pow_succ]
    ring

/-- **饱和引理 (ii)**（T3.8 的证明要点，`notes/c3b.md` §7.2）：对 `L ∈ O_N`，若 `(1+Y)·L ∈ O_N·L_N`，
则 `L ∈ O_N·L_N`。 -/
theorem saturation_one_add_Y {L : Module.End ℂ Arr} (hL : L ∈ OU)
    (h : ∃ Λ ∈ OU, (1 + opEinv) * L = Λ * LN) : ∃ Λ' ∈ OU, L = Λ' * LN := by
  obtain ⟨Λ, hΛ, hYL⟩ := h
  obtain ⟨Λ1, hΛ1, r, rfl⟩ := exists_left_decomp_one_add_Y hΛ
  -- `R·L_N = (1+Y)·(L − Λ1·L_N)`
  have key : pureOp r * LN = (1 + opEinv) * (L - Λ1 * LN) := by
    rw [mul_sub, hYL, add_mul, ← mul_assoc]
    abel
  have hT : L - Λ1 * LN ∈ OU := sub_mem hL (mul_mem hΛ1 LN_mem)
  obtain ⟨Bd, hBd⟩ := band_of_mem hT
  have hr : r = 0 := by
    apply pure_eq_zero_of_lowest
    intro a₀ ha hmin k1 q0
    set f := rowFun q0 (dlt k1) with hf
    set g := (L - Λ1 * LN) f with hg
    -- 左边每一行：`(R·L_N f)(k1 + a₀, q0 + j) = r_{a₀}(k1 + a₀, q0 + j)·[j = 0]`
    have hrow : ∀ j, (pureOp r * LN) f (k1 + a₀) (q0 + j)
        = (r a₀).evalEval ((k1 + a₀ : ℕ) : ℂ) ((q0 + j : ℕ) : ℂ) * (if j = 0 then 1 else 0) := by
      intro j
      rw [Module.End.mul_apply, pureOp_apply,
        row_lowest r ha hmin k1 (q0 + j) (fun k' => LN f k' (q0 + j)) (fun k' hk' => by
          rw [hf, LN_rowFun_dlt q0 k1 k' (q0 + j) hk'.le]
          simp [rowFun, dlt, show k' ≠ k1 by omega])]
      rw [hf, LN_rowFun_dlt q0 k1 k1 (q0 + j) le_rfl]
      by_cases hj : j = 0
      · subst hj; simp [rowFun, dlt]
      · simp [rowFun, hj]
    -- 交错行和
    have hsum := alt_sum_one_add_opEinv g (k1 + a₀) q0 (fun hq => by
      rw [hg]
      exact causal_of_mem hT f (q0 - 1) (fun k q hq' => by
        rw [hf]; simp only [rowFun]; split_ifs <;> first | rfl | omega) _ _ le_rfl) (Bd + 1)
    have hgB : g (k1 + a₀) (q0 + (Bd + 1)) = 0 :=
      hBd f q0 (fun k q hq => by rw [hf]; simp only [rowFun]; split_ifs <;> first | rfl | omega)
        _ _ (by omega)
    rw [hgB, mul_zero] at hsum
    have hL' : ∀ j, (-1 : ℂ) ^ j * ((1 + opEinv) g) (k1 + a₀) (q0 + j)
        = (-1 : ℂ) ^ j * ((r a₀).evalEval ((k1 + a₀ : ℕ) : ℂ) ((q0 + j : ℕ) : ℂ)
          * (if j = 0 then 1 else 0)) := by
      intro j
      rw [← hrow j, key, Module.End.mul_apply]
    simp only [hL'] at hsum
    rw [sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.mpr (by omega)) h)]
      at hsum
    simpa using hsum
  rw [hr, pureOp_zero, add_zero] at hYL
  refine ⟨Λ1, hΛ1, cancel_left_of_injective one_add_opEinv_injective ?_⟩
  rw [hYL, mul_assoc]

/-! ### 搬运：`N` 一侧与 `V` 一侧的交换关系 -/

/-- 辅助引理（T3.8）：`Δ·p = (p − p(k, m−1)) + p(k, m−1)·Δ`。 -/
theorem opD_mul_mulOp (p : Coef) :
    opD * mulOp p = mulOp (p - shiftM p) + mulOp (shiftM p) * opD := by
  rw [opD, sub_mul, one_mul, opEinv_mul_mulOp, map_sub, mul_sub, mul_one]
  abel

/-- 辅助引理（T3.8）：`shiftM (m − c) = m − (c + 1)`。 -/
theorem shiftM_cM_sub_natCast (c : ℕ) : shiftM (cM - (c : Coef)) = cM - ((c + 1 : ℕ) : Coef) := by
  simp only [shiftM, cM, sub_comp, X_comp, natCast_comp]
  push_cast
  ring

/-- 辅助引理（T3.8）：`Δ^c·m·Δ = ((m − c)·Δ + c)·Δ^c`。 -/
theorem opD_pow_cM_opD (c : ℕ) :
    opD ^ c * mulOp cM * opD
      = (mulOp (cM - (c : Coef)) * opD + (c : Module.End ℂ Arr)) * opD ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 : opD * mulOp (cM - (c : Coef)) = 1 + mulOp (cM - ((c + 1 : ℕ) : Coef)) * opD := by
      rw [opD_mul_mulOp, shiftM_cM_sub_natCast]
      congr 1
      rw [show cM - (c : Coef) - (cM - ((c + 1 : ℕ) : Coef)) = 1 by push_cast; ring, map_one]
    have h2 : opD * (c : Module.End ℂ Arr) = (c : Module.End ℂ Arr) * opD :=
      (Nat.cast_commute c opD).eq.symm
    calc opD ^ (c + 1) * mulOp cM * opD = opD * (opD ^ c * mulOp cM * opD) := by
          rw [pow_succ']; simp only [mul_assoc]
      _ = opD * ((mulOp (cM - (c : Coef)) * opD + (c : Module.End ℂ Arr)) * opD ^ c) := by
          rw [ih]
      _ = (opD * mulOp (cM - (c : Coef)) * opD + opD * (c : Module.End ℂ Arr)) * opD ^ c := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = ((1 + mulOp (cM - ((c + 1 : ℕ) : Coef)) * opD) * opD
            + (c : Module.End ℂ Arr) * opD) * opD ^ c := by rw [h1, h2]
      _ = (mulOp (cM - ((c + 1 : ℕ) : Coef)) * opD + ((c + 1 : ℕ) : Module.End ℂ Arr))
            * opD ^ (c + 1) := by
          rw [pow_succ']
          push_cast
          simp only [add_mul, one_mul, mul_assoc]
          abel

/-- 辅助引理（T3.8，`N` 一侧到 `V` 一侧）：对 `𝓛 ∈ O` 与任意 `c`，存在 `j` 与 `𝓜 ∈ O`，
使 `Δ^j·P·𝓛 = 𝓜·Δ^c·P`。 -/
theorem exists_N_to_V {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∀ c : ℕ, ∃ j : ℕ, ∃ M ∈ OU, opD ^ j * opP * T = M * opD ^ c * opP := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · intro c
      refine ⟨c, mulOp cK, cK_mem, ?_⟩
      rw [mul_assoc, P_mul_cK, ← mul_assoc, (commute_opD_cK.pow_left c).eq]
    · intro c
      refine ⟨c, mulOp (cM - (c : Coef)) * opD + (c : Module.End ℂ Arr),
        add_mem (mul_mem (mulOp_mem_OU _) opD_mem) (natCast_mem _ c), ?_⟩
      rw [mul_assoc, P_mul_cM, ← mul_assoc, ← mul_assoc, opD_pow_cM_opD]
    · intro c
      refine ⟨c, opX, opX_mem, ?_⟩
      rw [mul_assoc, P_mul_opX, ← mul_assoc, (commute_opD_opX.pow_left c).eq]
    · intro c
      refine ⟨c + 1, opEinv, opEinv_mem, ?_⟩
      calc opD ^ (c + 1) * opP * opEinv = opD ^ c * (opD * opP * opEinv) := by
            rw [pow_succ]; simp only [mul_assoc]
        _ = opEinv * opD ^ c * opP := by
            rw [opD_P_Y, ← mul_assoc, (commute_opD_opEinv.pow_left c).eq]
  | algebraMap r =>
    intro c
    refine ⟨c, algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, ?_⟩
    rw [← Algebra.commutes r (opD ^ c * opP), mul_assoc]
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨j1, M1, hM1, h1⟩ := hx c
    obtain ⟨j2, M2, hM2, h2⟩ := hy c
    refine ⟨j1 + j2, opD ^ j2 * M1 + opD ^ j1 * M2,
      add_mem (mul_mem (pow_mem opD_mem _) hM1) (mul_mem (pow_mem opD_mem _) hM2), ?_⟩
    calc opD ^ (j1 + j2) * opP * (x + y)
        = opD ^ j2 * (opD ^ j1 * opP * x) + opD ^ j1 * (opD ^ j2 * opP * y) := by
          rw [mul_add]
          congr 1
          · rw [add_comm j1 j2, pow_add]; simp only [mul_assoc]
          · rw [pow_add]; simp only [mul_assoc]
      _ = (opD ^ j2 * M1 + opD ^ j1 * M2) * opD ^ c * opP := by
          rw [h1, h2]; simp only [add_mul, mul_assoc]
  | mul x y _ _ hx hy =>
    intro c
    obtain ⟨j2, M2, hM2, h2⟩ := hy c
    obtain ⟨j1, M1, hM1, h1⟩ := hx j2
    refine ⟨j1, M1 * M2, mul_mem hM1 hM2, ?_⟩
    calc opD ^ j1 * opP * (x * y) = (opD ^ j1 * opP * x) * y := by simp only [mul_assoc]
      _ = M1 * (opD ^ j2 * opP * y) := by rw [h1]; simp only [mul_assoc]
      _ = M1 * M2 * opD ^ c * opP := by rw [h2]; simp only [mul_assoc]

/-- 辅助引理（T3.8）：`m·Δ^a·P = Δ^a·P·(q·(1+Y) − a·Y)`。 -/
theorem cM_opD_pow_P (a : ℕ) :
    mulOp cM * opD ^ a * opP
      = opD ^ a * opP * (mulOp cM * (1 + opEinv) - (a : Module.End ℂ Arr) * opEinv) := by
  induction a with
  | zero =>
    simp only [pow_zero, mul_one, one_mul, Nat.cast_zero, zero_mul, sub_zero]
    calc mulOp cM * opP = mulOp cM * (opD * opP * (1 + opEinv)) := by rw [opD_P_one_add]
      _ = (opP * mulOp cM) * (1 + opEinv) := by rw [P_mul_cM]; simp only [mul_assoc]
      _ = opP * (mulOp cM * (1 + opEinv)) := by rw [mul_assoc]
  | succ a ih =>
    -- `m·Δ = Δ·(m + 1) − 1`
    have hmD : mulOp cM * opD = opD * mulOp cM + opD - 1 := by
      have h := opD_mul_mulOp (cM + 1)
      have e1 : shiftM (cM + 1) = cM := by simp [shiftM, cM]
      rw [e1, show cM + 1 - cM = (1 : Coef) by ring, map_one, map_add, map_one, mul_add,
        mul_one] at h
      rw [h]
      abel
    have hPa : opD ^ a * opP = opD ^ (a + 1) * opP * (1 + opEinv) := by
      rw [pow_succ, mul_assoc (opD ^ a), mul_assoc (opD ^ a), opD_P_one_add]
    calc mulOp cM * opD ^ (a + 1) * opP = (mulOp cM * opD) * (opD ^ a * opP) := by
          rw [pow_succ']; simp only [mul_assoc]
      _ = opD * (mulOp cM * opD ^ a * opP) + opD * (opD ^ a * opP) - opD ^ a * opP := by
          rw [hmD]; simp only [add_mul, sub_mul, one_mul, mul_assoc]
      _ = opD ^ (a + 1) * opP * (mulOp cM * (1 + opEinv) - (a : Module.End ℂ Arr) * opEinv)
            + opD ^ (a + 1) * opP - opD ^ (a + 1) * opP * (1 + opEinv) := by
          have hA : opD * (opD ^ a * opP) = opD ^ (a + 1) * opP := by
            rw [pow_succ']; simp only [mul_assoc]
          have hB : opD * (opD ^ a * opP
              * (mulOp cM * (1 + opEinv) - (a : Module.End ℂ Arr) * opEinv))
              = opD ^ (a + 1) * opP
                * (mulOp cM * (1 + opEinv) - (a : Module.End ℂ Arr) * opEinv) := by
            rw [pow_succ']; simp only [mul_assoc]
          rw [ih, hB, hA, hPa]
      _ = opD ^ (a + 1) * opP
            * (mulOp cM * (1 + opEinv) - ((a + 1 : ℕ) : Module.End ℂ Arr) * opEinv) := by
          push_cast
          simp only [mul_sub, mul_add, add_mul, mul_one, one_mul]
          abel

/-- 辅助引理（T3.8，`V` 一侧回到 `N` 一侧）：对 `𝒬 ∈ O` 与任意 `a`，存在 `c` 与 `Z ∈ O`，
使 `𝒬·Δ^a·P = Δ^c·P·Z`。 -/
theorem exists_V_to_N {T : Module.End ℂ Arr} (hT : T ∈ OU) :
    ∀ a : ℕ, ∃ c : ℕ, ∃ Z ∈ OU, T * opD ^ a * opP = opD ^ c * opP * Z := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · intro a
      refine ⟨a, mulOp cK, cK_mem, ?_⟩
      rw [← (commute_opD_cK.pow_left a).eq, mul_assoc, mul_assoc, P_mul_cK]
    · intro a
      refine ⟨a, mulOp cM * (1 + opEinv) - (a : Module.End ℂ Arr) * opEinv,
        sub_mem (mul_mem cM_mem (add_mem (one_mem _) opEinv_mem))
          (mul_mem (natCast_mem _ a) opEinv_mem), cM_opD_pow_P a⟩
    · intro a
      refine ⟨a, opX, opX_mem, ?_⟩
      rw [← (commute_opD_opX.pow_left a).eq, mul_assoc, mul_assoc, P_mul_opX]
    · intro a
      refine ⟨a + 1, opEinv, opEinv_mem, ?_⟩
      rw [← (commute_opD_opEinv.pow_left a).eq, mul_assoc, ← opD_P_Y, pow_succ]
      simp only [mul_assoc]
  | algebraMap r =>
    intro a
    refine ⟨a, algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, ?_⟩
    rw [Algebra.commutes r (opD ^ a), mul_assoc, Algebra.commutes r opP, ← mul_assoc]
  | add x y _ _ hx hy =>
    intro a
    obtain ⟨c1, Z1, hZ1, h1⟩ := hx a
    obtain ⟨c2, Z2, hZ2, h2⟩ := hy a
    have hY : (1 + opEinv : Module.End ℂ Arr) ∈ OU := add_mem (one_mem _) opEinv_mem
    refine ⟨c1 + c2, (1 + opEinv) ^ c2 * Z1 + (1 + opEinv) ^ c1 * Z2,
      add_mem (mul_mem (pow_mem hY _) hZ1) (mul_mem (pow_mem hY _) hZ2), ?_⟩
    have e1 : opD ^ c1 * opP = opD ^ (c1 + c2) * opP * (1 + opEinv) ^ c2 := by
      conv_lhs => rw [← opD_pow_P_one_add_pow c2]
      rw [pow_add]; simp only [mul_assoc]
    have e2 : opD ^ c2 * opP = opD ^ (c1 + c2) * opP * (1 + opEinv) ^ c1 := by
      conv_lhs => rw [← opD_pow_P_one_add_pow c1]
      rw [add_comm c1 c2, pow_add]; simp only [mul_assoc]
    rw [add_mul, add_mul, h1, h2, e1, e2]
    simp only [mul_add, mul_assoc]
  | mul x y _ _ hx hy =>
    intro a
    obtain ⟨c2, Z2, hZ2, h2⟩ := hy a
    obtain ⟨c1, Z1, hZ1, h1⟩ := hx c2
    refine ⟨c1, Z1 * Z2, mul_mem hZ1 hZ2, ?_⟩
    calc x * y * opD ^ a * opP = x * (y * opD ^ a * opP) := by simp only [mul_assoc]
      _ = (x * opD ^ c2 * opP) * Z2 := by rw [h2]; simp only [mul_assoc]
      _ = opD ^ c1 * opP * (Z1 * Z2) := by rw [h1]; simp only [mul_assoc]

/-! ### 边界部分的消去 -/

/-- 辅助引理（T3.8）：若 `h` 在第二个下标 `≥ s` 的行上为 0，则 `Δ h` 在 `≥ s + 1` 的行上为 0。 -/
theorem opD_vanish_rows {h : Arr} {s : ℕ} (hh : ∀ k q, s ≤ q → h k q = 0) :
    ∀ k q, s + 1 ≤ q → opD h k q = 0 := by
  intro k q hq
  rw [opD_apply, hh k q (by omega)]
  simp only [show q ≠ 0 by omega, ↓reduceIte, hh k (q - 1) (by omega), sub_zero]

/-- 辅助引理（T3.8）：若 `g` 在象限 `k ≥ k0, q ≥ n` 上为 0，则 `Δ^n·P·g` 在象限 `k ≥ k0, m ≥ n` 上为 0
（`q < n` 的边界部分经 `P` 变成 `m` 的次数 `< n` 的多项式，被 `Δ^n` 消去）。 -/
theorem opD_pow_P_vanish (n : ℕ) : ∀ (g : Arr) (k0 : ℕ), (∀ k q, k0 ≤ k → n ≤ q → g k q = 0) →
    ∀ k m, k0 ≤ k → n ≤ m → (opD ^ n * opP) g k m = 0 := by
  induction n with
  | zero =>
    intro g k0 hg k m hk _
    simp only [pow_zero, one_mul, opP_apply]
    exact sum_eq_zero fun q _ => by rw [hg k q hk (Nat.zero_le q), mul_zero]
  | succ n ih =>
    intro g k0 hg k m hk hm
    set g0 : Arr := fun k q => if q = 0 then g k 0 else 0 with hg0
    set g' : Arr := fun k q => g k (q + 1) with hg'
    have hsplit : g = g0 + opEinv g' := by
      funext k q
      simp only [Pi.add_apply, hg0, hg', opEinv_apply]
      rcases q with _ | q
      · simp
      · simp
    have hP0 : opD (opP g0) = g0 := by
      funext k q
      have hc : ∀ m, opP g0 k m = g k 0 := by
        intro m
        rw [opP_apply, sum_eq_single 0]
        · simp [hg0]
        · intro b _ hb; simp [hg0, hb]
        · intro h; exact absurd (mem_range.mpr (Nat.succ_pos m)) h
      rw [opD_apply, hc q]
      rcases q with _ | q
      · simp [hg0]
      · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [hc q, sub_self]
        simp [hg0]
    have hrow : ∀ i, ∀ k q, i + 1 ≤ q → (opD ^ i) g0 k q = 0 := by
      intro i
      induction i with
      | zero => intro k q hq; simp [hg0, show q ≠ 0 by omega]
      | succ i ihi =>
        intro k q hq
        rw [pow_succ', Module.End.mul_apply]
        exact opD_vanish_rows ihi k q (by omega)
    have hsum : (opD ^ (n + 1) * opP) g = (opD ^ n) g0 + opEinv ((opD ^ n * opP) g') := by
      have e : (opD ^ (n + 1) * opP) g = (opD ^ n) (opD (opP g)) := by
        rw [pow_succ]; simp only [Module.End.mul_apply]
      rw [e, hsplit, map_add, map_add, hP0, map_add]
      congr 1
      have e2 : opD (opP (opEinv g')) = opEinv (opP g') := LinearMap.congr_fun opD_P_Y g'
      rw [e2]
      have e3 : (opD ^ n) (opEinv (opP g')) = opEinv ((opD ^ n) (opP g')) :=
        LinearMap.congr_fun (commute_opD_opEinv.pow_left n).eq (opP g')
      rw [e3]
      rfl
    rw [hsum, Pi.add_apply, Pi.add_apply, hrow n k m (by omega), zero_add, opEinv_apply]
    simp only [show m ≠ 0 by omega, ↓reduceIte]
    exact ih g' k0 (fun k q hk hq => hg k (q + 1) hk (by omega)) k (m - 1) hk (by omega)

/-! ### 主定理 -/

/-- 辅助引理（T3.8）：`Δ^n` 单射。 -/
theorem opD_pow_injective (n : ℕ) : Function.Injective (opD ^ n) := by
  rw [Module.End.coe_pow]
  exact opD_injective.iterate n

/-- 辅助引理（T3.8）：饱和引理 (ii) 的迭代：`(1+Y)^c·L ∈ O_N·L_N ⇒ L ∈ O_N·L_N`。 -/
theorem saturation_one_add_Y_pow (c : ℕ) :
    ∀ {L : Module.End ℂ Arr}, L ∈ OU → (∃ Λ ∈ OU, (1 + opEinv) ^ c * L = Λ * LN) →
      ∃ Λ' ∈ OU, L = Λ' * LN := by
  induction c with
  | zero => intro L _ h; simpa using h
  | succ c ih =>
    intro L hL h
    rw [pow_succ', mul_assoc] at h
    exact ih hL (saturation_one_add_Y
      (mul_mem (pow_mem (add_mem (one_mem _) opEinv_mem) c) hL) h)

/-- **T3.8（`N` 的部分）**：`Rel(N) = O_N·L_N`，即 `O_N = ℂ[k,q]⟨X, Y⟩` 中在某个象限上零化 `N`
的算子，恰好是 `Q·L_N`（`Q ∈ O_N`，`L_N = 1 − X − XY − (q−1)X³(1+Y)²`）。 -/
theorem RelN_eq : RelN = {R | ∃ Q ∈ OU, R = Q * LN} := by
  ext L
  constructor
  · rintro ⟨hL, k0, q0, hvan⟩
    -- 搬到 `V` 一侧：`Δ^j·P·L = M·P`
    obtain ⟨j, M, hM, hjM⟩ := exists_N_to_V hL 0
    rw [pow_zero, mul_one] at hjM
    -- `Δ^{q0}·M` 在象限上零化 `V`
    have hV : VanishOn ((opD ^ q0 * M) (opP Narr)) k0 (q0 + j) := by
      intro k m hk hm
      have e : (opD ^ q0 * M) (opP Narr) = (opD ^ (q0 + j) * opP) (L Narr) := by
        have := LinearMap.congr_fun hjM Narr
        simp only [Module.End.mul_apply] at this
        rw [pow_add]
        simp only [Module.End.mul_apply]
        rw [this]
      rw [e]
      exact opD_pow_P_vanish (q0 + j) (L Narr) k0 (fun k q hk hq => hvan k q hk (by omega))
        k m hk hm
    obtain ⟨Q, hQ, hQe⟩ := relV (mul_mem (pow_mem opD_mem q0) hM) ⟨k0, q0 + j, hV⟩
    -- `Δ^n·P·L = Q·Δ·P·L_N`（搬运恒等式）
    set n := q0 + j with hn
    have h1 : opD ^ n * opP * L = Q * (opD * opP * LN) := by
      rw [← L1V_P, hn, pow_add]
      calc opD ^ q0 * opD ^ j * opP * L = opD ^ q0 * (opD ^ j * opP * L) := by
            simp only [mul_assoc]
        _ = (opD ^ q0 * M) * opP := by rw [hjM]; simp only [mul_assoc]
        _ = Q * (L1V * opP) := by rw [hQe]; simp only [mul_assoc]
    -- 回到 `N` 一侧：`Q·Δ·P = Δ^c·P·Z`
    obtain ⟨c, Z, hZ, hcZ⟩ := exists_V_to_N hQ 1
    rw [pow_one] at hcZ
    have hY : (1 + opEinv : Module.End ℂ Arr) ∈ OU := add_mem (one_mem _) opEinv_mem
    -- `(1+Y)^c·L = (1+Y)^n·Z·L_N`
    have h2 : opD ^ n * (opD ^ c * (opP * ((1 + opEinv) ^ c * L)))
        = opD ^ n * (opD ^ c * (opP * ((1 + opEinv) ^ n * Z * LN))) := by
      calc opD ^ n * (opD ^ c * (opP * ((1 + opEinv) ^ c * L)))
          = opD ^ n * ((opD ^ c * opP * (1 + opEinv) ^ c) * L) := by simp only [mul_assoc]
        _ = opD ^ n * opP * L := by rw [opD_pow_P_one_add_pow]; simp only [mul_assoc]
        _ = Q * opD * opP * LN := by rw [h1]; simp only [mul_assoc]
        _ = opD ^ c * opP * Z * LN := by rw [hcZ]
        _ = opD ^ c * (opD ^ n * opP * (1 + opEinv) ^ n) * Z * LN := by
            rw [opD_pow_P_one_add_pow]
        _ = opD ^ n * (opD ^ c * (opP * ((1 + opEinv) ^ n * Z * LN))) := by
            simp only [mul_assoc]
            rw [← mul_assoc (opD ^ c) (opD ^ n), ← pow_add, add_comm c n, pow_add, mul_assoc]
    have h3 := cancel_left_of_injective (opD_pow_injective n) h2
    have h4 := cancel_left_of_injective (opD_pow_injective c) h3
    have h5 := cancel_left_of_injective opP_injective h4
    obtain ⟨Λ', hΛ', hL'⟩ := saturation_one_add_Y_pow c hL
      ⟨(1 + opEinv) ^ n * Z, mul_mem (pow_mem hY n) hZ, h5⟩
    exact ⟨Λ', hΛ', hL'⟩
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨mul_mem hQ LN_mem, ?_⟩
    obtain ⟨A, B, hreach⟩ := reach_of_mem hQ
    exact ⟨3 + A, 1 + B, hreach _ 3 1 LN_N⟩

/-- **T3.8（`N` 的部分，左理想形式）**：在环 `O_N` 中，`R` 在某个象限上零化 `N` 当且仅当 `R` 属于
`L_N` 生成的左理想 `O_N·L_N`（`Ideal.span {L_N}`；非交换环中 `Ideal` 指左理想）。 -/
theorem RelN_iff_mem_span (R : OU) :
    (∃ k0 q0 : ℕ, VanishOn ((R : Module.End ℂ Arr) Narr) k0 q0) ↔
      R ∈ Ideal.span {(⟨LN, LN_mem⟩ : OU)} := by
  rw [Ideal.mem_span_singleton']
  constructor
  · intro h
    have hR : (R : Module.End ℂ Arr) ∈ RelN := ⟨R.2, h⟩
    rw [RelN_eq] at hR
    obtain ⟨Q, hQ, hRQ⟩ := hR
    exact ⟨⟨Q, hQ⟩, Subtype.ext hRQ.symm⟩
  · rintro ⟨Q, rfl⟩
    have hR : ((Q * ⟨LN, LN_mem⟩ : OU) : Module.End ℂ Arr) ∈ RelN := by
      rw [RelN_eq]
      exact ⟨Q, Q.2, rfl⟩
    exact hR.2

end A207123
