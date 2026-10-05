import A207123.DFinite
import A207123.Binomial

/-!
# 报告 T3.7(3) 前半：`𝒩` 不是 D-finite（以及 T3.5(1) 的代换恒等式）

`DFinite.lean` 形式化了 T3.7(1)「`F` 不是 D-finite」。本文件对 `N(k,q)` 的二元母函数
`𝒩(x,y) = Σ_{k,q} N(k,q)·x^k·y^q` 做同样的事：形式化报告 T3.7(3) 的前半「`𝒩` 同样不是
D-finite」，以及证明要用的 T3.5(1) 代换关系 `1 + tF(x,t) = 𝒩(x, t/(1−t))/(1−t)`。
T3.7(3) 的后半（`N` 没有只依赖 `k` 的象限递推）不在本文件中。

## 定义

* `NKser K = Σ_{k,q} N(k,q)·x^k·y^q ∈ K[[x,y]]`，与 `PS2`、`FK` 一样写成 `K[[x]][[y]]`：外层变量是
  `y`、内层变量是 `x`，`[y^q]𝒩 = Ψ_q(x) = Σ_k N(k,q)·x^k`（`coeff_NKser`）。`N k q` 是 `Binomial.lean`
  的定义（长 `k`、值域恰为 `{1,…,q}` 的合法词个数，报告 T1.4）。
* D-finite 直接用 `DFinite.lean` 的 `IsDFinite`（Lipshitz 1989 Def. 2.1，`n = 2`，外围域取
  `Frac(K[[x,y]])`，全部偏导数 `∂_x^i ∂_y^j` 张成的 `K(x,y)`-空间有限维）。那里把 `PS2` 的外层变量叫 `t`，
  这里外层变量是 `y`，只是名字不同；定义本身对两个变量对称。
* `tFrac R = t/(1−t) = t + t² + ⋯ ∈ R[[t]]`（`coeff_tFrac`，且 `tFrac·(1−t) = t`：`tFrac_mul_one_sub_X`）。
* `substY K : K[[x]][[y]] →+* K[[x]][[t]]`：代换 `y ↦ t/(1−t)`，就是 Mathlib 的 `PowerSeries.subst`
  （系数环取 `K[[x]]`；`substY_apply` 是 `rfl`）。它是环同态，固定 `K[[x]]`（`substY_C`），把 `y` 映成
  `t/(1−t)`（`substY_X`），并与 `∂_x` 交换（`substY_dXK`）。
  注意：Mathlib 在 `K[[x]][[y]]` 上注册的 `K[[x]]`-代数结构 `PowerSeries.algebraPowerSeries` 是
  「`x^n ↦ y^n`」那一个，不是常数嵌入，所以这里不把 `substY` 写成 `K[[x]]`-代数同态，只记成环同态，
  再单独证明 `substY_C`。

## 结论

* `subst_NKser`、`substY_NKser`（**T3.5(1)**）：在 `K[[x,t]]` 中 `𝒩(x, t/(1−t)) = (1−t)·(1+t·F)`，
  即 `1 − t + t(1−t)F`（`subst_NKser'`）；`one_add_X_mul_FK_eq_subst` 是报告的原式
  `1 + tF = 𝒩(x, t/(1−t))/(1−t)`（`1/(1−t)` 写成 `mk 1 = 1 + t + t² + ⋯`）。对任何域 `K` 成立；
  `K = ℂ` 的情形是 `subst_NKser_complex`。
* `no_x_ODE_NK`（**T3.7(3)**，ODE 部分）：不存在不全为 0 的 `p_0, …, p_r ∈ ℂ[x,y]` 使
  `Σ_j p_j·∂_x^j 𝒩 = 0`。
* `not_isDFinite_NKser`（**T3.7(3)**）：对任何域 `K` 与环同态 `σ : K →+* ℂ`（即 `K ⊆ ℂ`），`𝒩` 在 `K`
  上不是 D-finite；`not_isDFinite_NK` 是 `K = ℂ` 的情形。

## 证明路线（`notes/c3b.md` §7.1 证明一）

* T3.5(1)：逐 `x^k·t^m` 系数验证。`(t/(1−t))^q = (1−t)·Σ_n C(n,q)·t^n`（`tFrac_pow`），所以
  `𝒩(x, t/(1−t))` 的 `x^k·t^m` 系数是 `Σ_q N(k,q)·(C(m,q) − C(m−1,q)) = V_k(m) − V_k(m−1)`
  （`m = 0` 时是 `V_k(0)`），其中 `V_k(m) = Σ_q N(k,q)·C(m,q)` 即 `Binomial.lean` 的 `Vn`；
  另一方面由 `U_eq_Vn`（`U_k(m) = V_k(m+1)`，T1.4(1)）与 `V_k(0) = N(k,0) = [k = 0]`，
  `1 + tF = Σ_{k,m} V_k(m)·x^k·t^m`（`one_add_X_mul_FK_eq_Vn`），乘 `1 − t` 得到同样的系数。
* 设 `Σ_j p_j·∂_x^j 𝒩 = 0`，`p_j ∈ ℂ[x,y]` 不全为 0。作用 `substY`：
  `p_j ↦ p̂_j = p_j(x, t/(1−t)) ∈ ℂ[x][[t]]`（`substY_polyToPS2`），`∂_x^j 𝒩 ↦ ∂_x^j 𝒩̂`，
  `𝒩̂ = 1 − t + t(1−t)F`，而 `j ≥ 1` 时 `∂_x^j 𝒩̂ = t(1−t)·∂_x^j F`（`dXK_iter_substY_NKser`）。
  于是 `Σ_j c_j·∂_x^j F = ρ`，`c_j = t(1−t)·p̂_j`，`ρ = −(1−t)·p̂_0`。`p ≠ 0 ⇒ p̂ ≠ 0`
  （`polySubst_ne_zero`）。
* `ρ = 0`：与 `no_x_ODE` 矛盾。`ρ ≠ 0`：作用 `ρ∂_x − ρ_x`，得到齐次方程 `Σ_j d_j·∂_x^j F = 0`，
  `d_j = ρ·∂_x c_j − ∂_x ρ·c_j + ρ·c_{j−1}`；取 `c_J ≠ 0` 的最大 `J`，`d_{J+1} = ρ·c_J ≠ 0`
  （`ℂ[x][[t]]` 是整环），仍与 `no_x_ODE` 矛盾（`no_x_ODE_inhom`）。
* 一般的 `K`：与 `not_isDFinite_FK` 相同，引理 D1（`exists_x_ODE_of_isDFinite`）给出 `K[x,y]` 系数的
  ODE，用 `σ` 逐系数映到 `ℂ`（`mapPS2`）。

与报告证明写法的差别（都只是细节上的等价处理，不改变任何陈述）：
* 报告乘 `(1−t)^E` 把 `p̂_j` 化成 `ℂ[x,t]` 中的多项式 `p̃_j`，再引用定理 1（系数取 `ℂ[x,t]`）。这里不清
  分母：`NonDFinite.lean` 的 `no_x_ODE` 已允许系数取 `ℂ[x][[t]]`（报告 T3.7(1) 也写了「甚至
  `C[x][[t]]`」），`p̂_j ∈ ℂ[x][[t]]` 可以直接用。
* `p̂ ≠ 0` 用「最低次项」论证代替报告的「基变换」论证：`p` 的最低 `y` 次项 `y^{e0}` 给出
  `[t^{e0}]p̂ = [y^{e0}]p ≠ 0`（因为 `(t/(1−t))^e = t^e + ⋯`）。`(ρ∂_x − ρ_x)𝓛 ≠ 0` 用最高阶系数
  `ρ·c_J ≠ 0`，与报告的「整环」是同一个理由。

## 没有形式化的部分

* `K[[x]][[y]] ≅ K[[x,y]]`（标准事实，与 `DFinite.lean` 相同，不形式化）。
* T3.7(3) 的后半「`N` 没有只依赖 `k` 的象限递推」（不在本文件）。
* T3.5(1) 的另一等价形式 `𝒩(x,y) = 1/(1+y) + y·F(x, y/(1+y))/(1+y)²`，以及 T3.5(2)(3)。
-/

open Finset

namespace A207123

/-! ### 定义 -/

section Defs

variable (K : Type*) [Field K]

/-- `𝒩(x,y) = Σ_{k,q} N(k,q)·x^k·y^q ∈ K[[x,y]]`（报告 T3.5 的 `𝒩`，`notes/c3b.md` 的 `Φ`），
写成 `K[[x]][[y]]`：外层变量 `y`、内层变量 `x`，`[y^q]𝒩 = Ψ_q(x) = Σ_k N(k,q)·x^k`。 -/
noncomputable def NKser : PS2 K := PowerSeries.mk fun q => PowerSeries.mk fun k => (N k q : K)

/-- 辅助引理（T3.7(3)，检查定义）：`𝒩` 的 `x^k·y^q` 系数是 `N(k,q)`。 -/
theorem coeff_NKser (k q : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff q (NKser K)) = (N k q : K) := by
  simp [NKser]

end Defs

/-! ### `t/(1−t)` 及其幂 -/

section TFrac

variable (R : Type*) [CommRing R]

/-- `t/(1−t) = t + t² + t³ + ⋯ ∈ R[[t]]`（写成 `t·(1 + t + t² + ⋯)`）。 -/
noncomputable def tFrac : PowerSeries R := PowerSeries.X * PowerSeries.mk 1

/-- 辅助引理（T3.5(1)，检查定义）：`t/(1−t)` 的系数是 `0, 1, 1, 1, …`。 -/
theorem coeff_tFrac (n : ℕ) : PowerSeries.coeff n (tFrac R) = if n = 0 then 0 else 1 := by
  rcases n with _ | n
  · simp [tFrac]
  · simp [tFrac, PowerSeries.coeff_succ_X_mul]

/-- 辅助引理（T3.5(1)，检查定义）：`tFrac·(1 − t) = t`，即 `tFrac` 确实是 `t/(1−t)`。 -/
theorem tFrac_mul_one_sub_X : tFrac R * (1 - PowerSeries.X) = PowerSeries.X := by
  rw [tFrac, mul_assoc, PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]

/-- 辅助引理（T3.5(1)）：`t/(1−t)` 的常数项为 0。 -/
theorem constantCoeff_tFrac : PowerSeries.constantCoeff (tFrac R) = 0 := by
  simp [tFrac]

/-- 辅助引理（T3.5(1)）：`t/(1−t)` 可以代入幂级数（常数项为 0）。 -/
theorem hasSubst_tFrac : PowerSeries.HasSubst (tFrac R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_tFrac R)

/-- 辅助引理（T3.5(1)）：`(t/(1−t))^q = (1 − t)·Σ_n C(n,q)·t^n`
（等价于 `Σ_n C(n,q)·t^n = t^q/(1−t)^{q+1}`，`notes/c3b.md` §1.3）。 -/
theorem tFrac_pow (q : ℕ) :
    tFrac R ^ q = (1 - PowerSeries.X) * PowerSeries.mk fun n => (n.choose q : R) := by
  induction q with
  | zero =>
    have h : (PowerSeries.mk fun n => ((n.choose 0 : ℕ) : R)) = PowerSeries.mk 1 := by
      refine PowerSeries.ext fun n => ?_
      simp
    rw [pow_zero, h, mul_comm, PowerSeries.mk_one_mul_one_sub_eq_one]
  | succ q ih =>
    have h1 : tFrac R ^ (q + 1) = PowerSeries.X * PowerSeries.mk fun n => (n.choose q : R) := by
      rw [pow_succ, ih, tFrac]
      calc (1 - PowerSeries.X) * PowerSeries.mk (fun n => (n.choose q : R)) *
            (PowerSeries.X * PowerSeries.mk 1)
          = PowerSeries.X * PowerSeries.mk (fun n => (n.choose q : R)) *
            (PowerSeries.mk 1 * (1 - PowerSeries.X)) := by ring
        _ = PowerSeries.X * PowerSeries.mk fun n => (n.choose q : R) := by
          rw [PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]
    rw [h1]
    refine PowerSeries.ext fun n => ?_
    rcases n with _ | n
    · simp [sub_mul]
    · rw [PowerSeries.coeff_succ_X_mul, sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul]
      simp only [PowerSeries.coeff_mk]
      rw [Nat.choose_succ_succ, Nat.cast_add]
      ring

/-- 辅助引理（T3.5(1)）：`[t^0](t/(1−t))^q = C(0,q)`（`q = 0` 时为 1，否则为 0）。 -/
theorem coeff_zero_tFrac_pow (q : ℕ) :
    PowerSeries.coeff 0 (tFrac R ^ q) = ((Nat.choose 0 q : ℕ) : R) := by
  rw [tFrac_pow, sub_mul, one_mul, map_sub, PowerSeries.coeff_zero_X_mul, sub_zero,
    PowerSeries.coeff_mk]

/-- 辅助引理（T3.5(1)）：`[t^{n+1}](t/(1−t))^q = C(n+1,q) − C(n,q)`。 -/
theorem coeff_succ_tFrac_pow (q n : ℕ) :
    PowerSeries.coeff (n + 1) (tFrac R ^ q) = ((n + 1).choose q : R) - (n.choose q : R) := by
  rw [tFrac_pow, sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]

/-- 辅助引理（T3.7(3)）：`m < q` 时 `[t^m](t/(1−t))^q = 0`。 -/
theorem coeff_tFrac_pow_of_lt {q m : ℕ} (h : m < q) : PowerSeries.coeff m (tFrac R ^ q) = 0 := by
  rcases m with _ | m
  · rw [coeff_zero_tFrac_pow, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
  · rw [coeff_succ_tFrac_pow, Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega),
      Nat.cast_zero, sub_zero]

/-- 辅助引理（T3.7(3)）：`[t^q](t/(1−t))^q = 1`。 -/
theorem coeff_self_tFrac_pow (q : ℕ) : PowerSeries.coeff q (tFrac R ^ q) = 1 := by
  rcases q with _ | q
  · rw [coeff_zero_tFrac_pow, Nat.choose_self, Nat.cast_one]
  · rw [coeff_succ_tFrac_pow, Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_one,
      Nat.cast_zero, sub_zero]

/-- 辅助引理（T3.5(1)）：`[t^m] f(t/(1−t)) = Σ_{q ≤ m} [y^q]f·[t^m](t/(1−t))^q`
（Mathlib 的系数公式是 `finsum`，这里化成有限和）。 -/
theorem coeff_subst_tFrac (f : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (f.subst (tFrac R)) =
      ∑ q ∈ range (m + 1), PowerSeries.coeff q f * PowerSeries.coeff m (tFrac R ^ q) := by
  rw [PowerSeries.coeff_subst' (hasSubst_tFrac R),
    finsum_eq_sum_of_support_subset _ (s := range (m + 1))]
  · simp only [smul_eq_mul]
  · intro q hq
    rw [Function.mem_support] at hq
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hq (by rw [coeff_tFrac_pow_of_lt R (by omega), smul_zero])

/-- 辅助引理（T3.5(1)）：逐系数作用环同态 `f` 把 `t/(1−t)` 映成 `t/(1−t)`。 -/
theorem map_tFrac {S : Type*} [CommRing S] (f : R →+* S) :
    PowerSeries.map f (tFrac R) = tFrac S := by
  rw [tFrac, tFrac, map_mul, PowerSeries.map_X]
  congr 1
  refine PowerSeries.ext fun n => ?_
  simp

end TFrac

/-! ### 代换 `y ↦ t/(1−t)` 与 T3.5(1) -/

section Subst

variable (K : Type*) [Field K]

/-- 代换 `y ↦ t/(1−t)`：`K[[x]][[y]] → K[[x]][[t]]`，即 Mathlib 的 `PowerSeries.subst (t/(1−t))`
（系数环取 `K[[x]]`，见 `substY_apply`）。它是环同态，对 `x` 不动（`substY_C`）。 -/
noncomputable def substY : PS2 K →+* PS2 K where
  toFun f := f.subst (tFrac (PowerSeries K))
  map_one' := by
    refine PowerSeries.ext fun m => ?_
    rw [coeff_subst_tFrac, Finset.sum_eq_single 0]
    · simp [PowerSeries.coeff_one]
    · intro q _ hq
      simp [PowerSeries.coeff_one, hq]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
  map_mul' f g := PowerSeries.subst_mul (hasSubst_tFrac (PowerSeries K)) f g
  map_zero' := by
    refine PowerSeries.ext fun m => ?_
    rw [coeff_subst_tFrac]
    simp
  map_add' f g := PowerSeries.subst_add (hasSubst_tFrac (PowerSeries K)) f g

/-- 辅助引理（T3.7(3)）：`substY` 就是 Mathlib 的代换 `f ↦ f(t/(1−t))`。 -/
theorem substY_apply (f : PS2 K) : substY K f = f.subst (tFrac (PowerSeries K)) := rfl

/-- 辅助引理（T3.5(1)）：`[t^m] f(x, t/(1−t)) = Σ_{q ≤ m} [y^q]f·[t^m](t/(1−t))^q`。 -/
theorem coeff_substY (f : PS2 K) (m : ℕ) :
    PowerSeries.coeff m (substY K f) =
      ∑ q ∈ range (m + 1), PowerSeries.coeff q f *
        PowerSeries.coeff m (tFrac (PowerSeries K) ^ q) := by
  rw [substY_apply]
  exact coeff_subst_tFrac (PowerSeries K) f m

/-- 辅助引理（T3.7(3)）：`(t/(1−t))^q` 的 `t^m` 系数是 `x` 的常数。 -/
theorem coeff_tFrac_pow_eq_C (q m : ℕ) :
    PowerSeries.coeff m (tFrac (PowerSeries K) ^ q) =
      PowerSeries.C (PowerSeries.coeff m (tFrac K ^ q)) := by
  rw [← map_tFrac K PowerSeries.C, ← map_pow, PowerSeries.coeff_map]

/-- 辅助引理（T3.7(3)，检查定义）：`substY` 把 `y` 映成 `t/(1−t)`。 -/
theorem substY_X : substY K PowerSeries.X = tFrac (PowerSeries K) := by
  rw [substY_apply, PowerSeries.subst_X (hasSubst_tFrac (PowerSeries K))]

/-- 辅助引理（T3.7(3)，检查定义）：`substY` 固定 `K[[x]]`（`y` 方向的常数）。 -/
theorem substY_C (r : PowerSeries K) : substY K (PowerSeries.C r) = PowerSeries.C r := by
  rw [substY_apply, PowerSeries.subst_C]
  rfl

/-- 辅助引理（T3.7(3)）：代换 `y ↦ t/(1−t)` 与 `∂_x` 交换（`(t/(1−t))^q` 的系数是 `x` 的常数）。 -/
theorem substY_dXK (f : PS2 K) : substY K (dXK K f) = dXK K (substY K f) := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_substY]
  simp only [dXK, PowerSeries.coeff_mk]
  rw [coeff_substY, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Derivation.leibniz, coeff_tFrac_pow_eq_C, PowerSeries.derivative_C, smul_zero, zero_add,
    smul_eq_mul, mul_comm]

/-- 辅助引理（T3.7(3)）：代换与 `∂_x^j` 交换。 -/
theorem substY_dXK_iter (j : ℕ) (f : PS2 K) :
    substY K ((dXK K)^[j] f) = (dXK K)^[j] (substY K f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, substY_dXK]

/-- 辅助引理（T3.5(1)）：`1 + t·F = Σ_{k,m} V_k(m)·x^k·t^m`，`V_k(m) = Σ_q N(k,q)·C(m,q)`
（`Vn`；由二项式基 `U_k(m) = V_k(m+1)`，且 `V_k(0) = N(k,0) = [k = 0]`）。 -/
theorem one_add_X_mul_FK_eq_Vn :
    (1 : PS2 K) + PowerSeries.X * FK K =
      PowerSeries.mk fun n => PowerSeries.mk fun k => (Vn k n : K) := by
  refine PowerSeries.ext fun n => PowerSeries.ext fun k => ?_
  rcases n with _ | n
  · rcases k with _ | k
    · simp [Vn, PowerSeries.coeff_one, N_init.1]
    · simp [Vn, PowerSeries.coeff_one, N_succ_zero]
  · simp [FK, PowerSeries.coeff_one, U_eq_Vn]

/-- **T3.5(1)**（代换关系，用 `substY` 写）：`𝒩(x, t/(1−t)) = (1 − t)·(1 + t·F(x,t))`。
这里 `PowerSeries.X` 是外层变量 `t`，`FK K = F = Σ_{k,m} U_k(m)·x^k·t^m`。 -/
theorem substY_NKser :
    substY K (NKser K) = (1 - PowerSeries.X) * (1 + PowerSeries.X * FK K) := by
  rw [one_add_X_mul_FK_eq_Vn]
  refine PowerSeries.ext fun m => PowerSeries.ext fun k => ?_
  rw [coeff_substY, map_sum]
  simp only [coeff_tFrac_pow_eq_C, PowerSeries.coeff_mul_C, NKser, PowerSeries.coeff_mk]
  rcases m with _ | n
  · rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_zero_X_mul, sub_zero, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, Vn]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coeff_zero_tFrac_pow]
  · rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, map_sub]
    simp only [PowerSeries.coeff_mk, Vn]
    push_cast
    have hext : ∑ q ∈ range (n + 1), (N k q : K) * (n.choose q : K) =
        ∑ q ∈ range (n + 1 + 1), (N k q : K) * (n.choose q : K) := by
      rw [Finset.sum_range_succ _ (n + 1), Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n),
        Nat.cast_zero, mul_zero, add_zero]
    rw [hext, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coeff_succ_tFrac_pow]
    ring

/-- **T3.5(1)**（代换关系，用 Mathlib 的 `PowerSeries.subst` 写）：在 `K[[x,t]]` 中，把 `𝒩(x,y)` 的
`y` 代换成 `t/(1−t)` 得到 `(1 − t)·(1 + t·F(x,t))`。 -/
theorem subst_NKser :
    ((NKser K).subst (tFrac (PowerSeries K)) : PS2 K) =
      (1 - PowerSeries.X) * (1 + PowerSeries.X * FK K) :=
  substY_NKser K

/-- **T3.5(1)**（展开形式，`notes/c3b.md` §7.1 的 `Φ̂`）：`𝒩(x, t/(1−t)) = 1 − t + t(1−t)·F(x,t)`。 -/
theorem subst_NKser' :
    ((NKser K).subst (tFrac (PowerSeries K)) : PS2 K) =
      1 - PowerSeries.X + PowerSeries.X * (1 - PowerSeries.X) * FK K := by
  rw [subst_NKser]
  ring

/-- **T3.5(1)**（报告原式）：`1 + t·F(x,t) = 𝒩(x, t/(1−t))/(1−t)`，其中 `1/(1−t)` 是
`mk 1 = 1 + t + t² + ⋯`（`mk 1·(1 − t) = 1`）。 -/
theorem one_add_X_mul_FK_eq_subst :
    (1 : PS2 K) + PowerSeries.X * FK K =
      PowerSeries.mk 1 * ((NKser K).subst (tFrac (PowerSeries K)) : PS2 K) := by
  rw [subst_NKser, ← mul_assoc, PowerSeries.mk_one_mul_one_sub_eq_one, one_mul]

/-- **T3.5(1)**（`K = ℂ`，即在 `ℂ[[x,t]]` 中）：`𝒩(x, t/(1−t)) = (1 − t)·(1 + t·F(x,t))`。 -/
theorem subst_NKser_complex :
    ((NKser ℂ).subst (tFrac (PowerSeries ℂ)) : PS2 ℂ) =
      (1 - PowerSeries.X) * (1 + PowerSeries.X * FK ℂ) :=
  subst_NKser ℂ

end Subst

/-! ### `∂_x` 的运算律 -/

section DXK

variable (K : Type*) [Field K]

/-- 辅助引理（T3.7(3)）：`∂_x` 可加。 -/
theorem dXK_add (f g : PS2 K) : dXK K (f + g) = dXK K f + dXK K g := by
  refine PowerSeries.ext fun m => ?_
  simp [dXK]

/-- 辅助引理（T3.7(3)）：`∂_x (f − g) = ∂_x f − ∂_x g`。 -/
theorem dXK_sub (f g : PS2 K) : dXK K (f - g) = dXK K f - dXK K g := by
  refine PowerSeries.ext fun m => ?_
  simp [dXK]

/-- 辅助引理（T3.7(3)）：`∂_x` 与有限和交换。 -/
theorem dXK_sum {ι : Type*} (s : Finset ι) (f : ι → PS2 K) :
    dXK K (∑ i ∈ s, f i) = ∑ i ∈ s, dXK K (f i) := by
  refine PowerSeries.ext fun m => ?_
  simp [dXK, map_sum]

/-- 辅助引理（T3.7(3)）：`∂_x` 的 Leibniz 律。 -/
theorem dXK_mul (f g : PS2 K) : dXK K (f * g) = dXK K f * g + f * dXK K g := by
  refine PowerSeries.ext fun m => ?_
  simp only [dXK, PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_add, map_sum,
    Derivation.leibniz, smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ij _ => by ring

/-- 辅助引理（T3.7(3)）：`∂_x t = 0`（`t` 是外层变量）。 -/
theorem dXK_X : dXK K PowerSeries.X = 0 := by
  refine PowerSeries.ext fun m => ?_
  by_cases h : m = 1 <;> simp [dXK, PowerSeries.coeff_X, h]

/-- 辅助引理（T3.7(3)）：`∂_x (1 − t) = 0`。 -/
theorem dXK_one_sub_X : dXK K (1 - PowerSeries.X) = 0 := by
  rw [dXK_sub, dXK_one, dXK_X, sub_zero]

/-- 辅助引理（T3.7(3)）：`∂_x u = 0` 时 `∂_x (u·f) = u·∂_x f`。 -/
theorem dXK_mul_of_dXK_eq_zero {u : PS2 K} (hu : dXK K u = 0) (f : PS2 K) :
    dXK K (u * f) = u * dXK K f := by
  rw [dXK_mul, hu, zero_mul, zero_add]

/-- 辅助引理（T3.7(3)）：`∂_x u = 0` 时 `∂_x^j (u·f) = u·∂_x^j f`。 -/
theorem dXK_iter_mul_of_dXK_eq_zero {u : PS2 K} (hu : dXK K u = 0) (j : ℕ) (f : PS2 K) :
    (dXK K)^[j] (u * f) = u * (dXK K)^[j] f := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dXK_mul_of_dXK_eq_zero K hu, ih]

/-- 辅助引理（T3.7(3)）：`𝒩̂ = (1 − t)(1 + tF)` 满足 `∂_x^j 𝒩̂ = t(1−t)·∂_x^j F + [j = 0]·(1 − t)`
（即 `j ≥ 1` 时 `∂_x^j 𝒩̂ = t(1−t)·∂_x^j F`）。 -/
theorem dXK_iter_substY_NKser (j : ℕ) :
    (dXK K)^[j] ((1 - PowerSeries.X) * (1 + PowerSeries.X * FK K)) =
      PowerSeries.X * (1 - PowerSeries.X) * (dXK K)^[j] (FK K) +
        (if j = 0 then 1 - PowerSeries.X else 0) := by
  have hT : dXK K (PowerSeries.X * (1 - PowerSeries.X)) = 0 := by
    rw [dXK_mul, dXK_X, dXK_one_sub_X, zero_mul, mul_zero, add_zero]
  rcases j with _ | j
  · simp only [Function.iterate_zero, id_eq, ↓reduceIte]
    ring
  · have h1 : dXK K ((1 - PowerSeries.X) * (1 + PowerSeries.X * FK K)) =
        PowerSeries.X * (1 - PowerSeries.X) * dXK K (FK K) := by
      rw [show (1 - PowerSeries.X) * (1 + PowerSeries.X * FK K) =
          (1 - PowerSeries.X) + PowerSeries.X * (1 - PowerSeries.X) * FK K by ring,
        dXK_add, dXK_one_sub_X, zero_add, dXK_mul_of_dXK_eq_zero K hT]
    rw [Function.iterate_succ_apply, h1, dXK_iter_mul_of_dXK_eq_zero K hT,
      ← Function.iterate_succ_apply]
    simp

end DXK

/-! ### 多项式在代换下的像 -/

section PolySubst

/-- 辅助定义（T3.7(3)）：`p(x,y) ↦ p̂ = p(x, t/(1−t)) ∈ ℂ[x][[t]]`（`p` 写成 `y` 的多项式、系数为
`x` 的多项式，与 `polyToPS2` 的约定一致）。 -/
noncomputable def polySubst (p : Polynomial (Polynomial ℂ)) : PowerSeries (Polynomial ℂ) :=
  Polynomial.eval₂ PowerSeries.C (tFrac (Polynomial ℂ)) p

/-- 辅助引理（T3.7(3)）：`p ≠ 0 ⇒ p(x, t/(1−t)) ≠ 0`。证明：`p` 的最低 `y` 次项 `y^{e0}` 给出
`[t^{e0}]p̂ = [y^{e0}]p ≠ 0`，因为 `(t/(1−t))^e = t^e + ⋯`。 -/
theorem polySubst_ne_zero {p : Polynomial (Polynomial ℂ)} (hp : p ≠ 0) : polySubst p ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff p.natTrailingDegree) h
  rw [polySubst, Polynomial.eval₂_eq_sum_range, map_sum, map_zero,
    Finset.sum_eq_single p.natTrailingDegree] at hc
  · rw [PowerSeries.coeff_C_mul, coeff_self_tFrac_pow, mul_one] at hc
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp hc
  · intro e _ hne
    rw [PowerSeries.coeff_C_mul]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, zero_mul]
    · rw [coeff_tFrac_pow_of_lt _ hgt, mul_zero]
  · intro h'
    exact absurd (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree p))) h'

/-- 辅助定义（T3.7(3)）：系数嵌入 `ℂ[x][[t]] → ℂ[[x,t]]` 作为环同态（就是 `embedC`）。 -/
noncomputable def embedCHom : PowerSeries (Polynomial ℂ) →+* PS2 ℂ :=
  PowerSeries.map (Polynomial.coeToPowerSeries.ringHom (R := ℂ))

/-- 辅助引理（T3.7(3)）：`embedC` 就是 `embedCHom`（定义上相等）。 -/
theorem embedC_eq_embedCHom (c : PowerSeries (Polynomial ℂ)) : embedC c = embedCHom c := rfl

/-- 辅助引理（T3.7(3)）：代换把多项式 `p(x,y)` 的像映成 `p(x, t/(1−t)) ∈ ℂ[x][[t]]` 的像。 -/
theorem substY_polyToPS2 (p : Polynomial (Polynomial ℂ)) :
    substY ℂ (polyToPS2 ℂ p) = embedC (polySubst p) := by
  have h : (substY ℂ).comp (polyToPS2 ℂ) =
      embedCHom.comp (Polynomial.eval₂RingHom PowerSeries.C (tFrac (Polynomial ℂ))) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [polyToPS2, embedCHom, substY_C]
    · simp [polyToPS2, embedCHom, substY_X, map_tFrac]
  exact RingHom.congr_fun h p

end PolySubst

/-! ### 非齐次方程 `𝓛F = ρ` 无解 -/

section Inhom

/-- 辅助定义（T3.7(3)）：`ℂ[x][[t]]` 上的 `∂_x`（对每个 `t^n` 系数求 `x` 的形式导数）。 -/
noncomputable def dPX (c : PowerSeries (Polynomial ℂ)) : PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk fun n => Polynomial.derivative (PowerSeries.coeff n c)

/-- 辅助引理（T3.7(3)）：`∂_x 0 = 0`（`ℂ[x][[t]]` 上）。 -/
theorem dPX_zero : dPX 0 = 0 := by
  refine PowerSeries.ext fun n => ?_
  simp [dPX]

/-- 辅助引理（T3.7(3)）：`∂_x` 与系数嵌入 `ℂ[x][[t]] → ℂ[[x,t]]` 交换。 -/
theorem dXK_embedC (c : PowerSeries (Polynomial ℂ)) : dXK ℂ (embedC c) = embedC (dPX c) := by
  refine PowerSeries.ext fun n => ?_
  simp only [dXK, dPX, PowerSeries.coeff_mk, coeff_embedC, PowerSeries.derivative_coe]

/-- 辅助引理（T3.7(3)，`ρ ≠ 0` 的情形）：设 `c_j ∈ ℂ[x][[t]]`（`j > r` 时为 0）不全为 0、
`0 ≠ ρ ∈ ℂ[x][[t]]`，则 `Σ_{j ≤ r} c_j·∂_x^j F = ρ` 不成立。证明：作用 `ρ∂_x − ρ_x` 得到齐次方程
`Σ_{j ≤ r+1} d_j·∂_x^j F = 0`，`d_j = ρ·∂_x c_j − ∂_x ρ·c_j + ρ·c_{j−1}`；取 `c_J ≠ 0` 的最大 `J`，
`d_{J+1} = ρ·c_J ≠ 0`（整环），与 `no_x_ODE` 矛盾。 -/
theorem no_x_ODE_inhom_aux (r : ℕ) (c : ℕ → PowerSeries (Polynomial ℂ))
    (ρ : PowerSeries (Polynomial ℂ)) (hρ : ρ ≠ 0) (hc0 : ∀ j, r < j → c j = 0)
    (hc : ∃ j ≤ r, c j ≠ 0)
    (h : ∑ j ∈ range (r + 1), embedC (c j) * (dXK ℂ)^[j] (FK ℂ) = embedC ρ) : False := by
  classical
  -- `J`：最大的 `j ≤ r` 使 `c_j ≠ 0`
  set J := Nat.findGreatest (fun j => c j ≠ 0) r with hJ
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hcJ : c J ≠ 0 := by
    obtain ⟨j, hj, hcj⟩ := hc
    exact Nat.findGreatest_spec (P := fun j => c j ≠ 0) hj hcj
  have hcJ1 : c (J + 1) = 0 := by
    by_cases h1 : J + 1 ≤ r
    · exact not_not.mp (Nat.findGreatest_is_greatest (Nat.lt_succ_self J) h1)
    · exact hc0 _ (by omega)
  -- 齐次化后的系数：`(ρ∂_x − ρ_x)·Σ_j c_j ∂_x^j = Σ_j d_j ∂_x^j`
  set d : ℕ → PowerSeries (Polynomial ℂ) := fun j =>
    ρ * dPX (c j) - dPX ρ * c j + (if j = 0 then 0 else ρ * c (j - 1)) with hd
  have hdJ : d (J + 1) ≠ 0 := by
    simp only [hd, hcJ1, dPX_zero, mul_zero, sub_zero, add_tsub_cancel_right,
      Nat.add_one_ne_zero, ↓reduceIte, zero_add]
    exact mul_ne_zero hρ hcJ
  apply no_x_ODE (r + 1) d ⟨J + 1, by omega, hdJ⟩
  rw [← dXK_complex_eq_dX, ← FK_complex_eq_Fxt]
  have hDE := congrArg (dXK ℂ) h
  rw [dXK_sum, dXK_embedC] at hDE
  simp only [dXK_mul, dXK_embedC] at hDE
  have key : ∑ j ∈ range (r + 1 + 1), embedC (d j) * (dXK ℂ)^[j] (FK ℂ) =
      embedC ρ * ∑ j ∈ range (r + 1), (embedC (dPX (c j)) * (dXK ℂ)^[j] (FK ℂ) +
          embedC (c j) * dXK ℂ ((dXK ℂ)^[j] (FK ℂ))) -
        embedC (dPX ρ) * ∑ j ∈ range (r + 1), embedC (c j) * (dXK ℂ)^[j] (FK ℂ) := by
    have hsplit : ∀ j, embedC (d j) * (dXK ℂ)^[j] (FK ℂ) =
        embedC (ρ * dPX (c j) - dPX ρ * c j) * (dXK ℂ)^[j] (FK ℂ) +
          (if j = 0 then 0 else embedC (ρ * c (j - 1)) * (dXK ℂ)^[j] (FK ℂ)) := by
      intro j
      simp only [hd, embedC_eq_embedCHom]
      split_ifs <;> simp only [map_add, add_zero, add_mul]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
      Finset.sum_range_succ (fun j => embedC (ρ * dPX (c j) - dPX ρ * c j) *
        (dXK ℂ)^[j] (FK ℂ)) (r + 1),
      Finset.sum_range_succ' (fun j => if j = 0 then 0 else
        embedC (ρ * c (j - 1)) * (dXK ℂ)^[j] (FK ℂ)) (r + 1),
      hc0 (r + 1) (by omega), dPX_zero]
    simp only [mul_zero, sub_zero, embedC_eq_embedCHom, map_zero, zero_mul, add_zero,
      Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.iterate_succ_apply']
    simp only [map_sub, map_mul]
    ring
  rw [key, hDE, h]
  ring

/-- 辅助引理（T3.7(3)）：`F` 不满足任何非平凡的非齐次 `x` 方向 ODE：若 `c_0, …, c_r ∈ ℂ[x][[t]]`
不全为 0，则对任何 `ρ ∈ ℂ[x][[t]]`，`Σ_j c_j·∂_x^j F ≠ ρ`（报告 §7.1 把右端记作 `r`，这里记作 `ρ`：
`ρ = 0` 时与定理 1（`no_x_ODE`）矛盾，`ρ ≠ 0` 时用 `ρ∂_x − ρ_x` 齐次化，仍矛盾）。 -/
theorem no_x_ODE_inhom (r : ℕ) (c : ℕ → PowerSeries (Polynomial ℂ))
    (ρ : PowerSeries (Polynomial ℂ)) (hc : ∃ j ≤ r, c j ≠ 0) :
    ∑ j ∈ range (r + 1), embedC (c j) * dX^[j] Fxt ≠ embedC ρ := by
  intro h
  by_cases hρ : ρ = 0
  · apply no_x_ODE r c hc
    rw [h, hρ, embedC_eq_embedCHom, map_zero]
  · classical
    set c' : ℕ → PowerSeries (Polynomial ℂ) := fun j => if j ≤ r then c j else 0 with hc'
    refine no_x_ODE_inhom_aux r c' ρ hρ ?_ ?_ ?_
    · intro j hj
      simp only [hc', show ¬ j ≤ r by omega, ↓reduceIte]
    · obtain ⟨j, hj, hcj⟩ := hc
      exact ⟨j, hj, by simpa only [hc', hj, ↓reduceIte] using hcj⟩
    · rw [← h, dXK_complex_eq_dX, FK_complex_eq_Fxt]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hc', Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), ↓reduceIte]

end Inhom

/-! ### 主定理 -/

section Main

/-- **T3.7(3)**（ODE 部分，`notes/c3b.md` §7.1 证明一）：不存在不全为 0 的 `p_0, …, p_r ∈ ℂ[x,y]`
（写成 `y` 的多项式、系数为 `x` 的多项式）使 `Σ_j p_j·∂_x^j 𝒩 = 0`。证明：代换 `y ↦ t/(1−t)` 把它变成
`F` 的非齐次 `x` 方向 ODE `Σ_j t(1−t)p̂_j·∂_x^j F = −(1−t)p̂_0`，与 `no_x_ODE_inhom` 矛盾。 -/
theorem no_x_ODE_NK (r : ℕ) (p : ℕ → Polynomial (Polynomial ℂ)) (hp : ∃ j ≤ r, p j ≠ 0) :
    ∑ j ∈ range (r + 1), polyToPS2 ℂ (p j) * (dXK ℂ)^[j] (NKser ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg (substY ℂ) h
  rw [map_sum, map_zero] at h1
  simp only [map_mul, substY_polyToPS2, substY_dXK_iter, substY_NKser,
    dXK_iter_substY_NKser] at h1
  have hX2 : (PowerSeries.X * (1 - PowerSeries.X) : PowerSeries (Polynomial ℂ)) ≠ 0 := by
    refine mul_ne_zero PowerSeries.X_ne_zero fun h0 => ?_
    have := congrArg (PowerSeries.coeff 0) h0
    simp at this
  refine no_x_ODE_inhom r (fun j => PowerSeries.X * (1 - PowerSeries.X) * polySubst (p j))
    (-((1 - PowerSeries.X) * polySubst (p 0))) ?_ ?_
  · obtain ⟨j, hj, hpj⟩ := hp
    exact ⟨j, hj, mul_ne_zero hX2 (polySubst_ne_zero hpj)⟩
  · have h2 : ∀ j, embedC (polySubst (p j)) *
        (PowerSeries.X * (1 - PowerSeries.X) * (dXK ℂ)^[j] (FK ℂ) +
          (if j = 0 then 1 - PowerSeries.X else 0)) =
        embedC (PowerSeries.X * (1 - PowerSeries.X) * polySubst (p j)) * (dXK ℂ)^[j] (FK ℂ) +
          (if j = 0 then embedC (polySubst (p 0)) * (1 - PowerSeries.X) else 0) := by
      intro j
      simp only [embedC_eq_embedCHom, map_mul, map_sub, map_one, embedCHom, PowerSeries.map_X]
      split_ifs with hj
      · subst hj
        ring
      · ring
    rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_add_distrib, Finset.sum_ite_eq'] at h1
    simp only [Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte] at h1
    rw [dXK_complex_eq_dX, FK_complex_eq_Fxt] at h1
    rw [eq_neg_of_add_eq_zero_left h1]
    simp only [embedC_eq_embedCHom, map_neg, map_mul, map_sub, map_one, embedCHom,
      PowerSeries.map_X]
    ring

/-- 辅助引理（T3.7(3)）：换系数 `σ : K →+* L` 把 `K` 上的 `𝒩` 映成 `L` 上的 `𝒩`。 -/
theorem mapPS2_NKser {K : Type*} [Field K] {L : Type*} [Field L] (σ : K →+* L) :
    mapPS2 σ (NKser K) = NKser L := by
  ext m k
  simp [mapPS2, NKser]

/-- **T3.7(3)**（前半「`𝒩` 同样不是 D-finite」）：对任何域 `K` 与环同态 `σ : K →+* ℂ`（即 `K ⊆ ℂ`；
域上的环同态自动单射），`𝒩 = Σ_{k,q} N(k,q)·x^k·y^q ∈ K[[x,y]]` 不是 D-finite（Lipshitz 1989
Def. 2.1，`IsDFinite`）。证明：若是，引理 D1（`exists_x_ODE_of_isDFinite`）给出 `K[x,y]` 系数、不全为 0
的 `Σ_j p_j·∂_x^j 𝒩 = 0`；用 `σ` 把系数映到 `ℂ`，与 `no_x_ODE_NK` 矛盾。 -/
theorem not_isDFinite_NKser {K : Type*} [Field K] (σ : K →+* ℂ) : ¬ IsDFinite K (NKser K) := by
  intro hD
  obtain ⟨r, p, ⟨j, hj, hpj⟩, hode⟩ := exists_x_ODE_of_isDFinite hD
  have hinj : Function.Injective (Polynomial.map (Polynomial.mapRingHom σ)) :=
    Polynomial.map_injective _ (Polynomial.map_injective _ σ.injective)
  refine no_x_ODE_NK r (fun i => (p i).map (Polynomial.mapRingHom σ))
    ⟨j, hj, fun h => hpj (hinj (by rw [h, Polynomial.map_zero]))⟩ ?_
  have h := congrArg (mapPS2 σ) hode
  rw [map_sum, map_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mapPS2_polyToPS2, mapPS2_dXK_iter, mapPS2_NKser]

/-- **T3.7(3)**（前半，`K = ℂ`）：`𝒩 = Σ_{k,q} N(k,q)·x^k·y^q ∈ ℂ[[x,y]]` 不是 D-finite。 -/
theorem not_isDFinite_NK : ¬ IsDFinite ℂ (NKser ℂ) := not_isDFinite_NKser (RingHom.id ℂ)

end Main

end A207123

