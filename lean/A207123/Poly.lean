import A207123.Binomial
import A207123.Recurrence

/-!
# 报告 T1.2（(C1) 与 `U_k(m)` 的多项式性）与 T1.3(3)（`P_m` 无重因子、`G_m` 只有单极点）

## 形式化了什么

**T1.2（(C1)）**，报告原文：「k≥1 时 U_k(m)=Σ_{j=0}^{m}[U_{k−1}(j)+j·U_{k−3}(j)]；存在唯一 u_k∈ℚ[y]
使 u_k(m)=U_k(m)（m≥0），deg u_k=k，首项 2/k!（k≥2；k=0,1 为 1），u_k(−1)=0（k≥1），且多项式恒等式
u_k(y)−u_k(y−1)=u_{k−1}(y)+y·u_{k−3}(y)」。约定（T1.1）：U_0≡1、U_{−1}≡1、U_{−2}≡0、U_k(−1)=0（k≥1）。
* (C1) 求和式：`C1_sum`（一切 k ≥ 1，下标 `k−1`、`k−3` 按约定函数 `Uext` 取值），以及按情形写开的
  `C1_one`（k=1：`Σ_j [U_0(j) + j·0]`）、`C1_two`（k=2：`Σ_j [U_1(j) + j·1]`）、`C1_succ_three`（k≥3）；
* 存在唯一：`existsUnique_upoly`，以及「任何满足插值条件的多项式都等于 `upoly k`」`eq_upoly_of_eval`；
* 取值 `upoly_eval_nat`，次数 `natDegree_upoly`，首项 `leadingCoeff_upoly_eq`，`u_k(−1)=0`：`upoly_eval_neg_one`；
* 差分恒等式：`upoly_sub_comp`（一切 k ≥ 1，按约定函数 `uext` 取 `u_{−1}=1`、`u_{−2}=0`），以及按情形写开的
  `upoly_sub_comp_one`（`u_1(y)−u_1(y−1) = u_0(y) + y·0`）、`upoly_sub_comp_two`（`= u_1(y) + y·1`）、
  `upoly_sub_comp_succ_three`（k≥3）；
* 汇总定理 `T1_2`。附带：`upoly_le_two`（`u_k = (y+1)^k`，k ≤ 2）。

**T1.3(3)**，报告原文：「P_m 无重因子（b_i 两两互素：公共根会给 (i−j)x³=0；z³−z²−i 判别式 −i(4+27i)<0），
G_m 的极点全是单极点。」
* `isCoprime_bpoly`（`i ≠ j` 时 `b_i`、`b_j` 在 `ℚ[x]` 中互素）、`separable_bpoly`（`b_i` 与 `b_i′` 互素）、
  `separable_Ppoly`、`squarefree_Ppoly`（`P_m` 无重因子）；
* `simple_root_Ppoly`：`P_m` 的每个复根 `z` 都是单根（`rootMultiplicity = 1`），且 `W_m(z) ≠ 0`；
* 汇总定理 `T1_3_3`：上面各条，加上 `G_m = W_m/P_m`（`P_mul_G`）与 `W_m`、`P_m` 互素（`isCoprime_W_P`）。
  「G_m 的极点全是单极点」的含义见 `T1_3_3` 的说明。
* 报告括号里的判别式数值另在 `discr_reverse_bpoly` 中核对（下面 separable 的证明不用它）。

## 定义怎么取

* `binomPoly q`：多项式二项式 `C(y+1, q) = (y+1)·y·(y−1)⋯(y−q+2)/q!`，取为
  `(descPochhammer ℚ q).comp (X + 1)` 乘以 `1/q!`（`descPochhammer ℚ q = y(y−1)⋯(y−q+1)`）。
* `upoly k = Σ_{q=0}^{k} N(k,q)·C(y+1, q)`：报告 T1.4(1) 的二项式基展开（Lean 中的 `U_eq_sum_N`）。
  T1.2 的 `u_k` 由插值条件唯一确定（`existsUnique_upoly`），任何满足 `u(m) = U_k(m)`（∀ m ≥ 0）的多项式都等于
  `upoly k`，所以这个具体定义不改变陈述的含义；`T1_2` 也直接对「任意满足插值条件的 `p`」陈述。
* `Uext : ℤ → ℕ → ℕ`、`uext : ℤ → ℚ[X]`：按 T1.1 的约定把下标延拓到 −1、−2
  （`U_{−1} ≡ 1`、`U_{−2} ≡ 0`；`u_{−1} = 1`、`u_{−2} = 0`）。不能直接用 ℕ 减法 `k − 3`：k = 1 时它截断成 0，
  而 `U_0 ≡ 1 ≠ U_{−2} ≡ 0`。
* 多项式变量记作 `X`（报告的 `y`）；`u_k(y−1)` 写作 `(upoly k).comp (X − 1)`。`b_i`、`P_m`、`W_m`、`G_m` 用
  `Recurrence.lean` 中已有的 `bpoly`、`Ppoly`、`Wpoly`、`Gser`。

## 证明路线

* (C1)：对 m 归纳，即把引理 1（`lemma1`、`lemma1_one`、`lemma1_two`）对 j 望远镜求和；起点用 `U_k(0) = 1 =
  U_{k−1}(0) + 0`（`U_zero_right`），这一步相当于报告中用到的 `U_k(−1) = 0`。
* 多项式性：`u_k(m) = U_k(m)` 直接由 `U_eq_sum_N` 与 `C(y+1,q)` 在 `y = m` 处取值 `C(m+1,q)` 得到；
  次数与首项只来自 `q = k` 一项，首项系数 `N(k,k)/k!`，再用 `N(0,0) = N(1,1) = 1`（`N_init`）、
  `N(k,k) = 2`（k ≥ 2，`N_diag`）；`u_k(−1) = Σ_q N(k,q)·C(0,q) = N(k,0) = 0`（k ≥ 1，`N_succ_zero`）；
  唯一性：两个多项式在一切自然数处相等就相等；差分恒等式：两边在一切 `y = m+1`（m ≥ 0）处的值由引理 1 相等，
  无穷多个点相等，所以作为多项式相等。
  报告的证明是用求和引理 S 对 k 归纳构造 `u_k`；这里换成二项式基直接构造，没有用到求和引理 S。
* T1.3(3)：`b_j = b_i + (i−j)·x³`，而 `b_i` 与 `x` 互素（`1·b_i + (1 + i x²)·x = 1`），所以 `i ≠ j` 时
  `b_i`、`b_j` 互素（即报告的「公共根会给 (i−j)x³=0，但 b_i(0)=1」）。`3·b_i − x·b_i′ = 3 − 2x`，
  `3 − 2x` 不可约，且 `b_i′(3/2) = −1 − 27i/4 ≠ 0`，所以 `3 − 2x` 与 `b_i′` 互素，进而 `b_i` 与 `b_i′` 互素
  （对 i = 0 也成立）。最后用 `Polynomial.separable_prod'` 得 `P_m` separable，从而 squarefree。

## 没有形式化的部分

* 报告 T1.2 证明里的求和引理 S（「次数 d、首项 c 的 f 有唯一 S 满足 S(y)−S(y−1)=f、S(−1)=0，deg S=d+1、
  lc S=c/(d+1)」，对一般的 f）没有形式化；上面的证明不需要它。T1.2 与 T1.3(3) 的陈述本身全部形式化了。
-/

namespace A207123

open Polynomial Finset

/-! ## T1.2：(C1) 求和式 -/

/-- 按报告 T1.1 的约定把 `U` 的第一个下标延拓到 `−1, −2`：`Uext k m = U_k(m)`（`k ≥ 0`），
`Uext (−1) m = 1`（`U_{−1} ≡ 1`），`Uext (−2) m = 0`（`U_{−2} ≡ 0`）；`k ≤ −3` 时取 0（不会用到）。 -/
def Uext : ℤ → ℕ → ℕ
  | Int.ofNat k, m => U k m
  | Int.negSucc 0, _ => 1
  | Int.negSucc (_ + 1), _ => 0

/-- 辅助引理（T1.2）：非负下标处 `Uext k = U_k`。 -/
@[simp] theorem Uext_natCast (k m : ℕ) : Uext (k : ℤ) m = U k m := rfl

/-- 辅助引理（T1.2）：约定 `U_{−1} ≡ 1`。 -/
@[simp] theorem Uext_neg_one (m : ℕ) : Uext (-1) m = 1 := rfl

/-- 辅助引理（T1.2）：约定 `U_{−2} ≡ 0`。 -/
@[simp] theorem Uext_neg_two (m : ℕ) : Uext (-2) m = 0 := rfl

/-- 辅助引理（T1.2）：望远镜求和。若 `f 0 = g 0` 且 `f (m+1) = f m + g (m+1)`，则 `f m = Σ_{j=0}^{m} g j`。 -/
theorem eq_sum_of_succ {f g : ℕ → ℕ} (h0 : f 0 = g 0) (hs : ∀ m, f (m + 1) = f m + g (m + 1))
    (m : ℕ) : f m = ∑ j ∈ range (m + 1), g j := by
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [sum_range_succ, ← ih, hs]

/-- **T1.2 (C1)**，`k = 1` 的情形：`U_1(m) = Σ_{j=0}^{m} [U_0(j) + j·U_{−2}(j)]`，其中按约定 `U_{−2} ≡ 0`
（求和式里的 `j * 0`）。 -/
theorem C1_one (m : ℕ) : U 1 m = ∑ j ∈ range (m + 1), (U 0 j + j * 0) :=
  eq_sum_of_succ (f := U 1) (g := fun j => U 0 j + j * 0) (by simp [U_zero_right])
    (fun m => by
      show U 1 (m + 1) = U 1 m + (U 0 (m + 1) + (m + 1) * 0)
      rw [lemma1_one]; ring) m

/-- **T1.2 (C1)**，`k = 2` 的情形：`U_2(m) = Σ_{j=0}^{m} [U_1(j) + j·U_{−1}(j)]`，其中按约定 `U_{−1} ≡ 1`
（求和式里的 `j * 1`）。 -/
theorem C1_two (m : ℕ) : U 2 m = ∑ j ∈ range (m + 1), (U 1 j + j * 1) :=
  eq_sum_of_succ (f := U 2) (g := fun j => U 1 j + j * 1) (by simp [U_zero_right])
    (fun m => by
      show U 2 (m + 1) = U 2 m + (U 1 (m + 1) + (m + 1) * 1)
      rw [lemma1_two]; ring) m

/-- **T1.2 (C1)**，`k ≥ 3` 的情形（写作 `k + 3`）：
`U_{k+3}(m) = Σ_{j=0}^{m} [U_{k+2}(j) + j·U_k(j)]`。 -/
theorem C1_succ_three (k m : ℕ) :
    U (k + 3) m = ∑ j ∈ range (m + 1), (U (k + 2) j + j * U k j) :=
  eq_sum_of_succ (f := U (k + 3)) (g := fun j => U (k + 2) j + j * U k j) (by simp [U_zero_right])
    (fun m => by
      show U (k + 3) (m + 1) = U (k + 3) m + (U (k + 2) (m + 1) + (m + 1) * U k (m + 1))
      rw [lemma1, add_assoc]) m

/-- **T1.2 (C1)**：对一切 `k ≥ 1`、`m ≥ 0`，`U_k(m) = Σ_{j=0}^{m} [U_{k−1}(j) + j·U_{k−3}(j)]`。
下标 `k−1`、`k−3` 在 ℤ 中计算，按 T1.1 的约定 `U_{−1} ≡ 1`、`U_{−2} ≡ 0` 取值（`Uext`）；
k = 1、2、≥3 三种情形分别写开就是 `C1_one`、`C1_two`、`C1_succ_three`。 -/
theorem C1_sum (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    U k m = ∑ j ∈ range (m + 1), (Uext ((k : ℤ) - 1) j + j * Uext ((k : ℤ) - 3) j) := by
  match k, hk with
  | 1, _ =>
    rw [show ((1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num, show ((1 : ℕ) : ℤ) - 3 = -2 by norm_num]
    simpa only [Uext_natCast, Uext_neg_two] using C1_one m
  | 2, _ =>
    rw [show ((2 : ℕ) : ℤ) - 1 = ((1 : ℕ) : ℤ) by norm_num, show ((2 : ℕ) : ℤ) - 3 = -1 by norm_num]
    simpa only [Uext_natCast, Uext_neg_one] using C1_two m
  | k + 3, _ =>
    rw [show ((k + 3 : ℕ) : ℤ) - 1 = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
      show ((k + 3 : ℕ) : ℤ) - 3 = ((k : ℕ) : ℤ) by push_cast; ring]
    simpa only [Uext_natCast] using C1_succ_three k m

/-! ## T1.2：多项式 `u_k` -/

/-- 多项式二项式 `C(y+1, q) = (y+1)·y·(y−1)⋯(y−q+2)/q!`：`descPochhammer ℚ q = y(y−1)⋯(y−q+1)`
复合 `y ↦ y+1` 后乘以 `1/q!`。 -/
noncomputable def binomPoly (q : ℕ) : ℚ[X] :=
  C ((q.factorial : ℚ)⁻¹) * (descPochhammer ℚ q).comp (X + 1)

/-- `u_k(y) = Σ_{q=0}^{k} N(k,q)·C(y+1, q)`（报告 T1.4(1) 的二项式基展开）。由 `existsUnique_upoly`，它就是
T1.2 中唯一满足 `u_k(m) = U_k(m)`（m ≥ 0）的多项式。 -/
noncomputable def upoly (k : ℕ) : ℚ[X] := ∑ q ∈ range (k + 1), C (N k q : ℚ) * binomPoly q

/-- 辅助引理（T1.2）：`C(y+1, q)` 在自然数 `y = m` 处取值 `C(m+1, q)`。 -/
theorem binomPoly_eval_nat (q m : ℕ) : (binomPoly q).eval (m : ℚ) = ((m + 1).choose q : ℚ) := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one,
    Nat.cast_choose_eq_descPochhammer_div ℚ, Nat.cast_add, Nat.cast_one]
  ring

/-- 辅助引理（T1.2）：`C(y+1, q)` 在 `y = −1` 处取值 `C(0, q) = [q = 0]`。 -/
theorem binomPoly_eval_neg_one (q : ℕ) : (binomPoly q).eval (-1) = if q = 0 then 1 else 0 := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, neg_add_cancel,
    descPochhammer_eval_zero]
  split_ifs with h <;> simp [h]

/-- 辅助引理（T1.2）：`descPochhammer ℚ q ∘ (y+1)` 是首一多项式。 -/
theorem monic_descComp (q : ℕ) : ((descPochhammer ℚ q).comp (X + 1)).Monic := by
  simpa using (monic_descPochhammer ℚ q).comp_X_add_C 1

/-- 辅助引理（T1.2）：`descPochhammer ℚ q ∘ (y+1)` 的次数是 `q`。 -/
theorem natDegree_descComp (q : ℕ) : ((descPochhammer ℚ q).comp (X + 1)).natDegree = q := by
  have h1 : (X + 1 : ℚ[X]).natDegree = 1 := by compute_degree!
  rw [natDegree_comp, descPochhammer_natDegree, h1, mul_one]

/-- 辅助引理（T1.2）：`C(y+1, q)` 的 `y^q` 系数是 `1/q!`。 -/
theorem coeff_binomPoly_self (q : ℕ) : (binomPoly q).coeff q = ((q.factorial : ℚ))⁻¹ := by
  have h := (monic_descComp q).coeff_natDegree
  rw [natDegree_descComp] at h
  rw [binomPoly, coeff_C_mul, h, mul_one]

/-- 辅助引理（T1.2）：`n > q` 时 `C(y+1, q)` 的 `y^n` 系数是 0。 -/
theorem coeff_binomPoly_of_lt {q n : ℕ} (h : q < n) : (binomPoly q).coeff n = 0 := by
  rw [binomPoly, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_descComp]; exact h), mul_zero]

/-- **T1.2**：`u_k(m) = U_k(m)`（一切 `m ≥ 0`）。由 `U_eq_sum_N`：`U_k(m) = Σ_q N(k,q)·C(m+1,q)`。 -/
theorem upoly_eval_nat (k m : ℕ) : (upoly k).eval (m : ℚ) = (U k m : ℚ) := by
  rw [upoly, eval_finsetSum, U_eq_sum_N]
  push_cast
  refine sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, binomPoly_eval_nat]

/-- 辅助引理（T1.2）：`u_k(m+1) = U_k(m+1)`（`upoly_eval_nat` 换一种写法）。 -/
theorem upoly_eval_succ (k m : ℕ) : (upoly k).eval ((m : ℚ) + 1) = (U k (m + 1) : ℚ) := by
  have h := upoly_eval_nat k (m + 1)
  push_cast at h
  exact h

/-- **T1.2**：`u_k(−1) = 0`（`k ≥ 1`）：`u_k(−1) = Σ_q N(k,q)·C(0,q) = N(k,0) = 0`。 -/
theorem upoly_eval_neg_one (k : ℕ) (hk : 1 ≤ k) : (upoly k).eval (-1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [upoly, eval_finsetSum]
  simp [binomPoly_eval_neg_one, N_succ_zero]

/-- 辅助引理（T1.2）：`n > k` 时 `u_k` 的 `y^n` 系数是 0。 -/
theorem coeff_upoly_of_lt {k n : ℕ} (h : k < n) : (upoly k).coeff n = 0 := by
  rw [upoly, finsetSum_coeff]
  refine sum_eq_zero fun q hq => ?_
  rw [coeff_C_mul, coeff_binomPoly_of_lt (by rw [mem_range] at hq; omega), mul_zero]

/-- 辅助引理（T1.2）：`u_k` 的 `y^k` 系数是 `N(k,k)/k!`（只有 `q = k` 一项有贡献）。 -/
theorem coeff_upoly_self (k : ℕ) : (upoly k).coeff k = (N k k : ℚ) / (k.factorial : ℚ) := by
  rw [upoly, finsetSum_coeff, sum_range_succ, sum_eq_zero (fun q hq => by
    rw [coeff_C_mul, coeff_binomPoly_of_lt (mem_range.mp hq), mul_zero]), zero_add,
    coeff_C_mul, coeff_binomPoly_self, div_eq_mul_inv]

/-- 辅助引理（T1.2）：`N(k,k) > 0`（`N(0,0) = N(1,1) = 1`，k ≥ 2 时 `N(k,k) = 2`）。 -/
theorem N_self_pos (k : ℕ) : 0 < N k k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · rw [N_init.1]; norm_num
  · rw [N_init.2.1]; norm_num
  · rw [N_diag k hk]; norm_num

/-- **T1.2**：`deg u_k = k`。 -/
theorem natDegree_upoly (k : ℕ) : (upoly k).natDegree = k := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    exact coeff_upoly_of_lt hn
  · rw [coeff_upoly_self]
    exact div_ne_zero (by exact_mod_cast (N_self_pos k).ne')
      (by exact_mod_cast (Nat.factorial_pos k).ne')

/-- 辅助引理（T1.2）：`u_k` 的首项系数是 `N(k,k)/k!`。 -/
theorem leadingCoeff_upoly (k : ℕ) :
    (upoly k).leadingCoeff = (N k k : ℚ) / (k.factorial : ℚ) := by
  rw [leadingCoeff, natDegree_upoly, coeff_upoly_self]

/-- **T1.2**：`u_k` 的首项系数，`k = 0, 1` 时为 1，`k ≥ 2` 时为 `2/k!`。 -/
theorem leadingCoeff_upoly_eq (k : ℕ) :
    (upoly k).leadingCoeff = if k ≤ 1 then 1 else 2 / (k.factorial : ℚ) := by
  rw [leadingCoeff_upoly]
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · rw [N_init.1]; norm_num
  · rw [N_init.2.1]; norm_num
  · rw [N_diag k hk]
    simp [show ¬k ≤ 1 by omega]

/-- 辅助引理（T1.2）：两个 `ℚ` 系数多项式若在一切自然数处取值相同，则相等（无穷多个点相等）。 -/
theorem poly_eq_of_eval_nat {p q : ℚ[X]} (h : ∀ m : ℕ, p.eval (m : ℚ) = q.eval (m : ℚ)) :
    p = q := by
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Nat.cast_injective)
  rintro _ ⟨m, rfl⟩
  exact h m

/-- 辅助引理（T1.2）：两个 `ℚ` 系数多项式若在一切 `y = m+1`（`m ≥ 0`）处取值相同，则相等。 -/
theorem poly_eq_of_eval_succ {p q : ℚ[X]}
    (h : ∀ m : ℕ, p.eval ((m : ℚ) + 1) = q.eval ((m : ℚ) + 1)) : p = q := by
  apply eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun m : ℕ => (m : ℚ) + 1) := by
    intro a b hab
    simpa using hab
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨m, rfl⟩
  exact h m

/-- **T1.2**（存在唯一）：对每个 `k ≥ 0`，存在唯一的 `u ∈ ℚ[y]` 使 `u(m) = U_k(m)` 对一切 `m ≥ 0` 成立
（就是 `upoly k`）。 -/
theorem existsUnique_upoly (k : ℕ) : ∃! p : ℚ[X], ∀ m : ℕ, p.eval (m : ℚ) = (U k m : ℚ) :=
  ⟨upoly k, upoly_eval_nat k, fun p hp => poly_eq_of_eval_nat fun m => by rw [hp, upoly_eval_nat]⟩

/-- **T1.2**（唯一性的另一种写法）：任何满足 `p(m) = U_k(m)`（一切 `m ≥ 0`）的多项式都等于 `upoly k`。 -/
theorem eq_upoly_of_eval {k : ℕ} {p : ℚ[X]} (hp : ∀ m : ℕ, p.eval (m : ℚ) = (U k m : ℚ)) :
    p = upoly k :=
  poly_eq_of_eval_nat fun m => by rw [hp, upoly_eval_nat]

/-- 辅助引理（T1.2）：小 `k` 的显式形式 `u_k = (y+1)^k`（`k ≤ 2`），即 `u_0 = 1`、`u_1 = y+1`、`u_2 = (y+1)²`
（由 `U_k(m) = (m+1)^k`，`U_of_le_two`）。 -/
theorem upoly_le_two {k : ℕ} (hk : k ≤ 2) : upoly k = (X + 1) ^ k :=
  (eq_upoly_of_eval fun m => by simp [U_of_le_two hk]).symm

/-- 按约定把 `u` 的下标延拓到 `−1, −2`：`uext k = u_k`（`k ≥ 0`，即 `upoly k`），`uext (−1) = 1`，
`uext (−2) = 0`；`k ≤ −3` 时取 0（不会用到）。 -/
noncomputable def uext : ℤ → ℚ[X]
  | Int.ofNat k => upoly k
  | Int.negSucc 0 => 1
  | Int.negSucc (_ + 1) => 0

/-- 辅助引理（T1.2）：非负下标处 `uext k = u_k`。 -/
@[simp] theorem uext_natCast (k : ℕ) : uext (k : ℤ) = upoly k := rfl

/-- 辅助引理（T1.2）：约定 `u_{−1} = 1`。 -/
@[simp] theorem uext_neg_one : uext (-1) = 1 := rfl

/-- 辅助引理（T1.2）：约定 `u_{−2} = 0`。 -/
@[simp] theorem uext_neg_two : uext (-2) = 0 := rfl

/-- **T1.2**（差分恒等式，`k = 1`）：`u_1(y) − u_1(y−1) = u_0(y) + y·u_{−2}(y)`，按约定 `u_{−2} = 0`。 -/
theorem upoly_sub_comp_one : upoly 1 - (upoly 1).comp (X - 1) = upoly 0 + X * 0 := by
  apply poly_eq_of_eval_succ
  intro m
  have h : (U 1 (m + 1) : ℚ) = U 1 m + U 0 (m + 1) := by exact_mod_cast lemma1_one m
  simp only [eval_sub, eval_X, eval_comp, eval_one, add_sub_cancel_right, upoly_eval_succ,
    upoly_eval_nat, mul_zero, add_zero]
  linear_combination h

/-- **T1.2**（差分恒等式，`k = 2`）：`u_2(y) − u_2(y−1) = u_1(y) + y·u_{−1}(y)`，按约定 `u_{−1} = 1`。 -/
theorem upoly_sub_comp_two : upoly 2 - (upoly 2).comp (X - 1) = upoly 1 + X * 1 := by
  apply poly_eq_of_eval_succ
  intro m
  have h : (U 2 (m + 1) : ℚ) = U 2 m + U 1 (m + 1) + ((m : ℚ) + 1) * 1 := by
    exact_mod_cast lemma1_two m
  simp only [eval_sub, eval_add, eval_mul, eval_X, eval_comp, eval_one,
    add_sub_cancel_right, upoly_eval_succ, upoly_eval_nat]
  linear_combination h

/-- **T1.2**（差分恒等式，`k ≥ 3`，写作 `k + 3`）：`u_{k+3}(y) − u_{k+3}(y−1) = u_{k+2}(y) + y·u_k(y)`。 -/
theorem upoly_sub_comp_succ_three (k : ℕ) :
    upoly (k + 3) - (upoly (k + 3)).comp (X - 1) = upoly (k + 2) + X * upoly k := by
  apply poly_eq_of_eval_succ
  intro m
  have h : (U (k + 3) (m + 1) : ℚ) =
      U (k + 3) m + U (k + 2) (m + 1) + ((m : ℚ) + 1) * U k (m + 1) := by
    exact_mod_cast lemma1 k m
  simp only [eval_sub, eval_add, eval_mul, eval_X, eval_comp, eval_one,
    add_sub_cancel_right, upoly_eval_succ, upoly_eval_nat]
  linear_combination h

/-- **T1.2**（差分恒等式）：对一切 `k ≥ 1`，作为 `ℚ[y]` 中的多项式恒等式
`u_k(y) − u_k(y−1) = u_{k−1}(y) + y·u_{k−3}(y)`，下标在 ℤ 中计算，按约定 `u_{−1} = 1`、`u_{−2} = 0`
（`uext`）。k = 1、2、≥3 分别写开就是 `upoly_sub_comp_one`、`upoly_sub_comp_two`、`upoly_sub_comp_succ_three`。 -/
theorem upoly_sub_comp (k : ℕ) (hk : 1 ≤ k) :
    upoly k - (upoly k).comp (X - 1) = uext ((k : ℤ) - 1) + X * uext ((k : ℤ) - 3) := by
  match k, hk with
  | 1, _ =>
    rw [show ((1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num, show ((1 : ℕ) : ℤ) - 3 = -2 by norm_num,
      uext_natCast, uext_neg_two]
    exact upoly_sub_comp_one
  | 2, _ =>
    rw [show ((2 : ℕ) : ℤ) - 1 = ((1 : ℕ) : ℤ) by norm_num, show ((2 : ℕ) : ℤ) - 3 = -1 by norm_num,
      uext_natCast, uext_neg_one]
    exact upoly_sub_comp_two
  | k + 3, _ =>
    rw [show ((k + 3 : ℕ) : ℤ) - 1 = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
      show ((k + 3 : ℕ) : ℤ) - 3 = ((k : ℕ) : ℤ) by push_cast; ring, uext_natCast, uext_natCast]
    exact upoly_sub_comp_succ_three k

/-- **T1.2**（汇总）。对每个 `k ≥ 0`：
1. (C1)：`k ≥ 1` 时 `U_k(m) = Σ_{j=0}^{m} [U_{k−1}(j) + j·U_{k−3}(j)]`（一切 `m ≥ 0`；约定 `U_{−1} ≡ 1`、
   `U_{−2} ≡ 0` 由 `Uext` 实现）；
2. 存在唯一的 `u_k ∈ ℚ[y]` 使 `u_k(m) = U_k(m)`（一切 `m ≥ 0`）；
3. 任何这样的多项式 `p`（即 `u_k`）满足：`deg p = k`；首项系数 `k ≤ 1` 时为 1、`k ≥ 2` 时为 `2/k!`；
   `k ≥ 1` 时 `p(−1) = 0`；`k ≥ 1` 时 `p(y) − p(y−1) = u_{k−1}(y) + y·u_{k−3}(y)`，其中 `u_j`（`j ≥ 0`）是
   第 2 条中对应 `j` 的唯一插值多项式（`upoly j`），`u_{−1} = 1`、`u_{−2} = 0`（`uext`）。 -/
theorem T1_2 (k : ℕ) :
    (1 ≤ k → ∀ m : ℕ,
      U k m = ∑ j ∈ range (m + 1), (Uext ((k : ℤ) - 1) j + j * Uext ((k : ℤ) - 3) j)) ∧
    (∃! p : ℚ[X], ∀ m : ℕ, p.eval (m : ℚ) = (U k m : ℚ)) ∧
    (∀ p : ℚ[X], (∀ m : ℕ, p.eval (m : ℚ) = (U k m : ℚ)) →
      p.natDegree = k ∧
      p.leadingCoeff = (if k ≤ 1 then 1 else 2 / (k.factorial : ℚ)) ∧
      (1 ≤ k → p.eval (-1) = 0) ∧
      (1 ≤ k → p - p.comp (X - 1) = uext ((k : ℤ) - 1) + X * uext ((k : ℤ) - 3))) := by
  refine ⟨fun hk m => C1_sum k hk m, existsUnique_upoly k, fun p hp => ?_⟩
  obtain rfl := eq_upoly_of_eval hp
  exact ⟨natDegree_upoly k, leadingCoeff_upoly_eq k, upoly_eval_neg_one k, upoly_sub_comp k⟩

/-! ## T1.3(3)：`P_m` 无重因子，`G_m` 的极点都是单极点 -/

/-- 辅助引理（T1.3(3)）：`b_i′ = −1 − 3i·x²`。 -/
theorem derivative_bpoly (i : ℕ) : derivative (bpoly ℚ i) = -1 - C ((i : ℚ) * 3) * X ^ 2 := by
  rw [bpoly, derivative_sub, derivative_sub, derivative_one, derivative_X, derivative_C_mul_X_pow]
  norm_num

/-- 辅助引理（T1.3(3)）：`b_i′(r) = −1 − 3i·r²`。 -/
theorem eval_derivative_bpoly (i : ℕ) (r : ℚ) :
    (derivative (bpoly ℚ i)).eval r = -1 - 3 * i * r ^ 2 := by
  rw [derivative_bpoly]
  simp only [eval_sub, eval_neg, eval_one, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- 辅助引理（T1.3(3)）：`3·b_i − x·b_i′ = 3 − 2x`。 -/
theorem three_mul_bpoly_sub (i : ℕ) :
    3 * bpoly ℚ i - X * derivative (bpoly ℚ i) = 3 - 2 * X := by
  rw [derivative_bpoly, bpoly, C_mul, map_ofNat C 3]
  ring

/-- **T1.3(3)**：每个 `b_i = 1 − x − i·x³`（`i ≥ 0`）在 `ℚ[x]` 中 separable，即与导数 `b_i′` 互素
（无重根）。证明：`3·b_i − x·b_i′ = 3 − 2x` 不可约，且 `b_i′(3/2) = −1 − 27i/4 ≠ 0`。 -/
theorem separable_bpoly (i : ℕ) : (bpoly ℚ i).Separable := by
  have hirr : Irreducible (3 - 2 * X : ℚ[X]) := irreducible_of_degree_eq_one (by compute_degree!)
  have hcop : IsCoprime (3 - 2 * X : ℚ[X]) (derivative (bpoly ℚ i)) := by
    rw [hirr.coprime_iff_not_dvd]
    intro hdvd
    have h := eval_dvd (x := (3 / 2 : ℚ)) hdvd
    have h0 : (3 - 2 * X : ℚ[X]).eval (3 / 2) = 0 := by norm_num
    rw [h0, zero_dvd_iff, eval_derivative_bpoly] at h
    have : (0 : ℚ) ≤ i := Nat.cast_nonneg i
    nlinarith
  have e : (3 - 2 * X : ℚ[X]) = 3 * bpoly ℚ i + (-X) * derivative (bpoly ℚ i) := by
    rw [← three_mul_bpoly_sub]; ring
  rw [e] at hcop
  have h3 : IsUnit (3 : ℚ[X]) := by
    rw [← map_ofNat C 3]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  exact (isCoprime_mul_unit_left_left h3 _ _).mp hcop.of_add_mul_right_left

/-- **T1.3(3)**：`i ≠ j` 时 `b_i` 与 `b_j` 在 `ℚ[x]` 中互素。证明：`b_j = b_i + (i−j)·x³`，而 `b_i` 与 `x`
互素（`b_i(0) = 1`）；这就是报告「公共根会给 (i−j)x³ = 0」的代数形式。 -/
theorem isCoprime_bpoly {i j : ℕ} (hij : i ≠ j) : IsCoprime (bpoly ℚ i) (bpoly ℚ j) := by
  have hX : IsCoprime (bpoly ℚ i) X := ⟨1, 1 + C (i : ℚ) * X ^ 2, by rw [bpoly]; ring⟩
  have hc : IsUnit (C ((i : ℚ) - j)) :=
    isUnit_C.mpr (Ne.isUnit (sub_ne_zero.mpr (by exact_mod_cast hij)))
  have h3 : IsCoprime (bpoly ℚ i) (C ((i : ℚ) - j) * X ^ 3) :=
    (isCoprime_mul_unit_left_right hc _ _).mpr hX.pow_right
  have e : bpoly ℚ j = C ((i : ℚ) - j) * X ^ 3 + bpoly ℚ i * 1 := by
    simp only [bpoly, map_sub]
    ring
  rw [e]
  exact h3.add_mul_left_right 1

/-- **T1.3(3)**：对一切 `m ≥ 0`，`P_m = ∏_{i=0}^{m} b_i` 在 `ℚ[x]` 中 separable（与导数互素）。 -/
theorem separable_Ppoly (m : ℕ) : (Ppoly ℚ m).Separable := by
  unfold Ppoly
  exact separable_prod' (fun i _ j _ hij => isCoprime_bpoly hij) (fun i _ => separable_bpoly i)

/-- **T1.3(3)**：对一切 `m ≥ 0`，`P_m` 无重因子（在 `ℚ[x]` 中 squarefree）。 -/
theorem squarefree_Ppoly (m : ℕ) : Squarefree (Ppoly ℚ m) := (separable_Ppoly m).squarefree

/-- **T1.3(3)**：`P_m` 的每个复根 `z` 都是单根（`rootMultiplicity = 1`），且 `W_m(z) ≠ 0`
（由 `W_m`、`P_m` 互素）。所以 `G_m = W_m/P_m` 在 `z` 处是一阶极点。 -/
theorem simple_root_Ppoly (m : ℕ) (z : ℂ) (hz : (Ppoly ℂ m).IsRoot z) :
    (Ppoly ℂ m).rootMultiplicity z = 1 ∧ (Wpoly ℂ m).eval z ≠ 0 := by
  have hsep : (Ppoly ℂ m).Separable := by
    rw [← Ppoly_map ℚ (algebraMap ℚ ℂ) m]
    exact (separable_Ppoly m).map
  have hne : Ppoly ℂ m ≠ 0 := hsep.ne_zero
  have h1 := rootMultiplicity_le_one_of_separable hsep z
  have h2 := (rootMultiplicity_pos hne).mpr hz
  refine ⟨by omega, ?_⟩
  have hcop : IsCoprime (Wpoly ℂ m) (Ppoly ℂ m) := by
    have := (isCoprime_W_P m).map (mapRingHom (algebraMap ℚ ℂ))
    rwa [coe_mapRingHom, Ppoly_map, Wpoly_map] at this
  obtain ⟨a, b, hab⟩ := hcop
  intro hW
  have := congrArg (eval z) hab
  rw [eval_add, eval_mul, eval_mul, hW, hz.eq_zero, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

/-- 辅助引理（T1.3(3)，只用于核对报告括号里的判别式；上面 separable 的证明不依赖它）：
`b_i` 的反转多项式是 `z³ − z² − i`（`z ≠ 0` 时 `z³·b_i(1/z) = z³ − z² − i`）；作为三次式
`⟨1, −1, 0, −i⟩`（`Cubic`），其判别式为 `−i(4+27i)`，`i ≥ 1` 时为负。 -/
theorem discr_reverse_bpoly (i : ℕ) :
    (∀ z : ℚ, z ≠ 0 → z ^ 3 * (bpoly ℚ i).eval z⁻¹ = z ^ 3 - z ^ 2 - i) ∧
    (⟨1, -1, 0, -(i : ℚ)⟩ : Cubic ℚ).discr = -(i : ℚ) * (4 + 27 * i) ∧
    (1 ≤ i → (⟨1, -1, 0, -(i : ℚ)⟩ : Cubic ℚ).discr < 0) := by
  have hd : (⟨1, -1, 0, -(i : ℚ)⟩ : Cubic ℚ).discr = -(i : ℚ) * (4 + 27 * i) := by
    simp only [Cubic.discr]
    ring
  refine ⟨fun z hz => ?_, hd, fun hi => ?_⟩
  · rw [eval_bpoly]
    field_simp
  · rw [hd]
    have : (1 : ℚ) ≤ i := by exact_mod_cast hi
    nlinarith

/-- **T1.3(3)**（汇总）。对一切 `m ≥ 0`：
1. `b_i`（`i ≥ 0`）两两互素；2. 每个 `b_i` separable；
3. `P_m` separable，从而无重因子（squarefree）；
4. `G_m = W_m/P_m`：形式幂级数恒等式 `P_m·G_m = W_m`（`P_mul_G`）；
5. `W_m` 与 `P_m` 在 `ℚ[x]` 中互素（`isCoprime_W_P`，T1.3(2)），即 `W_m/P_m` 是既约分式；
6. `P_m` 的每个复根 `z` 都是单根，且 `W_m(z) ≠ 0`。

「G_m 的极点全是单极点」的含义：由 4，`G_m` 是有理函数 `W_m/P_m` 的 Taylor 展开；由 5 它既约，
所以 `G_m` 的极点恰是 `P_m` 的复根；在根 `z` 处极点的阶是 `P_m` 在 `z` 的重数减去 `W_m` 在 `z` 的重数，
由 6 等于 `1 − 0 = 1`。 -/
theorem T1_3_3 (m : ℕ) :
    (∀ i j : ℕ, i ≠ j → IsCoprime (bpoly ℚ i) (bpoly ℚ j)) ∧
    (∀ i : ℕ, (bpoly ℚ i).Separable) ∧
    (Ppoly ℚ m).Separable ∧ Squarefree (Ppoly ℚ m) ∧
    (↑(Ppoly ℚ m) : PowerSeries ℚ) * Gser m = ↑(Wpoly ℚ m) ∧
    IsCoprime (Wpoly ℚ m) (Ppoly ℚ m) ∧
    (∀ z : ℂ, (Ppoly ℂ m).IsRoot z →
      (Ppoly ℂ m).rootMultiplicity z = 1 ∧ (Wpoly ℂ m).eval z ≠ 0) :=
  ⟨fun _ _ h => isCoprime_bpoly h, separable_bpoly, separable_Ppoly m, squarefree_Ppoly m,
    P_mul_G m, isCoprime_W_P m, simple_root_Ppoly m⟩

end A207123
