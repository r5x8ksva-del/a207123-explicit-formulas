import A207123.Recurrence
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# 报告 T2.7 的前半：`Σ_{j<m} P_j` 不是 Gosper 可和的

**T2.7**（前半，`partialSum_P_not_hypergeometric`）：取基域 `ℚ(x)`（`RatFunc ℚ`），部分和
`Σ_{j<m} P_j`（`P_j = ∏_{i≤j}(1 − x − i·x³)`）关于 `m` 不等于任何超几何项加常数，
即不存在超几何项 `T(m)` 与常数 `c ∈ ℚ(x)` 使 `Σ_{j<m} P_j = T(m) + c` 对充分大的 `m` 成立。

**超几何项的取法**（`IsHyperTerm`）：`T : ℕ → K` 满足一阶多项式系数递推
`q(m)·T(m+1) = p(m)·T(m)`（`p, q ∈ K[m]`，`q ≠ 0`，对充分大的 `m` 成立）。通常的定义是「`T(m) ≠ 0` 且
`T(m+1)/T(m)` 是 `m` 的有理函数」，它是这里的特例，所以这里的不存在性结论比通常的说法更强（没有加强假设）。

**证明**（报告的论证）：
* 由 `T(m+1) − T(m) = P_m` 与 `q(m)T(m+1) = p(m)T(m)` 得 `(p−q)(m)·T(m) = q(m)·P_m`；`D := p − q ≠ 0`。
  记 `y = q/D`，则 `T = y·P`，而 `P_{m+1} = b_{m+1}·P_m`，`b_{m+1} = L(m) = 1 − x − (m+1)x³`，所以
  `y(m+1)·L(m) − y(m) = 1`，即多项式恒等式 `D·q(m+1)·L = D(m+1)·(q + D)`（在无穷多个 `m` 处成立）。
* `no_gosper_solution`：这个方程没有有理解。把 `y` 约成最简分式 `A/B`，得 `B·A(m+1)·L = B(m+1)·(A + B)`，
  于是 `B ∣ B(m+1)`；两者次数与首项相同，所以 `B(m+1) = B`，`B` 是常数（报告：「分母的根沿 +1 无限传递
  ⇒ y 是多项式」）；再比较次数：`A(m+1)·L` 比 `A + B` 高一次，矛盾。

报告 T2.7 的推论部分（依赖 Wilf–Zeilberger 1992、Zeilberger 1990 的 holonomic 理论，本文未重证）没有形式化。
-/

open Polynomial Finset

namespace A207123

/-- 超几何项（广义）：`T` 对充分大的 `m` 满足 `q(m)·T(m+1) = p(m)·T(m)`，`p, q ∈ K[m]`，`q ≠ 0`。 -/
def IsHyperTerm {K : Type*} [Field K] (T : ℕ → K) : Prop :=
  ∃ p q : K[X], q ≠ 0 ∧ ∃ m0 : ℕ, ∀ m, m0 ≤ m → q.eval (m : K) * T (m + 1) = p.eval (m : K) * T m

/-- 辅助引理（T2.7）：特征 0 的域上，多项式在无穷多个自然数处为零则为零多项式。 -/
theorem eq_zero_of_eval_nat_ge {K : Type*} [Field K] [CharZero K] (f : K[X]) (m0 : ℕ)
    (h : ∀ m, m0 ≤ m → f.eval (m : K) = 0) : f = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + m0 : ℕ) : K))
  · intro a b hab
    have := Nat.cast_injective (R := K) hab
    omega
  · intro n
    exact h (n + m0) (by omega)

/-- 辅助引理（T2.7）。 -/
theorem natDegree_X_add_one_gos {K : Type*} [Field K] : (X + 1 : K[X]).natDegree = 1 := by
  rw [← C_1, natDegree_X_add_C]

/-- 辅助引理（T2.7）。 -/
theorem leadingCoeff_X_add_one_gos {K : Type*} [Field K] : (X + 1 : K[X]).leadingCoeff = 1 := by
  rw [← C_1, leadingCoeff_X_add_C]

/-- 辅助引理（T2.7）：平移 `p(m) ↦ p(m+1)` 不改变次数与首项系数。 -/
theorem natDegree_comp_X_add_one {K : Type*} [Field K] (p : K[X]) :
    (p.comp (X + 1)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_one_gos, mul_one]

/-- 辅助引理（T2.7）。 -/
theorem leadingCoeff_comp_X_add_one {K : Type*} [Field K] (p : K[X]) :
    (p.comp (X + 1)).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_X_add_one_gos]; exact one_ne_zero),
    leadingCoeff_X_add_one_gos, one_pow, mul_one]

/-- 辅助引理（T2.7）：平移保持非零。 -/
theorem comp_X_add_one_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    p.comp (X + 1) ≠ 0 := by
  intro h0
  have := congrArg natDegree h0
  rw [natDegree_comp_X_add_one, natDegree_zero] at this
  have hc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero this
  rw [hc, C_comp] at h0
  exact hp (hc.trans h0)

/-- 辅助引理（T2.7）：平移后与自身相等的多项式（特征 0）是常数。 -/
theorem eq_C_of_comp_X_add_one {K : Type*} [Field K] [CharZero K] {B : K[X]}
    (h : B.comp (X + 1) = B) : B = C (B.eval 0) := by
  have hval : ∀ n : ℕ, B.eval (n : K) = B.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := congrArg (fun f : K[X] => f.eval (n : K)) h
      simp only [eval_comp, eval_add, eval_X, eval_one] at this
      rw [Nat.cast_succ, this, ih]
  have h0 : B - C (B.eval 0) = 0 := by
    apply eq_zero_of_eval_nat_ge _ 0
    intro m _
    rw [eval_sub, eval_C, hval, sub_self]
  exact sub_eq_zero.mp h0

/-- **T2.7**（核心：Gosper 方程无有理解）：设 `K` 是特征 0 的域，`L ∈ K[m]` 是一次多项式。则不存在
`D ≠ 0` 与 `q` 使 `D·q(m+1)·L = D(m+1)·(q + D)`；即 `y = q/D` 不满足 `y(m+1)·L(m) − y(m) = 1`。 -/
theorem no_gosper_solution {K : Type*} [Field K] [CharZero K] (L : K[X]) (hL : L.natDegree = 1)
    (q D : K[X]) (hD : D ≠ 0) : D * q.comp (X + 1) * L ≠ D.comp (X + 1) * (q + D) := by
  classical
  intro h
  have hL0 : L ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hL; exact zero_ne_one hL
  -- 约成最简分式 `q/D = A/B`
  set g := GCDMonoid.gcd q D with hg
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hD
  set A := q / g with hA
  set B := D / g with hB
  have hqA : g * A = q := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left q D)
  have hDB : g * B = D := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right q D)
  have hcop : IsCoprime A B := isCoprime_div_gcd_div_gcd hD
  have hB0 : B ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hDB; exact hD hDB.symm
  have hσg : g.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hg0
  -- 消去 `g·g(m+1)`
  have h' : B * A.comp (X + 1) * L = B.comp (X + 1) * (A + B) := by
    rw [← hqA, ← hDB, mul_comp, mul_comp] at h
    have h2 : (g * g.comp (X + 1)) * (B * A.comp (X + 1) * L)
        = (g * g.comp (X + 1)) * (B.comp (X + 1) * (A + B)) := by
      linear_combination h
    exact mul_left_cancel₀ (mul_ne_zero hg0 hσg) h2
  -- `B ∣ B(m+1)`，于是 `B(m+1) = B`，`B` 是常数
  have hdvd : B ∣ B.comp (X + 1) := by
    have h1 : B ∣ B.comp (X + 1) * (A + B) := ⟨A.comp (X + 1) * L, by rw [← h']; ring⟩
    have hcop' : IsCoprime B (A + B) := by
      have := hcop.symm.add_mul_left_right 1
      rwa [mul_one] at this
    exact hcop'.dvd_of_dvd_mul_right h1
  have hσB0 : B.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hB0
  have hshift : B.comp (X + 1) = B := by
    by_contra hne
    have hsub : B.comp (X + 1) - B ≠ 0 := sub_ne_zero.mpr hne
    have hlt : (B.comp (X + 1) - B).degree < (B.comp (X + 1)).degree := by
      apply degree_sub_lt_left
      · rw [degree_eq_natDegree hB0, degree_eq_natDegree hσB0, natDegree_comp_X_add_one]
      · exact hσB0
      · exact leadingCoeff_comp_X_add_one B
    have hle := degree_le_of_dvd (dvd_sub hdvd dvd_rfl) hsub
    rw [degree_eq_natDegree hσB0, natDegree_comp_X_add_one, ← degree_eq_natDegree hB0] at hlt
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  have hBC := eq_C_of_comp_X_add_one hshift
  set b := B.eval 0 with hb
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0, C_0] at hBC; exact hB0 hBC
  -- 剩下 `A(m+1)·L = A + b`，次数矛盾
  rw [hshift, hBC] at h'
  have h3 : A.comp (X + 1) * L = A + C b := by
    have h4 : C b * (A.comp (X + 1) * L) = C b * (A + C b) := by
      rw [← mul_assoc]; exact h'
    exact mul_left_cancel₀ (C_ne_zero.mpr hb0) h4
  by_cases hA0 : A = 0
  · rw [hA0, zero_comp, zero_mul, zero_add] at h3
    exact hb0 (C_eq_zero.mp h3.symm)
  · have hσA0 : A.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hA0
    have hdeg := congrArg natDegree h3
    rw [natDegree_mul hσA0 hL0, natDegree_comp_X_add_one, hL] at hdeg
    have hle : (A + C b).natDegree ≤ A.natDegree := by
      apply (natDegree_add_le _ _).trans
      rw [natDegree_C]
      exact max_le le_rfl (Nat.zero_le _)
    omega

/-! ### 应用到 `P_m` -/

/-- `ℚ(x)` 中的 `P_m`。 -/
noncomputable def PK (m : ℕ) : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) (Ppoly ℚ m)

/-- `L(m) = 1 − x − (m+1)·x³ ∈ ℚ(x)[m]`。 -/
noncomputable def Lgos : (RatFunc ℚ)[X] :=
  C (-(RatFunc.X ^ 3)) * X + C (1 - RatFunc.X - RatFunc.X ^ 3)

/-- 辅助引理（T2.7）。 -/
theorem natDegree_Lgos : Lgos.natDegree = 1 := by
  rw [Lgos]
  apply natDegree_linear
  rw [neg_ne_zero]
  exact pow_ne_zero 3 RatFunc.X_ne_zero

/-- 辅助引理（T2.7）：`P_{m+1} = P_m·L(m)`。 -/
theorem PK_succ (m : ℕ) : PK (m + 1) = PK m * Lgos.eval (m : RatFunc ℚ) := by
  have hb : algebraMap ℚ[X] (RatFunc ℚ) (bpoly ℚ (m + 1)) =
      1 - RatFunc.X - ((m : RatFunc ℚ) + 1) * RatFunc.X ^ 3 := by
    simp [bpoly, RatFunc.algebraMap_X]
  have hL : Lgos.eval (m : RatFunc ℚ) =
      1 - RatFunc.X - ((m : RatFunc ℚ) + 1) * RatFunc.X ^ 3 := by
    simp only [Lgos, eval_add, eval_mul, eval_C, eval_X]
    ring
  rw [PK, PK, Ppoly_succ, map_mul, hb, hL]

/-- 辅助引理（T2.7）：`P_m ≠ 0`。 -/
theorem PK_ne_zero (m : ℕ) : PK m ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (Ppoly_ne_zero m)

/-- **T2.7**（前半）：取基域 `ℚ(x)`，部分和 `Σ_{j<m} P_j` 关于 `m` 不等于任何超几何项加常数
（不是 Gosper 可和的）：不存在超几何项 `T`（`IsHyperTerm`）与常数 `c ∈ ℚ(x)`，使
`Σ_{j<m} P_j = T(m) + c` 对充分大的 `m` 成立。 -/
theorem partialSum_P_not_hypergeometric :
    ¬ ∃ (T : ℕ → RatFunc ℚ) (c : RatFunc ℚ), IsHyperTerm T ∧
      ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∑ j ∈ range m, PK j = T m + c := by
  rintro ⟨T, c, ⟨p, q, hq, m1, hrec⟩, m0, hsum⟩
  set M := max m0 m1 with hM
  -- `T(m+1) = T(m) + P_m`
  have hT : ∀ m, M ≤ m → T (m + 1) = T m + PK m := by
    intro m hm
    have h1 := hsum (m + 1) (by omega)
    have h2 := hsum m (by omega)
    rw [sum_range_succ, h2] at h1
    linear_combination -h1
  set D := p - q with hDdef
  -- `D(m)·T(m) = q(m)·P_m`
  have hDT : ∀ m, M ≤ m → D.eval (m : RatFunc ℚ) * T m = q.eval (m : RatFunc ℚ) * PK m := by
    intro m hm
    have h1 := hrec m (by omega)
    rw [hT m hm] at h1
    rw [hDdef, eval_sub]
    linear_combination -h1
  have hD : D ≠ 0 := by
    intro hD0
    apply hq
    apply eq_zero_of_eval_nat_ge q M
    intro m hm
    have h1 := hDT m hm
    rw [hD0, eval_zero, zero_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (PK_ne_zero m)
  -- 多项式恒等式 `D·q(m+1)·L = D(m+1)·(q + D)` 在 `m ≥ M` 处成立
  have hE : ∀ m, M ≤ m → (D * q.comp (X + 1) * Lgos - D.comp (X + 1) * (q + D)).eval
      (m : RatFunc ℚ) = 0 := by
    intro m hm
    have h0 := hDT m hm
    have h1 := hDT (m + 1) (by omega)
    have h2 := hT m hm
    have h3 := PK_succ m
    rw [Nat.cast_succ] at h1
    have hP := PK_ne_zero m
    have key : PK m * (D * q.comp (X + 1) * Lgos - D.comp (X + 1) * (q + D)).eval
        (m : RatFunc ℚ) = 0 := by
      simp only [eval_sub, eval_mul, eval_add, eval_comp, eval_X, eval_one]
      rw [h3] at h1
      linear_combination -(D.eval (m : RatFunc ℚ)) * h1 + D.eval ((m : RatFunc ℚ) + 1) * h0
        + D.eval (m : RatFunc ℚ) * D.eval ((m : RatFunc ℚ) + 1) * h2
    exact (mul_eq_zero.mp key).resolve_left hP
  have hpoly := eq_zero_of_eval_nat_ge _ M hE
  exact no_gosper_solution Lgos natDegree_Lgos q D hD (sub_eq_zero.mp hpoly)

end A207123
