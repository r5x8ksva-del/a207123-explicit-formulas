import A207123.Poly
import A207123.Reduction

/-!
# 报告 T1.9（(C8)）：奇偶分解 a_k(n) = p(n) + (−1)^n q(n)、次数与首项、母函数的最简分母与最小递推阶

## 形式化了什么

报告 `notes/report_parts/02_C1.md` 的 **T1.9** 原文：「由 T1.0(a) 与 T1.2：a_k(n)=E(n)（n 偶）或 O(n)（n 奇），
E(n)=u_k(n/2)²、O(n)=u_k((n+1)/2)u_k((n−1)/2) 都是 2k 次多项式，故 a_k(n)=p(n)+(−1)^n q(n)；展开
u(y+h)u(y−h)=u²+h²(uu''−u'²)+O(h⁴) 得 deg q=2k−2（首项 c²k/(2·4^k)，c=lc u_k），deg p=2k（首项 c²/4^k）；
两部分 g.f. 的分子在 x=±1 处非零，所以 g.f. 最简分母恰为 (1−x)^{2k+1}(1+x)^{2k−1}，最小递推阶 4k。」
（`notes/c1.md` §10 给出 p=(E+O)/2、q=(E−O)/2；那里的 c 只对 k ≥ 1 给出：k ≥ 2 时 2/k!，k = 1 时 1。）

1. 奇偶分解（一切 k ≥ 0）：
   * `a_eq_evenPart`、`a_eq_oddPart`：n 偶时 a_k(n) = E(n)，n 奇时 a_k(n) = O(n)；
     `natDegree_evenPart`、`natDegree_oddPart`：E、O 都是 2k 次；
   * `a_eq_parity`：对一切 n ≥ 0，a_k(n) = p(n) + (−1)ⁿ q(n)，p = (E+O)/2、q = (E−O)/2；
   * `parity_unique`、`existsUnique_parity`：满足该式的 (p, q) ∈ ℚ[X]² 存在且唯一。
2. 次数与首项（c = lc u_k；由 T1.2，k ≤ 1 时 c = 1，k ≥ 2 时 c = 2/k!）：
   * `natDegree_parP`、`leadingCoeff_parP`：deg p = 2k，lc p = c²/4^k；
   * `natDegree_parQ`、`leadingCoeff_parQ`（k ≥ 1）：deg q = 2k−2，lc q = c²k/(2·4^k)；
     `parQ_zero`：k = 0 时 q = 0；
   * k = 1 的核对：`parQ_one`（q = 1/8，常数）、`parP_one`（p = x²/4 + x + 7/8）、`a_one_formula`。
3. 母函数（k ≥ 1）：
   * `gf_parP`：(1−x)^{2k+1}·Σ_n p(n)xⁿ = A(x)，A ∈ ℚ[x]，deg A ≤ 2k，A(1) = (2k)!·c²/4^k ≠ 0
     （这一条对 k = 0 也成立）；
   * `gf_parQ`：(1+x)^{2k−1}·Σ_n (−1)ⁿ q(n)xⁿ = B(x)，deg B ≤ 2k−2，B(−1) = (2k−2)!·c²k/(2·4^k) ≠ 0；
   * `gf_aSer`：(1−x)^{2k+1}(1+x)^{2k−1}·Σ_n a_k(n)xⁿ = Num(x)，deg Num < 4k，Num(1) ≠ 0，Num(−1) ≠ 0；
     `isCoprime_parDen`：Num 与 (1−x)^{2k+1}(1+x)^{2k−1} 互素；`parDen_dvd_of_mul_aSer`：任何使
     C·Σ_n a_k(n)xⁿ 成为多项式的 C ∈ ℚ[x] 都被 (1−x)^{2k+1}(1+x)^{2k−1} 整除，即最简分母恰为它；
   * `parity_recurrence`（4k 阶递推存在）、`parity_order_lower_bound`（任何系数不全为零的递推，即使只要求
     对充分大的 n 成立，阶也 ≥ 4k）、`parity_min_order`：最小线性递推阶恰为 4k。
4. 汇总定理 `T1_9`。
5. k = 0 的边界（反例，见文末「发现的问题」）：`a_zero_left`（a_0(n) ≡ 1）、`parity_min_order_zero`
   （k = 0 时最小递推阶是 1，不是 4k = 0）。

## 定义怎么取

* `halfU k = u_k(x/2)`（`Poly.lean` 的 `upoly k` 复合 x ↦ x/2）；`evenPart k = E = (halfU k)²`；
  `oddPart k = O = halfU k(x+1)·halfU k(x−1)`。于是 E(n) = u_k(n/2)²、O(n) = u_k((n+1)/2)·u_k((n−1)/2)
  （`eval_evenPart`、`eval_oddPart`），与报告一致；`parP k = (E+O)/2`、`parQ k = (E−O)/2`，与 `c1.md` §10 一致。
  由 T1.2（`existsUnique_upoly`），`upoly k` 就是唯一满足 u(m) = U_k(m)（m ≥ 0）的多项式 u_k。
* `a k n` 是 `Reduction.lean` 中按原题定义的 n×k 0/1 矩阵个数，这里只通过 `a_eq`（T1.0(a)）使用；
  所有等式都在 ℚ 中陈述（`(a k n : ℚ)`）。
* 母函数是 ℚ 上的形式幂级数：`aSer k = Σ_n a_k(n)xⁿ`，`altSer ε f = Σ_n εⁿ f(n)xⁿ`。
  「g.f. = A(x)/(1−x)^{2k+1}」写成 (1−x)^{2k+1}·Σ_n p(n)xⁿ = A（1−x 在 ℚ⟦x⟧ 中可逆，两者等价）。
* 「最简分母恰为 D」写成：D·F 是多项式，且对任何多项式 C，只要 C·F 是多项式就有 D ∣ C
  （与 `Recurrence.lean` 的 `P_dvd_of_mul_G_poly` 同一写法）；另外 D(0) = 1（`coeff_zero_parDen`）。
  「最小递推阶」与 `Recurrence.lean` 的 `min_order` 同一写法：ℚ 系数、γ_0 = 1、对一切 n ≥ d 成立的
  Σ_{i=0}^{d} γ_i·a_k(n−i) = 0 中 d 的最小值。
* `taylor r f = f(x + r)`（Mathlib 的 `Polynomial.taylor`）。

## 证明路线

* 奇偶分解：`a_eq` 给出 a_k(2j) = U_k(j)²、a_k(2j+1) = U_k(j+1)·U_k(j)，再用 `upoly_eval_nat`。
  唯一性：若 p'(n) + (−1)ⁿq'(n) 也等于 a_k(n)，则 p'+q' 与 p+q 在一切偶数处相等，p'−q' 与 p−q 在一切奇数处
  相等；无穷多点相等的多项式相等。
* 次数与首项：E、O 的首项都是 (c/2^k)²，所以 p = (E+O)/2 的首项是 c²/4^k。对 q，令 g = halfU k
  （deg g = k，lc g = c/2^k），则 E − O = g(x)² − g(x+1)·g(x−1)。报告用导数展开
  u(y+h)u(y−h) = u² + h²(uu''−u'²) + O(h⁴)；这里换成等价的系数计算（`sq_sub_taylor_mul_taylor`）：
  记 A = g(x+1) − g(x)、B = g(x−1) − g(x)，则 g² − g(x+1)g(x−1) = −(g·(A+B) + A·B)；
  由 Taylor 系数公式（`coeff_taylor_eq_sum`），一阶差分 A、B 的次数 ≤ k−1，x^{k−1} 系数为 ±k·lc g
  （`taylor_sub_self`）；A + B = −(A(x−1) − A(x)) 再用一次一阶差分，次数 ≤ k−2，x^{k−2} 系数为
  k(k−1)·lc g。合起来 E − O 的次数 ≤ 2k−2，x^{2k−2} 系数为 −(k(k−1) − k²)(lc g)² = k·c²/4^k，
  所以 lc q = c²k/(2·4^k)。这正是报告中 h²(u'²−uu'') 的首项 h²·kc²·y^{2k−2} 在 y = n/2、h = 1/2 时的值。
* 母函数：`gf_poly`：若 deg f ≤ d、ε² = 1，则 (1−εx)^{d+1}·Σ_n εⁿf(n)xⁿ 是次数 ≤ d 的多项式 A，
  A(ε) = d!·[x^d]f。对 d 归纳，关键是 (1−εx)·Σ εⁿf(n)xⁿ = Σ εⁿ(f(n)−f(n−1))xⁿ + f(−1)
  （`one_sub_mul_altSer`），一阶差分次数降 1，x^d 系数为 (d+1)·[x^{d+1}]f。取 ε = 1、f = p、d = 2k 得 A；
  取 ε = −1、f = q、d = 2k−2 得 B。Num = A·(1+x)^{2k−1} + B·(1−x)^{2k+1}，Num(1) = 2^{2k−1}·A(1) ≠ 0，
  Num(−1) = 2^{2k+1}·B(−1) ≠ 0，所以 Num 与一次不可约式 1∓x 都互素。最简分母与最小阶的论证照搬
  `Recurrence.lean` 的 `P_dvd_of_mul_G_poly`、`order_lower_bound`、`min_order`
  （报告引用的「有理序列的最小阶 = 既约分母次数」没有作为一般引理单独形式化，而是对本例直接证明）。

## 没有形式化的部分

* 报告证明中的导数展开式 u(y+h)u(y−h) = u² + h²(uu''−u'²) + O(h⁴) 本身没有形式化；上面改用系数计算，
  只证明了结论需要的部分（次数 ≤ 2k−2，且 n^{2k−2} 系数为 kc²/4^k）。
* T1.9 末句「c5b 用 OEIS 快照核对了 A207118–A207122 的经验递推与此一致（见 T5.4）」是对外部 OEIS 数据的核对，
  「核对：c1.C8-pq」是 Python 数值核对，两者都不在 Lean 中。
* 除此之外，T1.9 的陈述（奇偶分解与唯一性、deg/lc、两部分 g.f. 与分子在 ±1 处非零、最简分母、
  最小递推阶 4k）全部形式化了。

## 发现的问题：T1.9 原文缺条件 k ≥ 1

02_C1.md 的 T1.9 原文（以及任务说明 (C8) 的「对所有 k」）没有写 k ≥ 1，但「deg q = 2k−2」「最简分母
(1−x)^{2k+1}(1+x)^{2k−1}」「最小递推阶 4k」都只对 k ≥ 1 成立。反例 k = 0：a_0(n) ≡ 1（`a_zero_left`），
q = 0（`parQ_zero`），Σ a_0(n)xⁿ = 1/(1−x)，(1+x)^{2k−1} = (1+x)^{−1} 不是多项式，最小递推阶是 1 而不是 4k = 0
（`parity_min_order_zero`）。`notes/c1.md` §10 只对 k ≥ 1 定义了 c，本文件的相应定理都带 `1 ≤ k`。
奇偶分解与唯一性、deg p = 2k、lc p = c²/4^k 对 k = 0 也成立，那里不需要这个条件。
-/

namespace A207123

open Polynomial Finset

/-! ## 定义 -/

/-- `g_k(n) := u_k(n/2)`，即 `upoly k` 复合 `n ↦ n/2`。 -/
noncomputable def halfU (k : ℕ) : ℚ[X] := (upoly k).comp (C (1 / 2 : ℚ) * X)

/-- 报告的 `E(n) = u_k(n/2)²`（作为 `n` 的多项式）。 -/
noncomputable def evenPart (k : ℕ) : ℚ[X] := halfU k ^ 2

/-- 报告的 `O(n) = u_k((n+1)/2)·u_k((n−1)/2)`（作为 `n` 的多项式）。 -/
noncomputable def oddPart (k : ℕ) : ℚ[X] := (halfU k).comp (X + 1) * (halfU k).comp (X - 1)

/-- 报告的 `p = (E + O)/2`。 -/
noncomputable def parP (k : ℕ) : ℚ[X] := C (1 / 2 : ℚ) * (evenPart k + oddPart k)

/-- 报告的 `q = (E − O)/2`。 -/
noncomputable def parQ (k : ℕ) : ℚ[X] := C (1 / 2 : ℚ) * (evenPart k - oddPart k)

/-! ## 取值 -/

/-- 辅助引理（T1.9）：`g_k(x) = u_k(x/2)`。 -/
theorem eval_halfU (k : ℕ) (x : ℚ) : (halfU k).eval x = (upoly k).eval (x / 2) := by
  rw [halfU, eval_comp, eval_mul, eval_C, eval_X]
  ring_nf

/-- 辅助引理（T1.9）：`E(x) = u_k(x/2)²`。 -/
theorem eval_evenPart (k : ℕ) (x : ℚ) : (evenPart k).eval x = (upoly k).eval (x / 2) ^ 2 := by
  rw [evenPart, eval_pow, eval_halfU]

/-- 辅助引理（T1.9）：`O(x) = u_k((x+1)/2)·u_k((x−1)/2)`。 -/
theorem eval_oddPart (k : ℕ) (x : ℚ) :
    (oddPart k).eval x = (upoly k).eval ((x + 1) / 2) * (upoly k).eval ((x - 1) / 2) := by
  rw [oddPart, eval_mul, eval_comp, eval_comp, eval_add, eval_sub, eval_X, eval_one, eval_halfU,
    eval_halfU]

/-- 辅助引理（T1.9）：`p + q = E`。 -/
theorem eval_parP_add_parQ (k : ℕ) (x : ℚ) :
    (parP k).eval x + (parQ k).eval x = (evenPart k).eval x := by
  rw [parP, parQ, eval_mul, eval_mul, eval_C, eval_add, eval_sub]
  ring

/-- 辅助引理（T1.9）：`p − q = O`。 -/
theorem eval_parP_sub_parQ (k : ℕ) (x : ℚ) :
    (parP k).eval x - (parQ k).eval x = (oddPart k).eval x := by
  rw [parP, parQ, eval_mul, eval_mul, eval_C, eval_add, eval_sub]
  ring

/-! ## T1.9 第一部分：`a_k(n) = p(n) + (−1)^n q(n)`，`p`、`q` 唯一 -/

/-- 辅助引理（T1.9，由 T1.0(a) `a_eq`）：`a_k(2j) = U_k(j)²`。 -/
theorem a_even (k j : ℕ) : (a k (2 * j) : ℚ) = (U k j : ℚ) ^ 2 := by
  rw [a_eq, show (2 * j + 1) / 2 = j by omega, show 2 * j / 2 = j by omega]
  push_cast
  ring

/-- 辅助引理（T1.9，由 T1.0(a) `a_eq`）：`a_k(2j+1) = U_k(j+1)·U_k(j)`。 -/
theorem a_odd (k j : ℕ) : (a k (2 * j + 1) : ℚ) = (U k (j + 1) : ℚ) * (U k j : ℚ) := by
  rw [a_eq, show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1) / 2 = j by omega]
  push_cast
  ring

/-- 辅助引理（T1.9）：n 偶时 `a_k(n) = E(n)`。 -/
theorem a_eq_evenPart (k j : ℕ) : (a k (2 * j) : ℚ) = (evenPart k).eval ((2 * j : ℕ) : ℚ) := by
  rw [a_even, eval_evenPart]
  push_cast
  rw [show 2 * (j : ℚ) / 2 = (j : ℚ) by ring, upoly_eval_nat]

/-- 辅助引理（T1.9）：n 奇时 `a_k(n) = O(n)`。 -/
theorem a_eq_oddPart (k j : ℕ) :
    (a k (2 * j + 1) : ℚ) = (oddPart k).eval ((2 * j + 1 : ℕ) : ℚ) := by
  rw [a_odd, eval_oddPart]
  push_cast
  rw [show (2 * (j : ℚ) + 1 + 1) / 2 = ((j + 1 : ℕ) : ℚ) by push_cast; ring,
    show (2 * (j : ℚ) + 1 - 1) / 2 = (j : ℚ) by ring, upoly_eval_nat, upoly_eval_nat]

/-- **T1.9**（存在性）：对一切 `n ≥ 0`，`a_k(n) = p(n) + (−1)^n·q(n)`，
其中 `p = (E+O)/2`、`q = (E−O)/2`。 -/
theorem a_eq_parity (k n : ℕ) :
    (a k n : ℚ) = (parP k).eval (n : ℚ) + (-1) ^ n * (parQ k).eval (n : ℚ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [a_eq_evenPart, ← eval_parP_add_parQ, pow_mul]
    norm_num
  · rw [a_eq_oddPart, ← eval_parP_sub_parQ, pow_succ, pow_mul]
    norm_num
    ring

/-- 辅助引理（T1.9）：两个多项式若在一切偶数 `2j` 处取值相同，则相等。 -/
theorem eq_of_eval_even_nat {f g : ℚ[X]}
    (h : ∀ j : ℕ, f.eval ((2 * j : ℕ) : ℚ) = g.eval ((2 * j : ℕ) : ℚ)) : f = g := by
  apply eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun j : ℕ => ((2 * j : ℕ) : ℚ)) := by
    intro x y hxy
    have := Nat.cast_injective (R := ℚ) hxy
    omega
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨j, rfl⟩
  exact h j

/-- 辅助引理（T1.9）：两个多项式若在一切奇数 `2j+1` 处取值相同，则相等。 -/
theorem eq_of_eval_odd_nat {f g : ℚ[X]}
    (h : ∀ j : ℕ, f.eval ((2 * j + 1 : ℕ) : ℚ) = g.eval ((2 * j + 1 : ℕ) : ℚ)) : f = g := by
  apply eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun j : ℕ => ((2 * j + 1 : ℕ) : ℚ)) := by
    intro x y hxy
    have := Nat.cast_injective (R := ℚ) hxy
    omega
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨j, rfl⟩
  exact h j

/-- **T1.9**（唯一性）：若 `p'`、`q'` 满足 `a_k(n) = p'(n) + (−1)^n q'(n)`（一切 `n ≥ 0`），则
`p' = p`、`q' = q`。 -/
theorem parity_unique (k : ℕ) {p q : ℚ[X]}
    (h : ∀ n : ℕ, (a k n : ℚ) = p.eval (n : ℚ) + (-1) ^ n * q.eval (n : ℚ)) :
    p = parP k ∧ q = parQ k := by
  have h1 : p + q = parP k + parQ k := by
    apply eq_of_eval_even_nat
    intro j
    have e1 := h (2 * j)
    have e2 := a_eq_parity k (2 * j)
    rw [pow_mul] at e1 e2
    norm_num at e1 e2
    rw [eval_add, eval_add]
    push_cast
    linarith
  have h2 : p - q = parP k - parQ k := by
    apply eq_of_eval_odd_nat
    intro j
    have e1 := h (2 * j + 1)
    have e2 := a_eq_parity k (2 * j + 1)
    rw [pow_succ, pow_mul] at e1 e2
    norm_num at e1 e2
    rw [eval_sub, eval_sub]
    push_cast
    linarith
  refine ⟨Polynomial.funext fun x => ?_, Polynomial.funext fun x => ?_⟩
  · have e1 := congrArg (eval x) h1
    have e2 := congrArg (eval x) h2
    simp only [eval_add, eval_sub] at e1 e2
    linarith
  · have e1 := congrArg (eval x) h1
    have e2 := congrArg (eval x) h2
    simp only [eval_add, eval_sub] at e1 e2
    linarith

/-- **T1.9**（第一部分）：存在唯一的一对 `(p, q) ∈ ℚ[X] × ℚ[X]`，使 `a_k(n) = p(n) + (−1)^n·q(n)`
对一切 `n ≥ 0` 成立；这一对就是 `(parP k, parQ k) = ((E+O)/2, (E−O)/2)`。 -/
theorem existsUnique_parity (k : ℕ) :
    ∃! pq : ℚ[X] × ℚ[X],
      ∀ n : ℕ, (a k n : ℚ) = pq.1.eval (n : ℚ) + (-1) ^ n * pq.2.eval (n : ℚ) := by
  refine ⟨(parP k, parQ k), a_eq_parity k, ?_⟩
  rintro ⟨p, q⟩ h
  obtain ⟨rfl, rfl⟩ := parity_unique k h
  rfl

/-! ## 移位多项式的系数 -/

/-- 辅助引理（T1.9）：`f(x+h)` 的 `x^j` 系数 `= Σ_{i<N} C(i+j, j)·f_{i+j}·h^i`
（条件 `deg f < N + j`，`N ≥ 1`；由 Mathlib 的 `taylor_coeff` 与 `hasseDeriv_coeff`）。 -/
theorem coeff_taylor_eq_sum (h : ℚ) (f : ℚ[X]) (j N : ℕ) (hN0 : 0 < N)
    (hN : f.natDegree < N + j) :
    (taylor h f).coeff j = ∑ i ∈ range N, ((i + j).choose j : ℚ) * f.coeff (i + j) * h ^ i := by
  have hd : (hasseDeriv j f).natDegree < N := by
    have := natDegree_hasseDeriv_le f j
    omega
  rw [taylor_coeff, eval_eq_sum_range' hd]
  refine sum_congr rfl fun i _ => ?_
  rw [hasseDeriv_coeff]

/-- 辅助引理（T1.9，一阶差分）：若 `deg f ≤ m+1`，则 `f(x+h) − f(x)` 的次数 `≤ m`，
`x^m` 系数为 `(m+1)·h·f_{m+1}`。 -/
theorem taylor_sub_self (h : ℚ) (f : ℚ[X]) (m : ℕ) (hf : f.natDegree ≤ m + 1) :
    (taylor h f - f).natDegree ≤ m ∧
      (taylor h f - f).coeff m = ((m : ℚ) + 1) * h * f.coeff (m + 1) := by
  have hc1 : (taylor h f).coeff (m + 1) = f.coeff (m + 1) := by
    rw [coeff_taylor_eq_sum h f (m + 1) 1 (by omega) (by omega), sum_range_one]
    simp
  have hc0 : (taylor h f).coeff m = f.coeff m + ((m : ℚ) + 1) * f.coeff (m + 1) * h := by
    rw [coeff_taylor_eq_sum h f m 2 (by omega) (by omega), sum_range_succ, sum_range_one]
    simp only [zero_add, Nat.choose_self, Nat.cast_one, pow_zero, mul_one, one_mul, pow_one]
    rw [add_comm 1 m, Nat.choose_succ_self_right]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [coeff_sub]
    rcases (by omega : j = m + 1 ∨ m + 1 < j) with rfl | hlt
    · rw [hc1, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; omega),
        coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  · rw [coeff_sub, hc0]
    ring

/-- 辅助引理（T1.9，报告的 `u(y+h)u(y−h) = u² + h²(uu''−u'²) + O(h⁴)` 在 `h = 1` 的系数形式）：
若 `deg f ≤ m+1`，则 `f(x)² − f(x+1)·f(x−1)` 的次数 `≤ 2m`，`x^{2m}` 系数为 `(m+1)·f_{m+1}²`。 -/
theorem sq_sub_taylor_mul_taylor (f : ℚ[X]) (m : ℕ) (hf : f.natDegree ≤ m + 1) :
    (f ^ 2 - taylor 1 f * taylor (-1) f).natDegree ≤ 2 * m ∧
      (f ^ 2 - taylor 1 f * taylor (-1) f).coeff (2 * m) =
        ((m : ℚ) + 1) * f.coeff (m + 1) ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℚ[X], A = taylor 1 f - f := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℚ[X], B = taylor (-1) f - f := ⟨_, rfl⟩
  obtain ⟨hA1, hA2⟩ := taylor_sub_self 1 f m hf
  obtain ⟨hB1, hB2⟩ := taylor_sub_self (-1) f m hf
  rw [← hA] at hA1 hA2
  rw [← hB] at hB1 hB2
  have hsum : A + B = -(taylor (-1) A - A) := by
    rw [hA, hB, map_sub, taylor_taylor, show (-1 : ℚ) + 1 = 0 by norm_num, taylor_zero]
    ring
  have hD : f ^ 2 - taylor 1 f * taylor (-1) f = -(f * (A + B) + A * B) := by
    rw [hA, hB]
    ring
  have hAB1 : (A * B).natDegree ≤ m + m := natDegree_mul_le_of_le hA1 hB1
  have hAB2 : (A * B).coeff (m + m) = A.coeff m * B.coeff m :=
    coeff_mul_add_eq_of_natDegree_le hA1 hB1
  rw [hD, natDegree_neg, coeff_neg]
  rcases m with _ | l
  · -- `m = 0`：`A` 是常数，`A + B = 0`
    have hA0 : A = C (A.coeff 0) := eq_C_of_natDegree_le_zero hA1
    have hsum0 : A + B = 0 := by rw [hsum, hA0, taylor_C, sub_self, neg_zero]
    rw [hsum0, mul_zero, zero_add]
    refine ⟨by simpa using hAB1, ?_⟩
    simp only [Nat.mul_zero, Nat.add_zero] at hAB2 ⊢
    rw [hAB2, hA2, hB2]
    push_cast
    ring
  · -- `m = l + 1`：`A + B = −(A(x−1) − A(x))`，再用一次一阶差分
    obtain ⟨hC1, hC2⟩ := taylor_sub_self (-1) A l hA1
    have hS1 : (A + B).natDegree ≤ l := by rw [hsum, natDegree_neg]; exact hC1
    have hS2 : (A + B).coeff l = ((l : ℚ) + 1) * A.coeff (l + 1) := by
      rw [hsum, coeff_neg, hC2]
      ring
    have hFS1 : (f * (A + B)).natDegree ≤ l + 1 + 1 + l := natDegree_mul_le_of_le hf hS1
    have hFS2 : (f * (A + B)).coeff (2 * (l + 1)) = f.coeff (l + 1 + 1) * (A + B).coeff l := by
      rw [show 2 * (l + 1) = l + 1 + 1 + l by ring]
      exact coeff_mul_add_eq_of_natDegree_le hf hS1
    have hAB2' : (A * B).coeff (2 * (l + 1)) = A.coeff (l + 1) * B.coeff (l + 1) := by
      rw [show 2 * (l + 1) = l + 1 + (l + 1) by ring]
      exact hAB2
    refine ⟨(natDegree_add_le _ _).trans (max_le (hFS1.trans (by omega)) (hAB1.trans (by omega))),
      ?_⟩
    rw [coeff_add, hFS2, hAB2', hS2, hA2, hB2]
    push_cast
    ring

/-! ## T1.9 第二部分：次数与首项系数 -/

/-- 辅助引理（T1.9）：`c = lc u_k ≠ 0`（由 T1.2：`k ≤ 1` 时为 1，`k ≥ 2` 时为 `2/k!`）。 -/
theorem leadingCoeff_upoly_ne_zero (k : ℕ) : (upoly k).leadingCoeff ≠ 0 := by
  rw [leadingCoeff_upoly_eq]
  split_ifs
  · exact one_ne_zero
  · exact div_ne_zero two_ne_zero (by exact_mod_cast (Nat.factorial_pos k).ne')

/-- 辅助引理（T1.9）：`deg g_k = k`。 -/
theorem natDegree_halfU (k : ℕ) : (halfU k).natDegree = k := by
  rw [halfU, natDegree_comp, natDegree_upoly, natDegree_C_mul_X _ (by norm_num), mul_one]

/-- 辅助引理（T1.9）：`lc g_k = c·(1/2)^k`。 -/
theorem leadingCoeff_halfU (k : ℕ) :
    (halfU k).leadingCoeff = (upoly k).leadingCoeff * (1 / 2) ^ k := by
  rw [halfU, leadingCoeff_comp (by rw [natDegree_C_mul_X _ (by norm_num)]; norm_num),
    leadingCoeff_C_mul_X, natDegree_upoly]

/-- 辅助引理（T1.9）：`g_k ≠ 0`。 -/
theorem halfU_ne_zero (k : ℕ) : halfU k ≠ 0 := by
  intro h
  have := leadingCoeff_halfU k
  rw [h, leadingCoeff_zero] at this
  exact mul_ne_zero (leadingCoeff_upoly_ne_zero k) (by positivity) this.symm

/-- 辅助引理（T1.9）：`O(x) = g(x+1)·g(x−1)`，用 `taylor r g = g(x + r)` 写出。 -/
theorem oddPart_eq_taylor (k : ℕ) :
    oddPart k = taylor 1 (halfU k) * taylor (-1) (halfU k) := by
  rw [oddPart, taylor_apply, taylor_apply, map_neg, map_one, ← sub_eq_add_neg]

/-- 辅助引理（T1.9）：`deg E = 2k`（报告：E 是 2k 次多项式）。 -/
theorem natDegree_evenPart (k : ℕ) : (evenPart k).natDegree = 2 * k := by
  rw [evenPart, natDegree_pow, natDegree_halfU]

/-- 辅助引理（T1.9）：`deg O = 2k`（报告：O 是 2k 次多项式）。 -/
theorem natDegree_oddPart (k : ℕ) : (oddPart k).natDegree = 2 * k := by
  have h0 : ∀ r : ℚ, taylor r (halfU k) ≠ 0 := fun r h =>
    halfU_ne_zero k ((taylor_eq_zero r (halfU k)).mp h)
  rw [oddPart_eq_taylor, natDegree_mul (h0 1) (h0 (-1)), natDegree_taylor, natDegree_taylor,
    natDegree_halfU]
  ring

/-- 辅助引理（T1.9）：`E`、`O` 的 `x^{2k}` 系数都是 `(lc g_k)²`。 -/
theorem coeff_evenPart_oddPart (k : ℕ) :
    (evenPart k).coeff (2 * k) = (halfU k).leadingCoeff ^ 2 ∧
      (oddPart k).coeff (2 * k) = (halfU k).leadingCoeff ^ 2 := by
  constructor
  · rw [← natDegree_evenPart k, coeff_natDegree, evenPart, leadingCoeff_pow]
  · rw [← natDegree_oddPart k, coeff_natDegree, oddPart_eq_taylor, leadingCoeff_mul,
      leadingCoeff_taylor, leadingCoeff_taylor, sq]

/-- 辅助引理（T1.9）：`(c·(1/2)^k)² = c²/4^k`。 -/
theorem sq_mul_half_pow (c : ℚ) (k : ℕ) : (c * (1 / 2) ^ k) ^ 2 = c ^ 2 / 4 ^ k := by
  have h : ((1 / 2 : ℚ) ^ k) ^ 2 = 1 / 4 ^ k := by
    rw [← pow_mul, pow_mul', one_div_pow, one_div_pow]
    norm_num
  rw [mul_pow, h, mul_one_div]

/-- 辅助引理（T1.9）：`p` 的 `x^{2k}` 系数是 `(lc g_k)²`。 -/
theorem coeff_parP_two_mul (k : ℕ) : (parP k).coeff (2 * k) = (halfU k).leadingCoeff ^ 2 := by
  obtain ⟨h1, h2⟩ := coeff_evenPart_oddPart k
  rw [parP, coeff_C_mul, coeff_add, h1, h2]
  ring

/-- **T1.9**：`deg p = 2k`。 -/
theorem natDegree_parP (k : ℕ) : (parP k).natDegree = 2 * k := by
  have hle : (parP k).natDegree ≤ 2 * k := by
    rw [parP]
    refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans ?_)
    rw [natDegree_evenPart, natDegree_oddPart, max_self]
  refine natDegree_eq_of_le_of_coeff_ne_zero hle ?_
  rw [coeff_parP_two_mul]
  exact pow_ne_zero 2 (leadingCoeff_ne_zero.mpr (halfU_ne_zero k))

/-- **T1.9**：`p` 的首项系数是 `c²/4^k`（`c = lc u_k`）。 -/
theorem leadingCoeff_parP (k : ℕ) :
    (parP k).leadingCoeff = (upoly k).leadingCoeff ^ 2 / 4 ^ k := by
  rw [leadingCoeff, natDegree_parP, coeff_parP_two_mul, leadingCoeff_halfU, sq_mul_half_pow]

/-- 辅助引理（T1.9）：`q = (g² − g(x+1)g(x−1))/2`。 -/
theorem parQ_eq (k : ℕ) :
    parQ k = C (1 / 2 : ℚ) * (halfU k ^ 2 - taylor 1 (halfU k) * taylor (-1) (halfU k)) := by
  rw [parQ, evenPart, oddPart_eq_taylor]

/-- 辅助引理（T1.9）：`k ≥ 1` 时 `deg q ≤ 2k−2`，且 `x^{2k−2}` 系数为 `k·(lc g_k)²/2`。 -/
theorem coeff_parQ (k : ℕ) (hk : 1 ≤ k) :
    (parQ k).natDegree ≤ 2 * k - 2 ∧
      (parQ k).coeff (2 * k - 2) = (1 / 2) * (k : ℚ) * (halfU k).leadingCoeff ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hdeg : (halfU (m + 1)).natDegree ≤ m + 1 := (natDegree_halfU _).le
  obtain ⟨h1, h2⟩ := sq_sub_taylor_mul_taylor (halfU (m + 1)) m hdeg
  have hc : (halfU (m + 1)).coeff (m + 1) = (halfU (m + 1)).leadingCoeff := by
    rw [leadingCoeff, natDegree_halfU]
  rw [show 2 * (m + 1) - 2 = 2 * m by omega, parQ_eq]
  refine ⟨(natDegree_C_mul_le _ _).trans h1, ?_⟩
  rw [coeff_C_mul, h2, hc]
  push_cast
  ring

/-- **T1.9**：`k ≥ 1` 时 `deg q = 2k − 2`。 -/
theorem natDegree_parQ (k : ℕ) (hk : 1 ≤ k) : (parQ k).natDegree = 2 * k - 2 := by
  obtain ⟨h1, h2⟩ := coeff_parQ k hk
  refine natDegree_eq_of_le_of_coeff_ne_zero h1 ?_
  rw [h2]
  have : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  exact mul_ne_zero (mul_ne_zero (by norm_num) this)
    (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr (halfU_ne_zero k)))

/-- **T1.9**：`k ≥ 1` 时 `q` 的首项系数是 `c²k/(2·4^k)`（`c = lc u_k`）。 -/
theorem leadingCoeff_parQ (k : ℕ) (hk : 1 ≤ k) :
    (parQ k).leadingCoeff = (upoly k).leadingCoeff ^ 2 * k / (2 * 4 ^ k) := by
  rw [leadingCoeff, natDegree_parQ k hk, (coeff_parQ k hk).2, leadingCoeff_halfU, sq_mul_half_pow]
  ring

/-- 辅助引理（T1.9）：`g_0 = 1`。 -/
theorem halfU_zero : halfU 0 = 1 := by
  rw [halfU, upoly_le_two (by norm_num), pow_zero, one_comp]

/-- **T1.9**：`k = 0` 时 `q = 0`。 -/
theorem parQ_zero : parQ 0 = 0 := by
  rw [parQ, evenPart, oddPart, halfU_zero, one_comp, one_comp]
  ring

/-- **T1.9**（`k = 1` 的核对）：`q = 1/8`（常数）。 -/
theorem parQ_one : parQ 1 = C (1 / 8 : ℚ) := by
  refine Polynomial.funext fun x => ?_
  rw [parQ, eval_mul, eval_C, eval_C, eval_sub, eval_evenPart, eval_oddPart,
    upoly_le_two (by norm_num)]
  simp only [pow_one, eval_add, eval_X, eval_one]
  ring

/-- **T1.9**（`k = 1` 的核对）：`p = x²/4 + x + 7/8`。 -/
theorem parP_one : parP 1 = C (1 / 4 : ℚ) * X ^ 2 + X + C (7 / 8 : ℚ) := by
  refine Polynomial.funext fun x => ?_
  rw [parP, eval_mul, eval_C, eval_add, eval_evenPart, eval_oddPart, upoly_le_two (by norm_num)]
  simp only [pow_one, eval_add, eval_X, eval_one, eval_mul, eval_C, eval_pow]
  ring

/-- **T1.9**（`k = 1` 的核对）：`a_1(n) = (2n² + 8n + 7)/8 + (−1)^n/8`
（例如 `a_1(0..4) = 1, 2, 4, 6, 9`）。 -/
theorem a_one_formula (n : ℕ) :
    (a 1 n : ℚ) = (2 * (n : ℚ) ^ 2 + 8 * n + 7) / 8 + (-1) ^ n / 8 := by
  rw [a_eq_parity, parP_one, parQ_one]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-! ## T1.9 第三部分：母函数、最简分母与最小递推阶 -/

/-- `Σ_n ε^n·f(n)·x^n`（`ℚ` 上的形式幂级数）。`ε = 1` 时是 `Σ_n f(n) x^n`，`ε = −1` 时是
`Σ_n (−1)^n f(n) x^n`。 -/
noncomputable def altSer (ε : ℚ) (f : ℚ[X]) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ε ^ n * f.eval (n : ℚ)

/-- `Σ_n a_k(n)·x^n`（`ℚ` 上的形式幂级数）。 -/
noncomputable def aSer (k : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n => (a k n : ℚ)

/-- 报告中的分母 `(1−x)^{2k+1}(1+x)^{2k−1}`。 -/
noncomputable def parDen (k : ℕ) : ℚ[X] := (1 - X) ^ (2 * k + 1) * (1 + X) ^ (2 * k - 1)

/-- 辅助引理（T1.9）：`altSer ε f` 的 `x^n` 系数。 -/
theorem coeff_altSer (ε : ℚ) (f : ℚ[X]) (n : ℕ) :
    PowerSeries.coeff n (altSer ε f) = ε ^ n * f.eval (n : ℚ) := by
  rw [altSer, PowerSeries.coeff_mk]

/-- 辅助引理（T1.9）：`aSer k` 的 `x^n` 系数是 `a_k(n)`。 -/
theorem coeff_aSer (k n : ℕ) : PowerSeries.coeff n (aSer k) = (a k n : ℚ) := by
  rw [aSer, PowerSeries.coeff_mk]

/-- 辅助引理（T1.9）：`altSer ε 0 = 0`。 -/
theorem altSer_zero (ε : ℚ) : altSer ε 0 = 0 := by
  ext n
  rw [coeff_altSer, eval_zero, mul_zero, map_zero]

/-- 辅助引理（T1.9）：`(1 − εx)·Σ ε^n f(n) x^n = Σ ε^n [f(n) − f(n−1)] x^n + f(−1)`。 -/
theorem one_sub_mul_altSer (ε : ℚ) (f : ℚ[X]) :
    (↑(1 - C ε * X : ℚ[X]) : PowerSeries ℚ) * altSer ε f =
      altSer ε (f - taylor (-1) f) + PowerSeries.C (f.eval (-1)) := by
  have e : (↑(1 - C ε * X : ℚ[X]) : PowerSeries ℚ) * altSer ε f =
      altSer ε f - PowerSeries.C ε * (PowerSeries.X * altSer ε f) := by
    rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X]
    ring
  rw [e]
  ext n
  rw [map_sub, map_add, PowerSeries.coeff_C_mul, coeff_altSer, coeff_altSer, PowerSeries.coeff_C,
    eval_sub, taylor_eval]
  rcases n with _ | j
  · rw [PowerSeries.coeff_zero_X_mul]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, coeff_altSer]
    simp only [Nat.cast_add, Nat.cast_one, add_neg_cancel_right, Nat.add_one_ne_zero, ↓reduceIte,
      add_zero]
    ring

/-- 辅助引理（T1.9）：若 `deg f ≤ d` 且 `ε² = 1`，则 `(1 − εx)^{d+1}·Σ_n ε^n f(n) x^n` 是次数 `≤ d` 的
多项式 `A`，且 `A(ε) = d!·f_d`（`f_d` 是 `f` 的 `x^d` 系数）。对 `d` 归纳，每一步用 `one_sub_mul_altSer`
把 `f` 换成一阶差分 `f(n) − f(n−1)`（次数降 1，`x^d` 系数为 `(d+1)·f_{d+1}`）。 -/
theorem gf_poly (ε : ℚ) (hε : ε * ε = 1) (d : ℕ) :
    ∀ f : ℚ[X], f.natDegree ≤ d → ∃ A : ℚ[X], A.natDegree ≤ d ∧
      (↑((1 - C ε * X) ^ (d + 1) : ℚ[X]) : PowerSeries ℚ) * altSer ε f = ↑A ∧
      A.eval ε = (d.factorial : ℚ) * f.coeff d := by
  induction d with
  | zero =>
    intro f hf
    have hfc : f = C (f.coeff 0) := eq_C_of_natDegree_le_zero hf
    have h0 : f - taylor (-1) f = 0 := by rw [hfc, taylor_C, sub_self]
    have h1 : f.eval (-1) = f.coeff 0 := by
      conv_lhs => rw [hfc]
      rw [eval_C]
    refine ⟨C (f.coeff 0), by rw [natDegree_C], ?_, ?_⟩
    · rw [zero_add, pow_one, one_sub_mul_altSer, h0, h1, altSer_zero, zero_add, Polynomial.coe_C]
    · rw [eval_C, Nat.factorial_zero, Nat.cast_one, one_mul]
  | succ d ih =>
    intro f hf
    obtain ⟨h1, h2⟩ := taylor_sub_self (-1) f d hf
    have hf'deg : (f - taylor (-1) f).natDegree ≤ d := by
      rw [← neg_sub, natDegree_neg]
      exact h1
    have hf'coeff : (f - taylor (-1) f).coeff d = ((d : ℚ) + 1) * f.coeff (d + 1) := by
      rw [← neg_sub, coeff_neg, h2]
      ring
    obtain ⟨A', hA'deg, hA'eq, hA'eval⟩ := ih _ hf'deg
    refine ⟨A' + C (f.eval (-1)) * (1 - C ε * X) ^ (d + 1), ?_, ?_, ?_⟩
    · have hlin : (1 - C ε * X : ℚ[X]).natDegree ≤ 1 := by compute_degree
      refine (natDegree_add_le _ _).trans (max_le (hA'deg.trans (Nat.le_succ d)) ?_)
      refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le (d + 1) hlin).trans ?_)
      omega
    · rw [pow_succ (1 - C ε * X) (d + 1), Polynomial.coe_mul, mul_assoc, one_sub_mul_altSer,
        mul_add, hA'eq, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C]
      ring
    · rw [eval_add, hA'eval, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_mul, eval_C,
        eval_X, hε, sub_self, zero_pow (by omega : d + 1 ≠ 0), mul_zero, add_zero, hf'coeff,
        Nat.factorial_succ]
      push_cast
      ring

/-- **T1.9**（母函数的 `p` 部分）：`Σ_n p(n)·x^n = A(x)/(1−x)^{2k+1}`，其中 `A ∈ ℚ[x]`，`deg A ≤ 2k`，
`A(1) = (2k)!·c²/4^k ≠ 0`（`c = lc u_k`）。写成形式幂级数等式 `(1−x)^{2k+1}·Σ_n p(n) x^n = A`。 -/
theorem gf_parP (k : ℕ) :
    ∃ A : ℚ[X], A.natDegree ≤ 2 * k ∧
      (↑((1 - X) ^ (2 * k + 1) : ℚ[X]) : PowerSeries ℚ) *
          PowerSeries.mk (fun n => (parP k).eval (n : ℚ)) = ↑A ∧
      A.eval 1 = ((2 * k).factorial : ℚ) * ((upoly k).leadingCoeff ^ 2 / 4 ^ k) ∧
      A.eval 1 ≠ 0 := by
  obtain ⟨A, h1, h2, h3⟩ := gf_poly 1 (by norm_num) (2 * k) (parP k) (natDegree_parP k).le
  have e1 : PowerSeries.mk (fun n => (parP k).eval (n : ℚ)) = altSer 1 (parP k) := by
    ext n
    rw [PowerSeries.coeff_mk, coeff_altSer, one_pow, one_mul]
  have e2 : (1 - C (1 : ℚ) * X : ℚ[X]) = 1 - X := by rw [map_one, one_mul]
  have hval : A.eval 1 = ((2 * k).factorial : ℚ) * ((upoly k).leadingCoeff ^ 2 / 4 ^ k) := by
    rw [h3, ← leadingCoeff_parP k, leadingCoeff, natDegree_parP]
  refine ⟨A, h1, by rw [e1, ← e2, h2], hval, ?_⟩
  rw [hval]
  exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
    (div_ne_zero (pow_ne_zero 2 (leadingCoeff_upoly_ne_zero k)) (pow_ne_zero k (by norm_num)))

/-- **T1.9**（母函数的 `q` 部分，`k ≥ 1`）：`Σ_n (−1)^n q(n)·x^n = B(x)/(1+x)^{2k−1}`，其中 `B ∈ ℚ[x]`，
`deg B ≤ 2k−2`，`B(−1) = (2k−2)!·c²k/(2·4^k) ≠ 0`。写成形式幂级数等式
`(1+x)^{2k−1}·Σ_n (−1)^n q(n) x^n = B`。 -/
theorem gf_parQ (k : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℚ[X], B.natDegree ≤ 2 * k - 2 ∧
      (↑((1 + X) ^ (2 * k - 1) : ℚ[X]) : PowerSeries ℚ) *
          PowerSeries.mk (fun n => (-1) ^ n * (parQ k).eval (n : ℚ)) = ↑B ∧
      B.eval (-1) = ((2 * k - 2).factorial : ℚ) * ((upoly k).leadingCoeff ^ 2 * k / (2 * 4 ^ k)) ∧
      B.eval (-1) ≠ 0 := by
  obtain ⟨B, h1, h2, h3⟩ :=
    gf_poly (-1) (by norm_num) (2 * k - 2) (parQ k) (natDegree_parQ k hk).le
  have e2 : ((1 - C (-1 : ℚ) * X) ^ (2 * k - 2 + 1) : ℚ[X]) = (1 + X) ^ (2 * k - 1) := by
    rw [show 2 * k - 2 + 1 = 2 * k - 1 by omega, map_neg, map_one, neg_one_mul, sub_neg_eq_add]
  have hval : B.eval (-1) =
      ((2 * k - 2).factorial : ℚ) * ((upoly k).leadingCoeff ^ 2 * k / (2 * 4 ^ k)) := by
    rw [h3, ← leadingCoeff_parQ k hk, leadingCoeff, natDegree_parQ k hk]
  refine ⟨B, h1, ?_, hval, ?_⟩
  · rw [← e2]
    exact h2
  · rw [hval]
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
      (div_ne_zero (mul_ne_zero (pow_ne_zero 2 (leadingCoeff_upoly_ne_zero k)) hk0)
        (mul_ne_zero two_ne_zero (pow_ne_zero k (by norm_num))))

/-- 辅助引理（T1.9）：`Σ_n a_k(n) x^n = Σ_n p(n) x^n + Σ_n (−1)^n q(n) x^n`（由 `a_eq_parity`）。 -/
theorem aSer_eq_add (k : ℕ) :
    aSer k = PowerSeries.mk (fun n => (parP k).eval (n : ℚ)) +
      PowerSeries.mk (fun n => (-1) ^ n * (parQ k).eval (n : ℚ)) := by
  ext n
  rw [map_add, coeff_aSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, a_eq_parity]

/-- **T1.9**（母函数）：`k ≥ 1` 时 `(1−x)^{2k+1}(1+x)^{2k−1}·Σ_n a_k(n) x^n` 是多项式 `Num`，
`deg Num < 4k`，且 `Num(1) ≠ 0`、`Num(−1) ≠ 0`（`Num = A·(1+x)^{2k−1} + B·(1−x)^{2k+1}`）。 -/
theorem gf_aSer (k : ℕ) (hk : 1 ≤ k) :
    ∃ Num : ℚ[X], Num.natDegree < 4 * k ∧ (↑(parDen k) : PowerSeries ℚ) * aSer k = ↑Num ∧
      Num.eval 1 ≠ 0 ∧ Num.eval (-1) ≠ 0 := by
  obtain ⟨A, hA1, hA2, -, hA4⟩ := gf_parP k
  obtain ⟨B, hB1, hB2, -, hB4⟩ := gf_parQ k hk
  have hp1 : (1 + X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  have hm1 : (1 - X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  refine ⟨A * (1 + X) ^ (2 * k - 1) + B * (1 - X) ^ (2 * k + 1), ?_, ?_, ?_, ?_⟩
  · have d1 := natDegree_mul_le_of_le hA1 (natDegree_pow_le_of_le (2 * k - 1) hp1)
    have d2 := natDegree_mul_le_of_le hB1 (natDegree_pow_le_of_le (2 * k + 1) hm1)
    exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by omega) (by omega))
  · rw [aSer_eq_add, parDen, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_mul, ← hA2, ← hB2]
    ring
  · rw [eval_add, eval_mul, eval_mul, eval_pow, eval_pow, eval_add, eval_sub, eval_one, eval_X,
      sub_self, zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, add_zero]
    exact mul_ne_zero hA4 (pow_ne_zero _ (by norm_num))
  · rw [eval_add, eval_mul, eval_mul, eval_pow, eval_pow, eval_add, eval_sub, eval_one, eval_X,
      add_neg_cancel, zero_pow (by omega : 2 * k - 1 ≠ 0), mul_zero, zero_add]
    exact mul_ne_zero hB4 (pow_ne_zero _ (by norm_num))

/-- 辅助引理（T1.9）：若多项式 `N` 满足 `N(1) ≠ 0`、`N(−1) ≠ 0`，则 `N` 与
`(1−x)^{2k+1}(1+x)^{2k−1}` 互素（`1 ∓ x` 是一次不可约式）。 -/
theorem isCoprime_parDen {Num : ℚ[X]} (h1 : Num.eval 1 ≠ 0) (h2 : Num.eval (-1) ≠ 0) (k : ℕ) :
    IsCoprime Num (parDen k) := by
  have c1 : IsCoprime Num (1 - X) := by
    have hirr : Irreducible (1 - X : ℚ[X]) := irreducible_of_degree_eq_one (by compute_degree!)
    refine (hirr.coprime_iff_not_dvd.mpr fun hdvd => h1 ?_).symm
    have := eval_dvd (x := (1 : ℚ)) hdvd
    rwa [eval_sub, eval_one, eval_X, sub_self, zero_dvd_iff] at this
  have c2 : IsCoprime Num (1 + X) := by
    have hirr : Irreducible (1 + X : ℚ[X]) := irreducible_of_degree_eq_one (by compute_degree!)
    refine (hirr.coprime_iff_not_dvd.mpr fun hdvd => h2 ?_).symm
    have := eval_dvd (x := (-1 : ℚ)) hdvd
    rwa [eval_add, eval_one, eval_X, add_neg_cancel, zero_dvd_iff] at this
  rw [parDen]
  exact c1.pow_right.mul_right c2.pow_right

/-- **T1.9**（最简分母）：`k ≥ 1` 时，若 `C·Σ_n a_k(n) x^n` 是多项式（`C ∈ ℚ[x]`），则
`(1−x)^{2k+1}(1+x)^{2k−1} ∣ C`。即 g.f. 的最简分母恰为 `(1−x)^{2k+1}(1+x)^{2k−1}`。 -/
theorem parDen_dvd_of_mul_aSer (k : ℕ) (hk : 1 ≤ k) (Cp Q : ℚ[X])
    (h : (↑Cp : PowerSeries ℚ) * aSer k = ↑Q) : parDen k ∣ Cp := by
  obtain ⟨Num, -, hNum, h1, h2⟩ := gf_aSer k hk
  have key : Cp * Num = parDen k * Q := by
    apply Polynomial.coe_injective ℚ
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hNum, ← h]
    ring
  exact (isCoprime_parDen h1 h2 k).symm.dvd_of_dvd_mul_right ⟨Q, key⟩

/-- 辅助引理（T1.9）：`k ≥ 1` 时 `deg (1−x)^{2k+1}(1+x)^{2k−1} = 4k`。 -/
theorem natDegree_parDen (k : ℕ) (hk : 1 ≤ k) : (parDen k).natDegree = 4 * k := by
  have h1 : (1 - X : ℚ[X]).natDegree = 1 := by compute_degree!
  have h2 : (1 + X : ℚ[X]).natDegree = 1 := by compute_degree!
  have n1 : (1 - X : ℚ[X]) ≠ 0 := fun h => by
    rw [h, natDegree_zero] at h1
    exact zero_ne_one h1
  have n2 : (1 + X : ℚ[X]) ≠ 0 := fun h => by
    rw [h, natDegree_zero] at h2
    exact zero_ne_one h2
  rw [parDen, natDegree_mul (pow_ne_zero _ n1) (pow_ne_zero _ n2), natDegree_pow, natDegree_pow,
    h1, h2]
  omega

/-- 辅助引理（T1.9）：`(1−x)^{2k+1}(1+x)^{2k−1}` 的常数项为 1。 -/
theorem coeff_zero_parDen (k : ℕ) : (parDen k).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, parDen, eval_mul, eval_pow, eval_pow, eval_sub, eval_add, eval_one,
    eval_X, sub_zero, add_zero, one_pow, one_pow, one_mul]

/-- **T1.9**（递推存在）：`k ≥ 1` 时，`(1−x)^{2k+1}(1+x)^{2k−1}` 的系数 `d_0 = 1, d_1, …, d_{4k}` 给出
`a_k(n)` 的 `4k` 阶线性递推 `Σ_{i=0}^{4k} d_i·a_k(n−i) = 0`（一切 `n ≥ 4k`）。 -/
theorem parity_recurrence (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 4 * k ≤ n) :
    ∑ i ∈ range (4 * k + 1), (parDen k).coeff i * (a k (n - i) : ℚ) = 0 := by
  obtain ⟨Num, hdeg, hNum, -, -⟩ := gf_aSer k hk
  have h := congrArg (PowerSeries.coeff n) hNum
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hn)] at h
  simp only [Polynomial.coeff_coe, coeff_aSer] at h
  refine (Finset.sum_subset ?_ ?_).trans h
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_parDen k hk]; omega), zero_mul]

/-- **T1.9**（阶的下界）：`k ≥ 1` 时，若 `γ_0, …, γ_d` 不全为零，且对一切 `n ≥ max(n_0, d)` 都有
`Σ_{i=0}^{d} γ_i·a_k(n−i) = 0`，则 `d ≥ 4k`。 -/
theorem parity_order_lower_bound (k : ℕ) (hk : 1 ≤ k) (d n0 : ℕ) (γ : ℕ → ℚ)
    (hγ : ∃ i ≤ d, γ i ≠ 0)
    (h : ∀ n, n0 ≤ n → d ≤ n → ∑ i ∈ range (d + 1), γ i * (a k (n - i) : ℚ) = 0) :
    4 * k ≤ d := by
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℚ[X], Γ = ∑ i ∈ range (d + 1), C (γ i) * X ^ i := ⟨_, rfl⟩
  have hΓcoeff : ∀ j, Γ.coeff j = if j ≤ d then γ j else 0 := by
    intro j
    rw [hΓ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_add_one_iff]
  have hΓne : Γ ≠ 0 := by
    obtain ⟨i, hi, hγi⟩ := hγ
    intro h0
    have := hΓcoeff i
    rw [h0, Polynomial.coeff_zero, ite_eq_left hi] at this
    exact hγi this.symm
  have hF : ∀ n, max n0 d ≤ n → PowerSeries.coeff n ((↑Γ : PowerSeries ℚ) * aSer k) = 0 := by
    intro n hn
    have hn0 : n0 ≤ n := le_trans (le_max_left _ _) hn
    have hdn : d ≤ n := le_trans (le_max_right _ _) hn
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Polynomial.coeff_coe, coeff_aSer]
    calc ∑ x ∈ range n.succ, Γ.coeff x * (a k (n - x) : ℚ)
        = ∑ x ∈ range (d + 1), Γ.coeff x * (a k (n - x) : ℚ) := by
          symm
          apply Finset.sum_subset
          · intro i hi
            simp only [Finset.mem_range] at hi ⊢
            omega
          · intro i _ hi
            simp only [Finset.mem_range, not_lt] at hi
            rw [hΓcoeff, ite_eq_right (by omega), zero_mul]
      _ = ∑ x ∈ range (d + 1), γ x * (a k (n - x) : ℚ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_range] at hi
          rw [hΓcoeff, ite_eq_left (by omega)]
      _ = 0 := h n hn0 hdn
  have hQ : (↑Γ : PowerSeries ℚ) * aSer k =
      ↑(PowerSeries.trunc (max n0 d) ((↑Γ : PowerSeries ℚ) * aSer k)) := by
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases hn : n < max n0 d
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn]
      exact hF n (by omega)
  have hdvd := parDen_dvd_of_mul_aSer k hk Γ _ hQ
  have := natDegree_le_of_dvd hdvd hΓne
  rw [natDegree_parDen k hk] at this
  have hΓdeg : Γ.natDegree ≤ d := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hΓcoeff, ite_eq_right (by omega)]
  omega

/-- **T1.9**（最小递推阶）：`k ≥ 1` 时，`a_k(n)` 关于 `n` 的最小线性递推阶恰为 `4k`
（首项系数归一 `γ_0 = 1`，递推对一切 `n ≥ d` 成立）。 -/
theorem parity_min_order (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {d | ∃ γ : ℕ → ℚ, γ 0 = 1 ∧
      ∀ n, d ≤ n → ∑ i ∈ range (d + 1), γ i * (a k (n - i) : ℚ) = 0} (4 * k) := by
  refine ⟨⟨fun i => (parDen k).coeff i, coeff_zero_parDen k,
    fun n hn => parity_recurrence k hk n hn⟩, ?_⟩
  rintro d ⟨γ, hγ0, hγ⟩
  exact parity_order_lower_bound k hk d 0 γ ⟨0, Nat.zero_le d, by rw [hγ0]; exact one_ne_zero⟩
    (fun n _ hn => hγ n hn)

/-! ## `k = 0` 的边界：T1.9 后半需要 `k ≥ 1` -/

/-- 辅助引理（T1.9 的 `k = 0` 边界）：`a_0(n) = 1`（一切 `n ≥ 0`；由 `a_eq` 与 `U_0 ≡ 1`）。 -/
theorem a_zero_left (n : ℕ) : a 0 n = 1 := by
  rw [a_eq, U_zero_left, U_zero_left]

/-- **T1.9 的反例（`k = 0`）**：报告 T1.9 原文（以及任务说明 (C8) 的「对所有 k」）没有写 `k ≥ 1`。
`k = 0` 时 `a_0(n) ≡ 1`，`q = 0`（`parQ_zero`，没有「2k−2 = −2 次」可言），`Σ a_0(n)xⁿ = 1/(1−x)`
（`(1+x)^{2k−1} = (1+x)^{−1}` 不是多项式），最小线性递推阶是 1 而不是 `4k = 0`。 -/
theorem parity_min_order_zero :
    IsLeast {d | ∃ γ : ℕ → ℚ, γ 0 = 1 ∧
      ∀ n, d ≤ n → ∑ i ∈ range (d + 1), γ i * (a 0 (n - i) : ℚ) = 0} 1 := by
  refine ⟨⟨fun i => if i = 0 then 1 else -1, by simp, fun n _ => ?_⟩, ?_⟩
  · simp [sum_range_succ, a_zero_left]
  · rintro d ⟨γ, hγ0, hγ⟩
    by_contra hd
    obtain rfl : d = 0 := by omega
    have := hγ 0 le_rfl
    simp [a_zero_left, hγ0] at this

/-! ## 汇总 -/

/-- **T1.9**（汇总）。记 `c = lc u_k`（T1.2 `leadingCoeff_upoly_eq`：`k ≤ 1` 时 `c = 1`，
`k ≥ 2` 时 `c = 2/k!`），`E(n) = u_k(n/2)²`、`O(n) = u_k((n+1)/2)·u_k((n−1)/2)`，
`p = parP k = (E+O)/2`、`q = parQ k = (E−O)/2`。
1. `E`、`O` 都是 `2k` 次多项式；对一切 `n ≥ 0`，`a_k(n) = p(n) + (−1)^n q(n)`；任何满足此式的
   `(p', q') ∈ ℚ[X]²` 都等于 `(p, q)`（所以这样的一对存在且唯一）；
2. `deg p = 2k`，`lc p = c²/4^k`；`k ≥ 1` 时 `deg q = 2k−2`，`lc q = c²k/(2·4^k)`；`k = 0` 时 `q = 0`；
3. `k ≥ 1` 时：
   * `Σ_n p(n)xⁿ = A(x)/(1−x)^{2k+1}`、`Σ_n (−1)ⁿq(n)xⁿ = B(x)/(1+x)^{2k−1}`（写成形式幂级数等式），
     `A`、`B` 是多项式，`A(1) ≠ 0`，`B(−1) ≠ 0`；
   * `(1−x)^{2k+1}(1+x)^{2k−1}·Σ_n a_k(n)xⁿ` 是次数 `< 4k` 的多项式，且与
     `(1−x)^{2k+1}(1+x)^{2k−1}` 互素；
   * 最简分母恰为 `(1−x)^{2k+1}(1+x)^{2k−1}`：任何使 `C·Σ_n a_k(n)xⁿ` 成为多项式的 `C ∈ ℚ[x]`
     都被它整除；
   * `a_k(n)` 关于 `n` 的最小线性递推阶恰为 `4k`。 -/
theorem T1_9 (k : ℕ) :
    (evenPart k).natDegree = 2 * k ∧ (oddPart k).natDegree = 2 * k ∧
    (∀ n : ℕ, (a k n : ℚ) = (parP k).eval (n : ℚ) + (-1) ^ n * (parQ k).eval (n : ℚ)) ∧
    (∀ p q : ℚ[X], (∀ n : ℕ, (a k n : ℚ) = p.eval (n : ℚ) + (-1) ^ n * q.eval (n : ℚ)) →
      p = parP k ∧ q = parQ k) ∧
    (parP k).natDegree = 2 * k ∧
    (parP k).leadingCoeff = (upoly k).leadingCoeff ^ 2 / 4 ^ k ∧
    (1 ≤ k → (parQ k).natDegree = 2 * k - 2 ∧
      (parQ k).leadingCoeff = (upoly k).leadingCoeff ^ 2 * k / (2 * 4 ^ k)) ∧
    (k = 0 → parQ k = 0) ∧
    (1 ≤ k →
      (∃ A : ℚ[X], A.natDegree ≤ 2 * k ∧ (↑((1 - X) ^ (2 * k + 1) : ℚ[X]) : PowerSeries ℚ) *
          PowerSeries.mk (fun n => (parP k).eval (n : ℚ)) = ↑A ∧ A.eval 1 ≠ 0) ∧
      (∃ B : ℚ[X], B.natDegree ≤ 2 * k - 2 ∧ (↑((1 + X) ^ (2 * k - 1) : ℚ[X]) : PowerSeries ℚ) *
          PowerSeries.mk (fun n => (-1) ^ n * (parQ k).eval (n : ℚ)) = ↑B ∧ B.eval (-1) ≠ 0) ∧
      (∃ Num : ℚ[X], Num.natDegree < 4 * k ∧
          (↑(parDen k) : PowerSeries ℚ) * aSer k = ↑Num ∧ IsCoprime Num (parDen k)) ∧
      (∀ Cp Q : ℚ[X], (↑Cp : PowerSeries ℚ) * aSer k = ↑Q → parDen k ∣ Cp) ∧
      IsLeast {d | ∃ γ : ℕ → ℚ, γ 0 = 1 ∧
        ∀ n, d ≤ n → ∑ i ∈ range (d + 1), γ i * (a k (n - i) : ℚ) = 0} (4 * k)) := by
  refine ⟨natDegree_evenPart k, natDegree_oddPart k, a_eq_parity k,
    fun p q h => parity_unique k h, natDegree_parP k, leadingCoeff_parP k,
    fun hk => ⟨natDegree_parQ k hk, leadingCoeff_parQ k hk⟩,
    fun hk => by subst hk; exact parQ_zero,
    fun hk => ⟨?_, ?_, ?_, parDen_dvd_of_mul_aSer k hk, parity_min_order k hk⟩⟩
  · obtain ⟨A, hA1, hA2, -, hA4⟩ := gf_parP k
    exact ⟨A, hA1, hA2, hA4⟩
  · obtain ⟨B, hB1, hB2, -, hB4⟩ := gf_parQ k hk
    exact ⟨B, hB1, hB2, hB4⟩
  · obtain ⟨Num, h1, h2, h3, h4⟩ := gf_aSer k hk
    exact ⟨Num, h1, h2, isCoprime_parDen h3 h4 k⟩

end A207123
