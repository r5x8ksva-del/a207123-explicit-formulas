import A207123.Binomial
import A207123.Poly

/-!
# 报告 T4.1、T4.2(3)、T5.2：近对角线 `N(k, k−d)` 与 `u_k` 的高次系数

记 `D(k,d) := N(k, k−d)`（`ndD`，越界取 0）。

* **T4.1**（一切 `d ≥ 0`）：
  - `T4_1_a`：存在唯一 `p_d ∈ ℚ[X]` 使 `D(k,d) = p_d(k)` 对一切 `k ≥ 2d+2` 成立；
  - 汇总定理 `T4_1`：对这个 `p_d`，`deg p_d = 2d`，首项 `2/(2^d·d!)`，`d ≥ 1` 时次首项系数是首项的
    `−(4d²−3d)` 倍，缺陷 `e_d(2d+1) = (−1)^{d+1}(d+1)!`、`e_d(2d) = (−1)^{d+1}(d+2)!/2`；
  - `T4_1_threshold`：门槛 `2d+2` 精确，没有多项式在一切 `k ≥ 2d+1` 处等于 `D(k,d)`；
  - `ndPoly_zero_one`：`p_0 = 2`、`p_1 = k² − k − 4`（`p_2` 见 `NumStruct.lean` 的 `N_sub_two`）。
  没有形式化：「首项是 `S(k,k−d)` 首项的 2 倍」的比较、`p_3`–`p_5` 的显式式（报告对 `d ≤ 12` 做计算机辅助证明）、
  以 `m = k−2d−1` 展开时系数的符号（`d ≤ 46` 全正、`d = 47` 起有反例，属于计算结论）、门槛以下的例外值表。
* **T4.2(3)**：`T4_2_3`：基点 `2d+2` 的 Newton 系数 `T_{d,i} = Δ^i p_d(2d+2)`（`0 ≤ i ≤ 2d`）都是正整数，
  末项 `2·(2d−1)!!`。「改用基点 `2d+1` 时并非总为正」的反例（`d = 69` 等）是计算结论，没有形式化。
* **T5.2**：`T5_2_formula`：`B_d(k) := (k−d)!·[m^{k−d}]u_k = Σ_{e≤d} (−1)^{d−e}·N(k,k−e)·ẽ_{d−e}(k−e)`（`k ≥ d`）；
  `T5_2_top`（`[m^k]u_k = 2/k!`，`k ≥ 2`）、`T5_2_sub`（`[m^{k−1}]u_k = (k²−2k−1)/(k−1)!`，`k ≥ 4`）与
  `T5_2_sub_three`（`k = 3` 的例外）。没有形式化：「`k ≥ 2d+2` 时 `B_d(k)` 是 `2d` 次多项式、门槛精确」、
  `[m^{k−2}]`、`[m^{k−3}]` 的显式式、`U_k(m) = (2/k!)(m+μ_k)^k(1+O(m^{−2}))` 与 `C(m+1,·)` 基下的展开。

`u_k` 是 `Poly.lean` 的 `upoly k`（T1.2 中唯一的插值多项式），所以 `[m^j]U_k(m)` 就是 `(upoly k).coeff j`。
-/

namespace A207123

open Polynomial Finset
open scoped Nat

/-! ## 1. 递推（†）与 Newton 序列 -/

/-- 报告 T4.1 的 `D(k,d) := N(k,k−d)`，第二个下标取整数，按报告约定越界取 0：
`0 ≤ d ≤ k` 时为 `N(k, k−d)`，否则（`d < 0` 或 `d > k`）为 0。 -/
def ndD (k : ℕ) (d : ℤ) : ℕ := if 0 ≤ d ∧ d ≤ k then N k (k - d.toNat) else 0

/-- 辅助引理（T4.1）：若 `q = k − d`（`q ≥ 0`），则 `D(k,d) = N(k,q)`（`d < 0` 时两边都是 0）。 -/
theorem ndD_eq (k : ℕ) (d : ℤ) (q : ℕ) (hq : (q : ℤ) = k - d) : ndD k d = N k q := by
  unfold ndD
  split_ifs with h
  · congr 1
    omega
  · rw [N_eq_zero_of_lt (by omega)]

/-- **T4.1 的递推（†）**：`k ≥ 3`、`k − d ≥ 1` 时
`D(k,d) = D(k−1,d) + D(k−1,d−1) + (k−d−1)·[D(k−3,d−1) + 2·D(k−3,d−2) + D(k−3,d−3)]`，
`d < 0`（以及 `d > k`）时 `D ≡ 0`。由三角递推 `N_tri` 取 `q = k − d` 得到。 -/
theorem ndD_rec (k d : ℕ) (hk : 3 ≤ k) (hkd : d + 1 ≤ k) :
    (ndD k d : ℤ) = ndD (k - 1) d + ndD (k - 1) ((d : ℤ) - 1)
      + ((k : ℤ) - d - 1) * (ndD (k - 3) ((d : ℤ) - 1) + 2 * ndD (k - 3) ((d : ℤ) - 2)
        + ndD (k - 3) ((d : ℤ) - 3)) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 3 := ⟨k - 3, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, K + 2 = d + r := ⟨K + 2 - d, by omega⟩
  have h := N_tri K r
  rw [ndD_eq (K + 3) d (r + 1) (by omega), ndD_eq (K + 3 - 1) d r (by omega),
    ndD_eq (K + 3 - 1) ((d : ℤ) - 1) (r + 1) (by omega),
    ndD_eq (K + 3 - 3) ((d : ℤ) - 2) r (by omega),
    ndD_eq (K + 3 - 3) ((d : ℤ) - 3) (r + 1) (by omega),
    show K + 3 - 1 = K + 2 by omega, show K + 3 - 3 = K by omega]
  rcases r with _ | r
  · have hc : ((K + 3 : ℕ) : ℤ) - d - 1 = 0 := by omega
    rw [hc, h]
    push_cast
    ring
  · have h' : (N (K + 3) (r + 1 + 1) : ℤ) = N (K + 2) (r + 1) + N (K + 2) (r + 1 + 1)
        + ((r : ℤ) + 1) * (N K r + 2 * N K (r + 1) + N K (r + 1 + 1)) := by
      rw [h, Nat.add_sub_cancel]
      push_cast
      ring
    have hc : ((K + 3 : ℕ) : ℤ) - d - 1 = (r : ℤ) + 1 := by omega
    rw [ndD_eq K ((d : ℤ) - 1) r (by omega), h', hc]

/-- `ndSeq d n = D(2d+2+n, d) = N(2d+2+n, d+2+n)`（取值于 ℤ）：`D(·,d)` 从门槛 `2d+2` 起的序列。 -/
def ndSeq (d n : ℕ) : ℤ := N (2 * d + 2 + n) (d + 2 + n)

/-- `ndSub d j n`：`j ≤ d` 时为 `ndSeq (d−j) n`，否则为 0（约定 `D(·,d′) ≡ 0`（`d′ < 0`））。 -/
def ndSub (d j n : ℕ) : ℤ := if j ≤ d then ndSeq (d - j) n else 0

/-- 辅助引理（T4.1）：`ndSeq` 按定义展开（下标用等式给出）。 -/
theorem ndSeq_eq (d n a b : ℕ) (ha : a = 2 * d + 2 + n) (hb : b = d + 2 + n) :
    ndSeq d n = (N a b : ℤ) := by
  subst ha hb
  rfl

/-- 辅助引理（T4.1）：`j ≤ d+m+1` 时 `ndSub d j m = N(2d+2+m−2j, d+2+m−j)`
（`j > d` 时两边都是 0，因为第二个下标大于第一个）。 -/
theorem ndSub_eq (d j m a b : ℕ) (hj : j ≤ d + m + 1) (ha : a = 2 * d + 2 + m - 2 * j)
    (hb : b = d + 2 + m - j) : ndSub d j m = (N a b : ℤ) := by
  unfold ndSub
  split_ifs with h
  · exact ndSeq_eq _ _ _ _ (by omega) (by omega)
  · rw [N_eq_zero_of_lt (by omega)]
    simp

/-- 辅助引理（T4.1）：（†）在多项式区的形式，`d ≥ 1`：
`a_d(n+1) = a_d(n) + a_{d−1}(n+2) + (d+2+n)·[a_{d−1}(n) + 2·a_{d−2}(n+2) + a_{d−3}(n+4)]`，
`a_e(n) := D(2e+2+n, e)`，下标为负的项取 0。 -/
theorem ndSeq_succ (d n : ℕ) (hd : 1 ≤ d) :
    ndSeq d (n + 1) = ndSeq d n + ndSub d 1 (n + 2)
      + ((d : ℤ) + 2 + n) * (ndSub d 1 n + 2 * ndSub d 2 (n + 2) + ndSub d 3 (n + 4)) := by
  have h := N_tri (2 * d + n) (d + 2 + n)
  rw [ndSeq_eq d (n + 1) (2 * d + n + 3) (d + 2 + n + 1) (by omega) (by omega),
    ndSeq_eq d n (2 * d + n + 2) (d + 2 + n) (by omega) (by omega),
    ndSub_eq d 1 (n + 2) (2 * d + n + 2) (d + 2 + n + 1) (by omega) (by omega) (by omega),
    ndSub_eq d 1 n (2 * d + n) (d + 2 + n - 1) (by omega) (by omega) (by omega),
    ndSub_eq d 2 (n + 2) (2 * d + n) (d + 2 + n) (by omega) (by omega) (by omega),
    ndSub_eq d 3 (n + 4) (2 * d + n) (d + 2 + n + 1) (by omega) (by omega) (by omega), h]
  push_cast
  ring

/-! ## 2. Newton 系数的运算（`ℕ → R` 上的前向差分） -/

section NC

variable {R : Type*} [CommRing R]

/-- 辅助引理（T4.2(3)）：`Δf(n) = f(n+1) − f(n)`。 -/
theorem ndFD_apply (F : ℕ → R) (n : ℕ) : fwdDiff (1 : ℕ) F n = F (n + 1) - F n := rfl

/-- 辅助引理（T4.2(3)）：Newton 公式 `f(n) = Σ_{l≤n} C(n,l)·Δ^l f(0)`。 -/
theorem ndNC_newton (f : ℕ → R) (n : ℕ) :
    f n = ∑ l ∈ range (n + 1), (n.choose l : R) * (fwdDiff (1 : ℕ))^[l] f 0 := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at h
  exact h

/-- 辅助引理（T4.2(3)）：基点右移 `s`：`Δ^l[f(·+s)](0) = Σ_j C(s,j)·Δ^{l+j}f(0)`。 -/
theorem ndNC_shift (f : ℕ → R) (s l : ℕ) :
    (fwdDiff (1 : ℕ))^[l] (fun n => f (n + s)) 0
      = ∑ j ∈ range (s + 1), (s.choose j : R) * (fwdDiff (1 : ℕ))^[l + j] f 0 := by
  rw [fwdDiff_iter_comp_add, zero_add]
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) ((fwdDiff (1 : ℕ))^[l] f) s 0
  simp only [zero_add, smul_eq_mul, mul_one] at h
  rw [h]
  refine sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul, ← Function.iterate_add_apply, add_comm j l]

/-- 辅助引理（T4.2(3)）：`Δ^l` 可加。 -/
theorem ndNC_add (A B : ℕ → R) (l : ℕ) :
    (fwdDiff (1 : ℕ))^[l] (fun n => A n + B n) 0
      = (fwdDiff (1 : ℕ))^[l] A 0 + (fwdDiff (1 : ℕ))^[l] B 0 :=
  congrFun (fwdDiff_iter_add (1 : ℕ) A B l) 0

/-- 辅助引理（T4.2(3)）：`Δ^l` 与数乘交换。 -/
theorem ndNC_smul (c : R) (A : ℕ → R) (l : ℕ) :
    (fwdDiff (1 : ℕ))^[l] (fun n => c * A n) 0 = c * (fwdDiff (1 : ℕ))^[l] A 0 :=
  congrFun (fwdDiff_iter_const_smul (1 : ℕ) c A l) 0

/-- 辅助引理（T4.2(3)）：`Δ^l(Δf)(0) = Δ^{l+1}f(0)`。 -/
theorem ndNC_fd (f : ℕ → R) (l : ℕ) :
    (fwdDiff (1 : ℕ))^[l] (fwdDiff (1 : ℕ) f) 0 = (fwdDiff (1 : ℕ))^[l + 1] f 0 := by
  rw [Function.iterate_succ_apply]

/-- 辅助引理（T4.2(3)）：零函数的各阶差分为零。 -/
theorem ndNC_zero_fun (l : ℕ) : (fwdDiff (1 : ℕ))^[l] (fun _ : ℕ => (0 : R)) = fun _ => 0 :=
  Function.iterate_fixed (fwdDiff_const (1 : ℕ) (0 : R)) l

/-- 辅助引理（T4.2(3)）：乘以 `(α+n)`：
`Δ^{l+1}[(α+n)f](n) = (α+l+1+n)·Δ^{l+1}f(n) + (l+1)·Δ^l f(n)`；
取 `n = 0` 即报告的「把 Newton 系数 `f_l` 变为 `f_l(α+l) + l·f_{l−1}`」。 -/
theorem ndNC_mul (f : ℕ → R) (α : R) (l n : ℕ) :
    (fwdDiff (1 : ℕ))^[l + 1] (fun m => (α + m) * f m) n
      = (α + (l + 1) + n) * (fwdDiff (1 : ℕ))^[l + 1] f n
        + (l + 1) * (fwdDiff (1 : ℕ))^[l] f n := by
  induction l generalizing n with
  | zero =>
    simp only [zero_add, Function.iterate_one, Function.iterate_zero_apply, ndFD_apply]
    push_cast
    ring
  | succ l ih =>
    rw [Function.iterate_succ_apply', ndFD_apply, ih (n + 1), ih n]
    simp only [Function.iterate_succ_apply', ndFD_apply]
    push_cast
    ring

end NC

/-! ## 3. Newton 系数 `T_{d,i}` 的正性（T4.2(3) 的核心） -/

/-- `ndT d i = Δ^i a_d(0)`：`a_d(n) = D(2d+2+n, d)` 在基点 0（即 `k = 2d+2`）的第 `i` 个 Newton 系数。 -/
def ndT (d i : ℕ) : ℤ := (fwdDiff (1 : ℕ))^[i] (ndSeq d) 0

/-- 辅助引理（T4.1）：`a_0(n) = N(2+n, 2+n) = 2`。 -/
theorem ndSeq_zero (n : ℕ) : ndSeq 0 n = 2 := by
  rw [ndSeq_eq 0 n (2 + n) (2 + n) (by omega) (by omega), N_diag (2 + n) (by omega)]
  norm_num

/-- 辅助引理（T4.2(3)）：`T_{0,0} = 2`。 -/
theorem ndT_zero_zero : ndT 0 0 = 2 := ndSeq_zero 0

/-- 辅助引理（T4.2(3)）：`T_{0,l+1} = 0`。 -/
theorem ndT_zero_succ (l : ℕ) : ndT 0 (l + 1) = 0 := by
  unfold ndT
  rw [Function.iterate_succ_apply]
  have h : fwdDiff (1 : ℕ) (ndSeq 0) = fun _ => 0 := by
    funext n
    rw [ndFD_apply, ndSeq_zero, ndSeq_zero, sub_self]
  rw [h, ndNC_zero_fun]

/-- 辅助引理（T4.2(3)）：`ndSub d j` 右移 `s` 后的 Newton 系数非负，且下标 `l > 2(d−j)` 时为 0
（`j > d` 时整个序列为 0）。 -/
theorem ndNC_sub_shift (d j s : ℕ)
    (H : j ≤ d → (∀ l, 0 ≤ ndT (d - j) l) ∧ (∀ l, 2 * (d - j) < l → ndT (d - j) l = 0))
    (l : ℕ) :
    0 ≤ (fwdDiff (1 : ℕ))^[l] (fun n => ndSub d j (n + s)) 0 ∧
      (2 * d < l + 2 * j → (fwdDiff (1 : ℕ))^[l] (fun n => ndSub d j (n + s)) 0 = 0) := by
  by_cases hj : j ≤ d
  · have hfun : (fun n => ndSub d j (n + s)) = fun n => ndSeq (d - j) (n + s) := by
      funext n
      simp [ndSub, hj]
    rw [hfun, ndNC_shift]
    obtain ⟨h0, h1⟩ := H hj
    refine ⟨sum_nonneg fun i _ => mul_nonneg (by positivity) (h0 (l + i)), fun hl => ?_⟩
    refine sum_eq_zero fun i _ => ?_
    have h2 : ndT (d - j) (l + i) = 0 := h1 _ (by omega)
    unfold ndT at h2
    rw [h2, mul_zero]
  · have hfun : (fun n => ndSub d j (n + s)) = fun _ => 0 := by
      funext n
      simp [ndSub, hj]
    rw [hfun, ndNC_zero_fun]
    exact ⟨le_refl _, fun _ => rfl⟩

/-- `ndH d n = a_{d−1}(n) + 2·a_{d−2}(n+2) + a_{d−3}(n+4)`（下标为负的项取 0）。 -/
def ndH (d n : ℕ) : ℤ := ndSub d 1 n + 2 * ndSub d 2 (n + 2) + ndSub d 3 (n + 4)

/-- 辅助引理（T4.2(3)）：`d ≥ 1` 时 `Δa_d(n) = a_{d−1}(n+2) + (d+2+n)·ndH d n`。 -/
theorem ndSeq_fd (d : ℕ) (hd : 1 ≤ d) :
    fwdDiff (1 : ℕ) (ndSeq d) = fun n => ndSub d 1 (n + 2) + ((d : ℤ) + 2 + n) * ndH d n := by
  funext n
  rw [ndFD_apply, ndSeq_succ d n hd, ndH]
  ring

/-- 辅助引理（T4.2(3)）：`T_{d,l+1}` 拆成两部分的 Newton 系数之和。 -/
theorem ndT_succ (d l : ℕ) (hd : 1 ≤ d) :
    ndT d (l + 1) = (fwdDiff (1 : ℕ))^[l] (fun n => ndSub d 1 (n + 2)) 0
      + (fwdDiff (1 : ℕ))^[l] (fun n => ((d : ℤ) + 2 + n) * ndH d n) 0 := by
  rw [ndT, ← ndNC_fd, ndSeq_fd d hd, ndNC_add]

/-- 辅助引理（T4.2(3)，c4 命题 3.6 的归纳）：对一切 `d`，
`T_{d,l} > 0`（`l ≤ 2d`）、`T_{d,l} = 0`（`l > 2d`）、`T_{d,2d} = 2·(2d−1)!!`，
且 `d ≥ 1` 时 `T_{d,2d−1} = (d+3)·T_{d,2d}`（后者用于 T4.1(c)）。 -/
theorem ndT_main (d : ℕ) :
    (∀ l, l ≤ 2 * d → 0 < ndT d l) ∧ (∀ l, 2 * d < l → ndT d l = 0) ∧
    ndT d (2 * d) = 2 * ((2 * d - 1)‼ : ℤ) ∧
    (1 ≤ d → ndT d (2 * d - 1) = ((d : ℤ) + 3) * ndT d (2 * d)) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, fun h => absurd h (by norm_num)⟩
    · obtain rfl : l = 0 := by omega
      rw [ndT_zero_zero]
      norm_num
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      exact ndT_zero_succ l'
    · rw [show 2 * 0 = 0 from rfl, ndT_zero_zero]
      norm_num [Nat.doubleFactorial]
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    obtain ⟨IHpos, IHzero, IHtop, IHsec⟩ := ih e (by omega)
    have IHnn : ∀ l, 0 ≤ ndT e l := fun l => by
      by_cases hl : l ≤ 2 * e
      · exact (IHpos l hl).le
      · rw [IHzero l (by omega)]
    have Hj : ∀ j, 1 ≤ j → j ≤ e + 1 →
        (∀ l, 0 ≤ ndT (e + 1 - j) l) ∧ (∀ l, 2 * (e + 1 - j) < l → ndT (e + 1 - j) l = 0) := by
      intro j hj1 hj2
      obtain ⟨hp, hz, -, -⟩ := ih (e + 1 - j) (by omega)
      refine ⟨fun l => ?_, hz⟩
      by_cases hl : l ≤ 2 * (e + 1 - j)
      · exact (hp l hl).le
      · rw [hz l (by omega)]
    have hA := fun l => ndNC_sub_shift (e + 1) 1 2 (Hj 1 le_rfl) l
    have hK2 := fun l => ndNC_sub_shift (e + 1) 2 2 (Hj 2 (by norm_num)) l
    have hK3 := fun l => ndNC_sub_shift (e + 1) 3 4 (Hj 3 (by norm_num)) l
    have hsub1 : ndSub (e + 1) 1 = ndSeq e := by
      funext n
      simp [ndSub]
    have hAval : ∀ l, (fwdDiff (1 : ℕ))^[l] (fun n => ndSub (e + 1) 1 (n + 2)) 0
        = ndT e l + 2 * ndT e (l + 1) + ndT e (l + 2) := by
      intro l
      rw [hsub1, ndNC_shift]
      simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right, Nat.choose_one_right,
        Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, add_zero, zero_add, one_mul]
      rfl
    have hH : ∀ l, (fwdDiff (1 : ℕ))^[l] (ndH (e + 1)) 0 = ndT e l
        + 2 * (fwdDiff (1 : ℕ))^[l] (fun n => ndSub (e + 1) 2 (n + 2)) 0
        + (fwdDiff (1 : ℕ))^[l] (fun n => ndSub (e + 1) 3 (n + 4)) 0 := by
      intro l
      have h1 := ndNC_add (fun n => ndSub (e + 1) 1 n + 2 * ndSub (e + 1) 2 (n + 2))
        (fun n => ndSub (e + 1) 3 (n + 4)) l
      have h2 := ndNC_add (ndSub (e + 1) 1) (fun n => 2 * ndSub (e + 1) 2 (n + 2)) l
      have h3 := ndNC_smul (2 : ℤ) (fun n => ndSub (e + 1) 2 (n + 2)) l
      have hfun : ndH (e + 1) = fun n => ndSub (e + 1) 1 n + 2 * ndSub (e + 1) 2 (n + 2)
          + ndSub (e + 1) 3 (n + 4) := rfl
      rw [hfun, h1, h2, h3, hsub1]
      rfl
    have hM0 : (fwdDiff (1 : ℕ))^[0] (fun n => (((e + 1 : ℕ) : ℤ) + 2 + n) * ndH (e + 1) n) 0
        = (((e + 1 : ℕ) : ℤ) + 2) * (fwdDiff (1 : ℕ))^[0] (ndH (e + 1)) 0 := by
      simp
    have hMs : ∀ l, (fwdDiff (1 : ℕ))^[l + 1]
          (fun n => (((e + 1 : ℕ) : ℤ) + 2 + n) * ndH (e + 1) n) 0
        = (((e + 1 : ℕ) : ℤ) + 2 + (l + 1)) * (fwdDiff (1 : ℕ))^[l + 1] (ndH (e + 1)) 0
          + (l + 1) * (fwdDiff (1 : ℕ))^[l] (ndH (e + 1)) 0 := by
      intro l
      rw [ndNC_mul (ndH (e + 1)) (((e + 1 : ℕ) : ℤ) + 2) l 0]
      push_cast
      ring
    have hHge : ∀ l, ndT e l ≤ (fwdDiff (1 : ℕ))^[l] (ndH (e + 1)) 0 := by
      intro l
      rw [hH l]
      have := (hK2 l).1
      have := (hK3 l).1
      linarith
    have hHnn : ∀ l, 0 ≤ (fwdDiff (1 : ℕ))^[l] (ndH (e + 1)) 0 := fun l =>
      (IHnn l).trans (hHge l)
    have hHzero : ∀ l, 2 * e < l → (fwdDiff (1 : ℕ))^[l] (ndH (e + 1)) 0 = 0 := by
      intro l hl
      rw [hH l, IHzero l hl, (hK2 l).2 (by omega), (hK3 l).2 (by omega)]
      ring
    -- 正性
    have pos : ∀ l, l ≤ 2 * (e + 1) → 0 < ndT (e + 1) l := by
      intro l hl
      rcases l with _ | l
      · have h := N_tri (2 * e + 1) (e + 2)
        have h1 : ndT (e + 1) 0 = (N (2 * e + 1 + 3) (e + 2 + 1) : ℤ) :=
          ndSeq_eq (e + 1) 0 _ _ (by omega) (by omega)
        have h2 : ndSeq e 1 = (N (2 * e + 1 + 2) (e + 2 + 1) : ℤ) :=
          ndSeq_eq e 1 _ _ (by omega) (by omega)
        have h3 : ndSeq e 1 = ndT e 0 + ndT e 1 := by
          show ndSeq e 1 = ndSeq e 0 + (fwdDiff (1 : ℕ))^[1] (ndSeq e) 0
          rw [Function.iterate_one, ndFD_apply]
          ring
        have h4 := IHpos 0 (by omega)
        have h5 := IHnn 1
        have h6 : N (2 * e + 1 + 2) (e + 2 + 1) ≤ N (2 * e + 1 + 3) (e + 2 + 1) := by
          rw [h]
          exact Nat.le_add_right_of_le (Nat.le_add_left _ _)
        have h7 : (N (2 * e + 1 + 2) (e + 2 + 1) : ℤ) ≤ N (2 * e + 1 + 3) (e + 2 + 1) := by
          exact_mod_cast h6
        rw [h1]
        rw [h2] at h3
        linarith
      · rw [ndT_succ (e + 1) l (by omega)]
        have hA0 := (hA l).1
        rcases l with _ | l
        · rw [hM0]
          have := hHge 0
          have := IHpos 0 (by omega)
          have h8 : (0 : ℤ) < (((e + 1 : ℕ) : ℤ) + 2) := by positivity
          have h9 : 0 < (fwdDiff (1 : ℕ))^[0] (ndH (e + 1)) 0 := by linarith
          have := mul_pos h8 h9
          linarith
        · rw [hMs l]
          have h1 := hHnn (l + 1)
          have h2 := IHpos l (by omega)
          have h3 := hHge l
          have h8 : (0 : ℤ) ≤ (((e + 1 : ℕ) : ℤ) + 2 + ((l : ℤ) + 1)) := by positivity
          have h9 := mul_nonneg h8 h1
          have h10 : (0 : ℤ) < ((l : ℤ) + 1) * (fwdDiff (1 : ℕ))^[l] (ndH (e + 1)) 0 :=
            mul_pos (by positivity) (by linarith)
          linarith
    -- 高阶为零
    have zero : ∀ l, 2 * (e + 1) < l → ndT (e + 1) l = 0 := by
      intro l hl
      obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [ndT_succ (e + 1) l (by omega)]
      obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [hMs l, (hA (l + 1)).2 (by omega), hHzero (l + 1) (by omega), hHzero l (by omega)]
      ring
    -- 末项
    have top : ndT (e + 1) (2 * (e + 1)) = (2 * (e : ℤ) + 1) * ndT e (2 * e) := by
      rw [show 2 * (e + 1) = 2 * e + 1 + 1 by ring, ndT_succ (e + 1) (2 * e + 1) (by omega),
        hMs (2 * e), (hA (2 * e + 1)).2 (by omega), hHzero (2 * e + 1) (by omega), hH (2 * e),
        (hK2 (2 * e)).2 (by omega), (hK3 (2 * e)).2 (by omega)]
      push_cast
      ring
    -- 次末项
    have sec : ndT (e + 1) (2 * (e + 1) - 1)
        = (((e + 1 : ℕ) : ℤ) + 3) * ndT (e + 1) (2 * (e + 1)) := by
      rw [top, show 2 * (e + 1) - 1 = 2 * e + 1 by omega, ndT_succ (e + 1) (2 * e) (by omega),
        hAval (2 * e), IHzero (2 * e + 1) (by omega), IHzero (2 * e + 2) (by omega)]
      rcases e with _ | e
      · rw [show 2 * 0 = 0 from rfl, hM0, hH 0, (hK2 0).2 (by norm_num), (hK3 0).2 (by norm_num),
          ndT_zero_zero]
        norm_num
      · have hs := IHsec (by omega)
        rw [show 2 * (e + 1) - 1 = 2 * e + 1 by omega,
          show 2 * (e + 1) = 2 * e + 1 + 1 by ring] at hs
        rw [show 2 * (e + 1) = 2 * e + 1 + 1 by ring, hMs (2 * e + 1), hH (2 * e + 1 + 1),
          hH (2 * e + 1), (hK2 (2 * e + 1 + 1)).2 (by omega), (hK3 (2 * e + 1 + 1)).2 (by omega),
          (hK2 (2 * e + 1)).2 (by omega), (hK3 (2 * e + 1)).2 (by omega), hs]
        push_cast
        ring
    refine ⟨pos, zero, ?_, fun _ => sec⟩
    rw [top, IHtop, show 2 * (e + 1) - 1 = 2 * e + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    ring

/-! ## 4. 多项式 `p_d`（Newton 形式）与 T4.1 -/

/-- `ndFF B l = ∏_{j<l} (X − (B + j))`（下降阶乘多项式的平移）。 -/
noncomputable def ndFF (B : ℚ) (l : ℕ) : ℚ[X] := ∏ j ∈ range l, (X - C (B + j))

/-- 辅助引理（T4.1）：`ndFF B l` 在 `B + n` 处取值 `n(n−1)⋯(n−l+1)`。 -/
theorem ndFF_eval (B : ℚ) (l n : ℕ) : (ndFF B l).eval (B + n) = (n.descFactorial l : ℚ) := by
  induction l with
  | zero => simp [ndFF]
  | succ l ih =>
    rw [ndFF, prod_range_succ, eval_mul, ← ndFF, ih, Nat.descFactorial_succ]
    simp only [eval_sub, eval_X, eval_C]
    by_cases h : l ≤ n
    · push_cast [Nat.cast_sub h]
      ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp

/-- 辅助引理（T4.1）：`deg ndFF B l = l`。 -/
theorem ndFF_natDegree (B : ℚ) (l : ℕ) : (ndFF B l).natDegree = l := by
  rw [ndFF, natDegree_finsetProd_X_sub_C_eq_card, card_range]

/-- 辅助引理（T4.1）：`ndFF B l` 首一。 -/
theorem ndFF_monic (B : ℚ) (l : ℕ) : (ndFF B l).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- 辅助引理（T4.1）：`[X^l] ndFF B l = 1`。 -/
theorem ndFF_coeff_self (B : ℚ) (l : ℕ) : (ndFF B l).coeff l = 1 := by
  have h := (ndFF_monic B l).coeff_natDegree
  rwa [ndFF_natDegree] at h

/-- 辅助引理（T4.1）：`m > l` 时 `[X^m] ndFF B l = 0`。 -/
theorem ndFF_coeff_of_lt (B : ℚ) {l m : ℕ} (h : l < m) : (ndFF B l).coeff m = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [ndFF_natDegree]; exact h)

/-- 辅助引理（T4.1(c)）：`[X^l] ndFF B (l+1) = −Σ_{j≤l} (B + j)`。 -/
theorem ndFF_coeff_pred (B : ℚ) (l : ℕ) :
    (ndFF B (l + 1)).coeff l = -∑ j ∈ range (l + 1), (B + j) := by
  have h := prod_X_sub_C_coeff_card_pred (range (l + 1)) (fun j : ℕ => B + j) (by simp)
  rw [card_range, Nat.add_sub_cancel] at h
  exact h

/-- 辅助引理（T4.1）：`ndFF B (l+1) = ndFF B l · (X − (B + l))`。 -/
theorem ndFF_succ (B : ℚ) (l : ℕ) : ndFF B (l + 1) = ndFF B l * (X - C (B + l)) := by
  simp only [ndFF, prod_range_succ]

/-- 报告的 `p_d`，取 Newton 形式：`p_d(X) = Σ_{l≤2d} T_{d,l}·C(X − (2d+2), l)`，
其中 `C(X − B, l) = ndFF B l / l!`。由 `T4_1_a`，它就是 T4.1(a) 中唯一的多项式。 -/
noncomputable def ndPoly (d : ℕ) : ℚ[X] :=
  ∑ l ∈ range (2 * d + 1), C ((ndT d l : ℚ) / (l ! : ℚ)) * ndFF (2 * d + 2) l

/-- 辅助引理（T4.1）：两端之外的项都为 0 时可以改变求和上限。 -/
theorem ndSum_range_eq {β : Type*} [AddCommMonoid β] {f : ℕ → β} {a b : ℕ}
    (ha : ∀ q, a ≤ q → f q = 0) (hb : ∀ q, b ≤ q → f q = 0) :
    ∑ q ∈ range a, f q = ∑ q ∈ range b, f q := by
  rcases le_total a b with hab | hab
  · rw [← sum_range_add_sum_Ico f hab, sum_eq_zero (fun q hq => ha q (mem_Ico.mp hq).1), add_zero]
  · rw [← sum_range_add_sum_Ico f hab, sum_eq_zero (fun q hq => hb q (mem_Ico.mp hq).1), add_zero]

/-- 辅助引理（T4.1）：`a_d(n) = Σ_{l≤n} C(n,l)·T_{d,l}`。 -/
theorem ndSeq_newton (d n : ℕ) :
    ndSeq d n = ∑ l ∈ range (n + 1), (n.choose l : ℤ) * ndT d l :=
  ndNC_newton (ndSeq d) n

/-- 辅助引理（T4.1）：`p_d(2d+2+n) = a_d(n) = D(2d+2+n, d)`（一切 `n ≥ 0`）。 -/
theorem ndPoly_eval (d n : ℕ) : (ndPoly d).eval ((2 * d + 2 : ℚ) + n) = (ndSeq d n : ℚ) := by
  rw [ndPoly, eval_finsetSum]
  simp only [eval_mul, eval_C, ndFF_eval]
  have h1 : ∀ l ∈ range (2 * d + 1), (ndT d l : ℚ) / (l ! : ℚ) * (n.descFactorial l : ℚ)
      = (n.choose l : ℚ) * (ndT d l : ℚ) := by
    intro l _
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    have : (l ! : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [sum_congr rfl h1, ndSeq_newton]
  push_cast
  apply ndSum_range_eq
  · intro q hq
    rw [(ndT_main d).2.1 q (by omega)]
    simp
  · intro q hq
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- 辅助引理（T4.1）：`ndPoly_eval`，取值点用等式给出。 -/
theorem ndPoly_eval' (d n : ℕ) (x : ℚ) (hx : x = 2 * d + 2 + n) :
    (ndPoly d).eval x = (ndSeq d n : ℚ) := by
  rw [hx]
  exact ndPoly_eval d n

/-- 辅助引理（T4.1(a)）：`D(k,d) = p_d(k)`（`k ≥ 2d+2`）。 -/
theorem ndPoly_spec (d k : ℕ) (hk : 2 * d + 2 ≤ k) :
    (N k (k - d) : ℚ) = (ndPoly d).eval (k : ℚ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = 2 * d + 2 + n := ⟨k - (2 * d + 2), by omega⟩
  have h := ndPoly_eval d n
  rw [ndSeq_eq d n (2 * d + 2 + n) (2 * d + 2 + n - d) (by omega) (by omega)] at h
  push_cast at h ⊢
  rw [h]

/-- 辅助引理（T4.1(a)）：在一切 `k ≥ K` 处取值相同的两个多项式相等。 -/
theorem ndPoly_eq_of_eval_ge {p q : ℚ[X]} (K : ℕ)
    (h : ∀ k : ℕ, K ≤ k → p.eval (k : ℚ) = q.eval (k : ℚ)) : p = q := by
  apply eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => ((K + n : ℕ) : ℚ)) := by
    intro a b hab
    simp only [Nat.cast_add, add_right_inj, Nat.cast_inj] at hab
    exact hab
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨n, rfl⟩
  exact h (K + n) (by omega)

/-- **T4.1(a)**：对每个 `d ≥ 0`，存在唯一的 `p_d ∈ ℚ[X]` 使 `D(k,d) = N(k,k−d) = p_d(k)` 对一切
`k ≥ 2d+2` 成立。 -/
theorem T4_1_a (d : ℕ) :
    ∃! p : ℚ[X], ∀ k : ℕ, 2 * d + 2 ≤ k → (N k (k - d) : ℚ) = p.eval (k : ℚ) :=
  ⟨ndPoly d, fun k hk => ndPoly_spec d k hk, fun p hp =>
    ndPoly_eq_of_eval_ge (2 * d + 2) fun k hk => by rw [← hp k hk, ndPoly_spec d k hk]⟩

/-- 辅助引理（T4.1(a)）：满足 T4.1(a) 条件的多项式就是 `ndPoly d`。 -/
theorem eq_ndPoly {d : ℕ} {p : ℚ[X]}
    (hp : ∀ k : ℕ, 2 * d + 2 ≤ k → (N k (k - d) : ℚ) = p.eval (k : ℚ)) : p = ndPoly d :=
  ndPoly_eq_of_eval_ge (2 * d + 2) fun k hk => by rw [← hp k hk, ndPoly_spec d k hk]

/-- 辅助引理（T4.1(b)）：`[X^{2d}] p_d = T_{d,2d}/(2d)!`。 -/
theorem ndPoly_coeff_top (d : ℕ) :
    (ndPoly d).coeff (2 * d) = (ndT d (2 * d) : ℚ) / ((2 * d) ! : ℚ) := by
  rw [ndPoly, finsetSum_coeff, sum_range_succ, sum_eq_zero, zero_add, coeff_C_mul,
    ndFF_coeff_self, mul_one]
  intro l hl
  rw [coeff_C_mul, ndFF_coeff_of_lt _ (mem_range.mp hl), mul_zero]

/-- 辅助引理（T4.1(b)）：`deg p_d ≤ 2d`。 -/
theorem ndPoly_natDegree_le (d : ℕ) : (ndPoly d).natDegree ≤ 2 * d := by
  rw [ndPoly]
  apply natDegree_sum_le_of_forall_le
  intro l hl
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [ndFF_natDegree]
  have := mem_range.mp hl
  omega

/-- 辅助引理（T4.1(b)）：`deg p_d = 2d`。 -/
theorem ndPoly_natDegree (d : ℕ) : (ndPoly d).natDegree = 2 * d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (ndPoly_natDegree_le d)
  rw [ndPoly_coeff_top]
  have h := (ndT_main d).1 (2 * d) le_rfl
  have h' : (ndT d (2 * d) : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  exact div_ne_zero h' (by positivity)

/-- 辅助引理（T4.1(b)）：`(2d)! = 2^d·d!·(2d−1)!!`。 -/
theorem ndFact_eq (d : ℕ) : (2 * d) ! = 2 ^ d * d ! * (2 * d - 1)‼ := by
  rcases d with _ | e
  · rfl
  · have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * e + 1)
    have h2 := Nat.doubleFactorial_two_mul (e + 1)
    have h3 : 2 * (e + 1) = 2 * e + 1 + 1 := by ring
    have h4 : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
    rw [h4, h3, h1, ← h3, h2]

/-- 辅助引理（T4.1(b)）：首项系数 `2/(2^d·d!)`。 -/
theorem ndPoly_leadingCoeff (d : ℕ) : (ndPoly d).leadingCoeff = 2 / (2 ^ d * d ! : ℚ) := by
  rw [leadingCoeff, ndPoly_natDegree, ndPoly_coeff_top, (ndT_main d).2.2.1, ndFact_eq]
  have h1 : ((2 * d - 1)‼ : ℚ) ≠ 0 := by positivity
  have h2 : (d ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- 辅助引理（T4.1(c)）：`Σ_{j<n} j = n(n−1)/2`（在 ℚ 中）。 -/
theorem ndSum_id (n : ℕ) : ∑ j ∈ range n, (j : ℚ) = (n : ℚ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- 辅助引理（T4.1(c)）：`d ≥ 1` 时次首项系数 `= 首项系数 × (−(4d²−3d))`。 -/
theorem ndPoly_coeff_sub (d : ℕ) (hd : 1 ≤ d) :
    (ndPoly d).coeff (2 * d - 1) = (ndPoly d).leadingCoeff * (-(4 * (d : ℚ) ^ 2 - 3 * d)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hsec := (ndT_main (e + 1)).2.2.2 (by omega)
  have i1 : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
  have i2 : 2 * (e + 1) = 2 * e + 1 + 1 := by ring
  rw [i1, i2] at hsec
  rw [leadingCoeff, ndPoly_natDegree, ndPoly_coeff_top, i1, i2]
  have hc : (ndPoly (e + 1)).coeff (2 * e + 1) =
      (ndT (e + 1) (2 * e + 1) : ℚ) / ((2 * e + 1) ! : ℚ)
        - (ndT (e + 1) (2 * e + 1 + 1) : ℚ) / ((2 * e + 1 + 1) ! : ℚ) *
          ∑ j ∈ range (2 * e + 1 + 1), ((2 * ((e + 1 : ℕ) : ℚ) + 2) + j) := by
    rw [ndPoly, finsetSum_coeff, show 2 * (e + 1) + 1 = 2 * e + 1 + 1 + 1 by ring,
      sum_range_succ, sum_range_succ, sum_eq_zero, zero_add, coeff_C_mul, coeff_C_mul,
      ndFF_coeff_self, ndFF_coeff_pred]
    · ring
    · intro l hl
      rw [coeff_C_mul, ndFF_coeff_of_lt _ (by have := mem_range.mp hl; omega), mul_zero]
  rw [hc, hsec, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ndSum_id,
    Nat.factorial_succ (2 * e + 1)]
  have hF : ((2 * e + 1) ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### T4.1(d)：缺陷值 -/

/-- `p_{d−j}`（`j ≤ d`），否则为 0。 -/
noncomputable def ndPolySub (d j : ℕ) : ℚ[X] := if j ≤ d then ndPoly (d - j) else 0

/-- 辅助引理（T4.1(d)）：`p_{d−j}(2d+2+m−2j) = a_{d−j}(m)`（`j > d` 时两边都是 0）。 -/
theorem ndPolySub_eval (d j m : ℕ) (x : ℚ) (hx : x = 2 * (d : ℚ) + 2 + m - 2 * j) :
    (ndPolySub d j).eval x = (ndSub d j m : ℚ) := by
  unfold ndPolySub ndSub
  split_ifs with h
  · apply ndPoly_eval' (d - j) m x
    rw [hx]
    push_cast [Nat.cast_sub h]
    ring
  · simp

/-- 辅助引理（T4.1(d)）：多项式恒等式（报告证明的 (c)），`d ≥ 1`：
`p_d(X) − p_d(X−1) = p_{d−1}(X−1) + (X−d−1)·[p_{d−1}(X−3) + 2p_{d−2}(X−3) + p_{d−3}(X−3)]`
（`p_{d′} = 0`，`d′ < 0`）。 -/
theorem ndPoly_diff (d : ℕ) (hd : 1 ≤ d) :
    ndPoly d - (ndPoly d).comp (X - C 1) =
      (ndPolySub d 1).comp (X - C 1) + (X - C ((d : ℚ) + 1)) *
        ((ndPolySub d 1).comp (X - C 3) + C 2 * (ndPolySub d 2).comp (X - C 3)
          + (ndPolySub d 3).comp (X - C 3)) := by
  apply ndPoly_eq_of_eval_ge (2 * d + 3)
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = 2 * d + 3 + n := ⟨k - (2 * d + 3), by omega⟩
  generalize hx : ((2 * d + 3 + n : ℕ) : ℚ) = x
  have hx' : x = 2 * (d : ℚ) + 3 + n := by
    rw [← hx]
    push_cast
    ring
  simp only [eval_sub, eval_add, eval_mul, eval_comp, eval_X, eval_C]
  rw [ndPoly_eval' d (n + 1) x (by rw [hx']; push_cast; ring),
    ndPoly_eval' d n (x - 1) (by rw [hx']; ring),
    ndPolySub_eval d 1 (n + 2) (x - 1) (by rw [hx']; push_cast; ring),
    ndPolySub_eval d 1 n (x - 3) (by rw [hx']; push_cast; ring),
    ndPolySub_eval d 2 (n + 2) (x - 3) (by rw [hx']; push_cast; ring),
    ndPolySub_eval d 3 (n + 4) (x - 3) (by rw [hx']; push_cast; ring)]
  have h' : (ndSeq d (n + 1) : ℚ) = ndSeq d n + ndSub d 1 (n + 2)
      + ((d : ℚ) + 2 + n) * (ndSub d 1 n + 2 * ndSub d 2 (n + 2) + ndSub d 3 (n + 4)) := by
    exact_mod_cast ndSeq_succ d n hd
  rw [h', hx']
  ring

/-- 辅助引理（T4.1(d)）：`ndPoly_diff` 在任意点 `x` 处取值。 -/
theorem ndPoly_diff_eval (d : ℕ) (hd : 1 ≤ d) (x : ℚ) :
    (ndPoly d).eval x - (ndPoly d).eval (x - 1) =
      (ndPolySub d 1).eval (x - 1) + (x - (d + 1)) *
        ((ndPolySub d 1).eval (x - 3) + 2 * (ndPolySub d 2).eval (x - 3)
          + (ndPolySub d 3).eval (x - 3)) := by
  have h := congrArg (eval x) (ndPoly_diff d hd)
  simpa only [eval_sub, eval_add, eval_mul, eval_comp, eval_X, eval_C] using h

/-- 辅助引理（T4.1）：`p_0 = 2`。 -/
theorem ndPoly_zero : ndPoly 0 = C 2 := by
  rw [ndPoly, show 2 * 0 + 1 = 1 from rfl, sum_range_one, ndT_zero_zero]
  simp [ndFF]

/-- 缺陷 `e_d(2d+1) = D(2d+1,d) − p_d(2d+1)`。 -/
noncomputable def ndE1 (d : ℕ) : ℚ := (N (2 * d + 1) (d + 1) : ℚ) - (ndPoly d).eval (2 * (d : ℚ) + 1)

/-- 缺陷 `e_d(2d) = D(2d,d) − p_d(2d)`。 -/
noncomputable def ndE0 (d : ℕ) : ℚ := (N (2 * d) d : ℚ) - (ndPoly d).eval (2 * (d : ℚ))

/-- 辅助引理（T4.1(d)）：`e_{d}(2d+1) = −(d+1)·e_{d−1}(2d−1)`（写成 `d = e+1`）。 -/
theorem ndE1_succ (e : ℕ) : ndE1 (e + 1) = -((e : ℚ) + 2) * ndE1 e := by
  have hsub1 : ndPolySub (e + 1) 1 = ndPoly e := by simp [ndPolySub]
  have hA := ndPoly_diff_eval (e + 1) (by omega) (2 * (e : ℚ) + 4)
  rw [ndPoly_eval' (e + 1) 0 (2 * (e : ℚ) + 4) (by push_cast; ring),
    ndPolySub_eval (e + 1) 1 1 (2 * (e : ℚ) + 4 - 1) (by push_cast; ring),
    ndPolySub_eval (e + 1) 2 1 (2 * (e : ℚ) + 4 - 3) (by push_cast; ring),
    ndPolySub_eval (e + 1) 3 3 (2 * (e : ℚ) + 4 - 3) (by push_cast; ring), hsub1,
    show (2 * (e : ℚ) + 4 - 3) = 2 * (e : ℚ) + 1 by ring,
    show (2 * (e : ℚ) + 4 - 1) = 2 * ((e + 1 : ℕ) : ℚ) + 1 by push_cast; ring,
    ndSeq_eq (e + 1) 0 (2 * e + 1 + 3) (e + 2 + 1) (by omega) (by omega),
    ndSub_eq (e + 1) 1 1 (2 * e + 1 + 2) (e + 2 + 1) (by omega) (by omega) (by omega),
    ndSub_eq (e + 1) 2 1 (2 * e + 1) (e + 2) (by omega) (by omega) (by omega),
    ndSub_eq (e + 1) 3 3 (2 * e + 1) (e + 2 + 1) (by omega) (by omega) (by omega)] at hA
  have hT : (N (2 * e + 1 + 3) (e + 2 + 1) : ℚ) = N (2 * e + 1 + 2) (e + 2)
      + N (2 * e + 1 + 2) (e + 2 + 1) + ((e : ℚ) + 2) * (N (2 * e + 1) (e + 1)
        + 2 * N (2 * e + 1) (e + 2) + N (2 * e + 1) (e + 2 + 1)) := by
    have h := N_tri (2 * e + 1) (e + 2)
    rw [show e + 2 - 1 = e + 1 by omega] at h
    exact_mod_cast h
  have hN : N (2 * (e + 1) + 1) (e + 1 + 1) = N (2 * e + 1 + 2) (e + 2) := by
    rw [show 2 * (e + 1) + 1 = 2 * e + 1 + 2 by ring]
  unfold ndE1
  rw [hN]
  push_cast at hA ⊢
  linear_combination hA - hT

/-- 辅助引理（T4.1(d)）：`e_d(2d) = e_d(2d+1) − d·e_{d−1}(2d−2)`（写成 `d = e+1`）。 -/
theorem ndE0_succ (e : ℕ) : ndE0 (e + 1) = ndE1 (e + 1) - ((e : ℚ) + 1) * ndE0 e := by
  have hsub1 : ndPolySub (e + 1) 1 = ndPoly e := by simp [ndPolySub]
  have hB := ndPoly_diff_eval (e + 1) (by omega) (2 * (e : ℚ) + 3)
  rw [ndPolySub_eval (e + 1) 1 0 (2 * (e : ℚ) + 3 - 1) (by push_cast; ring),
    ndPolySub_eval (e + 1) 2 0 (2 * (e : ℚ) + 3 - 3) (by push_cast; ring),
    ndPolySub_eval (e + 1) 3 2 (2 * (e : ℚ) + 3 - 3) (by push_cast; ring), hsub1,
    ndSub_eq (e + 1) 1 0 (2 * e + 2) (e + 1 + 1) (by omega) (by omega) (by omega),
    ndSub_eq (e + 1) 2 0 (2 * e) (e + 1) (by omega) (by omega) (by omega),
    ndSub_eq (e + 1) 3 2 (2 * e) (e + 1 + 1) (by omega) (by omega) (by omega),
    show (2 * (e : ℚ) + 3 - 3) = 2 * (e : ℚ) by ring,
    show (2 * (e : ℚ) + 3 - 1) = 2 * ((e + 1 : ℕ) : ℚ) by push_cast; ring,
    show (2 * (e : ℚ) + 3) = 2 * ((e + 1 : ℕ) : ℚ) + 1 by push_cast; ring] at hB
  have hT : (N (2 * e + 3) (e + 1 + 1) : ℚ) = N (2 * e + 2) (e + 1) + N (2 * e + 2) (e + 1 + 1)
      + ((e : ℚ) + 1) * (N (2 * e) e + 2 * N (2 * e) (e + 1) + N (2 * e) (e + 1 + 1)) := by
    have h := N_tri (2 * e) (e + 1)
    rw [show e + 1 - 1 = e by omega] at h
    exact_mod_cast h
  have hN1 : N (2 * (e + 1) + 1) (e + 1 + 1) = N (2 * e + 3) (e + 1 + 1) := by
    rw [show 2 * (e + 1) + 1 = 2 * e + 3 by ring]
  have hN0 : N (2 * (e + 1)) (e + 1) = N (2 * e + 2) (e + 1) := by
    rw [show 2 * (e + 1) = 2 * e + 2 by ring]
  unfold ndE0 ndE1
  rw [hN1, hN0]
  push_cast at hB ⊢
  linear_combination hB - hT

/-- 辅助引理（T4.1(d)）：`e_d(2d+1) = (−1)^{d+1}(d+1)!`。 -/
theorem ndE1_closed (d : ℕ) : ndE1 d = (-1) ^ (d + 1) * ((d + 1) ! : ℚ) := by
  induction d with
  | zero =>
    unfold ndE1
    rw [ndPoly_zero, eval_C]
    norm_num [N_init.2.1]
  | succ e ih =>
    rw [ndE1_succ, ih, Nat.factorial_succ (e + 1)]
    push_cast
    ring

/-- 辅助引理（T4.1(d)）：`e_d(2d) = (−1)^{d+1}(d+2)!/2`。 -/
theorem ndE0_closed (d : ℕ) : ndE0 d = (-1) ^ (d + 1) * ((d + 2) ! : ℚ) / 2 := by
  induction d with
  | zero =>
    unfold ndE0
    rw [ndPoly_zero, eval_C]
    norm_num [N_init.1]
  | succ e ih =>
    rw [ndE0_succ, ndE1_closed, ih]
    have f1 : ((e + 1 + 1) ! : ℚ) = ((e : ℚ) + 2) * (e + 1) ! := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have f3 : ((e + 1 + 2) ! : ℚ) = ((e : ℚ) + 3) * ((e : ℚ) + 2) * (e + 1) ! := by
      rw [show e + 1 + 2 = e + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [f1, f3]
    ring

/-- **T4.1**（汇总）。对每个 `d ≥ 0`（`D(k,d) = N(k,k−d)`）：
* (a) 存在唯一 `p_d ∈ ℚ[X]` 使 `D(k,d) = p_d(k)` 对一切 `k ≥ 2d+2` 成立；
* 对这个 `p_d`（即任何满足 (a) 的多项式）：
  (b) `deg p_d = 2d`，首项系数 `2/(2^d·d!)`；
  (c) `d ≥ 1` 时次首项系数 = 首项系数 × `(−(4d²−3d))`（`d = 0` 时 `p_0 = 2` 没有次首项）；
  (d) 缺陷 `e_d(k) := D(k,d) − p_d(k)` 满足 `e_d(2d+1) = (−1)^{d+1}(d+1)!`，
  `e_d(2d) = (−1)^{d+1}(d+2)!/2`（`d = 0` 时 `k = 0`，`N(0,0) = 1`）。 -/
theorem T4_1 (d : ℕ) :
    (∃! p : ℚ[X], ∀ k : ℕ, 2 * d + 2 ≤ k → (N k (k - d) : ℚ) = p.eval (k : ℚ)) ∧
    ∀ p : ℚ[X], (∀ k : ℕ, 2 * d + 2 ≤ k → (N k (k - d) : ℚ) = p.eval (k : ℚ)) →
      p.natDegree = 2 * d ∧ p.leadingCoeff = 2 / (2 ^ d * d ! : ℚ) ∧
      (1 ≤ d → p.coeff (2 * d - 1) = p.leadingCoeff * (-(4 * (d : ℚ) ^ 2 - 3 * d))) ∧
      (N (2 * d + 1) (2 * d + 1 - d) : ℚ) - p.eval ((2 * d + 1 : ℕ) : ℚ)
        = (-1) ^ (d + 1) * ((d + 1) ! : ℚ) ∧
      (N (2 * d) (2 * d - d) : ℚ) - p.eval ((2 * d : ℕ) : ℚ)
        = (-1) ^ (d + 1) * ((d + 2) ! : ℚ) / 2 := by
  refine ⟨T4_1_a d, fun p hp => ?_⟩
  obtain rfl := eq_ndPoly hp
  refine ⟨ndPoly_natDegree d, ndPoly_leadingCoeff d, ndPoly_coeff_sub d, ?_, ?_⟩
  · rw [show 2 * d + 1 - d = d + 1 by omega, ← ndE1_closed d, ndE1]
    push_cast
    rfl
  · rw [show 2 * d - d = d by omega, ← ndE0_closed d, ndE0]
    push_cast
    rfl

/-- **T4.1**（门槛精确）：没有多项式在一切 `k ≥ 2d+1` 处等于 `D(k,d)`，即 `k = 2d+1` 永远是例外。 -/
theorem T4_1_threshold (d : ℕ) :
    ¬ ∃ p : ℚ[X], ∀ k : ℕ, 2 * d + 1 ≤ k → (N k (k - d) : ℚ) = p.eval (k : ℚ) := by
  rintro ⟨p, hp⟩
  have hpd : p = ndPoly d := eq_ndPoly fun k hk => hp k (by omega)
  have h1 := hp (2 * d + 1) le_rfl
  rw [hpd, show 2 * d + 1 - d = d + 1 by omega] at h1
  have h2 := ndE1_closed d
  unfold ndE1 at h2
  push_cast at h1
  rw [h1, sub_self] at h2
  have h3 : ((d + 1) ! : ℚ) ≠ 0 := by positivity
  have h4 : ((-1 : ℚ)) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero h4 h3 h2.symm

/-- **T4.1**（`d ≤ 1` 的显式式子）：`p_0 = 2`，`p_1 = k² − k − 4`。 -/
theorem ndPoly_zero_one : ndPoly 0 = C 2 ∧ ndPoly 1 = X ^ 2 - X - C 4 := by
  refine ⟨ndPoly_zero, ?_⟩
  symm
  apply eq_ndPoly
  intro k hk
  have := N_subdiag k (by omega)
  simp only [eval_sub, eval_pow, eval_X, eval_C]
  exact_mod_cast this

/-! ## 5. T4.2(3)：基点 `2d+2` 的 Newton 系数 -/

/-- 辅助引理（T4.2(3)）：`Δ^i p_d(2d+2) = T_{d,i}`（`Δf(K) = f(K+1) − f(K)`，作用在 `x ↦ p_d(x)` 上）。 -/
theorem ndPoly_fwdDiff (d i : ℕ) :
    (fwdDiff (1 : ℚ))^[i] (fun x => (ndPoly d).eval x) (2 * d + 2) = (ndT d i : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, ndT, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [nsmul_eq_mul, mul_one, zero_add, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  rw [ndPoly_eval]

/-- **T4.2(3)**：设 `p_d` 是 T4.1(a) 的多项式。基点 `2d+2` 的 Newton 系数
`T_{d,i} := Δ^i p_d(2d+2)`（`Δf(K) = f(K+1) − f(K)`）对 `0 ≤ i ≤ 2d` 都是正整数，
且末项 `T_{d,2d} = 2·(2d−1)!!`。 -/
theorem T4_2_3 (d : ℕ) (p : ℚ[X])
    (hp : ∀ k : ℕ, 2 * d + 2 ≤ k → (N k (k - d) : ℚ) = p.eval (k : ℚ)) :
    (∀ i, i ≤ 2 * d → ∃ t : ℕ, 0 < t ∧
      (fwdDiff (1 : ℚ))^[i] (fun x => p.eval x) (2 * d + 2) = t) ∧
    (fwdDiff (1 : ℚ))^[2 * d] (fun x => p.eval x) (2 * d + 2) = 2 * ((2 * d - 1)‼ : ℚ) := by
  obtain rfl := eq_ndPoly hp
  refine ⟨fun i hi => ⟨(ndT d i).toNat, ?_, ?_⟩, ?_⟩
  · have := (ndT_main d).1 i hi
    omega
  · have := (ndT_main d).1 i hi
    rw [ndPoly_fwdDiff]
    have h2 : ((ndT d i).toNat : ℤ) = ndT d i := Int.toNat_of_nonneg this.le
    exact_mod_cast h2.symm
  · rw [ndPoly_fwdDiff, (ndT_main d).2.2.1]
    push_cast
    ring

/-! ## 6. T5.2：`m` 的次首项系数 -/

/-- 辅助引理（T5.2）：`descPochhammer(q) ∘ (X+1) = ∏_{i<q} (X − (i−1))`。 -/
theorem ndDesc_comp (q : ℕ) : (descPochhammer ℚ q).comp (X + 1) = ndFF (-1) q := by
  induction q with
  | zero => simp [ndFF]
  | succ q ih =>
    rw [descPochhammer_succ_right, mul_comp, ih, ndFF_succ]
    congr 1
    rw [sub_comp, X_comp, natCast_comp, map_add, map_neg, map_one, map_natCast]
    ring

/-- 辅助引理（T5.2）：`C(y+1, q) = (1/q!)·∏_{i=−1}^{q−2} (y − i)`。 -/
theorem binomPoly_eq_ndFF (q : ℕ) : binomPoly q = C ((q ! : ℚ)⁻¹) * ndFF (-1) q := by
  rw [binomPoly, ndDesc_comp]

/-- 辅助引理（T5.2）：`[y^q] C(y+1, q+1) = (1/(q+1)!)·(−Σ_{i<q+1}(i−1))`。 -/
theorem binomPoly_coeff_pred (q : ℕ) :
    (binomPoly (q + 1)).coeff q
      = ((q + 1) ! : ℚ)⁻¹ * (-∑ j ∈ range (q + 1), ((-1 : ℚ) + j)) := by
  rw [binomPoly_eq_ndFF, coeff_C_mul, ndFF_coeff_pred]

/-- 辅助引理（T5.2）：`[m^k] u_{k+1}`（只有 `q = k, k+1` 两项有贡献）。 -/
theorem upoly_coeff_pred (k : ℕ) :
    (upoly (k + 1)).coeff k = (N (k + 1) (k + 1) : ℚ) *
        (((k + 1) ! : ℚ)⁻¹ * (-∑ j ∈ range (k + 1), ((-1 : ℚ) + j)))
      + (N (k + 1) k : ℚ) * ((k ! : ℚ)⁻¹) := by
  rw [upoly, finsetSum_coeff, sum_range_succ, sum_range_succ, sum_eq_zero, zero_add, coeff_C_mul,
    coeff_C_mul, binomPoly_coeff_pred, coeff_binomPoly_self]
  · ring
  · intro q hq
    rw [coeff_C_mul, coeff_binomPoly_of_lt (mem_range.mp hq), mul_zero]

/-- **T5.2**（显式，首项）：`[m^k] u_k = 2/k!`（`k ≥ 2`）。 -/
theorem T5_2_top (k : ℕ) (hk : 2 ≤ k) : (upoly k).coeff k = 2 / (k ! : ℚ) := by
  rw [coeff_upoly_self, N_diag k hk]
  push_cast
  ring

/-- **T5.2**（显式，次首项）：`[m^{k−1}] u_k = (k²−2k−1)/(k−1)!`（`k ≥ 4`）。 -/
theorem T5_2_sub (k : ℕ) (hk : 4 ≤ k) :
    (upoly k).coeff (k - 1) = ((k : ℚ) ^ 2 - 2 * k - 1) / ((k - 1) ! : ℚ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hN := N_subdiag (j + 1) hk
  rw [show j + 1 - 1 = j by omega] at hN ⊢
  have hN' : (N (j + 1) j : ℚ) = ((j : ℚ) + 1) ^ 2 - (j + 1) - 4 := by
    have := congrArg (Int.cast : ℤ → ℚ) hN
    push_cast at this
    exact this
  rw [upoly_coeff_pred, N_diag (j + 1) (by omega), hN', sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul, ndSum_id, Nat.factorial_succ j]
  have hf : (j ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **T5.2**（显式，`k = 3` 的例外）：`[m^2] u_3 = 2`（`k ≥ 4` 的公式在 `k = 3` 给 1）。 -/
theorem T5_2_sub_three : (upoly 3).coeff 2 = 2 ∧ ((3 : ℚ) ^ 2 - 2 * 3 - 1) / ((3 - 1) ! : ℚ) = 1 := by
  refine ⟨?_, by norm_num [Nat.factorial]⟩
  have h := upoly_coeff_pred 2
  rw [show (2 : ℕ) + 1 = 3 from rfl, N_diag 3 (by norm_num), N_three_two] at h
  rw [h]
  norm_num [sum_range_succ, Nat.factorial]

/-- `e_j(−1, 0, 1, …, n−2)`：数 `−1, 0, …, n−2`（共 `n` 个）的 `j` 次初等对称多项式。 -/
noncomputable def ndEsym (j n : ℕ) : ℚ :=
  ((Multiset.range n).map (fun i : ℕ => (i : ℚ) - 1)).esymm j

/-- 辅助引理（T5.2）：`ndFF (−1) q` 写成多重集乘积。 -/
theorem ndFF_neg_one_eq (q : ℕ) :
    ndFF (-1) q = (((Multiset.range q).map (fun i : ℕ => (i : ℚ) - 1)).map
      (fun t => X - C t)).prod := by
  rw [ndFF, Finset.prod_eq_multiset_prod, Multiset.map_map, Finset.range_val]
  congr 1
  apply Multiset.map_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [show (-1 : ℚ) + i = i - 1 by ring]

/-- 辅助引理（T5.2，Vieta）：`m ≤ q` 时 `[y^m] ∏_{i<q}(y − (i−1)) = (−1)^{q−m}·e_{q−m}(−1,…,q−2)`。 -/
theorem ndFF_neg_one_coeff (q m : ℕ) (hm : m ≤ q) :
    (ndFF (-1) q).coeff m = (-1) ^ (q - m) * ndEsym (q - m) q := by
  rw [ndFF_neg_one_eq, Multiset.prod_X_sub_C_coeff _ (by simpa using hm)]
  simp [ndEsym]

/-- 辅助引理（T5.2）：`m ≤ q` 时 `[y^m] C(y+1, q) = (1/q!)·(−1)^{q−m}·e_{q−m}(−1,…,q−2)`。 -/
theorem binomPoly_coeff (q m : ℕ) (hm : m ≤ q) :
    (binomPoly q).coeff m = (q ! : ℚ)⁻¹ * ((-1) ^ (q - m) * ndEsym (q - m) q) := by
  rw [binomPoly_eq_ndFF, coeff_C_mul, ndFF_neg_one_coeff q m hm]

/-- **T5.2**（公式）：记 `B_d(k) := (k−d)!·[m^{k−d}] u_k`（`u_k` 为 T1.2 的插值多项式 `upoly k`）。
对一切 `k ≥ d`：`B_d(k) = Σ_{e=0}^{d} (−1)^{d−e}·N(k,k−e)·ẽ_{d−e}(k−e)`，
`ẽ_j(n) = e_j(−1,0,…,n−2)/n^{\underline j}`（这里 `n = k−e ≥ j = d−e`，`n^{\underline j} ≠ 0`）。 -/
theorem T5_2_formula (d k : ℕ) (hk : d ≤ k) :
    ((k - d) ! : ℚ) * (upoly k).coeff (k - d) =
      ∑ e ∈ range (d + 1), (-1 : ℚ) ^ (d - e) * (N k (k - e) : ℚ) *
        (ndEsym (d - e) (k - e) / ((k - e).descFactorial (d - e) : ℚ)) := by
  set G : ℕ → ℚ := fun q => ((k - d) ! : ℚ) * (C (N k q : ℚ) * binomPoly q).coeff (k - d)
    with hG
  have h1 : ((k - d) ! : ℚ) * (upoly k).coeff (k - d) = ∑ q ∈ range (k + 1), G q := by
    rw [upoly, finsetSum_coeff, mul_sum]
  have h2 : ∑ q ∈ range (k + 1), G q = ∑ e ∈ range (k + 1), G (k - e) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun e _ => ?_
    rw [show k + 1 - 1 - e = k - e by omega]
  have h3 : ∑ e ∈ range (k + 1), G (k - e) = ∑ e ∈ range (d + 1), G (k - e) := by
    rw [← sum_range_add_sum_Ico _ (show d + 1 ≤ k + 1 by omega)]
    have hz : ∑ e ∈ Ico (d + 1) (k + 1), G (k - e) = 0 := by
      refine sum_eq_zero fun e he => ?_
      rw [mem_Ico] at he
      simp only [hG]
      rw [coeff_C_mul, coeff_binomPoly_of_lt (by omega), mul_zero, mul_zero]
    rw [hz, add_zero]
  rw [h1, h2, h3]
  refine sum_congr rfl fun e he => ?_
  have he' := mem_range.mp he
  simp only [hG]
  rw [coeff_C_mul, binomPoly_coeff (k - e) (k - d) (by omega),
    show k - e - (k - d) = d - e by omega]
  have hfd := Nat.factorial_mul_descFactorial (show d - e ≤ k - e by omega)
  rw [show k - e - (d - e) = k - d by omega] at hfd
  have hpos : ((k - e).descFactorial (d - e) : ℚ) ≠ 0 := by
    have : (k - e).descFactorial (d - e) ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
      omega
    exact_mod_cast this
  have hpos2 : ((k - d) ! : ℚ) ≠ 0 := by positivity
  rw [← hfd]
  push_cast
  field_simp

end A207123
