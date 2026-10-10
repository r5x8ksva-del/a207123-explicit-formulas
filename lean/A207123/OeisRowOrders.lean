import A207123.OeisRows
import A207123.RootAsymp

/-!
# 论文注记 3.5：行递推的阶是最小的，且等于不同乘积的个数

论文注记 3.5 的后半句：「by the Berlekamp–Massey algorithm their orders 10, 22, 28, 49, 55, 85 are minimal, and they
are the numbers of distinct products of a characteristic root of the first factor with one of the second」。本文件把它
对第 `n = 2,…,7` 行形式化：

* `row_min_order_two` … `row_min_order_seven`：`k ↦ a_k(n)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零，
  系数可取复数）的最小阶是 `e = 10, 22, 28, 49, 55, 85`（`IsLeast`）；`e` 阶的那条就是 OEIS 的经验递推
  （`OeisRows.lean`，从 `k = 0` 起成立）。
* `card_row_products_two` … `card_row_products_seven`：`σ ∈ sig ⌈n/2⌉`、`τ ∈ sig ⌊n/2⌋` 的乘积 `στ` 恰有 `e` 个不同的值。

证明：
* 最小性（`order_ge_of_hankel`）：`k ↦ a_k(n)` 从 `k = 0` 起满足 `rowPoly n` 给出的递推（`row_rec`），其常数项
  `∏(−στ) ≠ 0`。若 `d` 阶递推 `Σ_i c_i·a_{k+i}(n) = 0` 只对 `k ≥ k₀` 成立，则 `w_k = Σ_i c_i·a_{k+i}(n)` 也满足
  `rowPoly n` 的递推、且 `k ≥ k₀` 时为 0，于是向后推得 `w ≡ 0`（`eq_zero_of_rec_of_eventually`）；`d < e` 时
  `e × e` 的 Hankel 矩阵 `(a_{i+j}(n))` 就有非零的零化向量（`hankel_det_eq_zero`）。行列式非零的证书是它模 `p = 97`
  的逆矩阵 `W`：把 `[a_0(n) mod p, …, a_{2e−1}(n) mod p]` 与 `W` 的每一列（倒序）按 `B = 2^20` 进位打包成整数，
  一次乘法后第 `e − 1 + i` 位就是 `(H·W)_{ij}`（Kronecker 代换；`(p − 1)·Σ c < B` 保证没有进位），`kronCheck` 在
  内核里核对这些位模 `p` 构成单位矩阵（`hankel_det_ne_zero_of_kron`，`decide +kernel`）。
* 不同乘积的个数：每个 `σ ∈ sig m` 在某一层 `i ≤ m`（`i = 0` 时 `σ = 1`，否则 `σ³ − σ² = i`；`IsLevel`），
  `σ^l = A + Bσ + Cσ²`，`(A, B, C)` 由 `lvStep` 递推。`lvCheck` 核对每一对层上 `Σ_l γ_l (στ)^l` 约化后的 9 个系数
  都为 0，于是每个乘积都是 OEIS 特征多项式 `Σ_l γ_l X^l`（`e` 次）的根，个数 ≤ e（`card_products_le`）；反过来
  `∏_λ (X − λ)`（`λ` 取遍不同乘积）给出 `k ↦ a_k(n)` 的递推，由最小性个数 ≥ e（`card_products_ge`）。
系数表与逆矩阵的列由 `code/main_extra/oeis_row_orders_lean.py` 生成并在 Python 里核对；不用 `native_decide`。
-/

namespace A207123

open Finset Polynomial

/-! ## 向后延拓与 Hankel 矩阵 -/

/-- 辅助引理（注记 3.5）：向后延拓。若 `Σ_{j=0}^{r} p_j·w_{k+j} = 0` 对一切 `k` 成立、`p_0 ≠ 0`，且 `k ≥ k₀` 时
`w_k = 0`，则 `w ≡ 0`。 -/
theorem eq_zero_of_rec_of_eventually {w p : ℕ → ℂ} {r k0 : ℕ} (hp : p 0 ≠ 0)
    (hrec : ∀ k, ∑ j ∈ range (r + 1), p j * w (k + j) = 0) (hz : ∀ k, k0 ≤ k → w k = 0) (k : ℕ) :
    w k = 0 := by
  have key : ∀ t k, k0 ≤ k + t → w k = 0 := by
    intro t
    induction t with
    | zero => exact fun k hk => hz k (by omega)
    | succ t ih =>
      intro k hk
      have h1 := hrec k
      rw [Finset.sum_range_succ'] at h1
      have h2 : ∑ j ∈ range r, p (j + 1) * w (k + (j + 1)) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [ih (k + (j + 1)) (by omega), mul_zero]
      rw [h2, zero_add, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left hp
  exact key k0 k (by omega)

/-- 辅助引理（注记 3.5）：若 `Σ_{i=0}^{d} c_i·s_{k+i} = 0` 对一切 `k` 成立，`c_d ≠ 0`、`d < e`，则 `e × e` 的 Hankel
矩阵 `(s_{i+j})` 的行列式为 0。 -/
theorem hankel_det_eq_zero {s c : ℕ → ℂ} {d e : ℕ} (hd : d < e) (hc : c d ≠ 0)
    (h : ∀ k, ∑ i ∈ range (d + 1), c i * s (k + i) = 0) :
    (Matrix.of fun i j : Fin e => s (i + j)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => if (j : ℕ) ≤ d then c j else 0, fun hv => hc ?_, ?_⟩
  · simpa using congr_fun hv ⟨d, hd⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => s (i + j) * if j ≤ d then c j else 0) e,
      ← Finset.sum_range_add_sum_Ico _ (show d + 1 ≤ e by omega)]
    have h0 : ∑ j ∈ Ico (d + 1) e, (s (i + j) * if j ≤ d then c j else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [Finset.mem_Ico] at hj
        rw [ite_eq_right (by omega), mul_zero]
    rw [h0, add_zero, ← h i]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [ite_eq_left (by omega), mul_comm]

/-- 辅助引理（注记 3.5）：设 `Σ_{j=0}^{r} p_j·s_{k+j} = 0` 对一切 `k` 成立、`p_0 ≠ 0`，且 `e × e` 的 Hankel 行列式
`det (s_{i+j})` 非零。若 `Σ_{i=0}^{d} c_i·s_{k+i} = 0`（`c_d ≠ 0`）对一切 `k ≥ k₀` 成立，则 `d ≥ e`。 -/
theorem order_ge_of_hankel {s p c : ℕ → ℂ} {r e d k0 : ℕ} (hp : p 0 ≠ 0)
    (hrec : ∀ k, ∑ j ∈ range (r + 1), p j * s (k + j) = 0)
    (hH : (Matrix.of fun i j : Fin e => s (i + j)).det ≠ 0) (hc : c d ≠ 0)
    (h : ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * s (k + i) = 0) : e ≤ d := by
  by_contra hlt
  have hrw : ∀ k, ∑ j ∈ range (r + 1), p j * ∑ i ∈ range (d + 1), c i * s (k + j + i) = 0 := by
    intro k
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc ∑ j ∈ range (r + 1), p j * (c i * s (k + j + i))
        = c i * ∑ j ∈ range (r + 1), p j * s (k + i + j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show k + j + i = k + i + j by omega]
          ring
      _ = 0 := by rw [hrec (k + i), mul_zero]
  have hw := eq_zero_of_rec_of_eventually (w := fun k => ∑ i ∈ range (d + 1), c i * s (k + i)) hp hrw h
  exact hH (hankel_det_eq_zero (by omega) hc hw)

/-- 辅助引理（注记 3.5）：`rowPoly n` 的常数项非零（各根 `στ` 都非零）。 -/
theorem rowPoly_coeff_zero_ne (n : ℕ) : (rowPoly n).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero, rowPoly, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
  rw [Finset.mem_product] at hq
  rw [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
  exact mul_ne_zero (mem_sig.mp hq.1).1 (mem_sig.mp hq.2).1

/-- 辅助引理（注记 3.5）：若 `e × e` 的 Hankel 行列式 `det (a_{i+j}(n))` 非零，则 `k ↦ a_k(n)` 的常系数递推
`Σ_{i=0}^{d} c_i·a_{k+i}(n) = 0`（`c_d ≠ 0`，对一切 `k ≥ k₀` 成立）的阶 `d ≥ e`。 -/
theorem row_order_ge {n e d k0 : ℕ} {c : ℕ → ℂ}
    (hH : (Matrix.of fun i j : Fin e => (a (i + j) n : ℂ)).det ≠ 0) (hc : c d ≠ 0)
    (h : ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) n : ℂ) = 0) : e ≤ d :=
  order_ge_of_hankel (s := fun k => (a k n : ℂ)) (p := fun i => (rowPoly n).coeff i)
    (rowPoly_coeff_zero_ne n) (row_rec n) hH hc h

/-- 辅助引理（注记 3.5）：设 `γ_e = 1`、`Σ_{i=0}^{e} γ_i·a_{k+i}(n) = 0` 对一切 `k` 成立，且 `e × e` 的 Hankel 行列式
非零；则 `e` 是 `k ↦ a_k(n)` 的常系数递推的最小阶。 -/
theorem row_isLeast {n e : ℕ} {γ : List ℤ} (htop : γ.getD e 0 = 1)
    (hrec : ∀ k, ∑ i ∈ range (e + 1), (γ.getD i 0 : ℂ) * (a (k + i) n : ℂ) = 0)
    (hH : (Matrix.of fun i j : Fin e => (a (i + j) n : ℂ)).det ≠ 0) :
    IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
      ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) n : ℂ) = 0} e :=
  ⟨⟨0, fun i => (γ.getD i 0 : ℂ), by show ((γ.getD e 0 : ℤ) : ℂ) ≠ 0; rw [htop]; norm_num,
      fun k _ => hrec k⟩,
    fun _ ⟨_, _, hc, h⟩ => row_order_ge hH hc h⟩

/-! ## Hankel 行列式非零的证书：模 `p` 的逆矩阵（Kronecker 打包） -/

/-- `ofDig B [d₀, d₁, …] = d₀ + B·d₁ + B²·d₂ + …`。 -/
def ofDig (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + B * ofDig B ds

/-- `digs B x c = [x mod B, ⌊x/B⌋ mod B, …]`（前 `c` 位）。 -/
def digs (B : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | x, c + 1 => (x % B) :: digs B (x / B) c

/-- 长 `e`、第 `i` 位为 1、其余为 0 的列表。 -/
def hkUnit : ℕ → ℕ → List ℕ
  | 0, _ => []
  | e + 1, 0 => 1 :: List.replicate e 0
  | e + 1, i + 1 => 0 :: hkUnit e i

/-- Kronecker 核对。`S` 是打包的 `[s_0, s_1, …]`；对第 `j` 列 `c`（`e` 个数，`c_t = W_{e−1−t, j}`）：`c` 长 `e`，
`(p − 1)·Σ c < B`，且 `S·ofDig B c` 的第 `e − 1 + i` 位（`i < e`）模 `p` 是 `δ_{ij}`。 -/
def kronCheck (p B e S : ℕ) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | c :: cs, j => (c.length == e) && decide ((p - 1) * c.sum < B) &&
      ((digs B (S * ofDig B c / B ^ (e - 1)) e).map (· % p) == hkUnit e j) && kronCheck p B e S cs (j + 1)

/-- 列表对应的多项式 `Σ_k L_k X^k`（只在证明里用）。 -/
noncomputable def listPoly : List ℕ → ℕ[X]
  | [] => 0
  | d :: ds => C d + X * listPoly ds

/-- 辅助引理（注记 3.5）：`listPoly L` 在 `B` 处的值是 `ofDig B L`。 -/
theorem eval_listPoly (B : ℕ) : ∀ L : List ℕ, (listPoly L).eval B = ofDig B L
  | [] => by simp [listPoly, ofDig]
  | d :: ds => by simp [listPoly, ofDig, eval_listPoly B ds]

/-- 辅助引理（注记 3.5）：`listPoly L` 的系数是 `L` 的各项（超出部分为 0）。 -/
theorem coeff_listPoly : ∀ (L : List ℕ) (k : ℕ), (listPoly L).coeff k = L.getD k 0
  | [], k => by simp [listPoly]
  | d :: ds, 0 => by simp [listPoly]
  | d :: ds, k + 1 => by
    simp only [listPoly, coeff_add, coeff_C_succ, coeff_X_mul, zero_add, List.getD_cons_succ]
    exact coeff_listPoly ds k

/-- 辅助引理（注记 3.5）：系数都小于 `B` 时，`P(B)` 的第 `m` 位（`B` 进制）就是 `P` 的 `X^m` 系数。 -/
theorem digit_eval {B : ℕ} (hB : 0 < B) : ∀ (m : ℕ) (P : ℕ[X]), (∀ k, P.coeff k < B) →
    P.eval B / B ^ m % B = P.coeff m
  | 0, P, h => by
    have hP := X_mul_divX_add P
    rw [pow_zero, Nat.div_one]
    conv_lhs => rw [← hP]
    rw [eval_add, eval_mul, eval_X, eval_C, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0)]
  | m + 1, P, h => by
    have hP := X_mul_divX_add P
    have hd : P.eval B / B = (divX P).eval B := by
      conv_lhs => rw [← hP]
      rw [eval_add, eval_mul, eval_X, eval_C, add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (h 0),
        zero_add]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, hd,
      digit_eval hB m (divX P) fun k => by rw [coeff_divX]; exact h _, coeff_divX]

/-- 辅助引理（注记 3.5）：`digs` 的第 `i` 位。 -/
theorem getD_digs (B : ℕ) : ∀ (x c i : ℕ), i < c → (digs B x c).getD i 0 = x / B ^ i % B
  | _, 0, i, h => absurd h (Nat.not_lt_zero i)
  | x, c + 1, 0, _ => by simp [digs]
  | x, c + 1, i + 1, h => by
    simp only [digs, List.getD_cons_succ]
    rw [getD_digs B (x / B) c i (by omega), Nat.div_div_eq_div_mul, ← pow_succ']

/-- 辅助引理（注记 3.5）：列表的部分和不超过总和。 -/
theorem sum_range_getD_le : ∀ (c : List ℕ) (m : ℕ), ∑ t ∈ range m, c.getD t 0 ≤ c.sum
  | [], m => by simp
  | _ :: _, 0 => by simp
  | x :: xs, m + 1 => by
    rw [Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have := sum_range_getD_le xs m
    omega

/-- 辅助引理（注记 3.5）：乘积的系数写成按 `k` 的和。 -/
theorem coeff_mul_eq_sum_range (P Q : ℕ[X]) (m : ℕ) :
    (P * Q).coeff m = ∑ k ∈ range (m + 1), P.coeff k * Q.coeff (m - k) := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k t => P.coeff k * Q.coeff t) m

/-- 辅助引理（注记 3.5）：`P` 的系数都 `≤ p − 1`、`Q` 的系数是列表 `c` 时，`P·Q` 的系数都 `≤ (p − 1)·Σ c`。 -/
theorem coeff_mul_le {P Q : ℕ[X]} {p : ℕ} (c : List ℕ) (hP : ∀ k, P.coeff k ≤ p - 1)
    (hQ : ∀ t, Q.coeff t = c.getD t 0) (m : ℕ) : (P * Q).coeff m ≤ (p - 1) * c.sum := by
  have hrefl : ∑ k ∈ range (m + 1), Q.coeff (m - k) = ∑ t ∈ range (m + 1), c.getD t 0 := by
    rw [← Finset.sum_range_reflect (fun t => c.getD t 0) (m + 1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    simp only [hQ, show m + 1 - 1 - k = m - k by omega]
  rw [coeff_mul_eq_sum_range]
  calc ∑ k ∈ range (m + 1), P.coeff k * Q.coeff (m - k)
      ≤ ∑ k ∈ range (m + 1), (p - 1) * Q.coeff (m - k) :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (hP k)
    _ = (p - 1) * ∑ t ∈ range (m + 1), c.getD t 0 := by rw [← Finset.mul_sum, hrefl]
    _ ≤ (p - 1) * c.sum := Nat.mul_le_mul_left _ (sum_range_getD_le c _)

/-- 辅助引理（注记 3.5）：`Q` 的系数是长 `e` 的列表 `c` 时，`P·Q` 的 `X^{e−1+i}` 系数是
`Σ_{l<e} P_{i+l}·c_{e−1−l}`。 -/
theorem coeff_mul_mid {P Q : ℕ[X]} {e : ℕ} (c : List ℕ) (hc : c.length = e)
    (hQ : ∀ t, Q.coeff t = c.getD t 0) (he : 0 < e) (i : ℕ) :
    (P * Q).coeff (e - 1 + i) = ∑ l ∈ range e, P.coeff (i + l) * c.getD (e - 1 - l) 0 := by
  rw [coeff_mul_eq_sum_range, show e - 1 + i + 1 = i + e by omega, Finset.sum_range_add]
  have h1 : ∑ k ∈ range i, P.coeff k * Q.coeff (e - 1 + i - k) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_range] at hk
      rw [hQ, List.getD_eq_default _ _ (by omega), mul_zero]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  rw [hQ, show e - 1 + i - (i + l) = e - 1 - l by omega]

/-- 辅助引理（注记 3.5）：`(r.map (· % p))` 的各项。 -/
theorem getD_map_mod (p : ℕ) : ∀ (r : List ℕ) (j : ℕ), (r.map (· % p)).getD j 0 = r.getD j 0 % p
  | [], j => by simp
  | y :: ys, 0 => by simp
  | y :: ys, j + 1 => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map_mod p ys j

/-- 辅助引理（注记 3.5）：全零列表的各项。 -/
theorem getD_replicate_zero : ∀ (e j : ℕ), (List.replicate e 0).getD j 0 = 0
  | 0, j => by simp
  | e + 1, 0 => by simp [List.replicate_succ]
  | e + 1, j + 1 => by
    simp only [List.replicate_succ, List.getD_cons_succ]
    exact getD_replicate_zero e j

/-- 辅助引理（注记 3.5）：`hkUnit e i` 的各项。 -/
theorem getD_hkUnit : ∀ (e i j : ℕ), j < e → (hkUnit e i).getD j 0 = if i = j then 1 else 0
  | 0, _, j, h => absurd h (Nat.not_lt_zero j)
  | e + 1, 0, 0, _ => by simp [hkUnit]
  | e + 1, 0, j + 1, _ => by
    simp only [hkUnit, List.getD_cons_succ]
    rw [getD_replicate_zero, ite_eq_right (by omega)]
  | e + 1, i + 1, 0, _ => by
    simp only [hkUnit, List.getD_cons_zero]
    rw [ite_eq_right (by omega)]
  | e + 1, i + 1, j + 1, h => by
    simp only [hkUnit, List.getD_cons_succ]
    rw [getD_hkUnit e i j (by omega)]
    simp

/-- 辅助引理（注记 3.5）：`seg` 的各项。 -/
theorem getD_seg (f : ℕ → ℕ) : ∀ (k n l : ℕ), l < n → (seg f k n).getD l 0 = f (k + l)
  | _, 0, l, h => absurd h (Nat.not_lt_zero l)
  | k, n + 1, 0, _ => by simp [seg]
  | k, n + 1, l + 1, h => by
    simp only [seg, List.getD_cons_succ]
    rw [getD_seg f (k + 1) n l (by omega), show k + 1 + l = k + (l + 1) by omega]

/-- 辅助引理（注记 3.5）：`kronCheck` 为真，则每一列都满足三条核对。 -/
theorem kronCheck_spec {p B e S : ℕ} : ∀ (cols : List (List ℕ)) (j0 : ℕ), kronCheck p B e S cols j0 = true →
    ∀ j < cols.length, (cols.getD j []).length = e ∧ (p - 1) * (cols.getD j []).sum < B ∧
      (digs B (S * ofDig B (cols.getD j []) / B ^ (e - 1)) e).map (· % p) = hkUnit e (j0 + j)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | c :: cs, j0, h, j, hj => by
    simp only [kronCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases j with _ | j
    · simp only [List.getD_cons_zero, add_zero]
      exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    · simp only [List.getD_cons_succ]
      rw [show j0 + (j + 1) = j0 + 1 + j by omega]
      exact kronCheck_spec cs (j0 + 1) h.2 j (by simp at hj; omega)

/-- 辅助引理（注记 3.5）：若 `kronCheck p B e S cols 0` 为真（`S` 由 `[a_0(n), …, a_K(n)]` 模 `p` 打包，
`K + 1 = 2e`，`cols` 有 `e` 列，`p > 1`），则 `e × e` 的 Hankel 行列式 `det (a_{i+j}(n))` 非零：`(H mod p)·W = I`。 -/
theorem hankel_det_ne_zero_of_kron {n K e p B : ℕ} (cols : List (List ℕ)) (hp : 1 < p) (hB : 0 < B)
    (hcols : cols.length = e) (hK : K + 1 = 2 * e)
    (hc : kronCheck p B e (ofDig B ((rowList n K).map (· % p))) cols 0 = true) :
    (Matrix.of fun i j : Fin e => (a (i + j) n : ℂ)).det ≠ 0 := by
  have : Fact (1 < p) := ⟨hp⟩
  set sL := (rowList n K).map (· % p) with hsL
  have hs : ∀ k, (listPoly sL).coeff k ≤ p - 1 := by
    intro k
    rw [coeff_listPoly, hsL, getD_map_mod]
    have := Nat.mod_lt ((rowList n K).getD k 0) (by omega : 0 < p)
    omega
  have hsk : ∀ k, k < 2 * e → (listPoly sL).coeff k = a k n % p := by
    intro k hk
    rw [coeff_listPoly, hsL, getD_map_mod, rowList_eq, getD_seg _ _ _ _ (by omega), zero_add]
  set Hz : Matrix (Fin e) (Fin e) ℤ := Matrix.of fun i j => (a (i + j) n : ℤ) with hHz
  have hC : (Matrix.of fun i j : Fin e => (a (i + j) n : ℂ)) = (Int.castRingHom ℂ).mapMatrix Hz := by
    ext i j
    simp [hHz]
  have hz : Hz.det ≠ 0 := by
    intro h0
    let Wm : Matrix (Fin e) (Fin e) (ZMod p) :=
      Matrix.of fun l j => (((cols.getD j []).getD (e - 1 - l) 0 : ℕ) : ZMod p)
    have hmul : (Int.castRingHom (ZMod p)).mapMatrix Hz * Wm = 1 := by
      ext i j
      have hi := i.2
      have hj := j.2
      obtain ⟨hlen, hsum, hdig⟩ := kronCheck_spec cols 0 hc j (by omega)
      have hQ := coeff_listPoly (cols.getD (j : ℕ) [])
      have hd := congrArg (fun L => L.getD (i : ℕ) 0) hdig
      simp only [getD_map_mod, zero_add] at hd
      rw [getD_digs B _ e i hi, getD_hkUnit e j i hi, Nat.div_div_eq_div_mul, ← pow_add,
        ← eval_listPoly B sL, ← eval_listPoly B (cols.getD (j : ℕ) []), ← eval_mul,
        digit_eval hB _ _ fun m => lt_of_le_of_lt (coeff_mul_le _ hs hQ m) hsum,
        coeff_mul_mid _ hlen hQ (by omega)] at hd
      have hsum' : ∑ l ∈ range e, (listPoly sL).coeff (↑i + l) * (cols.getD (j : ℕ) []).getD (e - 1 - l) 0 =
          ∑ l ∈ range e, (a (↑i + l) n % p) * (cols.getD (j : ℕ) []).getD (e - 1 - l) 0 :=
        Finset.sum_congr rfl fun l hl => by
          rw [Finset.mem_range] at hl
          rw [hsk _ (by omega)]
      rw [hsum'] at hd
      have hd2 := congrArg (Nat.cast : ℕ → ZMod p) hd
      push_cast [ZMod.natCast_mod] at hd2
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hHz, Matrix.of_apply, Wm, eq_intCast,
        Int.cast_natCast]
      rw [Fin.sum_univ_eq_sum_range (fun l => ((a (↑i + l) n : ℕ) : ZMod p) *
        (((cols.getD (j : ℕ) []).getD (e - 1 - l) 0 : ℕ) : ZMod p)) e]
      refine hd2.trans ?_
      rcases eq_or_ne i j with hij | hij
      · subst hij
        simp
      · have hne : (j : ℕ) ≠ i := fun h => hij (Fin.ext h.symm)
        simp [hne, hij]
    have hdet := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det, h0, map_zero, zero_mul] at hdet
    exact zero_ne_one hdet
  rw [hC, ← RingHom.map_det]
  intro h
  exact hz (by simpa using h)

/-! ## 不同乘积的个数 -/

/-- `σ` 在第 `i` 层：`i = 0` 时 `σ = 1`，否则 `σ³ − σ² = i`。 -/
def IsLevel (i : ℕ) (σ : ℂ) : Prop := if i = 0 then σ = 1 else σ ^ 3 - σ ^ 2 = i

/-- 辅助引理（注记 3.5）：`sig m` 的每个根都在某一层 `i ≤ m`。 -/
theorem isLevel_of_mem_sig {m : ℕ} {σ : ℂ} (hσ : σ ∈ sig m) : ∃ i ≤ m, IsLevel i σ := by
  obtain ⟨i, him, hi⟩ := sig_level hσ
  refine ⟨i, him, ?_⟩
  unfold IsLevel
  split_ifs with h0
  · subst h0
    have hσ0 := (mem_sig.mp hσ).1
    have h3 : σ ^ 3 - σ ^ 2 = 0 := by rw [hi, Nat.cast_zero]
    have h2 : σ ^ 2 * (σ - 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hσ0
    · exact sub_eq_zero.mp h
  · exact hi

/-- 乘 `σ` 的一步：`A + Bσ + Cσ²` 乘 `σ`，用 `σ³ = σ² + i` 约化；`i = 0` 时 `σ = 1`，不变。 -/
def lvStep (i : ℕ) (x : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if i = 0 then x else ((i : ℤ) * x.2.2, x.1, x.2.1 + x.2.2)

/-- `(A, B, C)` 的第 `u` 个分量。 -/
def lvGet : ℕ → ℤ × ℤ × ℤ → ℤ
  | 0, x => x.1
  | 1, x => x.2.1
  | _ + 2, x => x.2.2

/-- `Σ_l γ_l·x_l[u]·y_l[v]`，`x_{l+1} = lvStep i x_l`、`y_{l+1} = lvStep j y_l`（可在内核里计算）。 -/
def lvAcc (i j u v : ℕ) : List ℤ → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℤ
  | [], _, _ => 0
  | g :: γ, x, y => g * lvGet u x * lvGet v y + lvAcc i j u v γ (lvStep i x) (lvStep j y)

/-- 每一对层 `(i, j)`（`i ≤ a`、`j ≤ b`）上 `Σ_l γ_l (στ)^l` 约化后的 9 个系数都为 0。 -/
def lvCheck (γ : List ℤ) (a b : ℕ) : Bool :=
  (List.range (a + 1)).all fun i => (List.range (b + 1)).all fun j =>
    (List.range 3).all fun u => (List.range 3).all fun v => lvAcc i j u v γ (1, 0, 0) (1, 0, 0) == 0

/-- `(A, B, C) ↦ A + Bσ + Cσ²`。 -/
noncomputable def lvEval (x : ℤ × ℤ × ℤ) (σ : ℂ) : ℂ := x.1 + x.2.1 * σ + x.2.2 * σ ^ 2

/-- `lvStep` 迭代 `l` 次，从 `(1, 0, 0)` 开始。 -/
def lvIter (i : ℕ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | l + 1 => lvStep i (lvIter i l)

/-- 辅助引理（注记 3.5）：`lvStep` 对应乘 `σ`。 -/
theorem lvEval_step {i : ℕ} {σ : ℂ} (hσ : IsLevel i σ) (x : ℤ × ℤ × ℤ) :
    lvEval (lvStep i x) σ = σ * lvEval x σ := by
  unfold IsLevel at hσ
  unfold lvStep lvEval
  split_ifs at hσ ⊢ with h0
  · rw [hσ]
    ring
  · push_cast
    linear_combination (-(x.2.2 : ℂ)) * hσ

/-- 辅助引理（注记 3.5）：`σ^l = A + Bσ + Cσ²`，`(A, B, C) = lvIter i l`。 -/
theorem lvEval_iter {i : ℕ} {σ : ℂ} (hσ : IsLevel i σ) : ∀ l, lvEval (lvIter i l) σ = σ ^ l
  | 0 => by simp [lvIter, lvEval]
  | l + 1 => by rw [lvIter, lvEval_step hσ, lvEval_iter hσ l, pow_succ, mul_comm]

/-- 辅助引理（注记 3.5）：`Σ_{u<3} x[u]·σ^u = A + Bσ + Cσ²`。 -/
theorem lvGet_sum (x : ℤ × ℤ × ℤ) (σ : ℂ) : ∑ u ∈ range 3, (lvGet u x : ℂ) * σ ^ u = lvEval x σ := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [lvGet, lvEval, pow_zero, pow_one, mul_one]

/-- 辅助引理（注记 3.5）：`Σ_l γ_l (στ)^{l₀+l}` 约化成 `Σ_{u,v<3} M_{uv}·σ^u τ^v`，`M_{uv}` 由 `lvAcc` 给出。 -/
theorem lvAcc_spec {i j : ℕ} {σ τ : ℂ} (hσ : IsLevel i σ) (hτ : IsLevel j τ) :
    ∀ (γ : List ℤ) (l0 : ℕ), lsumC (fun l => (σ * τ) ^ l) γ l0 =
      ∑ u ∈ range 3, ∑ v ∈ range 3, (lvAcc i j u v γ (lvIter i l0) (lvIter j l0) : ℂ) * (σ ^ u * τ ^ v)
  | [], l0 => by simp [lsumC, lvAcc]
  | g :: γ, l0 => by
    rw [lsumC, lvAcc_spec hσ hτ γ (l0 + 1)]
    simp only [lvAcc, Int.cast_add, Int.cast_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    have hx := lvEval_iter hσ l0
    have hy := lvEval_iter hτ l0
    rw [mul_pow, ← hx, ← hy, ← lvGet_sum, ← lvGet_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring

/-- 辅助引理（注记 3.5）：`lvCheck` 为真，则每个 `M_{uv}` 都为 0。 -/
theorem lvCheck_spec {γ : List ℤ} {a b : ℕ} (h : lvCheck γ a b = true) {i j u v : ℕ} (hi : i ≤ a)
    (hj : j ≤ b) (hu : u < 3) (hv : v < 3) : lvAcc i j u v γ (1, 0, 0) (1, 0, 0) = 0 := by
  simp only [lvCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i (by omega) j (by omega) u hu v hv

/-- 辅助引理（注记 3.5）：`lvCheck γ a b` 为真，则对 `σ ∈ sig a`、`τ ∈ sig b` 有 `Σ_l γ_l (στ)^l = 0`。 -/
theorem sum_prod_eq_zero_of_lvCheck {γ : List ℤ} {a b : ℕ} (hc : lvCheck γ a b = true) {σ τ : ℂ}
    (hσ : σ ∈ sig a) (hτ : τ ∈ sig b) : ∑ l ∈ range γ.length, (γ.getD l 0 : ℂ) * (σ * τ) ^ l = 0 := by
  obtain ⟨i, hi, hσi⟩ := isLevel_of_mem_sig hσ
  obtain ⟨j, hj, hτj⟩ := isLevel_of_mem_sig hτ
  have h := (sum_getD_eq_lsumC (fun l => (σ * τ) ^ l) γ 0).trans (lvAcc_spec hσi hτj γ 0)
  simp only [add_zero] at h
  rw [h]
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => ?_
  rw [Finset.mem_range] at hu hv
  rw [show lvIter i 0 = (1, 0, 0) from rfl, show lvIter j 0 = (1, 0, 0) from rfl,
    lvCheck_spec hc hi hj hu hv]
  simp

/-- 辅助引理（注记 3.5）：若 `γ` 长 `e + 1`、`γ_e = 1` 且 `lvCheck γ a b` 为真，则乘积 `στ`（`σ ∈ sig a`、
`τ ∈ sig b`）都是 `Σ_l γ_l X^l` 的根，不同的值至多 `e` 个。 -/
theorem card_products_le {γ : List ℤ} {a b e : ℕ} (hlen : γ.length = e + 1) (htop : γ.getD e 0 = 1)
    (hc : lvCheck γ a b = true) : #((sig a ×ˢ sig b).image fun p => p.1 * p.2) ≤ e := by
  set P : ℂ[X] := ∑ l ∈ range (e + 1), C (γ.getD l 0 : ℂ) * X ^ l with hP
  have hcoeff : P.coeff e = 1 := by
    rw [hP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.self_mem_range_succ e), htop, Int.cast_one]
  have hP0 : P ≠ 0 := fun h => by
    rw [h, coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have hdeg : P.natDegree ≤ e := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
    rw [Finset.mem_range] at hl
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  refine (card_le_degree_of_subset_roots fun z hz => ?_).trans hdeg
  rw [Finset.mem_val, Finset.mem_image] at hz
  obtain ⟨⟨σ, τ⟩, hst, rfl⟩ := hz
  rw [Finset.mem_product] at hst
  rw [mem_roots hP0, IsRoot.def, hP, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [← hlen]
  exact sum_prod_eq_zero_of_lvCheck hc hst.1 hst.2

/-- 辅助引理（注记 3.5）：若 `e` 是 `k ↦ a_k(n)` 的常系数递推的阶的下界，则乘积 `στ` 至少有 `e` 个不同的值：
`∏_λ (X − λ)`（`λ` 取遍不同乘积）给出一条这样的递推。 -/
theorem card_products_ge {n e : ℕ}
    (hmin : e ∈ lowerBounds {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
      ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) n : ℂ) = 0}) :
    e ≤ #((sig ((n + 1) / 2) ×ˢ sig (n / 2)).image fun p => p.1 * p.2) := by
  set Λ := (sig ((n + 1) / 2) ×ˢ sig (n / 2)).image fun p => p.1 * p.2 with hΛ
  set R : ℂ[X] := ∏ z ∈ Λ, (X - C z) with hR
  have hmon : R.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hdeg : R.natDegree = #Λ := by
    rw [hR, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  refine hmin ⟨0, fun i => R.coeff i, ?_, fun k _ => ?_⟩
  · show R.coeff #Λ ≠ 0
    rw [← hdeg, hmon.coeff_natDegree]
    exact one_ne_zero
  · show ∑ i ∈ range (#Λ + 1), R.coeff i * (a (k + i) n : ℂ) = 0
    simp_rw [a_row_expansion, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hroot : R.eval (q.1 * q.2) = 0 := by
      rw [hR, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_image_of_mem (fun p : ℂ × ℂ => p.1 * p.2) hq) (by simp)
    rw [eval_eq_sum_range, hdeg] at hroot
    calc ∑ i ∈ range (#Λ + 1), R.coeff i *
          (alpha ((n + 1) / 2) q.1 * alpha (n / 2) q.2 * (q.1 * q.2) ^ (k + i))
        = alpha ((n + 1) / 2) q.1 * alpha (n / 2) q.2 * (q.1 * q.2) ^ k *
            ∑ i ∈ range (#Λ + 1), R.coeff i * (q.1 * q.2) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by rw [hroot, mul_zero]

/-! ## 六行 -/

/-! ### 第 n = 2 行（A207069，阶 10） -/

/-- 第 2 行的 OEIS 递推的系数（前向形式，`γ_10 = 1`）。 -/
def rowGam2 : List ℤ := [1, 0, -1, -3, 0, 0, 6, -3, 2, -3, 1]

set_option maxRecDepth 100000 in
/-- 第 2 行 10×10 Hankel 矩阵模 97 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{9,j}, …, W_{0,j}]`；由脚本算出，`hankel_row_two` 里核对）。 -/
def rowCols2 : List (List ℕ) := [
  [12, 78, 28, 12, 42, 50, 1, 3, 0, 0],
  [0, 12, 78, 28, 12, 42, 50, 1, 3, 0],
  [85, 19, 81, 66, 83, 59, 41, 47, 1, 3],
  [58, 54, 26, 54, 19, 30, 56, 41, 50, 1],
  [96, 61, 52, 29, 48, 19, 30, 59, 42, 50],
  [47, 52, 58, 8, 20, 48, 19, 83, 12, 42],
  [30, 59, 39, 62, 8, 29, 54, 66, 28, 12],
  [49, 26, 48, 39, 58, 52, 26, 81, 78, 28],
  [93, 95, 26, 59, 52, 61, 54, 19, 12, 78],
  [80, 93, 49, 30, 47, 96, 58, 85, 0, 12]]

/-- 辅助引理（注记 3.5）：第 2 行的 OEIS 递推（`oeis_A207069`）写成 `Σ_i γ_i·a_{k+i}(2) = 0`。 -/
theorem row_rec_two (k : ℕ) : ∑ i ∈ range (10 + 1), (rowGam2.getD i 0 : ℂ) * (a (k + i) 2 : ℂ) = 0 := by
  refine (sum_getD_eq_lsumC (fun j => (a (k + j) 2 : ℂ)) rowGam2 0).trans ?_
  have h2 := congrArg (Int.cast : ℤ → ℂ) (oeis_A207069 k)
  simp only [aAlt_two] at h2
  push_cast at h2
  simp only [rowGam2, lsumC, add_zero]
  push_cast
  linear_combination h2

/-- 辅助引理（注记 3.5）：第 2 行 10×10 的 Hankel 行列式 `det (a_{i+j}(2))` 非零（模 97 的逆作证书）。 -/
theorem hankel_row_two : (Matrix.of fun i j : Fin 10 => (a (i + j) 2 : ℂ)).det ≠ 0 :=
  hankel_det_ne_zero_of_kron (p := 97) (B := 2 ^ 20) (K := 19) rowCols2 (by norm_num) (by norm_num) rfl
    (by norm_num) (by decide +kernel)

/-- **注记 3.5**（第 2 行递推的最小阶）：`k ↦ a_k(2)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零）的阶最小是 10：OEIS 的 10 阶递推（A207069）从 `k = 0` 起成立，更低阶的都不成立。 -/
theorem row_min_order_two : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) 2 : ℂ) = 0} 10 :=
  row_isLeast (γ := rowGam2) rfl row_rec_two hankel_row_two

/-- **注记 3.5**（第 2 行：不同乘积的个数）：`σ ∈ sig 1`、`τ ∈ sig 1` 的乘积 `στ` 恰有 10 个不同的值，等于第 2 行递推的最小阶。 -/
theorem card_row_products_two : #((sig 1 ×ˢ sig 1).image fun p => p.1 * p.2) = 10 :=
  le_antisymm (card_products_le (e := 10) (γ := rowGam2) rfl rfl (by decide +kernel))
    (card_products_ge (n := 2) row_min_order_two.2)

/-! ### 第 n = 3 行（A207070，阶 22） -/

/-- 第 3 行的 OEIS 递推的系数（前向形式，`γ_22 = 1`）。 -/
def rowGam3 : List ℤ := [16, 0, -24, -80, 4, 56, 228, -36, -39, -323, 64, -46, 305, -117, 119, -192, 89, -64, 56, -21, 9, -5, 1]

set_option maxRecDepth 100000 in
/-- 第 3 行 22×22 Hankel 矩阵模 97 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{21,j}, …, W_{0,j}]`；由脚本算出，`hankel_row_three` 里核对）。 -/
def rowCols3 : List (List ℕ) := [
  [8, 73, 14, 69, 29, 94, 30, 49, 7, 3, 43, 55, 3, 57, 34, 46, 60, 75, 72, 87, 71, 61],
  [75, 21, 69, 88, 1, 79, 76, 83, 50, 59, 83, 85, 5, 28, 42, 50, 74, 89, 84, 86, 33, 71],
  [26, 18, 51, 89, 87, 47, 21, 30, 84, 13, 90, 47, 39, 13, 47, 60, 88, 4, 36, 66, 86, 87],
  [94, 58, 87, 93, 76, 62, 86, 44, 33, 8, 25, 53, 72, 25, 49, 37, 48, 39, 83, 36, 84, 72],
  [46, 62, 21, 29, 18, 48, 57, 65, 68, 51, 77, 76, 81, 12, 15, 77, 93, 33, 39, 4, 89, 75],
  [90, 40, 87, 76, 62, 65, 45, 13, 47, 51, 51, 85, 29, 91, 41, 78, 67, 93, 48, 88, 74, 60],
  [86, 82, 36, 82, 61, 41, 86, 81, 6, 92, 5, 13, 9, 64, 67, 7, 78, 77, 37, 60, 50, 46],
  [64, 21, 61, 26, 74, 82, 45, 67, 2, 81, 52, 62, 89, 94, 39, 67, 41, 15, 49, 47, 42, 34],
  [39, 24, 89, 89, 0, 90, 38, 85, 82, 19, 1, 46, 46, 12, 94, 64, 91, 12, 25, 13, 28, 57],
  [35, 26, 67, 44, 74, 40, 10, 42, 29, 26, 65, 67, 6, 46, 89, 9, 29, 81, 72, 39, 5, 3],
  [50, 43, 50, 62, 4, 74, 16, 48, 78, 69, 62, 39, 67, 46, 62, 13, 85, 76, 53, 47, 85, 55],
  [16, 21, 87, 39, 65, 75, 88, 38, 25, 29, 67, 62, 65, 1, 52, 5, 51, 77, 25, 90, 83, 43],
  [71, 63, 3, 28, 23, 4, 50, 77, 82, 45, 29, 69, 26, 19, 81, 92, 51, 51, 8, 13, 59, 3],
  [8, 11, 62, 48, 54, 63, 65, 49, 52, 82, 25, 78, 29, 82, 2, 6, 47, 68, 33, 84, 50, 7],
  [53, 56, 93, 63, 27, 90, 35, 83, 49, 77, 38, 48, 42, 85, 67, 81, 13, 65, 44, 30, 83, 49],
  [4, 35, 12, 75, 77, 65, 94, 35, 65, 50, 88, 16, 10, 38, 45, 86, 45, 57, 86, 21, 76, 30],
  [79, 86, 96, 29, 4, 53, 65, 90, 63, 4, 75, 74, 40, 90, 82, 41, 65, 48, 62, 47, 79, 94],
  [47, 71, 62, 4, 69, 4, 77, 27, 54, 23, 65, 4, 74, 0, 74, 61, 62, 18, 76, 87, 1, 29],
  [8, 63, 37, 93, 4, 29, 75, 63, 48, 28, 39, 62, 44, 89, 26, 82, 76, 29, 93, 89, 88, 69],
  [64, 55, 24, 37, 62, 96, 12, 93, 62, 3, 87, 50, 67, 89, 61, 36, 87, 21, 87, 51, 69, 14],
  [40, 67, 55, 63, 71, 86, 35, 56, 11, 63, 21, 43, 26, 24, 21, 82, 40, 62, 58, 18, 21, 73],
  [96, 40, 64, 8, 47, 79, 4, 53, 8, 71, 16, 50, 35, 39, 64, 86, 90, 46, 94, 26, 75, 8]]

/-- 辅助引理（注记 3.5）：第 3 行的 OEIS 递推（`oeis_A207070`）写成 `Σ_i γ_i·a_{k+i}(3) = 0`。 -/
theorem row_rec_three (k : ℕ) : ∑ i ∈ range (22 + 1), (rowGam3.getD i 0 : ℂ) * (a (k + i) 3 : ℂ) = 0 := by
  refine (sum_getD_eq_lsumC (fun j => (a (k + j) 3 : ℂ)) rowGam3 0).trans ?_
  have h2 := congrArg (Int.cast : ℤ → ℂ) (oeis_A207070 k)
  simp only [aAlt_three] at h2
  push_cast at h2
  simp only [rowGam3, lsumC, add_zero]
  push_cast
  linear_combination h2

/-- 辅助引理（注记 3.5）：第 3 行 22×22 的 Hankel 行列式 `det (a_{i+j}(3))` 非零（模 97 的逆作证书）。 -/
theorem hankel_row_three : (Matrix.of fun i j : Fin 22 => (a (i + j) 3 : ℂ)).det ≠ 0 :=
  hankel_det_ne_zero_of_kron (p := 97) (B := 2 ^ 20) (K := 43) rowCols3 (by norm_num) (by norm_num) rfl
    (by norm_num) (by decide +kernel)

/-- **注记 3.5**（第 3 行递推的最小阶）：`k ↦ a_k(3)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零）的阶最小是 22：OEIS 的 22 阶递推（A207070）从 `k = 0` 起成立，更低阶的都不成立。 -/
theorem row_min_order_three : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) 3 : ℂ) = 0} 22 :=
  row_isLeast (γ := rowGam3) rfl row_rec_three hankel_row_three

/-- **注记 3.5**（第 3 行：不同乘积的个数）：`σ ∈ sig 2`、`τ ∈ sig 1` 的乘积 `στ` 恰有 22 个不同的值，等于第 3 行递推的最小阶。 -/
theorem card_row_products_three : #((sig 2 ×ˢ sig 1).image fun p => p.1 * p.2) = 22 :=
  le_antisymm (card_products_le (e := 22) (γ := rowGam3) rfl rfl (by decide +kernel))
    (card_products_ge (n := 3) row_min_order_three.2)

/-! ### 第 n = 4 行（A207124，阶 28） -/

/-- 第 4 行的 OEIS 递推的系数（前向形式，`γ_28 = 1`）。 -/
def rowGam4 : List ℤ := [256, 128, -448, -1632, -512, 1472, 4944, 1168, -2336, -7812, -1552, 1358, 7828, 761, 364, -4997, 82, -851, 2132, -374, 525, -637, 191, -140, 105, -30, 12, -6, 1]

set_option maxRecDepth 100000 in
/-- 第 4 行 28×28 Hankel 矩阵模 97 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{27,j}, …, W_{0,j}]`；由脚本算出，`hankel_row_four` 里核对）。 -/
def rowCols4 : List (List ℕ) := [
  [32, 78, 74, 43, 13, 2, 70, 27, 17, 48, 40, 73, 14, 50, 15, 42, 5, 44, 39, 52, 95, 25, 16, 69, 67, 19, 64, 42],
  [56, 25, 13, 11, 30, 40, 14, 66, 35, 19, 85, 35, 62, 76, 19, 18, 0, 27, 15, 22, 22, 25, 10, 3, 41, 29, 76, 64],
  [65, 18, 38, 18, 59, 13, 88, 29, 2, 93, 95, 73, 87, 84, 80, 22, 65, 20, 80, 34, 76, 50, 22, 79, 38, 52, 29, 19],
  [82, 10, 44, 23, 77, 43, 91, 9, 48, 14, 42, 41, 83, 91, 72, 57, 26, 27, 26, 57, 14, 30, 60, 67, 90, 38, 41, 67],
  [46, 42, 18, 53, 4, 96, 58, 1, 10, 37, 5, 85, 12, 12, 40, 84, 58, 35, 46, 22, 54, 16, 56, 46, 67, 79, 3, 69],
  [28, 24, 2, 71, 68, 79, 45, 39, 91, 42, 94, 24, 32, 0, 35, 51, 5, 20, 41, 18, 46, 83, 91, 56, 60, 22, 10, 16],
  [42, 7, 58, 28, 73, 79, 67, 0, 92, 35, 75, 5, 71, 55, 79, 65, 16, 6, 76, 30, 89, 86, 83, 16, 30, 50, 25, 25],
  [22, 87, 57, 76, 35, 67, 55, 8, 10, 30, 29, 2, 1, 85, 50, 33, 16, 47, 93, 44, 55, 89, 46, 54, 14, 76, 22, 95],
  [71, 18, 9, 63, 12, 49, 61, 56, 29, 95, 6, 86, 31, 43, 51, 66, 94, 51, 67, 94, 44, 30, 18, 22, 57, 34, 22, 52],
  [13, 20, 46, 20, 36, 37, 46, 0, 52, 74, 60, 64, 18, 31, 13, 44, 83, 79, 84, 67, 93, 76, 41, 46, 26, 80, 15, 39],
  [51, 95, 50, 68, 40, 74, 78, 54, 3, 87, 69, 18, 75, 87, 68, 24, 20, 83, 79, 51, 47, 6, 20, 35, 27, 20, 27, 44],
  [65, 49, 2, 40, 6, 58, 73, 92, 35, 40, 54, 44, 13, 26, 79, 63, 79, 20, 83, 94, 16, 16, 5, 58, 26, 65, 0, 5],
  [71, 29, 76, 86, 63, 32, 74, 21, 73, 74, 59, 4, 59, 75, 35, 59, 63, 24, 44, 66, 33, 65, 51, 84, 57, 22, 18, 42],
  [26, 3, 28, 3, 79, 76, 39, 75, 7, 30, 25, 28, 89, 62, 36, 35, 79, 68, 13, 51, 50, 79, 35, 40, 72, 80, 19, 15],
  [39, 88, 9, 28, 68, 37, 95, 9, 65, 57, 15, 54, 9, 88, 62, 75, 26, 87, 31, 43, 85, 55, 0, 12, 91, 84, 76, 50],
  [61, 31, 3, 83, 58, 51, 8, 55, 35, 15, 42, 26, 11, 9, 89, 59, 13, 75, 18, 31, 1, 71, 32, 12, 83, 87, 62, 14],
  [64, 56, 1, 51, 89, 86, 41, 53, 9, 39, 84, 71, 26, 54, 28, 4, 44, 18, 64, 86, 2, 5, 24, 85, 41, 73, 35, 73],
  [18, 8, 65, 86, 90, 23, 69, 95, 62, 69, 18, 84, 42, 15, 25, 59, 54, 69, 60, 6, 29, 75, 94, 5, 42, 95, 85, 40],
  [39, 35, 1, 11, 46, 77, 79, 16, 53, 17, 69, 39, 15, 57, 30, 74, 40, 87, 74, 95, 30, 35, 42, 37, 14, 93, 19, 48],
  [44, 55, 8, 84, 14, 86, 92, 87, 89, 53, 62, 9, 35, 65, 7, 73, 35, 3, 52, 29, 10, 92, 91, 10, 48, 2, 35, 17],
  [72, 24, 40, 69, 37, 13, 96, 76, 87, 16, 95, 53, 55, 9, 75, 21, 92, 54, 0, 56, 8, 0, 39, 1, 9, 29, 66, 27],
  [76, 68, 47, 29, 18, 43, 32, 96, 92, 79, 69, 41, 8, 95, 39, 74, 73, 78, 46, 61, 55, 67, 45, 58, 91, 88, 14, 70],
  [38, 79, 54, 96, 96, 7, 43, 13, 86, 77, 23, 86, 51, 37, 76, 32, 58, 74, 37, 49, 67, 79, 79, 96, 43, 13, 40, 2],
  [56, 6, 93, 58, 57, 96, 18, 37, 14, 46, 90, 89, 58, 68, 79, 63, 6, 40, 36, 12, 35, 73, 68, 4, 77, 59, 30, 13],
  [18, 11, 85, 36, 58, 96, 29, 69, 84, 11, 86, 51, 83, 28, 3, 86, 40, 68, 20, 63, 76, 28, 71, 53, 23, 18, 11, 43],
  [73, 47, 67, 85, 93, 54, 47, 40, 8, 1, 65, 1, 3, 9, 28, 76, 2, 50, 46, 9, 57, 58, 2, 18, 44, 38, 13, 74],
  [5, 89, 47, 11, 6, 79, 68, 24, 55, 35, 8, 56, 31, 88, 3, 29, 49, 95, 20, 18, 87, 7, 24, 42, 10, 18, 25, 78],
  [77, 5, 73, 18, 56, 38, 76, 72, 44, 39, 18, 64, 61, 39, 26, 71, 65, 51, 13, 71, 22, 42, 28, 46, 82, 65, 56, 32]]

/-- 辅助引理（注记 3.5）：第 4 行的 OEIS 递推（`oeis_A207124`）写成 `Σ_i γ_i·a_{k+i}(4) = 0`。 -/
theorem row_rec_four (k : ℕ) : ∑ i ∈ range (28 + 1), (rowGam4.getD i 0 : ℂ) * (a (k + i) 4 : ℂ) = 0 := by
  refine (sum_getD_eq_lsumC (fun j => (a (k + j) 4 : ℂ)) rowGam4 0).trans ?_
  have h2 := congrArg (Int.cast : ℤ → ℂ) (oeis_A207124 k)
  push_cast at h2
  simp only [rowGam4, lsumC, add_zero]
  push_cast
  linear_combination h2

/-- 辅助引理（注记 3.5）：第 4 行 28×28 的 Hankel 行列式 `det (a_{i+j}(4))` 非零（模 97 的逆作证书）。 -/
theorem hankel_row_four : (Matrix.of fun i j : Fin 28 => (a (i + j) 4 : ℂ)).det ≠ 0 :=
  hankel_det_ne_zero_of_kron (p := 97) (B := 2 ^ 20) (K := 55) rowCols4 (by norm_num) (by norm_num) rfl
    (by norm_num) (by decide +kernel)

/-- **注记 3.5**（第 4 行递推的最小阶）：`k ↦ a_k(4)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零）的阶最小是 28：OEIS 的 28 阶递推（A207124）从 `k = 0` 起成立，更低阶的都不成立。 -/
theorem row_min_order_four : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) 4 : ℂ) = 0} 28 :=
  row_isLeast (γ := rowGam4) rfl row_rec_four hankel_row_four

/-- **注记 3.5**（第 4 行：不同乘积的个数）：`σ ∈ sig 2`、`τ ∈ sig 2` 的乘积 `στ` 恰有 28 个不同的值，等于第 4 行递推的最小阶。 -/
theorem card_row_products_four : #((sig 2 ×ˢ sig 2).image fun p => p.1 * p.2) = 28 :=
  le_antisymm (card_products_le (e := 28) (γ := rowGam4) rfl rfl (by decide +kernel))
    (card_products_ge (n := 4) row_min_order_four.2)

/-! ### 第 n = 5 行（A207125，阶 49） -/

/-- 第 5 行的 OEIS 递推的系数（前向形式，`γ_49 = 1`）。 -/
def rowGam5 : List ℤ := [-4478976, -2239488, 10824192, 38257920, 7713792, -62083584, -153436032, -17630784, 178049664, 365057280, 33930144, -299576016, -585709344, -55353168, 321333520, 667860328, 67577952, -219301460, -562385994, -52348891, 82080698, 358454837, 21389899, 1251197, -176672722, 1202418, -21845322, 68838049, -7158188, 14534975, -21467119, 4568076, -5581642, 5342318, -1631553, 1432346, -1026031, 364391, -244890, 140046, -49378, 25871, -11988, 3685, -1469, 540, -124, 33, -9, 1]

set_option maxRecDepth 100000 in
/-- 第 5 行 49×49 Hankel 矩阵模 97 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{48,j}, …, W_{0,j}]`；由脚本算出，`hankel_row_five` 里核对）。 -/
def rowCols5 : List (List ℕ) := [
  [12, 78, 39, 19, 7, 43, 62, 78, 30, 2, 72, 11, 72, 10, 63, 23, 8, 8, 12, 1, 40, 77, 7, 9, 80, 91, 81, 24, 36, 87, 61, 79, 79, 69, 49, 18, 22, 31, 12, 80, 20, 84, 30, 83, 47, 86, 17, 10, 38],
  [44, 0, 42, 41, 27, 30, 36, 69, 96, 35, 75, 1, 58, 49, 16, 17, 12, 47, 67, 42, 13, 69, 43, 41, 83, 59, 49, 2, 66, 30, 72, 91, 54, 52, 24, 23, 7, 79, 1, 87, 23, 39, 92, 24, 54, 80, 23, 33, 10],
  [78, 8, 66, 9, 81, 66, 48, 5, 56, 25, 29, 67, 29, 12, 70, 81, 72, 24, 83, 3, 13, 75, 52, 89, 37, 80, 70, 13, 3, 38, 31, 16, 92, 74, 91, 30, 67, 60, 15, 33, 84, 59, 54, 81, 17, 52, 92, 23, 17],
  [60, 59, 54, 55, 88, 86, 61, 86, 73, 59, 6, 41, 67, 94, 40, 85, 0, 44, 32, 70, 90, 26, 28, 3, 25, 10, 50, 77, 20, 45, 15, 35, 49, 82, 33, 2, 59, 52, 92, 51, 33, 25, 0, 23, 3, 85, 52, 80, 86],
  [33, 57, 33, 65, 90, 44, 1, 4, 19, 6, 80, 17, 44, 42, 35, 41, 94, 66, 65, 25, 42, 76, 17, 18, 4, 95, 82, 75, 54, 10, 27, 73, 40, 2, 78, 30, 55, 36, 86, 34, 68, 49, 63, 19, 11, 3, 17, 54, 47],
  [84, 93, 55, 27, 93, 90, 75, 36, 90, 65, 67, 21, 5, 87, 49, 85, 82, 59, 69, 85, 4, 9, 1, 94, 94, 73, 87, 46, 37, 90, 38, 81, 36, 95, 45, 80, 0, 93, 54, 79, 63, 5, 92, 50, 19, 23, 81, 24, 83],
  [1, 65, 92, 93, 66, 76, 36, 49, 29, 17, 75, 3, 61, 61, 59, 90, 75, 74, 80, 53, 92, 31, 89, 92, 13, 14, 40, 28, 26, 7, 49, 19, 21, 16, 7, 37, 62, 86, 60, 39, 47, 8, 17, 92, 63, 0, 54, 92, 30],
  [22, 67, 59, 13, 57, 70, 37, 20, 62, 7, 85, 83, 76, 5, 78, 74, 49, 2, 67, 32, 3, 17, 18, 68, 57, 13, 71, 90, 74, 54, 64, 5, 49, 26, 11, 95, 39, 29, 70, 36, 0, 29, 8, 5, 49, 25, 59, 39, 84],
  [30, 79, 93, 82, 91, 94, 95, 39, 55, 21, 66, 17, 59, 61, 71, 95, 61, 24, 9, 69, 13, 72, 43, 81, 18, 34, 66, 12, 27, 30, 95, 27, 20, 85, 22, 16, 75, 4, 69, 12, 94, 0, 47, 63, 68, 33, 84, 23, 20],
  [82, 59, 19, 23, 38, 17, 71, 37, 22, 30, 50, 63, 17, 67, 54, 43, 91, 68, 22, 85, 23, 34, 11, 31, 0, 49, 90, 40, 83, 65, 60, 94, 43, 71, 71, 20, 33, 6, 93, 60, 12, 36, 39, 79, 34, 51, 33, 87, 80],
  [23, 10, 16, 24, 49, 96, 79, 39, 31, 49, 62, 9, 76, 5, 14, 93, 50, 45, 46, 50, 16, 1, 89, 1, 34, 34, 33, 55, 88, 85, 33, 77, 82, 21, 71, 42, 30, 28, 57, 93, 69, 70, 60, 54, 86, 92, 15, 1, 12],
  [54, 91, 9, 1, 78, 80, 10, 56, 2, 75, 37, 84, 96, 46, 26, 84, 55, 38, 68, 92, 19, 40, 6, 66, 62, 89, 3, 27, 15, 68, 11, 64, 60, 82, 71, 77, 61, 1, 28, 6, 4, 29, 86, 93, 36, 52, 60, 79, 31],
  [23, 14, 21, 0, 20, 68, 40, 34, 41, 72, 24, 80, 22, 75, 10, 28, 86, 11, 86, 68, 52, 65, 86, 33, 37, 36, 43, 94, 43, 20, 0, 88, 17, 57, 79, 33, 58, 61, 30, 33, 75, 39, 62, 0, 55, 59, 67, 7, 22],
  [80, 8, 7, 20, 96, 33, 87, 36, 48, 70, 33, 55, 77, 32, 38, 13, 75, 19, 18, 96, 61, 63, 55, 70, 2, 18, 53, 91, 93, 6, 6, 53, 53, 29, 63, 13, 33, 77, 42, 20, 16, 95, 37, 80, 30, 2, 30, 23, 18],
  [75, 46, 84, 72, 49, 24, 67, 62, 14, 16, 16, 12, 4, 27, 32, 83, 49, 53, 96, 38, 78, 10, 67, 16, 73, 39, 28, 32, 13, 68, 10, 13, 85, 67, 31, 63, 79, 71, 71, 71, 22, 11, 7, 45, 78, 33, 91, 24, 49],
  [25, 60, 33, 81, 37, 53, 45, 28, 85, 56, 55, 60, 43, 50, 20, 28, 40, 96, 8, 21, 60, 33, 74, 73, 53, 72, 68, 49, 42, 70, 29, 58, 59, 40, 67, 29, 57, 82, 21, 71, 85, 26, 16, 95, 2, 82, 74, 52, 69],
  [68, 28, 30, 68, 52, 94, 92, 34, 82, 47, 84, 36, 51, 16, 1, 83, 52, 68, 10, 30, 61, 4, 86, 63, 60, 54, 15, 82, 13, 24, 81, 86, 33, 59, 85, 53, 17, 60, 82, 43, 20, 49, 21, 36, 40, 49, 92, 54, 79],
  [33, 28, 12, 39, 5, 26, 36, 43, 35, 35, 70, 10, 56, 94, 1, 66, 22, 49, 2, 96, 20, 29, 63, 12, 4, 66, 94, 58, 96, 45, 84, 9, 86, 58, 13, 53, 88, 64, 77, 94, 27, 5, 19, 81, 73, 35, 16, 91, 79],
  [82, 69, 50, 42, 45, 1, 11, 63, 21, 77, 61, 49, 33, 59, 21, 71, 70, 84, 32, 84, 23, 68, 60, 50, 21, 34, 73, 41, 25, 71, 55, 84, 81, 29, 10, 6, 0, 11, 33, 60, 95, 64, 49, 38, 27, 15, 31, 72, 61],
  [9, 68, 70, 2, 4, 7, 27, 76, 68, 63, 72, 79, 38, 23, 45, 66, 8, 26, 89, 78, 68, 54, 80, 39, 37, 13, 93, 45, 92, 88, 71, 45, 24, 70, 68, 6, 20, 68, 85, 65, 30, 54, 7, 90, 10, 45, 38, 30, 87],
  [72, 50, 53, 1, 1, 66, 85, 63, 76, 67, 96, 72, 78, 15, 62, 25, 14, 96, 43, 20, 25, 47, 13, 1, 73, 62, 93, 41, 9, 92, 25, 96, 13, 42, 13, 93, 43, 15, 88, 83, 27, 74, 26, 37, 54, 20, 3, 66, 36],
  [8, 51, 80, 39, 57, 11, 47, 82, 52, 53, 77, 37, 88, 86, 94, 90, 67, 37, 11, 55, 28, 95, 53, 71, 95, 24, 45, 58, 41, 45, 41, 58, 82, 49, 32, 91, 94, 27, 55, 40, 12, 90, 28, 46, 75, 77, 13, 2, 24],
  [17, 86, 20, 11, 5, 92, 64, 40, 23, 44, 65, 78, 53, 33, 14, 3, 18, 47, 89, 55, 13, 66, 60, 60, 39, 8, 51, 45, 93, 93, 73, 94, 15, 68, 28, 53, 43, 3, 33, 90, 66, 71, 40, 87, 82, 50, 70, 49, 81],
  [56, 47, 83, 81, 46, 2, 92, 86, 86, 18, 52, 56, 51, 38, 95, 69, 42, 87, 15, 6, 38, 91, 37, 25, 56, 31, 8, 24, 62, 13, 34, 66, 54, 72, 39, 18, 36, 89, 34, 49, 34, 13, 14, 73, 95, 10, 80, 59, 91],
  [15, 4, 87, 60, 30, 84, 68, 37, 64, 71, 82, 31, 22, 4, 54, 92, 19, 76, 69, 44, 16, 53, 16, 80, 32, 56, 39, 95, 73, 37, 21, 4, 60, 53, 73, 2, 37, 62, 34, 0, 18, 57, 13, 94, 4, 25, 37, 83, 80],
  [8, 88, 82, 44, 53, 10, 20, 84, 42, 40, 13, 3, 51, 46, 42, 40, 89, 60, 39, 23, 22, 19, 75, 19, 80, 25, 60, 71, 1, 39, 50, 12, 63, 73, 16, 70, 33, 66, 1, 31, 81, 68, 92, 94, 18, 3, 89, 41, 9],
  [15, 63, 65, 91, 9, 94, 32, 31, 41, 95, 72, 91, 85, 80, 37, 82, 43, 63, 76, 35, 36, 34, 20, 75, 16, 37, 60, 53, 13, 80, 60, 63, 86, 74, 67, 55, 86, 6, 89, 11, 43, 18, 89, 1, 17, 28, 52, 43, 7],
  [75, 6, 30, 16, 63, 90, 18, 75, 5, 82, 58, 56, 39, 31, 66, 44, 8, 65, 31, 62, 73, 26, 34, 19, 53, 91, 66, 95, 47, 54, 68, 29, 4, 33, 10, 63, 65, 40, 1, 34, 72, 17, 31, 9, 76, 26, 75, 69, 77],
  [80, 32, 59, 17, 9, 87, 77, 62, 12, 57, 55, 64, 58, 69, 64, 65, 59, 12, 35, 17, 66, 73, 36, 22, 16, 38, 13, 28, 25, 68, 23, 20, 61, 60, 78, 61, 52, 19, 16, 23, 13, 3, 92, 4, 42, 90, 13, 13, 40],
  [17, 7, 89, 50, 13, 86, 9, 24, 0, 83, 9, 84, 55, 0, 35, 90, 56, 72, 55, 5, 17, 62, 35, 23, 44, 6, 55, 55, 20, 78, 84, 96, 30, 21, 38, 96, 68, 92, 50, 85, 69, 32, 53, 85, 25, 70, 3, 42, 1],
  [7, 47, 11, 23, 60, 69, 19, 88, 11, 93, 0, 1, 82, 95, 27, 82, 40, 89, 36, 55, 35, 31, 76, 39, 69, 15, 89, 11, 43, 89, 32, 2, 10, 8, 96, 18, 86, 68, 46, 22, 9, 67, 80, 69, 65, 32, 83, 67, 12],
  [31, 71, 44, 0, 7, 49, 42, 89, 42, 35, 40, 9, 47, 49, 68, 61, 61, 45, 89, 72, 12, 65, 63, 60, 76, 87, 47, 37, 96, 26, 84, 49, 68, 96, 53, 19, 11, 38, 45, 68, 24, 2, 74, 59, 66, 44, 24, 47, 8],
  [48, 25, 77, 53, 43, 6, 86, 40, 62, 41, 2, 1, 42, 37, 29, 73, 76, 61, 40, 56, 59, 8, 43, 89, 19, 42, 18, 67, 14, 8, 70, 22, 52, 40, 49, 75, 86, 55, 50, 91, 61, 49, 75, 82, 94, 0, 72, 12, 8],
  [74, 17, 67, 14, 95, 22, 48, 59, 78, 33, 67, 3, 93, 86, 8, 3, 73, 61, 82, 90, 65, 44, 82, 40, 92, 69, 3, 90, 25, 66, 71, 66, 83, 28, 83, 13, 28, 84, 93, 43, 95, 74, 90, 85, 41, 85, 81, 17, 23],
  [82, 8, 22, 81, 12, 41, 29, 42, 96, 86, 75, 45, 65, 58, 74, 8, 29, 68, 27, 35, 64, 66, 37, 42, 54, 95, 14, 94, 62, 45, 21, 1, 1, 20, 32, 38, 10, 26, 14, 54, 71, 78, 59, 49, 35, 40, 70, 16, 63],
  [20, 60, 80, 7, 37, 51, 63, 87, 62, 81, 91, 50, 12, 84, 58, 86, 37, 49, 95, 0, 69, 31, 80, 46, 4, 38, 33, 86, 15, 23, 59, 94, 16, 50, 27, 32, 75, 46, 5, 67, 61, 5, 61, 87, 42, 94, 12, 49, 10],
  [75, 13, 92, 18, 21, 41, 5, 61, 18, 39, 57, 56, 60, 12, 65, 93, 42, 47, 82, 55, 58, 39, 85, 51, 22, 51, 53, 88, 78, 38, 33, 56, 51, 43, 4, 77, 22, 96, 76, 17, 59, 76, 61, 5, 44, 67, 29, 58, 72],
  [43, 63, 88, 34, 73, 65, 94, 29, 58, 25, 27, 85, 56, 50, 45, 3, 1, 9, 1, 84, 64, 56, 91, 3, 31, 56, 78, 37, 72, 79, 49, 10, 36, 60, 12, 55, 80, 84, 9, 63, 17, 83, 3, 21, 17, 41, 67, 1, 11],
  [76, 27, 31, 96, 6, 63, 18, 35, 29, 30, 76, 27, 57, 91, 75, 67, 2, 40, 0, 9, 55, 58, 72, 13, 82, 52, 65, 77, 96, 72, 61, 70, 84, 55, 16, 33, 24, 37, 62, 50, 66, 85, 75, 67, 80, 6, 29, 75, 72],
  [45, 77, 60, 57, 39, 41, 94, 55, 37, 4, 30, 25, 39, 81, 86, 33, 41, 35, 93, 83, 57, 82, 95, 40, 71, 18, 44, 53, 67, 63, 77, 35, 47, 56, 16, 70, 72, 75, 49, 30, 21, 7, 17, 65, 6, 59, 25, 35, 2],
  [62, 29, 47, 4, 8, 32, 58, 79, 52, 37, 29, 58, 18, 62, 96, 78, 62, 42, 11, 0, 12, 5, 41, 42, 64, 86, 23, 52, 76, 68, 21, 35, 82, 85, 14, 48, 41, 2, 31, 22, 55, 62, 29, 90, 19, 73, 56, 96, 30],
  [75, 36, 74, 60, 7, 16, 89, 47, 79, 55, 35, 29, 61, 87, 42, 59, 40, 89, 88, 24, 62, 75, 31, 84, 37, 86, 40, 82, 63, 76, 63, 43, 34, 28, 62, 36, 34, 56, 39, 37, 39, 20, 49, 36, 4, 86, 5, 69, 78],
  [83, 36, 80, 21, 93, 8, 77, 89, 58, 94, 18, 94, 5, 63, 29, 48, 86, 42, 19, 9, 77, 18, 32, 20, 68, 92, 64, 47, 85, 27, 11, 36, 92, 45, 67, 87, 40, 10, 79, 71, 95, 37, 36, 75, 1, 61, 48, 36, 62],
  [74, 88, 84, 74, 43, 44, 8, 16, 32, 41, 63, 65, 41, 51, 41, 22, 6, 49, 69, 86, 87, 90, 94, 10, 84, 2, 92, 11, 66, 7, 1, 26, 94, 53, 24, 33, 68, 80, 96, 17, 94, 70, 76, 90, 44, 86, 66, 30, 43],
  [17, 3, 16, 62, 15, 43, 93, 7, 8, 39, 6, 73, 21, 37, 12, 95, 43, 7, 60, 13, 9, 63, 9, 53, 30, 46, 5, 57, 1, 4, 45, 5, 52, 37, 49, 96, 20, 78, 49, 38, 91, 57, 66, 93, 90, 88, 81, 27, 7],
  [26, 29, 29, 43, 62, 74, 21, 60, 4, 57, 96, 34, 18, 7, 81, 14, 53, 0, 23, 50, 17, 16, 91, 44, 60, 81, 11, 39, 1, 2, 42, 39, 68, 81, 72, 20, 0, 1, 24, 23, 82, 13, 93, 27, 65, 55, 9, 41, 19],
  [52, 21, 60, 29, 16, 84, 80, 74, 47, 60, 31, 88, 92, 80, 22, 67, 77, 44, 11, 89, 59, 30, 65, 82, 87, 83, 20, 80, 53, 70, 50, 12, 30, 33, 84, 7, 21, 9, 16, 19, 93, 59, 92, 55, 33, 54, 66, 42, 39],
  [31, 37, 21, 29, 3, 88, 36, 36, 29, 77, 27, 63, 13, 60, 8, 17, 25, 71, 47, 7, 32, 6, 63, 88, 4, 47, 86, 51, 50, 68, 69, 28, 28, 60, 46, 8, 14, 91, 10, 59, 79, 67, 65, 93, 57, 59, 8, 0, 78],
  [89, 31, 52, 26, 17, 74, 83, 75, 62, 45, 76, 43, 75, 20, 82, 74, 48, 31, 7, 17, 80, 75, 15, 8, 15, 56, 17, 8, 72, 9, 82, 33, 68, 25, 75, 80, 23, 54, 23, 82, 30, 22, 1, 84, 33, 60, 78, 44, 12]]

/-- 辅助引理（注记 3.5）：第 5 行的 OEIS 递推（`oeis_A207125`）写成 `Σ_i γ_i·a_{k+i}(5) = 0`。 -/
theorem row_rec_five (k : ℕ) : ∑ i ∈ range (49 + 1), (rowGam5.getD i 0 : ℂ) * (a (k + i) 5 : ℂ) = 0 := by
  refine (sum_getD_eq_lsumC (fun j => (a (k + j) 5 : ℂ)) rowGam5 0).trans ?_
  have h2 := congrArg (Int.cast : ℤ → ℂ) (oeis_A207125 k)
  push_cast at h2
  simp only [rowGam5, lsumC, add_zero]
  push_cast
  linear_combination h2

/-- 辅助引理（注记 3.5）：第 5 行 49×49 的 Hankel 行列式 `det (a_{i+j}(5))` 非零（模 97 的逆作证书）。 -/
theorem hankel_row_five : (Matrix.of fun i j : Fin 49 => (a (i + j) 5 : ℂ)).det ≠ 0 :=
  hankel_det_ne_zero_of_kron (p := 97) (B := 2 ^ 20) (K := 97) rowCols5 (by norm_num) (by norm_num) rfl
    (by norm_num) (by decide +kernel)

/-- **注记 3.5**（第 5 行递推的最小阶）：`k ↦ a_k(5)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零）的阶最小是 49：OEIS 的 49 阶递推（A207125）从 `k = 0` 起成立，更低阶的都不成立。 -/
theorem row_min_order_five : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) 5 : ℂ) = 0} 49 :=
  row_isLeast (γ := rowGam5) rfl row_rec_five hankel_row_five

/-- **注记 3.5**（第 5 行：不同乘积的个数）：`σ ∈ sig 3`、`τ ∈ sig 2` 的乘积 `στ` 恰有 49 个不同的值，等于第 5 行递推的最小阶。 -/
theorem card_row_products_five : #((sig 3 ×ˢ sig 2).image fun p => p.1 * p.2) = 49 :=
  le_antisymm (card_products_le (e := 49) (γ := rowGam5) rfl rfl (by decide +kernel))
    (card_products_ge (n := 5) row_min_order_five.2)

/-! ### 第 n = 6 行（A207126，阶 55） -/

/-- 第 6 行的 OEIS 递推的系数（前向形式，`γ_55 = 1`）。 -/
def rowGam6 : List ℤ := [-362797056, -302330880, 856604160, 3505358592, 1620829440, -5380929792, -15012127872, -5301941184, 16580096064, 37974609216, 11902793184, -30229857072, -64172537712, -19604960064, 35807161968, 76800621528, 23867092008, -28245367596, -67602030126, -21250373533, 14352660423, 44790453292, 13745500241, -3770782754, -22753048028, -6343010388, -513770271, 9018675022, 2000328083, 997587885, -2839906825, -373557291, -510014161, 724111551, 9100169, 163399581, -151230139, 17307097, -36871821, 25675661, -5652383, 6009825, -3424827, 968051, -691695, 334471, -98913, 52118, -21328, 5679, -2222, 745, -151, 39, -10, 1]

set_option maxRecDepth 100000 in
/-- 第 6 行 55×55 Hankel 矩阵模 97 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{54,j}, …, W_{0,j}]`；由脚本算出，`hankel_row_six` 里核对）。 -/
def rowCols6 : List (List ℕ) := [
  [62, 9, 86, 72, 78, 18, 80, 86, 32, 13, 76, 43, 6, 22, 58, 58, 19, 16, 48, 84, 87, 42, 91, 14, 35, 1, 32, 75, 92, 34, 11, 24, 46, 4, 77, 37, 22, 12, 32, 87, 35, 29, 19, 79, 25, 34, 0, 65, 7, 83, 52, 66, 53, 80, 93],
  [60, 67, 50, 84, 8, 71, 9, 90, 31, 90, 72, 34, 70, 77, 37, 50, 6, 76, 24, 55, 78, 5, 50, 15, 49, 29, 16, 46, 18, 46, 35, 93, 54, 91, 14, 36, 52, 41, 55, 30, 23, 35, 4, 59, 42, 23, 50, 72, 3, 39, 21, 55, 32, 24, 80],
  [48, 16, 30, 53, 71, 66, 59, 10, 85, 62, 8, 91, 81, 91, 84, 19, 55, 11, 53, 51, 5, 7, 34, 62, 7, 89, 79, 41, 34, 61, 19, 64, 81, 95, 36, 8, 13, 70, 16, 22, 62, 31, 82, 62, 60, 78, 91, 6, 73, 95, 29, 16, 84, 32, 53],
  [36, 75, 27, 75, 44, 35, 63, 20, 6, 79, 65, 5, 46, 93, 54, 85, 13, 61, 79, 95, 70, 7, 49, 49, 4, 78, 79, 32, 87, 15, 27, 38, 3, 57, 84, 95, 83, 23, 77, 79, 39, 58, 31, 93, 73, 40, 60, 88, 89, 59, 38, 83, 16, 55, 66],
  [75, 33, 45, 17, 74, 76, 1, 11, 30, 53, 84, 87, 49, 55, 83, 84, 60, 6, 62, 75, 41, 48, 16, 4, 7, 31, 0, 74, 23, 47, 31, 50, 14, 88, 71, 85, 58, 21, 65, 54, 70, 85, 24, 85, 19, 83, 67, 12, 25, 84, 54, 38, 29, 21, 52],
  [5, 16, 10, 22, 28, 80, 20, 90, 36, 93, 48, 12, 31, 46, 28, 64, 29, 41, 31, 27, 17, 68, 37, 11, 25, 21, 19, 62, 68, 94, 9, 48, 14, 46, 74, 79, 34, 13, 33, 52, 4, 57, 67, 74, 33, 3, 69, 15, 79, 20, 84, 59, 95, 39, 83],
  [27, 46, 23, 94, 34, 2, 58, 64, 8, 52, 83, 51, 9, 19, 29, 76, 34, 17, 65, 0, 23, 66, 48, 77, 74, 12, 87, 86, 65, 82, 40, 3, 36, 58, 18, 81, 65, 51, 80, 43, 11, 42, 73, 63, 96, 7, 59, 65, 48, 79, 25, 89, 73, 3, 7],
  [1, 0, 72, 26, 64, 34, 63, 17, 28, 93, 56, 72, 32, 53, 88, 17, 18, 50, 35, 36, 20, 49, 48, 61, 31, 69, 96, 64, 45, 55, 31, 58, 62, 65, 11, 74, 29, 64, 86, 93, 49, 95, 58, 88, 7, 9, 76, 41, 65, 15, 12, 88, 6, 72, 65],
  [44, 9, 33, 91, 45, 41, 44, 42, 56, 47, 90, 9, 8, 26, 53, 1, 40, 83, 8, 51, 2, 23, 5, 80, 1, 1, 86, 6, 3, 95, 67, 52, 59, 9, 76, 58, 8, 9, 14, 84, 17, 86, 43, 54, 48, 21, 40, 76, 59, 69, 67, 60, 91, 50, 0],
  [54, 80, 62, 30, 15, 20, 70, 0, 73, 11, 60, 68, 33, 96, 64, 91, 77, 7, 81, 53, 11, 73, 96, 61, 26, 5, 32, 95, 83, 42, 42, 66, 42, 75, 26, 30, 49, 56, 40, 71, 30, 36, 65, 68, 57, 87, 21, 9, 7, 3, 83, 40, 78, 23, 34],
  [41, 7, 28, 43, 50, 17, 8, 39, 15, 10, 5, 56, 78, 49, 85, 6, 87, 21, 12, 28, 12, 8, 8, 56, 37, 28, 7, 21, 0, 69, 28, 12, 79, 94, 0, 65, 37, 27, 14, 62, 64, 64, 45, 25, 79, 57, 48, 7, 96, 33, 19, 73, 60, 42, 25],
  [70, 72, 95, 5, 61, 0, 85, 23, 14, 90, 78, 88, 50, 37, 25, 35, 34, 92, 12, 40, 61, 39, 62, 14, 47, 41, 2, 26, 84, 70, 58, 21, 78, 76, 71, 11, 83, 74, 20, 22, 17, 14, 93, 10, 25, 68, 54, 88, 63, 74, 85, 93, 62, 59, 79],
  [17, 37, 1, 30, 12, 64, 32, 20, 47, 17, 0, 28, 27, 56, 54, 84, 88, 14, 26, 59, 10, 15, 15, 54, 85, 30, 89, 39, 59, 23, 39, 85, 34, 78, 18, 14, 56, 46, 54, 8, 84, 16, 43, 93, 45, 65, 43, 58, 73, 67, 24, 31, 82, 4, 19],
  [55, 34, 8, 94, 89, 54, 19, 29, 57, 54, 62, 52, 32, 13, 83, 69, 91, 81, 64, 74, 53, 40, 63, 46, 57, 83, 74, 63, 50, 65, 95, 33, 43, 62, 10, 30, 72, 12, 54, 29, 69, 24, 16, 14, 64, 36, 86, 95, 42, 57, 85, 58, 31, 35, 29],
  [50, 43, 52, 71, 73, 67, 95, 92, 64, 73, 87, 27, 26, 75, 74, 44, 58, 90, 23, 86, 69, 17, 79, 32, 59, 52, 47, 21, 64, 44, 82, 34, 58, 32, 38, 89, 91, 7, 64, 20, 8, 69, 84, 17, 64, 30, 17, 49, 11, 4, 70, 39, 62, 23, 35],
  [35, 32, 30, 33, 62, 16, 54, 38, 37, 76, 14, 9, 10, 47, 10, 89, 1, 55, 28, 0, 56, 66, 43, 35, 63, 47, 15, 34, 42, 68, 29, 96, 54, 61, 22, 23, 18, 48, 16, 96, 20, 29, 8, 22, 62, 71, 84, 93, 43, 52, 54, 79, 22, 30, 87],
  [22, 43, 43, 86, 28, 84, 2, 36, 30, 30, 40, 33, 25, 31, 7, 58, 95, 87, 51, 52, 87, 24, 89, 40, 8, 96, 20, 61, 88, 7, 65, 28, 51, 19, 96, 95, 1, 11, 91, 16, 64, 54, 54, 20, 14, 40, 14, 86, 80, 33, 65, 77, 16, 55, 32],
  [41, 6, 9, 57, 30, 35, 46, 22, 44, 21, 84, 38, 27, 33, 1, 64, 72, 5, 54, 25, 41, 79, 41, 23, 15, 91, 29, 11, 51, 94, 93, 55, 40, 25, 15, 70, 66, 75, 11, 48, 7, 12, 46, 74, 27, 56, 9, 64, 51, 13, 21, 23, 70, 41, 12],
  [66, 93, 49, 66, 86, 88, 54, 85, 48, 53, 11, 2, 34, 64, 21, 58, 92, 74, 15, 44, 44, 50, 75, 93, 60, 62, 4, 28, 37, 11, 22, 58, 38, 21, 94, 47, 81, 66, 1, 18, 91, 72, 56, 83, 37, 49, 8, 29, 65, 34, 58, 83, 13, 52, 22],
  [48, 48, 93, 39, 80, 95, 1, 79, 71, 93, 62, 88, 70, 17, 5, 40, 3, 81, 16, 49, 88, 22, 32, 12, 56, 24, 51, 87, 56, 78, 71, 49, 17, 48, 85, 46, 47, 70, 95, 23, 89, 30, 14, 11, 65, 30, 58, 74, 81, 79, 85, 95, 8, 36, 37],
  [22, 55, 24, 4, 74, 33, 13, 94, 90, 56, 5, 34, 92, 85, 84, 18, 11, 15, 0, 36, 13, 28, 58, 58, 57, 77, 18, 50, 35, 36, 53, 85, 76, 69, 15, 85, 94, 15, 96, 22, 38, 10, 18, 71, 0, 26, 76, 11, 18, 74, 71, 84, 36, 14, 77],
  [67, 21, 87, 0, 73, 84, 91, 84, 93, 73, 56, 48, 87, 17, 14, 92, 48, 45, 78, 51, 78, 96, 53, 4, 78, 78, 38, 33, 92, 84, 20, 38, 59, 20, 69, 48, 21, 25, 19, 61, 32, 62, 78, 76, 94, 75, 9, 65, 58, 46, 88, 57, 95, 91, 4],
  [7, 42, 26, 26, 20, 40, 23, 30, 14, 60, 93, 24, 40, 21, 24, 44, 91, 74, 92, 46, 90, 2, 69, 44, 96, 71, 35, 19, 58, 84, 37, 14, 89, 59, 76, 17, 38, 40, 51, 54, 58, 43, 34, 78, 79, 42, 59, 62, 36, 14, 14, 3, 81, 54, 46],
  [66, 17, 70, 7, 86, 90, 16, 68, 78, 75, 0, 74, 1, 19, 41, 66, 57, 89, 51, 11, 40, 87, 59, 78, 1, 27, 90, 0, 55, 66, 58, 50, 14, 38, 85, 49, 58, 55, 28, 96, 34, 33, 85, 21, 12, 66, 52, 58, 3, 48, 50, 38, 64, 93, 24],
  [38, 75, 79, 6, 50, 12, 38, 70, 84, 45, 18, 18, 35, 26, 51, 17, 40, 43, 55, 82, 36, 35, 13, 26, 52, 9, 11, 40, 94, 58, 43, 58, 37, 20, 53, 71, 22, 93, 65, 29, 82, 95, 39, 58, 28, 42, 67, 31, 40, 9, 31, 27, 19, 35, 11],
  [93, 75, 8, 54, 56, 1, 81, 32, 11, 49, 23, 23, 18, 15, 72, 39, 92, 57, 33, 81, 96, 78, 60, 80, 84, 93, 0, 64, 50, 35, 58, 66, 84, 84, 36, 78, 11, 94, 7, 68, 44, 65, 23, 70, 69, 42, 95, 55, 82, 94, 47, 15, 61, 46, 34],
  [38, 44, 47, 70, 89, 54, 79, 74, 83, 96, 80, 31, 64, 83, 45, 55, 20, 54, 19, 26, 53, 19, 79, 60, 59, 75, 34, 37, 24, 50, 94, 55, 58, 92, 35, 56, 37, 51, 88, 42, 64, 50, 59, 84, 0, 83, 3, 45, 65, 68, 23, 87, 34, 18, 92],
  [16, 13, 58, 37, 91, 42, 91, 30, 10, 43, 81, 21, 52, 9, 27, 33, 83, 33, 59, 19, 64, 31, 66, 27, 90, 13, 50, 74, 37, 64, 40, 0, 19, 33, 50, 87, 28, 11, 61, 34, 21, 63, 39, 26, 21, 95, 6, 64, 86, 62, 74, 32, 41, 46, 75],
  [62, 75, 6, 8, 55, 67, 30, 59, 82, 35, 3, 49, 45, 83, 52, 89, 56, 16, 51, 52, 48, 51, 54, 85, 51, 12, 62, 50, 34, 0, 11, 90, 35, 38, 18, 51, 4, 29, 20, 15, 47, 74, 89, 2, 7, 32, 86, 96, 87, 19, 0, 79, 79, 16, 32],
  [92, 80, 21, 1, 85, 33, 51, 30, 37, 79, 42, 88, 1, 93, 35, 91, 67, 48, 35, 19, 14, 37, 13, 84, 9, 30, 12, 13, 75, 93, 9, 27, 71, 78, 77, 24, 62, 91, 96, 47, 52, 83, 30, 41, 28, 5, 1, 69, 12, 21, 31, 78, 89, 29, 1],
  [86, 53, 62, 59, 94, 84, 85, 65, 20, 3, 23, 85, 48, 23, 75, 47, 27, 53, 71, 77, 84, 20, 44, 11, 47, 9, 51, 90, 59, 84, 52, 1, 96, 78, 57, 56, 60, 15, 8, 63, 59, 57, 85, 47, 37, 26, 1, 31, 74, 25, 7, 4, 7, 49, 35],
  [66, 24, 83, 79, 89, 46, 14, 71, 26, 87, 79, 15, 71, 80, 84, 22, 62, 32, 15, 90, 42, 5, 43, 7, 11, 84, 85, 27, 60, 80, 26, 78, 44, 4, 58, 12, 93, 23, 40, 35, 32, 46, 54, 14, 56, 61, 80, 61, 77, 11, 4, 49, 62, 15, 14],
  [67, 23, 41, 80, 82, 14, 61, 91, 92, 61, 37, 88, 49, 35, 41, 77, 37, 92, 62, 92, 10, 16, 91, 43, 44, 13, 54, 66, 79, 60, 13, 59, 69, 53, 58, 32, 75, 41, 89, 43, 79, 63, 15, 62, 8, 96, 5, 48, 48, 37, 16, 49, 34, 50, 91],
  [20, 44, 14, 85, 43, 59, 15, 54, 24, 11, 59, 60, 92, 54, 28, 48, 37, 9, 6, 95, 63, 68, 16, 5, 20, 37, 51, 31, 19, 78, 35, 87, 2, 96, 28, 22, 50, 79, 24, 66, 17, 40, 15, 39, 8, 73, 23, 49, 66, 68, 48, 7, 7, 5, 42],
  [39, 74, 33, 14, 31, 87, 17, 87, 24, 70, 16, 55, 90, 11, 17, 87, 59, 32, 8, 5, 72, 63, 10, 42, 84, 14, 48, 64, 53, 96, 36, 40, 90, 78, 13, 88, 44, 41, 87, 56, 69, 53, 10, 61, 12, 11, 2, 20, 23, 17, 41, 70, 5, 78, 87],
  [57, 38, 96, 17, 28, 35, 90, 10, 47, 4, 55, 89, 65, 89, 10, 7, 74, 32, 77, 45, 5, 95, 92, 90, 77, 19, 52, 19, 26, 81, 82, 11, 46, 51, 36, 49, 44, 25, 52, 0, 86, 74, 59, 40, 28, 53, 51, 36, 0, 27, 75, 95, 51, 55, 84],
  [61, 89, 55, 70, 91, 61, 73, 79, 57, 40, 62, 18, 66, 19, 21, 37, 41, 69, 45, 77, 8, 6, 62, 15, 71, 35, 51, 59, 19, 33, 55, 51, 92, 78, 0, 16, 15, 54, 51, 28, 23, 64, 26, 12, 12, 81, 8, 35, 65, 31, 62, 79, 53, 24, 48],
  [83, 19, 60, 29, 24, 17, 38, 28, 27, 66, 66, 70, 94, 34, 52, 39, 20, 68, 69, 32, 32, 9, 92, 32, 53, 48, 16, 33, 54, 57, 43, 89, 74, 45, 15, 81, 74, 5, 87, 55, 90, 81, 14, 92, 21, 7, 83, 50, 17, 41, 6, 61, 11, 76, 16],
  [13, 70, 62, 27, 87, 66, 29, 11, 25, 53, 40, 95, 96, 75, 73, 86, 57, 20, 41, 74, 59, 37, 37, 62, 27, 67, 56, 83, 20, 92, 40, 57, 91, 48, 11, 3, 92, 72, 95, 1, 58, 91, 88, 34, 87, 77, 40, 18, 34, 29, 60, 13, 55, 6, 19],
  [73, 42, 91, 57, 93, 56, 63, 76, 26, 17, 70, 20, 10, 79, 50, 36, 86, 39, 37, 7, 87, 48, 77, 22, 47, 91, 89, 33, 55, 39, 17, 66, 44, 92, 18, 40, 58, 64, 58, 89, 44, 69, 84, 35, 6, 91, 1, 17, 76, 64, 84, 85, 19, 50, 58],
  [73, 31, 3, 73, 53, 13, 75, 37, 82, 32, 28, 11, 53, 52, 85, 50, 73, 52, 21, 10, 17, 28, 41, 84, 75, 35, 52, 27, 45, 72, 51, 41, 24, 14, 84, 5, 21, 1, 7, 10, 74, 83, 54, 25, 85, 64, 53, 88, 29, 28, 83, 54, 84, 37, 58],
  [90, 10, 50, 11, 81, 28, 7, 10, 33, 90, 92, 95, 30, 76, 52, 79, 75, 34, 19, 89, 11, 54, 35, 80, 23, 93, 83, 9, 83, 15, 26, 19, 21, 17, 85, 17, 64, 33, 31, 47, 75, 13, 56, 37, 49, 96, 26, 53, 19, 46, 55, 93, 91, 77, 22],
  [43, 4, 50, 78, 50, 51, 91, 72, 56, 66, 96, 92, 53, 30, 53, 10, 96, 94, 66, 65, 90, 92, 49, 71, 48, 1, 45, 52, 64, 18, 35, 1, 40, 87, 92, 70, 34, 27, 25, 10, 26, 32, 27, 50, 78, 33, 8, 32, 9, 31, 49, 46, 81, 70, 6],
  [86, 72, 38, 54, 70, 85, 71, 26, 31, 81, 54, 37, 92, 95, 11, 20, 95, 70, 18, 89, 55, 60, 88, 15, 85, 88, 49, 21, 31, 23, 18, 74, 24, 48, 34, 88, 2, 38, 33, 9, 27, 52, 28, 88, 56, 68, 9, 72, 51, 12, 87, 5, 91, 34, 43],
  [62, 59, 62, 31, 20, 29, 45, 79, 63, 47, 31, 54, 96, 92, 28, 70, 40, 66, 62, 55, 16, 59, 37, 79, 23, 42, 3, 81, 80, 23, 18, 0, 93, 56, 5, 62, 11, 84, 40, 14, 87, 62, 0, 78, 5, 60, 90, 56, 83, 48, 84, 65, 8, 72, 76],
  [17, 27, 15, 95, 21, 79, 22, 8, 44, 50, 47, 81, 66, 90, 32, 17, 53, 66, 40, 4, 70, 11, 61, 87, 3, 79, 35, 43, 96, 49, 45, 75, 60, 73, 56, 93, 53, 21, 30, 76, 73, 54, 17, 90, 10, 11, 47, 93, 52, 93, 53, 79, 62, 90, 13],
  [25, 10, 1, 47, 76, 38, 80, 24, 93, 44, 63, 31, 56, 33, 82, 26, 25, 27, 57, 47, 24, 24, 92, 26, 20, 37, 82, 10, 83, 11, 84, 78, 14, 93, 90, 71, 48, 44, 30, 37, 64, 57, 47, 14, 15, 73, 56, 28, 8, 36, 30, 6, 85, 31, 32],
  [74, 31, 3, 94, 20, 30, 77, 30, 24, 8, 79, 26, 72, 10, 37, 76, 11, 28, 79, 10, 87, 54, 91, 71, 65, 30, 59, 30, 74, 32, 70, 68, 30, 84, 94, 79, 85, 22, 36, 38, 92, 29, 20, 23, 39, 0, 42, 17, 64, 90, 11, 20, 10, 90, 86],
  [29, 86, 92, 32, 16, 70, 84, 77, 80, 22, 45, 71, 91, 7, 75, 63, 29, 38, 73, 90, 17, 15, 61, 14, 85, 51, 30, 91, 79, 81, 38, 16, 23, 91, 13, 1, 54, 46, 2, 54, 95, 19, 32, 85, 8, 70, 44, 63, 58, 20, 1, 63, 59, 9, 80],
  [67, 30, 91, 67, 21, 67, 70, 30, 38, 79, 29, 85, 51, 28, 13, 56, 66, 17, 61, 35, 87, 59, 14, 46, 84, 33, 67, 42, 54, 1, 12, 90, 40, 84, 33, 95, 88, 35, 84, 16, 67, 54, 64, 0, 17, 20, 41, 34, 2, 80, 76, 35, 66, 71, 18],
  [58, 53, 83, 71, 73, 21, 16, 20, 76, 21, 20, 70, 50, 81, 53, 93, 87, 24, 91, 28, 31, 43, 82, 89, 94, 85, 55, 91, 89, 56, 50, 86, 20, 73, 74, 80, 86, 30, 28, 62, 73, 89, 12, 61, 50, 15, 45, 64, 34, 28, 74, 44, 71, 8, 78],
  [69, 59, 60, 37, 71, 67, 32, 94, 47, 95, 31, 54, 78, 11, 73, 57, 27, 29, 70, 17, 14, 85, 80, 79, 59, 1, 8, 37, 70, 54, 6, 7, 26, 0, 4, 39, 66, 57, 86, 33, 71, 94, 30, 5, 43, 30, 91, 26, 94, 22, 17, 75, 53, 84, 72],
  [53, 23, 54, 60, 83, 91, 92, 3, 1, 15, 62, 38, 50, 50, 3, 91, 62, 60, 55, 96, 33, 14, 41, 83, 62, 21, 6, 58, 47, 8, 79, 70, 26, 87, 24, 93, 49, 9, 43, 30, 52, 8, 1, 95, 28, 62, 33, 72, 23, 10, 45, 27, 30, 50, 86],
  [73, 62, 23, 59, 53, 30, 86, 31, 10, 27, 59, 72, 4, 10, 31, 42, 70, 19, 89, 38, 74, 44, 23, 24, 53, 80, 75, 13, 44, 75, 75, 17, 42, 21, 55, 48, 93, 6, 43, 32, 43, 34, 37, 72, 7, 80, 9, 0, 46, 16, 33, 75, 16, 67, 9],
  [88, 73, 53, 69, 58, 67, 29, 74, 25, 17, 62, 86, 43, 90, 73, 73, 13, 83, 61, 57, 39, 20, 67, 66, 86, 92, 62, 16, 38, 93, 38, 66, 7, 67, 22, 48, 66, 41, 22, 35, 50, 55, 17, 70, 41, 54, 44, 1, 27, 5, 75, 36, 48, 60, 62]]

/-- 辅助引理（注记 3.5）：第 6 行的 OEIS 递推（`oeis_A207126`）写成 `Σ_i γ_i·a_{k+i}(6) = 0`。 -/
theorem row_rec_six (k : ℕ) : ∑ i ∈ range (55 + 1), (rowGam6.getD i 0 : ℂ) * (a (k + i) 6 : ℂ) = 0 := by
  refine (sum_getD_eq_lsumC (fun j => (a (k + j) 6 : ℂ)) rowGam6 0).trans ?_
  have h2 := congrArg (Int.cast : ℤ → ℂ) (oeis_A207126 k)
  push_cast at h2
  simp only [rowGam6, lsumC, add_zero]
  push_cast
  linear_combination h2

/-- 辅助引理（注记 3.5）：第 6 行 55×55 的 Hankel 行列式 `det (a_{i+j}(6))` 非零（模 97 的逆作证书）。 -/
theorem hankel_row_six : (Matrix.of fun i j : Fin 55 => (a (i + j) 6 : ℂ)).det ≠ 0 :=
  hankel_det_ne_zero_of_kron (p := 97) (B := 2 ^ 20) (K := 109) rowCols6 (by norm_num) (by norm_num) rfl
    (by norm_num) (by decide +kernel)

/-- **注记 3.5**（第 6 行递推的最小阶）：`k ↦ a_k(6)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零）的阶最小是 55：OEIS 的 55 阶递推（A207126）从 `k = 0` 起成立，更低阶的都不成立。 -/
theorem row_min_order_six : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) 6 : ℂ) = 0} 55 :=
  row_isLeast (γ := rowGam6) rfl row_rec_six hankel_row_six

/-- **注记 3.5**（第 6 行：不同乘积的个数）：`σ ∈ sig 3`、`τ ∈ sig 3` 的乘积 `στ` 恰有 55 个不同的值，等于第 6 行递推的最小阶。 -/
theorem card_row_products_six : #((sig 3 ×ˢ sig 3).image fun p => p.1 * p.2) = 55 :=
  le_antisymm (card_products_le (e := 55) (γ := rowGam6) rfl rfl (by decide +kernel))
    (card_products_ge (n := 6) row_min_order_six.2)

/-! ### 第 n = 7 行（A207127，阶 85） -/

/-- 第 7 行的 OEIS 递推的系数（前向形式，`γ_85 = 1`）。 -/
def rowGam7 : List ℤ := [-82170781731127296, -68475651442606080, 248794866908135424, 973115091056590848, 340333498176897024, -2129759193740083200, -5068707999762087936, -842463838702927872, 8894278787747807232, 16132821706296262656, 1288493772501417984, -23235629071699279872, -35632041588440432640, -1706149960629092352, 42268173079509467136, 58437094989686243328, 2887939270111002624, -56696829452796100608, -74155386899211190272, -5271114170652475392, 58035913196236812288, 74747053931918579712, 7710740741859591168, -46263593091806492160, -60910606360484891136, -8426293314130777856, 29001696212110566912, 40627618659809065600, 6954042835118706560, -14282822084351523904, -22389152106247372416, -4418865045976514272, 5429085403228467040, 10273265200251020496, 2190587059135330320, -1502759028308998816, -3953493496920048448, -850275238654182400, 239393332410432412, 1285870672369593082, 255789417360060438, 21154865730496055, -356641326189364413, -57394192756314261, -30462323265391834, 85238813721035527, 8416874103601210, 12397164148419178, -17755326582683868, -251735582682661, -3442351405160113, 3254553426680445, -274155640271866, 739141589649874, -527014304509161, 95798677241303, -127836810352284, 74973728810243, -19708041889332, 18049249228634, -9220909157736, 2930469039412, -2077668559612, 956433942970, -330145401354, 192557799542, -81087340968, 28313347286, -14035468772, 5411660781, -1815714481, 776325841, -271445106, 83877127, -30940490, 9629962, -2623048, 822163, -221157, 49933, -12754, 2822, -465, 85, -14, 1]

set_option maxRecDepth 100000 in
/-- 第 7 行 85×85 Hankel 矩阵模 97 的逆 `W` 的各列，倒序（第 `j` 个是 `[W_{84,j}, …, W_{0,j}]`；由脚本算出，`hankel_row_seven` 里核对）。 -/
def rowCols7 : List (List ℕ) := [
  [95, 86, 59, 2, 62, 55, 75, 64, 96, 58, 1, 23, 86, 34, 71, 79, 91, 5, 90, 60, 64, 0, 25, 0, 71, 85, 30, 16, 33, 82, 33, 22, 32, 27, 91, 71, 91, 92, 11, 69, 3, 57, 81, 49, 68, 43, 26, 61, 63, 63, 35, 59, 31, 90, 35, 29, 79, 3, 22, 59, 91, 89, 51, 79, 82, 2, 82, 32, 10, 39, 92, 36, 50, 69, 38, 36, 9, 6, 41, 41, 27, 40, 54, 59, 96],
  [85, 85, 49, 48, 90, 60, 70, 65, 43, 5, 84, 31, 58, 43, 85, 78, 2, 10, 35, 11, 72, 23, 46, 83, 48, 43, 5, 76, 75, 15, 84, 51, 50, 8, 6, 31, 12, 70, 66, 72, 89, 53, 19, 29, 8, 96, 4, 63, 56, 7, 26, 54, 23, 84, 9, 0, 96, 71, 4, 32, 16, 32, 96, 51, 84, 65, 34, 36, 82, 56, 53, 68, 17, 60, 54, 60, 71, 31, 95, 96, 3, 43, 4, 22, 59],
  [93, 57, 89, 52, 50, 0, 73, 67, 75, 64, 88, 3, 64, 52, 0, 54, 60, 62, 16, 60, 68, 66, 1, 19, 23, 47, 20, 77, 1, 65, 5, 64, 91, 20, 81, 13, 18, 53, 88, 79, 57, 68, 91, 64, 78, 84, 13, 40, 88, 83, 3, 24, 22, 30, 57, 79, 18, 84, 84, 48, 45, 67, 24, 90, 42, 53, 15, 75, 64, 0, 69, 26, 74, 32, 20, 29, 35, 36, 64, 0, 19, 10, 51, 4, 54],
  [41, 59, 28, 29, 52, 21, 79, 55, 73, 88, 79, 65, 61, 95, 77, 76, 63, 83, 52, 85, 18, 51, 77, 70, 12, 27, 86, 64, 68, 58, 30, 84, 19, 27, 12, 86, 20, 71, 91, 33, 55, 58, 77, 68, 24, 25, 90, 87, 79, 68, 45, 54, 76, 31, 40, 30, 19, 51, 14, 39, 64, 27, 84, 90, 69, 15, 29, 86, 22, 56, 6, 69, 28, 57, 56, 58, 46, 86, 59, 80, 13, 43, 10, 43, 40],
  [60, 71, 58, 15, 23, 42, 39, 48, 6, 82, 34, 23, 41, 94, 64, 91, 53, 85, 32, 1, 47, 9, 66, 85, 62, 67, 21, 54, 75, 63, 21, 50, 58, 53, 92, 56, 22, 4, 26, 16, 57, 34, 61, 31, 80, 77, 61, 71, 34, 29, 71, 35, 50, 75, 48, 61, 69, 96, 72, 73, 14, 65, 78, 87, 38, 5, 47, 53, 89, 67, 95, 87, 77, 53, 4, 43, 63, 38, 92, 67, 92, 13, 19, 3, 27],
  [12, 69, 89, 85, 36, 24, 85, 11, 71, 65, 21, 96, 78, 7, 93, 74, 70, 13, 26, 79, 58, 87, 48, 52, 68, 13, 20, 14, 20, 64, 16, 57, 18, 68, 72, 81, 34, 3, 94, 25, 41, 33, 19, 88, 9, 18, 45, 42, 43, 25, 86, 32, 23, 49, 59, 85, 3, 74, 9, 82, 7, 68, 72, 83, 37, 33, 2, 73, 69, 81, 73, 54, 58, 95, 81, 79, 17, 17, 54, 56, 67, 80, 0, 96, 41],
  [91, 11, 78, 68, 81, 39, 42, 38, 41, 8, 24, 56, 93, 25, 75, 77, 88, 77, 47, 66, 3, 90, 61, 95, 49, 71, 93, 81, 89, 30, 51, 3, 87, 62, 17, 35, 36, 38, 25, 30, 49, 59, 32, 93, 77, 62, 40, 40, 26, 81, 72, 30, 12, 84, 57, 82, 34, 11, 79, 31, 60, 46, 64, 52, 23, 68, 30, 59, 28, 37, 8, 30, 91, 48, 84, 92, 12, 27, 78, 54, 92, 59, 64, 95, 41],
  [23, 7, 86, 28, 38, 14, 85, 37, 34, 10, 1, 65, 67, 32, 82, 29, 81, 71, 67, 90, 32, 35, 41, 11, 81, 32, 7, 19, 17, 74, 72, 10, 54, 79, 1, 66, 77, 64, 46, 76, 59, 65, 96, 26, 66, 40, 95, 72, 32, 72, 57, 82, 94, 29, 21, 96, 1, 47, 85, 70, 96, 21, 30, 14, 64, 25, 40, 11, 63, 61, 85, 25, 21, 2, 68, 58, 40, 32, 27, 17, 38, 86, 36, 31, 6],
  [28, 35, 72, 2, 88, 96, 22, 1, 44, 13, 70, 36, 1, 6, 27, 32, 68, 95, 28, 18, 68, 84, 18, 81, 24, 82, 8, 83, 3, 86, 12, 60, 61, 16, 73, 80, 94, 93, 74, 34, 22, 43, 38, 31, 22, 68, 70, 51, 33, 8, 94, 77, 10, 10, 24, 93, 74, 18, 40, 62, 2, 80, 34, 22, 42, 16, 85, 50, 28, 63, 61, 51, 75, 24, 55, 49, 46, 40, 12, 17, 63, 46, 35, 71, 9],
  [38, 24, 8, 47, 22, 91, 64, 24, 58, 80, 8, 23, 15, 26, 92, 13, 30, 2, 65, 26, 16, 49, 60, 78, 0, 50, 9, 57, 28, 28, 59, 38, 55, 58, 92, 91, 13, 11, 33, 0, 56, 15, 19, 87, 64, 14, 68, 29, 70, 26, 14, 48, 31, 64, 24, 93, 24, 57, 3, 75, 45, 59, 56, 83, 34, 71, 76, 67, 47, 9, 53, 82, 32, 72, 34, 50, 49, 58, 92, 79, 43, 58, 29, 60, 36],
  [0, 59, 35, 60, 86, 43, 37, 86, 79, 51, 39, 16, 73, 80, 43, 26, 34, 49, 29, 58, 32, 37, 10, 9, 9, 65, 1, 63, 17, 55, 3, 89, 25, 58, 3, 31, 46, 77, 25, 34, 25, 92, 61, 59, 52, 2, 50, 78, 43, 77, 91, 46, 86, 6, 64, 79, 1, 87, 20, 68, 36, 53, 56, 48, 58, 11, 44, 11, 39, 25, 74, 60, 23, 26, 90, 34, 55, 68, 84, 81, 4, 56, 20, 54, 38],
  [1, 60, 95, 35, 54, 16, 94, 39, 26, 48, 18, 9, 15, 33, 84, 47, 35, 30, 81, 94, 0, 38, 48, 37, 30, 89, 36, 50, 42, 53, 66, 56, 0, 47, 73, 54, 35, 46, 27, 67, 5, 83, 30, 41, 15, 89, 27, 57, 2, 62, 85, 36, 76, 20, 37, 86, 34, 66, 10, 16, 46, 70, 89, 35, 83, 92, 87, 51, 95, 34, 53, 58, 32, 63, 26, 72, 24, 2, 48, 95, 53, 57, 32, 60, 69],
  [32, 96, 2, 1, 15, 63, 22, 66, 23, 95, 10, 21, 6, 24, 37, 3, 62, 48, 24, 21, 3, 16, 24, 23, 54, 96, 89, 29, 92, 67, 51, 14, 93, 83, 78, 73, 88, 76, 10, 0, 75, 35, 23, 34, 58, 65, 33, 24, 62, 34, 55, 43, 17, 35, 42, 26, 36, 34, 23, 7, 13, 60, 0, 6, 25, 15, 62, 89, 96, 27, 85, 32, 26, 32, 23, 32, 75, 21, 91, 58, 77, 28, 74, 17, 50],
  [56, 62, 49, 29, 49, 40, 22, 82, 68, 76, 37, 13, 32, 55, 5, 29, 87, 40, 39, 21, 48, 16, 54, 34, 57, 33, 34, 7, 41, 16, 19, 91, 43, 4, 83, 80, 33, 69, 3, 14, 10, 81, 8, 43, 16, 72, 66, 31, 47, 16, 55, 21, 90, 22, 25, 77, 25, 88, 51, 51, 40, 11, 2, 51, 41, 61, 58, 8, 18, 62, 4, 19, 32, 58, 60, 82, 51, 25, 30, 54, 87, 69, 26, 68, 36],
  [92, 1, 75, 9, 29, 62, 28, 10, 86, 12, 86, 54, 84, 85, 7, 88, 35, 70, 1, 85, 90, 69, 88, 3, 94, 92, 59, 31, 1, 79, 25, 7, 61, 65, 31, 54, 20, 36, 62, 31, 95, 43, 87, 25, 81, 13, 76, 83, 57, 66, 23, 89, 88, 96, 61, 7, 37, 47, 9, 21, 94, 28, 87, 46, 37, 23, 45, 73, 5, 45, 66, 4, 85, 53, 74, 53, 61, 85, 8, 73, 95, 6, 69, 53, 92],
  [9, 82, 60, 48, 56, 13, 23, 1, 85, 55, 59, 73, 75, 54, 73, 81, 7, 88, 25, 58, 71, 79, 67, 87, 73, 77, 15, 28, 12, 89, 66, 35, 13, 28, 70, 46, 63, 39, 60, 72, 76, 76, 17, 28, 93, 47, 85, 48, 67, 77, 80, 71, 52, 61, 84, 1, 90, 39, 69, 12, 13, 75, 1, 29, 55, 77, 70, 69, 75, 5, 45, 62, 27, 34, 25, 9, 63, 61, 37, 81, 67, 56, 0, 56, 39],
  [85, 87, 68, 96, 50, 45, 65, 59, 95, 94, 57, 44, 45, 18, 70, 39, 92, 1, 51, 46, 12, 21, 17, 36, 26, 31, 18, 24, 21, 24, 74, 85, 27, 57, 86, 50, 34, 70, 7, 79, 12, 69, 46, 31, 2, 9, 48, 90, 37, 8, 26, 16, 88, 88, 77, 67, 52, 55, 42, 65, 55, 6, 14, 46, 17, 34, 79, 38, 34, 75, 5, 18, 96, 95, 39, 47, 28, 63, 28, 69, 89, 22, 64, 82, 10],
  [20, 23, 12, 84, 85, 7, 56, 67, 25, 25, 78, 34, 17, 41, 51, 70, 24, 85, 30, 58, 22, 34, 35, 19, 2, 94, 3, 67, 17, 33, 5, 24, 47, 65, 64, 65, 49, 91, 7, 34, 29, 34, 37, 9, 58, 29, 50, 12, 89, 61, 91, 70, 83, 81, 29, 34, 49, 88, 78, 79, 1, 51, 61, 84, 22, 93, 31, 5, 38, 69, 73, 8, 89, 51, 11, 67, 50, 11, 59, 73, 53, 86, 75, 36, 32],
  [88, 70, 45, 78, 42, 44, 54, 51, 9, 75, 20, 0, 2, 23, 90, 73, 94, 58, 29, 89, 28, 73, 31, 22, 67, 92, 13, 26, 56, 22, 3, 66, 81, 58, 43, 76, 95, 78, 29, 22, 32, 75, 46, 29, 36, 94, 81, 37, 87, 50, 23, 67, 87, 67, 93, 9, 76, 70, 14, 51, 82, 26, 3, 16, 32, 86, 50, 31, 79, 70, 45, 58, 62, 87, 44, 76, 85, 40, 30, 2, 47, 29, 15, 34, 82],
  [47, 71, 45, 41, 84, 26, 50, 12, 92, 15, 12, 42, 76, 57, 53, 7, 84, 9, 90, 85, 86, 92, 11, 28, 7, 39, 46, 51, 27, 82, 41, 7, 55, 3, 36, 57, 66, 8, 40, 48, 30, 84, 60, 58, 38, 86, 50, 66, 38, 2, 33, 62, 34, 76, 69, 11, 50, 52, 13, 15, 87, 8, 17, 9, 96, 35, 86, 93, 34, 77, 23, 61, 15, 92, 11, 71, 16, 25, 68, 33, 5, 15, 53, 65, 2],
  [58, 60, 15, 33, 72, 26, 79, 49, 71, 64, 43, 46, 62, 69, 9, 54, 69, 64, 68, 4, 40, 71, 60, 89, 83, 73, 77, 70, 51, 27, 2, 19, 86, 32, 50, 16, 83, 96, 67, 6, 54, 28, 44, 10, 51, 27, 13, 6, 72, 49, 63, 59, 92, 47, 31, 34, 86, 15, 64, 57, 9, 50, 0, 32, 60, 96, 32, 22, 17, 55, 37, 41, 25, 83, 58, 34, 42, 64, 23, 37, 38, 69, 42, 84, 82],
  [4, 47, 91, 54, 14, 26, 44, 55, 20, 63, 71, 26, 31, 72, 25, 24, 33, 43, 91, 56, 19, 7, 13, 57, 0, 88, 90, 71, 53, 94, 28, 91, 17, 55, 75, 87, 71, 34, 52, 66, 30, 22, 57, 91, 26, 7, 57, 0, 52, 32, 57, 61, 62, 76, 74, 39, 76, 78, 43, 24, 61, 54, 22, 7, 32, 9, 16, 84, 46, 29, 46, 51, 6, 35, 48, 83, 22, 14, 52, 83, 87, 90, 90, 51, 79],
  [75, 18, 60, 87, 86, 75, 5, 58, 65, 31, 46, 29, 74, 33, 20, 54, 93, 30, 1, 27, 78, 57, 59, 87, 48, 78, 6, 45, 66, 20, 33, 61, 13, 70, 65, 62, 92, 81, 51, 83, 38, 57, 17, 91, 32, 45, 81, 44, 7, 14, 45, 11, 92, 46, 73, 26, 81, 29, 96, 29, 26, 66, 83, 22, 0, 17, 3, 61, 14, 1, 87, 2, 0, 89, 56, 56, 34, 30, 64, 72, 78, 84, 24, 96, 51],
  [16, 23, 87, 53, 10, 88, 29, 90, 55, 68, 70, 35, 10, 80, 63, 22, 59, 88, 3, 85, 57, 35, 20, 11, 76, 34, 3, 3, 80, 6, 52, 45, 21, 68, 32, 33, 22, 61, 29, 42, 54, 21, 40, 5, 39, 69, 82, 76, 61, 6, 12, 71, 27, 56, 57, 24, 72, 25, 35, 96, 46, 69, 66, 54, 50, 8, 26, 51, 6, 75, 28, 11, 60, 70, 53, 59, 80, 21, 46, 68, 65, 27, 67, 32, 89],
  [22, 3, 29, 75, 9, 47, 51, 53, 78, 76, 23, 20, 91, 85, 82, 17, 51, 86, 62, 2, 91, 20, 92, 96, 86, 75, 49, 9, 80, 45, 15, 62, 30, 79, 60, 19, 12, 52, 77, 35, 25, 1, 79, 31, 30, 54, 66, 77, 5, 67, 70, 78, 88, 88, 59, 6, 70, 25, 93, 29, 9, 46, 26, 61, 9, 87, 82, 1, 55, 13, 94, 40, 13, 46, 36, 45, 2, 96, 60, 7, 14, 64, 45, 16, 91],
  [14, 47, 57, 71, 71, 57, 16, 52, 67, 45, 92, 87, 24, 20, 54, 25, 7, 29, 82, 15, 38, 39, 94, 52, 47, 46, 51, 25, 11, 35, 93, 50, 18, 83, 17, 42, 20, 4, 5, 95, 26, 8, 73, 85, 62, 95, 60, 90, 54, 64, 86, 72, 81, 28, 37, 57, 18, 87, 55, 41, 29, 96, 29, 24, 57, 15, 51, 79, 65, 12, 21, 51, 7, 16, 68, 75, 62, 70, 31, 82, 73, 39, 48, 32, 59],
  [9, 9, 7, 47, 58, 60, 19, 82, 20, 2, 73, 7, 46, 88, 49, 43, 46, 83, 32, 8, 44, 32, 0, 67, 64, 27, 22, 19, 75, 50, 53, 27, 76, 55, 1, 96, 68, 45, 96, 6, 12, 71, 53, 42, 80, 4, 37, 39, 45, 11, 75, 40, 81, 85, 16, 64, 95, 35, 54, 55, 93, 35, 96, 43, 64, 13, 14, 78, 42, 69, 9, 51, 23, 10, 20, 3, 40, 85, 79, 9, 72, 14, 84, 4, 22],
  [68, 24, 9, 57, 16, 60, 96, 12, 58, 43, 13, 18, 2, 56, 7, 71, 82, 87, 95, 84, 2, 73, 15, 82, 52, 86, 71, 93, 15, 68, 39, 67, 25, 49, 26, 34, 30, 40, 46, 84, 54, 36, 18, 82, 42, 89, 15, 60, 18, 79, 84, 7, 87, 72, 59, 39, 27, 80, 35, 87, 25, 25, 29, 78, 15, 52, 70, 88, 55, 39, 47, 88, 34, 66, 87, 57, 18, 47, 11, 74, 96, 51, 84, 71, 3],
  [52, 89, 51, 26, 73, 67, 94, 2, 83, 61, 54, 30, 1, 53, 14, 33, 59, 91, 53, 46, 21, 28, 26, 35, 49, 38, 86, 96, 40, 92, 89, 3, 18, 75, 63, 26, 65, 36, 30, 87, 0, 30, 84, 73, 49, 2, 95, 95, 56, 70, 7, 40, 61, 81, 35, 29, 79, 27, 95, 18, 70, 72, 81, 76, 86, 50, 76, 49, 52, 90, 37, 25, 36, 34, 1, 24, 74, 1, 34, 3, 69, 19, 18, 96, 79],
  [38, 8, 78, 84, 41, 36, 27, 31, 42, 3, 14, 1, 20, 50, 5, 1, 88, 3, 65, 32, 88, 59, 9, 3, 30, 2, 26, 46, 71, 69, 11, 44, 32, 37, 71, 54, 17, 31, 14, 28, 66, 63, 20, 6, 11, 39, 72, 95, 55, 68, 3, 34, 14, 61, 95, 87, 29, 39, 64, 57, 6, 24, 26, 39, 34, 11, 9, 34, 67, 1, 7, 77, 26, 86, 79, 93, 93, 96, 82, 85, 61, 30, 79, 0, 29],
  [30, 34, 83, 36, 18, 17, 80, 17, 93, 69, 87, 85, 50, 77, 63, 44, 19, 31, 57, 62, 63, 16, 81, 73, 6, 1, 11, 72, 90, 51, 20, 77, 52, 74, 80, 5, 35, 25, 12, 1, 22, 16, 76, 7, 76, 22, 66, 65, 72, 56, 13, 6, 90, 80, 21, 95, 35, 59, 16, 37, 59, 57, 73, 74, 31, 69, 93, 29, 77, 84, 61, 25, 42, 37, 64, 24, 24, 21, 57, 59, 48, 40, 57, 9, 35],
  [0, 10, 42, 15, 82, 95, 13, 96, 57, 35, 48, 84, 42, 62, 10, 15, 24, 24, 33, 96, 84, 43, 67, 88, 14, 18, 80, 15, 87, 92, 24, 33, 94, 63, 34, 18, 34, 11, 44, 48, 28, 57, 23, 61, 8, 75, 57, 38, 84, 33, 68, 1, 16, 63, 80, 61, 81, 72, 85, 28, 88, 56, 46, 76, 47, 76, 67, 81, 88, 61, 96, 22, 35, 20, 6, 64, 10, 29, 84, 49, 75, 31, 30, 84, 90],
  [4, 26, 65, 71, 37, 73, 4, 37, 90, 69, 76, 22, 37, 88, 11, 75, 31, 13, 57, 41, 80, 88, 41, 85, 16, 55, 78, 86, 43, 39, 12, 55, 82, 96, 83, 79, 63, 10, 24, 54, 56, 4, 10, 25, 80, 58, 16, 57, 44, 24, 77, 30, 34, 16, 90, 14, 61, 87, 81, 81, 88, 27, 92, 62, 92, 34, 87, 83, 88, 52, 88, 90, 17, 76, 86, 31, 10, 94, 12, 23, 50, 76, 22, 23, 31],
  [56, 31, 19, 43, 58, 59, 12, 47, 45, 47, 3, 64, 12, 49, 25, 54, 59, 34, 14, 55, 81, 90, 90, 86, 18, 55, 0, 16, 76, 74, 50, 20, 72, 48, 90, 66, 87, 21, 32, 14, 5, 43, 12, 52, 12, 89, 40, 68, 78, 94, 8, 80, 30, 1, 6, 34, 40, 7, 40, 72, 78, 71, 11, 61, 59, 62, 67, 70, 16, 71, 89, 21, 43, 36, 46, 48, 77, 82, 30, 32, 35, 54, 24, 54, 59],
  [88, 49, 37, 27, 6, 57, 17, 72, 6, 17, 84, 28, 21, 91, 38, 46, 21, 83, 71, 92, 78, 75, 82, 63, 58, 84, 10, 15, 72, 77, 1, 85, 43, 61, 9, 32, 38, 67, 18, 72, 55, 78, 41, 34, 77, 50, 71, 83, 8, 20, 32, 8, 77, 68, 13, 3, 7, 84, 75, 86, 70, 12, 45, 57, 63, 33, 23, 91, 26, 80, 23, 55, 55, 85, 91, 14, 94, 57, 72, 86, 71, 45, 3, 26, 35],
  [9, 69, 34, 57, 85, 78, 55, 36, 68, 75, 40, 26, 83, 74, 44, 71, 53, 52, 68, 34, 20, 58, 62, 89, 24, 27, 28, 39, 27, 93, 47, 12, 55, 78, 48, 64, 88, 85, 85, 83, 37, 76, 60, 48, 20, 28, 65, 11, 61, 25, 20, 94, 24, 33, 56, 68, 70, 79, 11, 64, 67, 6, 14, 32, 49, 2, 50, 61, 8, 77, 66, 16, 34, 62, 77, 26, 8, 72, 81, 25, 29, 68, 83, 7, 63],
  [92, 91, 66, 33, 62, 41, 74, 11, 57, 31, 30, 63, 86, 15, 63, 29, 20, 26, 9, 36, 59, 81, 28, 94, 73, 35, 89, 17, 3, 61, 59, 9, 45, 55, 88, 46, 43, 42, 40, 41, 13, 0, 68, 10, 84, 19, 59, 41, 96, 61, 8, 78, 44, 84, 72, 55, 56, 18, 45, 54, 5, 61, 7, 52, 72, 38, 87, 89, 37, 67, 57, 47, 62, 2, 43, 70, 33, 32, 26, 43, 34, 79, 88, 56, 63],
  [87, 1, 90, 70, 96, 10, 79, 93, 78, 68, 37, 62, 47, 6, 36, 3, 60, 54, 14, 30, 27, 23, 65, 60, 13, 54, 75, 21, 15, 48, 61, 76, 25, 64, 50, 21, 10, 33, 73, 23, 27, 70, 49, 92, 22, 45, 18, 42, 41, 11, 83, 68, 57, 38, 65, 95, 95, 60, 39, 90, 77, 76, 44, 0, 6, 66, 37, 12, 90, 48, 83, 31, 24, 57, 78, 29, 51, 72, 40, 42, 71, 87, 40, 63, 61],
  [76, 96, 76, 59, 3, 22, 27, 50, 76, 15, 71, 28, 42, 48, 7, 10, 16, 45, 2, 69, 17, 6, 82, 19, 50, 16, 30, 92, 68, 73, 80, 68, 37, 63, 56, 32, 3, 39, 86, 69, 78, 56, 50, 87, 65, 2, 88, 18, 59, 65, 71, 40, 16, 57, 66, 72, 95, 15, 37, 60, 66, 82, 81, 57, 13, 50, 81, 50, 48, 85, 76, 66, 33, 27, 50, 68, 70, 95, 40, 45, 61, 90, 13, 4, 26],
  [2, 86, 18, 90, 9, 44, 5, 22, 53, 83, 76, 43, 32, 28, 27, 42, 15, 84, 23, 7, 74, 16, 66, 29, 76, 82, 53, 53, 84, 54, 92, 15, 32, 93, 67, 11, 54, 65, 92, 77, 14, 47, 19, 73, 53, 85, 2, 45, 19, 28, 50, 89, 58, 75, 22, 39, 2, 89, 4, 95, 54, 69, 45, 7, 27, 86, 94, 29, 9, 47, 13, 72, 65, 89, 2, 14, 68, 40, 62, 18, 77, 25, 84, 96, 43],
  [72, 27, 31, 62, 79, 83, 44, 93, 24, 61, 60, 12, 73, 20, 17, 95, 81, 49, 53, 56, 22, 91, 96, 94, 50, 71, 94, 75, 89, 50, 19, 31, 95, 74, 52, 76, 52, 41, 36, 80, 77, 42, 69, 38, 54, 53, 65, 22, 84, 20, 77, 12, 80, 8, 76, 11, 49, 42, 80, 62, 30, 39, 32, 26, 51, 38, 36, 58, 2, 93, 81, 16, 58, 15, 52, 64, 22, 66, 77, 9, 80, 24, 78, 8, 68],
  [25, 39, 27, 18, 72, 94, 62, 40, 10, 51, 95, 84, 23, 51, 43, 85, 48, 49, 42, 55, 11, 94, 12, 32, 30, 21, 13, 93, 45, 85, 16, 27, 16, 38, 2, 57, 66, 36, 0, 43, 52, 63, 81, 44, 38, 73, 87, 92, 10, 48, 34, 52, 25, 61, 7, 6, 73, 82, 42, 85, 31, 5, 91, 91, 10, 58, 29, 9, 31, 28, 25, 43, 34, 41, 59, 87, 31, 26, 93, 88, 31, 68, 64, 29, 49],
  [13, 20, 45, 74, 48, 26, 18, 37, 54, 95, 83, 48, 8, 71, 68, 54, 96, 71, 10, 17, 19, 80, 32, 80, 2, 86, 53, 31, 45, 58, 17, 27, 95, 79, 21, 26, 59, 94, 59, 19, 71, 70, 41, 81, 69, 19, 50, 49, 68, 60, 41, 12, 10, 23, 76, 20, 84, 18, 53, 73, 79, 40, 17, 57, 44, 60, 46, 37, 46, 17, 87, 8, 23, 30, 61, 19, 38, 96, 32, 19, 61, 77, 91, 19, 81],
  [78, 77, 96, 84, 96, 60, 35, 45, 30, 80, 85, 77, 56, 65, 32, 88, 20, 65, 41, 55, 8, 42, 60, 87, 90, 10, 91, 84, 12, 36, 0, 51, 35, 43, 68, 49, 86, 10, 36, 62, 31, 63, 70, 63, 42, 47, 56, 70, 0, 76, 78, 43, 4, 57, 16, 63, 30, 36, 71, 8, 1, 21, 57, 22, 28, 84, 75, 34, 69, 76, 43, 81, 35, 83, 92, 15, 43, 65, 59, 33, 34, 58, 68, 53, 57],
  [2, 1, 92, 47, 11, 50, 45, 22, 28, 66, 6, 10, 54, 36, 29, 91, 6, 37, 42, 75, 49, 17, 28, 52, 28, 19, 56, 15, 20, 94, 20, 74, 55, 37, 67, 54, 8, 63, 5, 9, 42, 31, 71, 52, 77, 14, 78, 27, 13, 37, 55, 5, 56, 28, 22, 66, 0, 54, 12, 26, 25, 54, 38, 30, 54, 30, 32, 29, 12, 76, 95, 10, 75, 5, 25, 56, 22, 59, 49, 41, 57, 55, 57, 89, 3],
  [93, 6, 31, 68, 53, 50, 50, 94, 65, 6, 8, 85, 73, 87, 42, 36, 8, 58, 1, 24, 58, 75, 88, 48, 67, 66, 83, 44, 13, 65, 69, 18, 48, 85, 77, 18, 14, 68, 70, 38, 9, 62, 19, 43, 80, 77, 69, 23, 41, 83, 72, 14, 54, 48, 1, 28, 87, 84, 6, 95, 35, 42, 83, 66, 6, 48, 22, 34, 79, 72, 31, 14, 0, 67, 34, 0, 34, 76, 30, 25, 16, 33, 79, 72, 69],
  [27, 15, 47, 39, 9, 54, 1, 85, 27, 85, 19, 20, 6, 70, 26, 13, 36, 82, 83, 91, 93, 74, 75, 63, 0, 6, 44, 19, 23, 49, 0, 72, 38, 53, 4, 12, 37, 91, 11, 70, 5, 36, 59, 0, 36, 92, 86, 73, 40, 85, 18, 32, 24, 44, 12, 14, 30, 46, 96, 5, 77, 29, 51, 52, 67, 40, 29, 7, 7, 60, 62, 3, 10, 27, 25, 33, 74, 46, 25, 94, 26, 91, 88, 66, 11],
  [87, 35, 52, 19, 78, 56, 73, 96, 51, 5, 64, 61, 18, 80, 88, 29, 46, 21, 31, 71, 41, 59, 82, 19, 17, 38, 9, 92, 64, 29, 42, 6, 96, 85, 52, 79, 41, 10, 91, 68, 63, 10, 94, 36, 41, 65, 39, 33, 42, 85, 67, 21, 10, 11, 25, 31, 36, 40, 45, 4, 52, 61, 81, 34, 96, 8, 78, 91, 70, 39, 36, 69, 76, 46, 77, 11, 93, 64, 38, 3, 4, 71, 53, 70, 92],
  [79, 74, 66, 52, 30, 77, 11, 37, 12, 27, 17, 22, 79, 59, 8, 16, 61, 21, 27, 25, 48, 30, 55, 81, 29, 32, 75, 0, 82, 95, 25, 58, 56, 88, 9, 7, 7, 41, 37, 14, 8, 86, 59, 66, 52, 54, 3, 10, 43, 88, 38, 87, 63, 34, 35, 17, 65, 30, 68, 20, 12, 22, 92, 71, 83, 66, 95, 49, 34, 63, 20, 33, 88, 35, 46, 13, 94, 77, 36, 34, 22, 20, 18, 12, 91],
  [46, 86, 57, 76, 26, 71, 10, 55, 67, 21, 27, 4, 8, 46, 56, 45, 5, 56, 32, 87, 7, 93, 92, 15, 60, 84, 13, 86, 56, 83, 3, 96, 84, 65, 25, 19, 7, 79, 12, 18, 54, 49, 26, 57, 76, 11, 32, 21, 46, 64, 32, 66, 79, 18, 5, 54, 26, 34, 96, 42, 19, 33, 62, 87, 16, 57, 76, 65, 50, 46, 54, 80, 73, 54, 31, 91, 80, 66, 35, 81, 56, 86, 13, 31, 71],
  [2, 58, 46, 39, 2, 69, 35, 81, 54, 41, 55, 9, 22, 51, 22, 57, 52, 24, 92, 4, 51, 8, 80, 48, 10, 52, 84, 55, 28, 3, 95, 24, 68, 71, 73, 25, 9, 52, 4, 77, 67, 68, 21, 2, 52, 67, 56, 50, 88, 48, 9, 90, 83, 34, 80, 71, 63, 26, 1, 17, 60, 32, 65, 75, 50, 36, 43, 64, 86, 70, 31, 83, 78, 73, 3, 92, 73, 1, 17, 72, 92, 12, 81, 6, 91],
  [67, 76, 52, 35, 41, 96, 39, 86, 73, 36, 79, 43, 62, 20, 30, 54, 12, 43, 60, 7, 90, 96, 50, 40, 9, 94, 9, 24, 7, 41, 1, 32, 5, 36, 71, 65, 88, 85, 53, 85, 37, 43, 79, 38, 74, 93, 63, 64, 55, 78, 61, 48, 96, 63, 74, 37, 75, 49, 55, 83, 79, 68, 70, 55, 32, 3, 58, 65, 57, 28, 65, 4, 83, 47, 58, 58, 16, 79, 62, 68, 53, 27, 20, 8, 27],
  [81, 19, 47, 10, 51, 36, 25, 34, 95, 71, 86, 75, 41, 19, 43, 79, 46, 42, 80, 74, 87, 33, 0, 36, 47, 83, 79, 32, 64, 77, 68, 54, 60, 5, 68, 84, 56, 96, 38, 48, 55, 35, 95, 16, 95, 32, 37, 25, 45, 55, 43, 72, 82, 94, 52, 32, 18, 25, 76, 18, 30, 21, 13, 17, 86, 55, 81, 47, 27, 13, 61, 43, 93, 0, 25, 55, 61, 54, 87, 18, 58, 19, 91, 50, 32],
  [37, 93, 42, 67, 94, 6, 7, 3, 96, 72, 43, 61, 5, 41, 84, 91, 47, 62, 50, 20, 27, 41, 37, 84, 3, 25, 88, 25, 38, 26, 64, 11, 54, 32, 24, 96, 58, 6, 72, 18, 74, 51, 27, 27, 31, 15, 68, 76, 9, 12, 85, 20, 55, 33, 77, 44, 3, 67, 27, 50, 62, 45, 61, 91, 19, 7, 66, 24, 85, 35, 7, 91, 14, 56, 89, 38, 60, 10, 3, 57, 50, 84, 64, 51, 22],
  [34, 59, 29, 29, 23, 61, 56, 21, 59, 38, 3, 88, 63, 11, 3, 91, 28, 76, 52, 55, 35, 56, 61, 22, 15, 15, 94, 43, 0, 67, 91, 64, 68, 1, 95, 3, 25, 42, 0, 69, 20, 0, 17, 16, 19, 92, 80, 61, 59, 47, 1, 50, 12, 24, 20, 11, 89, 39, 53, 93, 15, 52, 33, 28, 2, 41, 3, 5, 74, 66, 25, 19, 51, 66, 3, 59, 12, 72, 51, 16, 21, 30, 5, 84, 33],
  [4, 51, 40, 8, 62, 5, 7, 29, 33, 74, 55, 29, 75, 95, 22, 27, 1, 92, 42, 63, 78, 30, 43, 87, 35, 42, 96, 63, 5, 79, 67, 26, 77, 41, 3, 83, 95, 29, 49, 65, 94, 36, 58, 85, 50, 54, 73, 48, 61, 93, 77, 74, 39, 92, 51, 69, 92, 68, 50, 35, 45, 6, 20, 94, 27, 82, 22, 33, 24, 89, 79, 16, 67, 53, 55, 28, 86, 74, 30, 64, 63, 58, 65, 15, 82],
  [50, 52, 83, 33, 18, 12, 44, 63, 23, 49, 58, 91, 73, 79, 67, 63, 47, 54, 86, 8, 61, 45, 76, 40, 14, 25, 48, 13, 63, 5, 0, 38, 64, 7, 28, 56, 82, 64, 23, 13, 20, 12, 45, 45, 89, 84, 68, 15, 3, 27, 72, 76, 43, 87, 90, 71, 40, 15, 75, 11, 80, 80, 66, 53, 51, 27, 56, 17, 21, 12, 1, 41, 92, 42, 17, 28, 3, 17, 89, 20, 75, 68, 1, 75, 33],
  [84, 22, 1, 79, 11, 31, 62, 76, 18, 46, 26, 37, 33, 6, 63, 35, 19, 8, 9, 25, 90, 56, 2, 5, 26, 36, 70, 56, 13, 63, 43, 25, 32, 24, 55, 86, 0, 92, 19, 44, 15, 84, 31, 93, 75, 53, 92, 21, 17, 39, 15, 16, 86, 15, 72, 46, 96, 93, 19, 25, 9, 3, 45, 71, 70, 51, 26, 67, 24, 28, 31, 7, 29, 50, 63, 57, 83, 19, 81, 14, 54, 64, 77, 76, 16],
  [3, 29, 30, 75, 68, 51, 40, 62, 75, 68, 64, 22, 38, 54, 31, 93, 21, 90, 79, 56, 61, 67, 82, 44, 78, 19, 77, 70, 48, 96, 94, 88, 79, 9, 84, 13, 75, 9, 44, 83, 56, 91, 53, 13, 94, 53, 30, 75, 89, 28, 10, 0, 78, 80, 11, 26, 86, 71, 22, 51, 49, 3, 6, 90, 77, 46, 13, 3, 18, 15, 59, 34, 89, 36, 1, 9, 8, 7, 93, 20, 21, 86, 20, 5, 30],
  [35, 19, 8, 6, 41, 93, 3, 70, 93, 8, 81, 40, 46, 63, 22, 0, 70, 14, 41, 74, 8, 30, 82, 88, 5, 35, 19, 36, 25, 42, 15, 25, 83, 94, 52, 84, 32, 38, 6, 66, 19, 10, 86, 21, 71, 82, 16, 54, 35, 27, 84, 55, 55, 18, 1, 2, 38, 86, 27, 46, 75, 34, 78, 88, 73, 39, 92, 94, 31, 77, 92, 33, 96, 89, 65, 50, 82, 32, 71, 13, 67, 27, 47, 43, 85],
  [9, 29, 57, 14, 5, 29, 16, 31, 40, 93, 1, 88, 89, 33, 45, 28, 20, 25, 85, 32, 75, 1, 76, 2, 34, 5, 78, 26, 14, 35, 15, 3, 47, 9, 10, 60, 29, 17, 0, 67, 28, 90, 2, 30, 50, 76, 50, 13, 73, 24, 58, 18, 16, 14, 6, 30, 49, 52, 64, 47, 86, 76, 48, 0, 83, 7, 67, 2, 26, 73, 94, 57, 54, 30, 9, 0, 24, 81, 49, 68, 62, 12, 23, 48, 71],
  [77, 94, 56, 61, 40, 71, 42, 15, 19, 70, 41, 42, 82, 21, 14, 42, 66, 94, 81, 38, 21, 76, 69, 32, 2, 88, 44, 5, 40, 87, 22, 84, 36, 40, 48, 15, 81, 19, 63, 48, 52, 87, 80, 32, 94, 29, 19, 60, 94, 89, 63, 86, 85, 88, 73, 3, 35, 82, 67, 52, 96, 11, 87, 57, 89, 28, 22, 19, 36, 87, 3, 34, 23, 37, 9, 78, 81, 11, 95, 52, 85, 70, 19, 83, 0],
  [78, 21, 24, 75, 68, 29, 56, 68, 54, 85, 31, 17, 83, 17, 65, 37, 82, 65, 76, 69, 64, 21, 71, 69, 76, 82, 82, 2, 76, 43, 61, 37, 0, 50, 80, 92, 55, 82, 75, 88, 28, 60, 32, 12, 96, 66, 82, 65, 28, 62, 82, 90, 41, 67, 81, 9, 26, 15, 0, 94, 92, 20, 59, 13, 60, 11, 31, 35, 17, 67, 88, 54, 24, 48, 10, 60, 18, 41, 61, 48, 66, 77, 1, 46, 25],
  [14, 16, 71, 3, 48, 29, 0, 49, 62, 50, 63, 48, 91, 6, 68, 32, 37, 9, 60, 58, 94, 22, 21, 76, 1, 30, 67, 56, 45, 30, 56, 41, 33, 96, 8, 93, 30, 59, 74, 75, 17, 42, 80, 94, 91, 16, 6, 23, 81, 58, 75, 90, 88, 43, 16, 59, 28, 73, 32, 39, 20, 35, 57, 7, 71, 92, 73, 34, 21, 79, 69, 16, 16, 38, 37, 49, 84, 35, 90, 87, 9, 51, 66, 23, 0],
  [82, 77, 22, 86, 80, 24, 58, 92, 90, 12, 9, 90, 14, 55, 5, 30, 84, 26, 5, 25, 53, 94, 64, 21, 75, 8, 61, 90, 61, 78, 35, 27, 87, 90, 51, 7, 48, 41, 93, 58, 49, 8, 19, 11, 22, 74, 17, 27, 59, 20, 78, 81, 80, 84, 63, 88, 21, 2, 44, 38, 91, 57, 78, 19, 40, 86, 28, 22, 12, 71, 90, 48, 3, 0, 32, 16, 68, 32, 3, 58, 47, 18, 68, 72, 64],
  [65, 8, 49, 71, 48, 92, 61, 11, 66, 14, 9, 14, 46, 70, 68, 20, 36, 90, 59, 58, 25, 58, 69, 38, 32, 74, 56, 25, 8, 63, 55, 20, 74, 7, 4, 87, 25, 71, 91, 24, 75, 55, 17, 55, 56, 7, 69, 30, 36, 34, 92, 55, 41, 96, 62, 32, 46, 84, 8, 15, 2, 85, 27, 56, 4, 85, 89, 58, 46, 58, 85, 21, 21, 94, 58, 26, 18, 90, 66, 79, 1, 85, 60, 11, 60],
  [5, 79, 89, 66, 78, 91, 57, 67, 89, 71, 24, 78, 44, 37, 34, 3, 70, 39, 7, 59, 5, 60, 76, 81, 85, 41, 79, 9, 86, 42, 52, 50, 80, 60, 92, 32, 27, 31, 83, 1, 42, 41, 10, 42, 53, 23, 2, 14, 9, 68, 71, 14, 57, 33, 57, 65, 53, 95, 32, 82, 62, 3, 1, 91, 68, 90, 29, 30, 51, 25, 1, 39, 24, 81, 29, 65, 28, 67, 47, 26, 32, 52, 16, 35, 90],
  [50, 90, 38, 72, 20, 65, 21, 64, 84, 28, 89, 51, 90, 84, 2, 28, 60, 41, 39, 90, 26, 9, 65, 94, 25, 14, 90, 8, 54, 92, 76, 62, 42, 43, 24, 56, 21, 21, 82, 58, 37, 65, 71, 49, 49, 84, 45, 54, 26, 52, 83, 34, 13, 24, 31, 3, 91, 87, 83, 29, 86, 88, 30, 43, 64, 9, 58, 85, 1, 88, 70, 40, 48, 30, 49, 2, 95, 71, 77, 13, 85, 83, 62, 10, 5],
  [28, 21, 55, 28, 42, 37, 26, 28, 56, 12, 11, 16, 88, 73, 92, 67, 26, 60, 70, 36, 84, 37, 82, 66, 20, 70, 21, 19, 47, 1, 28, 47, 46, 12, 52, 5, 61, 46, 36, 8, 6, 20, 96, 48, 81, 15, 16, 60, 20, 53, 21, 59, 31, 24, 19, 88, 59, 82, 46, 7, 51, 59, 93, 33, 69, 84, 94, 24, 92, 7, 35, 87, 62, 35, 34, 30, 68, 81, 88, 70, 53, 63, 60, 2, 91],
  [82, 39, 9, 29, 50, 63, 75, 82, 76, 88, 91, 69, 6, 25, 53, 65, 67, 28, 3, 20, 30, 32, 37, 42, 28, 0, 93, 35, 63, 27, 91, 91, 79, 54, 57, 45, 16, 29, 13, 36, 91, 88, 54, 85, 95, 42, 10, 3, 29, 71, 46, 54, 75, 15, 44, 1, 33, 71, 43, 25, 17, 22, 54, 24, 54, 7, 73, 70, 39, 81, 88, 29, 3, 47, 26, 13, 32, 29, 77, 74, 91, 76, 54, 78, 79],
  [61, 19, 77, 19, 10, 11, 82, 52, 85, 8, 78, 16, 40, 52, 82, 53, 92, 2, 34, 68, 5, 68, 65, 14, 45, 22, 31, 63, 67, 22, 3, 84, 43, 30, 22, 56, 8, 88, 26, 42, 29, 32, 68, 43, 17, 27, 7, 36, 63, 44, 38, 25, 11, 10, 63, 5, 14, 7, 49, 54, 82, 63, 20, 25, 9, 53, 90, 51, 70, 73, 7, 5, 37, 84, 43, 92, 27, 82, 75, 93, 64, 77, 0, 85, 71],
  [71, 16, 29, 87, 37, 47, 55, 79, 37, 95, 56, 91, 74, 74, 52, 25, 73, 84, 37, 70, 55, 6, 17, 21, 33, 63, 54, 6, 79, 95, 11, 41, 19, 20, 51, 46, 59, 80, 70, 87, 36, 65, 71, 51, 20, 28, 48, 6, 15, 74, 91, 49, 88, 62, 77, 50, 53, 56, 88, 20, 85, 80, 33, 72, 69, 57, 23, 41, 18, 54, 85, 55, 24, 33, 80, 26, 6, 32, 25, 7, 94, 95, 52, 43, 34],
  [9, 11, 95, 26, 55, 68, 95, 68, 60, 55, 41, 84, 53, 74, 40, 6, 88, 90, 44, 46, 14, 91, 83, 82, 89, 46, 38, 33, 73, 75, 63, 5, 41, 62, 22, 8, 79, 18, 6, 73, 54, 56, 8, 23, 73, 32, 42, 47, 86, 83, 21, 12, 37, 42, 50, 20, 1, 2, 46, 24, 91, 10, 74, 31, 62, 76, 2, 17, 45, 75, 84, 32, 6, 15, 73, 15, 1, 67, 93, 78, 41, 61, 64, 58, 86],
  [89, 96, 20, 44, 60, 18, 45, 91, 93, 22, 85, 12, 84, 91, 16, 69, 16, 51, 78, 14, 90, 48, 17, 42, 88, 40, 22, 37, 91, 29, 88, 61, 75, 43, 9, 4, 22, 61, 20, 85, 10, 77, 48, 84, 12, 43, 28, 62, 63, 26, 28, 64, 22, 84, 85, 1, 30, 18, 7, 87, 20, 35, 29, 26, 46, 42, 0, 34, 44, 73, 54, 13, 21, 9, 16, 23, 36, 65, 56, 96, 23, 65, 3, 31, 23],
  [22, 86, 1, 42, 74, 10, 80, 61, 59, 46, 36, 85, 41, 56, 78, 91, 11, 89, 24, 9, 9, 63, 31, 41, 1, 81, 64, 26, 58, 55, 3, 43, 86, 79, 55, 27, 17, 64, 19, 8, 6, 85, 83, 95, 60, 76, 71, 37, 30, 40, 84, 3, 76, 48, 87, 14, 54, 13, 73, 92, 23, 70, 46, 71, 43, 12, 20, 78, 57, 59, 86, 37, 10, 18, 39, 8, 70, 1, 24, 21, 34, 79, 88, 84, 1],
  [57, 37, 8, 64, 14, 51, 5, 8, 56, 9, 46, 22, 55, 95, 8, 88, 12, 28, 71, 14, 12, 50, 85, 70, 93, 8, 68, 46, 49, 74, 38, 72, 71, 36, 41, 21, 27, 5, 85, 6, 66, 80, 95, 51, 61, 83, 15, 68, 31, 75, 17, 47, 69, 35, 69, 3, 61, 43, 2, 45, 76, 68, 31, 63, 64, 15, 75, 25, 94, 55, 12, 76, 95, 48, 51, 80, 13, 10, 8, 65, 82, 88, 64, 5, 58],
  [5, 86, 15, 76, 85, 72, 19, 96, 56, 56, 59, 93, 60, 37, 85, 76, 56, 84, 89, 66, 90, 62, 54, 19, 40, 93, 75, 18, 23, 33, 59, 96, 95, 73, 54, 67, 12, 51, 27, 65, 28, 30, 54, 10, 24, 53, 76, 78, 57, 68, 6, 45, 90, 57, 93, 42, 83, 58, 20, 67, 78, 55, 65, 20, 71, 92, 9, 25, 95, 85, 86, 68, 23, 26, 79, 58, 44, 34, 41, 71, 6, 73, 75, 43, 96],
  [30, 32, 71, 59, 26, 92, 64, 23, 96, 8, 61, 91, 68, 79, 52, 82, 28, 64, 67, 11, 92, 49, 68, 15, 31, 70, 62, 76, 63, 29, 21, 3, 34, 86, 81, 55, 37, 96, 85, 94, 22, 45, 37, 40, 93, 22, 50, 93, 11, 36, 72, 47, 37, 96, 17, 31, 2, 12, 82, 52, 53, 90, 58, 55, 49, 12, 51, 67, 59, 1, 10, 82, 66, 39, 86, 24, 1, 37, 38, 11, 48, 55, 67, 65, 64],
  [12, 4, 64, 76, 15, 89, 31, 64, 19, 5, 80, 45, 95, 55, 82, 75, 26, 21, 57, 61, 58, 0, 56, 42, 16, 3, 40, 62, 44, 7, 56, 7, 25, 39, 35, 10, 11, 73, 1, 50, 45, 35, 18, 62, 44, 5, 27, 79, 74, 55, 17, 12, 4, 13, 80, 27, 94, 96, 19, 16, 51, 29, 5, 44, 79, 50, 54, 56, 65, 23, 28, 22, 22, 94, 37, 64, 22, 85, 42, 85, 39, 79, 73, 70, 75],
  [94, 15, 75, 46, 32, 20, 89, 92, 72, 51, 10, 18, 68, 47, 11, 63, 37, 65, 91, 92, 24, 29, 29, 71, 29, 93, 51, 31, 12, 5, 61, 6, 36, 96, 69, 71, 77, 56, 54, 50, 50, 60, 26, 94, 83, 44, 22, 10, 41, 78, 57, 59, 73, 95, 17, 36, 67, 60, 60, 57, 47, 88, 75, 26, 26, 26, 44, 7, 45, 13, 62, 40, 63, 16, 43, 91, 96, 14, 39, 24, 42, 21, 0, 60, 55],
  [82, 84, 89, 94, 29, 32, 15, 26, 85, 14, 74, 60, 55, 37, 10, 50, 42, 20, 78, 48, 80, 48, 68, 40, 5, 41, 68, 11, 18, 62, 23, 94, 51, 41, 2, 26, 30, 78, 9, 53, 11, 96, 48, 72, 79, 9, 3, 96, 62, 85, 6, 58, 37, 82, 18, 41, 73, 16, 58, 71, 9, 10, 86, 14, 72, 84, 42, 85, 50, 56, 29, 49, 15, 54, 86, 22, 88, 38, 81, 36, 23, 52, 50, 90, 62],
  [83, 25, 4, 74, 94, 46, 76, 59, 76, 64, 42, 44, 26, 87, 19, 29, 28, 72, 66, 71, 86, 3, 75, 61, 14, 6, 75, 79, 33, 8, 29, 67, 10, 35, 39, 76, 52, 19, 39, 68, 47, 84, 74, 18, 62, 90, 59, 70, 33, 57, 27, 43, 71, 15, 36, 84, 26, 57, 47, 71, 75, 53, 87, 54, 33, 41, 78, 84, 96, 48, 9, 29, 1, 35, 60, 47, 2, 28, 68, 85, 15, 29, 52, 48, 2],
  [46, 30, 32, 4, 89, 75, 64, 71, 15, 8, 1, 20, 95, 29, 77, 9, 55, 38, 89, 49, 22, 71, 24, 56, 57, 8, 30, 1, 83, 40, 29, 42, 47, 52, 46, 57, 66, 52, 47, 31, 92, 96, 45, 27, 31, 18, 76, 90, 66, 34, 37, 19, 65, 42, 83, 78, 51, 9, 7, 57, 29, 87, 60, 91, 15, 45, 45, 12, 68, 60, 75, 49, 2, 95, 35, 8, 72, 86, 78, 89, 58, 28, 89, 49, 59],
  [6, 73, 30, 25, 84, 15, 4, 32, 86, 37, 86, 96, 11, 16, 19, 39, 21, 90, 79, 8, 77, 16, 21, 94, 29, 19, 29, 22, 52, 51, 59, 93, 19, 76, 58, 86, 74, 35, 15, 6, 1, 77, 20, 39, 27, 86, 96, 1, 91, 69, 49, 31, 26, 10, 34, 8, 89, 24, 9, 47, 3, 23, 18, 47, 60, 71, 70, 23, 87, 82, 1, 62, 96, 60, 59, 24, 35, 7, 11, 69, 71, 59, 57, 85, 86],
  [82, 6, 46, 83, 82, 94, 12, 30, 5, 57, 22, 89, 9, 71, 61, 82, 28, 50, 5, 65, 82, 14, 78, 77, 9, 35, 3, 84, 50, 4, 34, 37, 81, 67, 2, 46, 79, 87, 27, 93, 2, 78, 13, 25, 72, 2, 76, 87, 92, 9, 88, 56, 4, 0, 30, 38, 52, 68, 9, 14, 22, 16, 75, 4, 58, 47, 88, 20, 85, 9, 92, 56, 32, 1, 0, 38, 28, 23, 91, 12, 60, 41, 93, 85, 95]]

/-- 辅助引理（注记 3.5）：第 7 行的 OEIS 递推（`oeis_A207127`）写成 `Σ_i γ_i·a_{k+i}(7) = 0`。 -/
theorem row_rec_seven (k : ℕ) : ∑ i ∈ range (85 + 1), (rowGam7.getD i 0 : ℂ) * (a (k + i) 7 : ℂ) = 0 := by
  refine (sum_getD_eq_lsumC (fun j => (a (k + j) 7 : ℂ)) rowGam7 0).trans ?_
  have h2 := congrArg (Int.cast : ℤ → ℂ) (oeis_A207127 k)
  push_cast at h2
  simp only [rowGam7, lsumC, add_zero]
  push_cast
  linear_combination h2

/-- 辅助引理（注记 3.5）：第 7 行 85×85 的 Hankel 行列式 `det (a_{i+j}(7))` 非零（模 97 的逆作证书）。 -/
theorem hankel_row_seven : (Matrix.of fun i j : Fin 85 => (a (i + j) 7 : ℂ)).det ≠ 0 :=
  hankel_det_ne_zero_of_kron (p := 97) (B := 2 ^ 20) (K := 169) rowCols7 (by norm_num) (by norm_num) rfl
    (by norm_num) (by decide +kernel)

/-- **注记 3.5**（第 7 行递推的最小阶）：`k ↦ a_k(7)` 的常系数递推（对一切充分大的 `k` 成立、首项系数非零）的阶最小是 85：OEIS 的 85 阶递推（A207127）从 `k = 0` 起成立，更低阶的都不成立。 -/
theorem row_min_order_seven : IsLeast {d : ℕ | ∃ (k0 : ℕ) (c : ℕ → ℂ), c d ≠ 0 ∧
    ∀ k, k0 ≤ k → ∑ i ∈ range (d + 1), c i * (a (k + i) 7 : ℂ) = 0} 85 :=
  row_isLeast (γ := rowGam7) rfl row_rec_seven hankel_row_seven

/-- **注记 3.5**（第 7 行：不同乘积的个数）：`σ ∈ sig 4`、`τ ∈ sig 3` 的乘积 `στ` 恰有 85 个不同的值，等于第 7 行递推的最小阶。 -/
theorem card_row_products_seven : #((sig 4 ×ˢ sig 3).image fun p => p.1 * p.2) = 85 :=
  le_antisymm (card_products_le (e := 85) (γ := rowGam7) rfl rfl (by decide +kernel))
    (card_products_ge (n := 7) row_min_order_seven.2)

end A207123
