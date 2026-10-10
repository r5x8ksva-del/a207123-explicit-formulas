import A207123.AsympRemark
import A207123.OeisRows

/-!
# 论文注记 3.3 的数值（区间核对）

论文注记 3.3 的数值说法：`ρ_1 ≈ 1.46557`，`c_1 ≈ 2.20961`，`c_2 ≈ 7.84112`，`c_3 ≈ 28.97686`；在 `1 ≤ m ≤ 24` 内
`κ_m` 随 `m` 递增，`κ_1 ≈ 0.453`，`κ_4 ≈ 1.745`，`κ_24 ≈ 9.869`；相对误差 `U_k(m)/(c_m ρ_m^k) − 1` 在 `k = 3m` 时
`m = 2` 约 `−0.36`、`m = 24` 约 `−0.996`，在 `k = 10m` 时约 `−0.05` 与 `−0.41`。这里「≈ x」按四舍五入理解为
「与 x 之差小于 x 末位的半个单位」：`rho_one_approx`、`cm_one_approx`、`cm_two_approx`、`cm_three_approx`、
`kappa_one_approx`、`kappa_four_approx`、`kappa_twentyfour_approx`、`kappa_increasing`、`relerr_two_six`、
`relerr_twentyfour_seventytwo`、`relerr_two_twenty`、`relerr_twentyfour_twoforty`。

做法（区间算术）：

* `ρ_m`：`lo ≥ 1` 且 `lo³ − lo² < m < hi³ − hi²` 时 `lo < ρ_m < hi`（`lt_rho_of_cubic`、`rho_lt_of_cubic`；
  `y³ − y²` 在 `y ≥ 1` 上严格增，`Growth.lean` 的 `fcub_strictMonoOn`）。
* `c_m = N(ρ_m)/D(ρ_m)`（`cm_eq_frac`），`N(x) = x^{3m+3} + Σ_{j=1}^{m} j·m^{\underline j}·x^{3(m−j)+1}`、
  `D(x) = m!(x² + 3m)` 都在 `x ≥ 0` 上增，所以 `N(lo)/D(hi) ≤ c_m ≤ N(hi)/D(lo)`（`cm_bounds`）。
* 有理点上的 `N`、`D` 用可在内核里求值的 `cmNQ`、`cmDQ` 计算（`cmNQ_cast`、`cmDQ_cast`：与 `N`、`D` 相等），
  比较用 `decide +kernel`（内核求值，不引入公理）。
* `κ_m = c_{m−1}ρ_{m−1}³/c_m` 的区间由 `c_{m−1}`、`ρ_{m−1}`、`c_m` 的区间得出（`kappa_mem`、`kappa_one_mem`）。
* 相对误差：`U_k(m)` 的精确值用 `OeisRows.lean` 的 `Ucol` 在内核里算（`U_eq_Ucol_getD`），再由
  `U/(B·hi^k) ≤ U/(c_m ρ_m^k) ≤ U/(A·lo^k)` 夹住（`relerr_of_bounds`）。

区间端点由 `code/main_extra/remark33_numerics_lean.py` 用精确分数选出并核对（ρ 的区间宽 `10^{−12}`），
本文件后半的数值引理由它生成。
-/

namespace A207123

open Finset

/-! ## `ρ_m` 的区间：三次式变号 -/

/-- 辅助引理（注记 3.3）：`x ≥ 1` 且 `x³ − x² < m` 时 `x < ρ_m`。 -/
theorem lt_rho_of_cubic {m : ℕ} {x : ℝ} (hx : 1 ≤ x) (h : x ^ 3 - x ^ 2 < m) : x < rho m := by
  by_contra hle
  have h1 := (fcub_strictMonoOn m).monotoneOn (one_le_rho m) hx (not_lt.mp hle)
  simp only [fcub] at h1
  have hs := rho_spec m
  linarith

/-- 辅助引理（注记 3.3）：`x ≥ 1` 且 `x³ − x² > m` 时 `ρ_m < x`。 -/
theorem rho_lt_of_cubic {m : ℕ} {x : ℝ} (hx : 1 ≤ x) (h : (m : ℝ) < x ^ 3 - x ^ 2) : rho m < x := by
  by_contra hle
  have h1 := (fcub_strictMonoOn m).monotoneOn hx (one_le_rho m) (not_lt.mp hle)
  simp only [fcub] at h1
  have hs := rho_spec m
  linarith

/-! ## `c_m` 写成分子比分母 -/

/-- `c_m` 的分子：`N(x) = x^{3m+3} + Σ_{j=1}^{m} j·m^{\underline j}·x^{3(m−j)+1}`。 -/
noncomputable def cmN (m : ℕ) (x : ℝ) : ℝ :=
  x ^ (3 * m + 3) + ∑ j ∈ Icc 1 m, (j : ℝ) * (m.descFactorial j : ℝ) * x ^ (3 * (m - j) + 1)

/-- `c_m` 的分母：`D(x) = m!(x² + 3m)`。 -/
noncomputable def cmD (m : ℕ) (x : ℝ) : ℝ := (m.factorial : ℝ) * (x ^ 2 + 3 * m)

/-- 辅助引理（注记 3.3）：`c_m = N(ρ_m)/D(ρ_m)`。 -/
theorem cm_eq_frac (m : ℕ) : cm m = cmN m (rho m) / cmD m (rho m) := by
  have hρ : rho m ≠ 0 := (lt_of_lt_of_le one_pos (one_le_rho m)).ne'
  rw [cm, cmN, cmD, div_mul_eq_mul_div, mul_add, mul_one, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  have hpow : rho m ^ (3 * m + 3) = rho m ^ (3 * j + 2) * rho m ^ (3 * (m - j) + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have ha : rho m ^ (3 * j + 2) ≠ 0 := pow_ne_zero _ hρ
  rw [hpow]
  calc rho m ^ (3 * j + 2) * rho m ^ (3 * (m - j) + 1) *
        ((j : ℝ) * (m.descFactorial j : ℝ) * (rho m ^ (3 * j + 2))⁻¹)
      = (j : ℝ) * (m.descFactorial j : ℝ) * rho m ^ (3 * (m - j) + 1) *
          (rho m ^ (3 * j + 2) * (rho m ^ (3 * j + 2))⁻¹) := by ring
    _ = (j : ℝ) * (m.descFactorial j : ℝ) * rho m ^ (3 * (m - j) + 1) := by rw [mul_inv_cancel₀ ha, mul_one]

/-- 辅助引理（注记 3.3）：`N` 在 `x ≥ 0` 上增。 -/
theorem cmN_le {m : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : cmN m x ≤ cmN m y := by
  unfold cmN
  gcongr

/-- 辅助引理（注记 3.3）：`D` 在 `x ≥ 0` 上增。 -/
theorem cmD_le {m : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : cmD m x ≤ cmD m y := by
  unfold cmD
  gcongr

/-- 辅助引理（注记 3.3）：`D(x) > 0`（`x > 0`）。 -/
theorem cmD_pos {m : ℕ} {x : ℝ} (hx : 0 < x) : 0 < cmD m x := by
  unfold cmD
  have h2 : 0 < x ^ 2 := pow_pos hx 2
  have h3 : (0 : ℝ) ≤ 3 * m := by positivity
  exact mul_pos (by positivity) (by linarith)

/-- 辅助引理（注记 3.3）：`N(x) ≥ 0`（`x ≥ 0`）。 -/
theorem cmN_nonneg {m : ℕ} {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cmN m x := by
  unfold cmN
  positivity

/-- 辅助引理（注记 3.3）：`0 < lo ≤ ρ_m ≤ hi` 时 `N(lo)/D(hi) ≤ c_m ≤ N(hi)/D(lo)`。 -/
theorem cm_bounds {m : ℕ} {lo hi : ℝ} (h0 : 0 < lo) (hlo : lo ≤ rho m) (hhi : rho m ≤ hi) :
    cmN m lo / cmD m hi ≤ cm m ∧ cm m ≤ cmN m hi / cmD m lo := by
  have hρ : 0 < rho m := lt_of_lt_of_le h0 hlo
  rw [cm_eq_frac]
  constructor
  · exact div_le_div₀ (cmN_nonneg hρ.le) (cmN_le h0.le hlo) (cmD_pos hρ) (cmD_le hρ.le hhi)
  · exact div_le_div₀ (cmN_nonneg (by linarith)) (cmN_le hρ.le hhi) (cmD_pos h0) (cmD_le h0.le hlo)

/-! ## 有理点上的计算版本（可在内核里求值） -/

/-- `Σ_{j=1}^{n} j·m^{\underline j}·x^{3(m−j)+1}`，逐项递推。 -/
def cmTailQ (m : ℕ) (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => cmTailQ m x j + ((j + 1 : ℕ) : ℚ) * (m.descFactorial (j + 1) : ℚ) * x ^ (3 * (m - (j + 1)) + 1)

/-- 有理点上的 `N`。 -/
def cmNQ (m : ℕ) (x : ℚ) : ℚ := x ^ (3 * m + 3) + cmTailQ m x m

/-- 有理点上的 `D`。 -/
def cmDQ (m : ℕ) (x : ℚ) : ℚ := (m.factorial : ℚ) * (x ^ 2 + 3 * m)

/-- 辅助引理（注记 3.3）：`cmTailQ` 就是 `N` 里的和。 -/
theorem cmTailQ_cast (m : ℕ) (x : ℚ) : ∀ n, ((cmTailQ m x n : ℚ) : ℝ) =
    ∑ j ∈ Icc 1 n, (j : ℝ) * (m.descFactorial j : ℝ) * (x : ℝ) ^ (3 * (m - j) + 1)
  | 0 => by simp [cmTailQ]
  | n + 1 => by
    rw [cmTailQ, Rat.cast_add, cmTailQ_cast m x n, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    ring

/-- 辅助引理（注记 3.3）：`cmNQ m x = N(x)`。 -/
theorem cmNQ_cast (m : ℕ) (x : ℚ) : ((cmNQ m x : ℚ) : ℝ) = cmN m x := by
  rw [cmNQ, cmN, Rat.cast_add, Rat.cast_pow, cmTailQ_cast]

/-- 辅助引理（注记 3.3）：`cmDQ m x = D(x)`。 -/
theorem cmDQ_cast (m : ℕ) (x : ℚ) : ((cmDQ m x : ℚ) : ℝ) = cmD m x := by
  simp [cmDQ, cmD]

/-- 辅助引理（注记 3.3）：由 `ρ_m` 的有理区间与两个有理比较得到 `c_m` 的有理区间。 -/
theorem cm_mem {m : ℕ} {lo hi a b : ℚ} (hr : ((lo : ℚ) : ℝ) < rho m ∧ rho m < ((hi : ℚ) : ℝ)) (h0 : 0 < lo)
    (ha : a < cmNQ m lo / cmDQ m hi) (hb : cmNQ m hi / cmDQ m lo < b) :
    ((a : ℚ) : ℝ) < cm m ∧ cm m < ((b : ℚ) : ℝ) := by
  obtain ⟨c1, c2⟩ := cm_bounds (m := m) (lo := (lo : ℝ)) (hi := (hi : ℝ)) (by exact_mod_cast h0) hr.1.le hr.2.le
  rw [← cmNQ_cast, ← cmDQ_cast, ← Rat.cast_div] at c1 c2
  exact ⟨lt_of_lt_of_le (by exact_mod_cast ha) c1, lt_of_le_of_lt c2 (by exact_mod_cast hb)⟩

/-- 辅助引理（注记 3.3）：`0 ≤ p < q`、`0 < s ≤ r` 时 `p/r < q/s`。 -/
theorem frac_lt_frac {p q r s : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hs : 0 < s) (hsr : s ≤ r) : p / r < q / s := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  rw [div_lt_div_iff₀ hr hs]
  calc p * s ≤ p * r := mul_le_mul_of_nonneg_left hsr hp
    _ < q * r := mul_lt_mul_of_pos_right hpq hr

/-- 辅助引理（注记 3.3）：`κ_1 = 1/c_1` 的有理区间。 -/
theorem kappa_one_mem {a b kl ku : ℚ} (hc : ((a : ℚ) : ℝ) < cm 1 ∧ cm 1 < ((b : ℚ) : ℝ)) (ha : 0 < a)
    (hkl : kl ≤ 1 / b) (hku : 1 / a ≤ ku) : ((kl : ℚ) : ℝ) < kappaConst 1 ∧ kappaConst 1 < ((ku : ℚ) : ℝ) := by
  have hk : kappaConst 1 = 1 / cm 1 := by
    rw [kappaConst]
    norm_num [cm_zero, rho_zero]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hc0 : 0 < cm 1 := lt_trans haR hc.1
  rw [hk]
  constructor
  · calc ((kl : ℚ) : ℝ) ≤ ((1 / b : ℚ) : ℝ) := by exact_mod_cast hkl
      _ = 1 / (b : ℝ) := by push_cast; ring
      _ < 1 / cm 1 := one_div_lt_one_div_of_lt hc0 hc.2
  · calc 1 / cm 1 < 1 / (a : ℝ) := one_div_lt_one_div_of_lt haR hc.1
      _ = ((1 / a : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((ku : ℚ) : ℝ) := by exact_mod_cast hku

/-- 辅助引理（注记 3.3）：由 `c_{m−1}`、`ρ_{m−1}`、`c_m` 的有理区间得到 `κ_m = c_{m−1}ρ_{m−1}³/c_m` 的有理区间。 -/
theorem kappa_mem {m : ℕ} {a b lo hi a' b' kl ku : ℚ}
    (hc : ((a : ℚ) : ℝ) < cm (m - 1) ∧ cm (m - 1) < ((b : ℚ) : ℝ))
    (hr : ((lo : ℚ) : ℝ) < rho (m - 1) ∧ rho (m - 1) < ((hi : ℚ) : ℝ))
    (hc' : ((a' : ℚ) : ℝ) < cm m ∧ cm m < ((b' : ℚ) : ℝ))
    (ha : 0 < a) (hlo : 0 < lo) (ha' : 0 < a')
    (hkl : kl ≤ a * lo ^ 3 / b') (hku : b * hi ^ 3 / a' ≤ ku) :
    ((kl : ℚ) : ℝ) < kappaConst m ∧ kappaConst m < ((ku : ℚ) : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hloR : (0 : ℝ) < lo := by exact_mod_cast hlo
  have ha'R : (0 : ℝ) < a' := by exact_mod_cast ha'
  have hc0 : 0 < cm (m - 1) := lt_trans haR hc.1
  have hr0 : 0 < rho (m - 1) := lt_trans hloR hr.1
  have key1 : (a : ℝ) * (lo : ℝ) ^ 3 < cm (m - 1) * rho (m - 1) ^ 3 :=
    mul_lt_mul'' hc.1 (pow_lt_pow_left₀ hr.1 hloR.le (by norm_num)) haR.le (by positivity)
  have key2 : cm (m - 1) * rho (m - 1) ^ 3 < (b : ℝ) * (hi : ℝ) ^ 3 :=
    mul_lt_mul'' hc.2 (pow_lt_pow_left₀ hr.2 hr0.le (by norm_num)) hc0.le (by positivity)
  rw [kappaConst]
  constructor
  · calc ((kl : ℚ) : ℝ) ≤ ((a * lo ^ 3 / b' : ℚ) : ℝ) := by exact_mod_cast hkl
      _ = (a : ℝ) * (lo : ℝ) ^ 3 / (b' : ℝ) := by push_cast; ring
      _ < cm (m - 1) * rho (m - 1) ^ 3 / cm m :=
        frac_lt_frac (by positivity) key1 (lt_trans ha'R hc'.1) hc'.2.le
  · calc cm (m - 1) * rho (m - 1) ^ 3 / cm m < (b : ℝ) * (hi : ℝ) ^ 3 / (a' : ℝ) :=
          frac_lt_frac (by positivity) key2 ha'R hc'.1.le
      _ = ((b * hi ^ 3 / a' : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((ku : ℚ) : ℝ) := by exact_mod_cast hku

/-- 辅助引理（注记 3.3）：区间 `(lo, hi) ⊆ [t − ε, t + ε]` 时 `|x − t| < ε`。 -/
theorem approx_of_bounds {x lo hi t ε : ℝ} (h1 : lo < x) (h2 : x < hi) (hlo : t - ε ≤ lo) (hhi : hi ≤ t + ε) :
    |x - t| < ε := by
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- 辅助引理（注记 3.3）：`0 < y < x` 时 `u/x < u/y`（`u > 0`）。 -/
theorem div_lt_div_of_lt_left' {u x y : ℝ} (hu : 0 < u) (hy : 0 < y) (hyx : y < x) : u / x < u / y := by
  have hx : 0 < x := lt_trans hy hyx
  rw [div_lt_div_iff₀ hx hy]
  exact mul_lt_mul_of_pos_left hyx hu

/-- 辅助引理（注记 3.3）：由 `c_m`、`ρ_m` 的有理区间与两个有理比较，夹住相对误差 `U/(c_m ρ_m^k) − 1`。 -/
theorem relerr_of_bounds {u m k : ℕ} {a b lo hi t ε : ℚ}
    (hc : ((a : ℚ) : ℝ) < cm m ∧ cm m < ((b : ℚ) : ℝ)) (hr : ((lo : ℚ) : ℝ) < rho m ∧ rho m < ((hi : ℚ) : ℝ))
    (ha : 0 < a) (hlo : 0 < lo) (hu : 0 < u)
    (h1 : t - ε ≤ (u : ℚ) / (b * hi ^ k) - 1) (h2 : (u : ℚ) / (a * lo ^ k) - 1 ≤ t + ε) :
    |(u : ℝ) / (cm m * rho m ^ k) - 1 - (t : ℝ)| < (ε : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hloR : (0 : ℝ) < lo := by exact_mod_cast hlo
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hρ : 0 < rho m := lt_trans hloR hr.1
  have hbR : (0 : ℝ) < b := lt_trans (lt_trans haR hc.1) hc.2
  have hd1 : (a : ℝ) * (lo : ℝ) ^ k < cm m * rho m ^ k :=
    calc (a : ℝ) * (lo : ℝ) ^ k ≤ (a : ℝ) * rho m ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hloR.le hr.1.le k) haR.le
      _ < cm m * rho m ^ k := mul_lt_mul_of_pos_right hc.1 (pow_pos hρ k)
  have hd2 : cm m * rho m ^ k < (b : ℝ) * (hi : ℝ) ^ k :=
    calc cm m * rho m ^ k < (b : ℝ) * rho m ^ k := mul_lt_mul_of_pos_right hc.2 (pow_pos hρ k)
      _ ≤ (b : ℝ) * (hi : ℝ) ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hr.2.le k) hbR.le
  have l1 := div_lt_div_of_lt_left' huR (mul_pos haR (pow_pos hloR k)) hd1
  have l2 := div_lt_div_of_lt_left' huR (mul_pos (lt_trans haR hc.1) (pow_pos hρ k)) hd2
  have h1R : (t : ℝ) - ε ≤ (u : ℝ) / ((b : ℝ) * (hi : ℝ) ^ k) - 1 := by exact_mod_cast h1
  have h2R : (u : ℝ) / ((a : ℝ) * (lo : ℝ) ^ k) - 1 ≤ (t : ℝ) + ε := by exact_mod_cast h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- 辅助引理（注记 3.3）：`seg` 的第 `k` 项。 -/
theorem seg_getD (f : ℕ → ℕ) : ∀ (j n k : ℕ), k < n → (seg f j n).getD k 0 = f (j + k)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | j, n + 1, 0, _ => by simp [seg]
  | j, n + 1, k + 1, h => by
    rw [seg, List.getD_cons_succ, seg_getD f (j + 1) n k (by omega)]
    congr 1
    omega

/-- 辅助引理（注记 3.3）：`U_k(m)` 是 `Ucol K m` 的第 `k` 项（`k ≤ K`）。 -/
theorem U_eq_Ucol_getD (K m k : ℕ) (hk : k ≤ K) : U k m = (Ucol K m).getD k 0 := by
  rw [Ucol_eq, seg_getD _ 0 (K + 1) k (by omega), zero_add]

/-! ## 数值：ρ_m、c_m、κ_m 的有理区间（1 ≤ m ≤ 24；由 `code/main_extra/remark33_numerics_lean.py` 生成） -/

/-- 辅助引理（注记 3.3）：`ρ_1` 的有理区间。 -/
theorem rho_bnd_1 : ((366392807969 / 250000000000 : ℚ) : ℝ) < rho 1 ∧ rho 1 < ((1465571231877 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_2` 的有理区间。 -/
theorem rho_bnd_2 : ((1695620769559 / 1000000000000 : ℚ) : ℝ) < rho 2 ∧ rho 2 < ((42390519239 / 25000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_3` 的有理区间。 -/
theorem rho_bnd_3 : ((1863706527819 / 1000000000000 : ℚ) : ℝ) < rho 3 ∧ rho 3 < ((93185326391 / 50000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_4` 的有理区间。 -/
theorem rho_bnd_4 : ((1999999999999 / 1000000000000 : ℚ) : ℝ) < rho 4 ∧ rho 4 < ((2000000000001 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_5` 的有理区间。 -/
theorem rho_bnd_5 : ((33067864041 / 15625000000 : ℚ) : ℝ) < rho 5 ∧ rho 5 < ((16930746389 / 8000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_6` 的有理区间。 -/
theorem rho_bnd_6 : ((2218776585301 / 1000000000000 : ℚ) : ℝ) < rho 6 ∧ rho 6 < ((1109388292651 / 500000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_7` 的有理区间。 -/
theorem rho_bnd_7 : ((1155426081729 / 500000000000 : ℚ) : ℝ) < rho 7 ∧ rho 7 < ((2310852163459 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_8` 的有理区间。 -/
theorem rho_bnd_8 : ((1197429336933 / 500000000000 : ℚ) : ℝ) < rho 8 ∧ rho 8 < ((2394858673867 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_9` 的有理区间。 -/
theorem rho_bnd_9 : ((2472367863327 / 1000000000000 : ℚ) : ℝ) < rho 9 ∧ rho 9 < ((77261495729 / 31250000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_10` 的有理区间。 -/
theorem rho_bnd_10 : ((2544511528387 / 1000000000000 : ℚ) : ℝ) < rho 10 ∧ rho 10 < ((636127882097 / 250000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_11` 的有理区间。 -/
theorem rho_bnd_11 : ((1306067534669 / 500000000000 : ℚ) : ℝ) < rho 11 ∧ rho 11 < ((2612135069339 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_12` 的有理区间。 -/
theorem rho_bnd_12 : ((668972167393 / 250000000000 : ℚ) : ℝ) < rho 12 ∧ rho 12 < ((2675888669573 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_13` 的有理区间。 -/
theorem rho_bnd_13 : ((273628443543 / 100000000000 : ℚ) : ℝ) < rho 13 ∧ rho 13 < ((2736284435431 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_14` 的有理区间。 -/
theorem rho_bnd_14 : ((698433449819 / 250000000000 : ℚ) : ℝ) < rho 14 ∧ rho 14 < ((2793733799277 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_15` 的有理区间。 -/
theorem rho_bnd_15 : ((1424286450421 / 500000000000 : ℚ) : ℝ) < rho 15 ∧ rho 15 < ((2848572900843 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_16` 的有理区间。 -/
theorem rho_bnd_16 : ((45329380317 / 15625000000 : ℚ) : ℝ) < rho 16 ∧ rho 16 < ((2901080340289 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_17` 的有理区间。 -/
theorem rho_bnd_17 : ((2951489920611 / 1000000000000 : ℚ) : ℝ) < rho 17 ∧ rho 17 < ((737872480153 / 250000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_18` 的有理区间。 -/
theorem rho_bnd_18 : ((2999999999999 / 1000000000000 : ℚ) : ℝ) < rho 18 ∧ rho 18 < ((3000000000001 / 1000000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_19` 的有理区间。 -/
theorem rho_bnd_19 : ((3046780490963 / 1000000000000 : ℚ) : ℝ) < rho 19 ∧ rho 19 < ((761695122741 / 250000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_20` 的有理区间。 -/
theorem rho_bnd_20 : ((3091978188941 / 1000000000000 : ℚ) : ℝ) < rho 20 ∧ rho 20 < ((1545989094471 / 500000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_21` 的有理区间。 -/
theorem rho_bnd_21 : ((125428835651 / 40000000000 : ℚ) : ℝ) < rho 21 ∧ rho 21 < ((783930222819 / 250000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_22` 的有理区间。 -/
theorem rho_bnd_22 : ((635624124943 / 200000000000 : ℚ) : ℝ) < rho 22 ∧ rho 22 < ((794530156179 / 250000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_23` 的有理区间。 -/
theorem rho_bnd_23 : ((3219276205487 / 1000000000000 : ℚ) : ℝ) < rho 23 ∧ rho 23 < ((201204762843 / 62500000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`ρ_24` 的有理区间。 -/
theorem rho_bnd_24 : ((3259275292519 / 1000000000000 : ℚ) : ℝ) < rho 24 ∧ rho 24 < ((81481882313 / 25000000000 : ℚ) : ℝ) :=
  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩

/-- 辅助引理（注记 3.3）：`c_1` 的有理区间。 -/
theorem cm_bnd_1 : ((22096081317719 / 10000000000000 : ℚ) : ℝ) < cm 1 ∧ cm 1 < ((11048040658907 / 5000000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_1 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_2` 的有理区间。 -/
theorem cm_bnd_2 : ((2450349759169 / 312500000000 : ℚ) : ℝ) < cm 2 ∧ cm 2 < ((7841119229381 / 1000000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_2 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_3` 的有理区间。 -/
theorem cm_bnd_3 : ((3622107164619 / 125000000000 : ℚ) : ℝ) < cm 3 ∧ cm 3 < ((28976857317129 / 1000000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_3 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_4` 的有理区间。 -/
theorem cm_bnd_4 : ((2687499999981 / 25000000000 : ℚ) : ℝ) < cm 4 ∧ cm 4 < ((2687500000019 / 25000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_4 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_5` 的有理区间。 -/
theorem cm_bnd_5 : ((39701237132271 / 100000000000 : ℚ) : ℝ) < cm 5 ∧ cm 5 < ((39701237132587 / 100000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_5 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_6` 的有理区间。 -/
theorem cm_bnd_6 : ((14563168290571 / 10000000000 : ℚ) : ℝ) < cm 6 ∧ cm 6 < ((14563168290701 / 10000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_6 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_7` 的有理区间。 -/
theorem cm_bnd_7 : ((10607260007043 / 2000000000 : ℚ) : ℝ) < cm 7 ∧ cm 7 < ((53036300035731 / 10000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_7 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_8` 的有理区间。 -/
theorem cm_bnd_8 : ((19179307477201 / 1000000000 : ℚ) : ℝ) < cm 8 ∧ cm 8 < ((4794826869351 / 250000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_8 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_9` 的有理区间。 -/
theorem cm_bnd_9 : ((68897316046013 / 1000000000 : ℚ) : ℝ) < cm 9 ∧ cm 9 < ((68897316046797 / 1000000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_9 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_10` 的有理区间。 -/
theorem cm_bnd_10 : ((4919293913399 / 20000000 : ℚ) : ℝ) < cm 10 ∧ cm 10 < ((4919293913459 / 20000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_10 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_11` 的有理区间。 -/
theorem cm_bnd_11 : ((87303935833209 / 100000000 : ℚ) : ℝ) < cm 11 ∧ cm 11 < ((87303935834341 / 100000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_11 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_12` 的有理区间。 -/
theorem cm_bnd_12 : ((30822161893427 / 10000000 : ℚ) : ℝ) < cm 12 ∧ cm 12 < ((30822161893851 / 10000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_12 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_13` 的有理区间。 -/
theorem cm_bnd_13 : ((2165475325781 / 200000 : ℚ) : ℝ) < cm 13 ∧ cm 13 < ((10827376629063 / 1000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_13 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_14` 的有理区间。 -/
theorem cm_bnd_14 : ((37858343199113 / 1000000 : ℚ) : ℝ) < cm 14 ∧ cm 14 < ((37858343199689 / 1000000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_14 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_15` 的有理区间。 -/
theorem cm_bnd_15 : ((3294967274437 / 25000 : ℚ) : ℝ) < cm 15 ∧ cm 15 < ((13179869097959 / 100000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_15 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_16` 的有理区间。 -/
theorem cm_bnd_16 : ((45697404228681 / 100000 : ℚ) : ℝ) < cm 16 ∧ cm 16 < ((22848702114721 / 50000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_16 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_17` 的有理区间。 -/
theorem cm_bnd_17 : ((15783779388857 / 10000 : ℚ) : ℝ) < cm 17 ∧ cm 17 < ((15783779389131 / 10000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_17 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_18` 的有理区间。 -/
theorem cm_bnd_18 : ((13580233408031 / 2500 : ℚ) : ℝ) < cm 18 ∧ cm 18 < ((27160466817041 / 5000 : ℚ) : ℝ) :=
  cm_mem rho_bnd_18 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_19` 的有理区间。 -/
theorem cm_bnd_19 : ((18631540098921 / 1000 : ℚ) : ℝ) < cm 19 ∧ cm 19 < ((1863154009927 / 100 : ℚ) : ℝ) :=
  cm_mem rho_bnd_19 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_20` 的有理区间。 -/
theorem cm_bnd_20 : ((63699505511759 / 1000 : ℚ) : ℝ) < cm 20 ∧ cm 20 < ((7962438189124 / 125 : ℚ) : ℝ) :=
  cm_mem rho_bnd_20 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_21` 的有理区间。 -/
theorem cm_bnd_21 : ((21712132127459 / 100 : ℚ) : ℝ) < cm 21 ∧ cm 21 < ((10856066063947 / 50 : ℚ) : ℝ) :=
  cm_mem rho_bnd_21 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_22` 的有理区间。 -/
theorem cm_bnd_22 : ((36896486561997 / 50 : ℚ) : ℝ) < cm 22 ∧ cm 22 < ((73792973125519 / 100 : ℚ) : ℝ) :=
  cm_mem rho_bnd_22 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_23` 的有理区间。 -/
theorem cm_bnd_23 : ((25011231935881 / 10 : ℚ) : ℝ) < cm 23 ∧ cm 23 < ((12505615968207 / 5 : ℚ) : ℝ) :=
  cm_mem rho_bnd_23 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`c_24` 的有理区间。 -/
theorem cm_bnd_24 : ((84551075575569 / 10 : ℚ) : ℝ) < cm 24 ∧ cm 24 < ((42275537788712 / 5 : ℚ) : ℝ) :=
  cm_mem rho_bnd_24 (by norm_num) (by decide +kernel) (by decide +kernel)

/-- 辅助引理（注记 3.3）：`κ_1` 的有理区间。 -/
theorem kappa_bnd_1 : ((2262844677 / 5000000000 : ℚ) : ℝ) < kappaConst 1 ∧ kappaConst 1 < ((905137871 / 2000000000 : ℚ) : ℝ) :=
  kappa_one_mem cm_bnd_1 (by norm_num) (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_2` 的有理区间。 -/
theorem kappa_bnd_2 : ((2217675533 / 2500000000 : ℚ) : ℝ) < kappaConst 2 ∧ kappaConst 2 < ((4435351067 / 5000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 2) cm_bnd_1 rho_bnd_1 cm_bnd_2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_3` 的有理区间。 -/
theorem kappa_bnd_3 : ((1319207033 / 1000000000 : ℚ) : ℝ) < kappaConst 3 ∧ kappaConst 3 < ((659603517 / 500000000 : ℚ) : ℝ) :=
  kappa_mem (m := 3) cm_bnd_2 rho_bnd_2 cm_bnd_3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_4` 的有理区间。 -/
theorem kappa_bnd_4 : ((109057469 / 62500000 : ℚ) : ℝ) < kappaConst 4 ∧ kappaConst 4 < ((348983901 / 200000000 : ℚ) : ℝ) :=
  kappa_mem (m := 4) cm_bnd_3 rho_bnd_3 cm_bnd_4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_5` 的有理区间。 -/
theorem kappa_bnd_5 : ((541544837 / 250000000 : ℚ) : ℝ) < kappaConst 5 ∧ kappaConst 5 < ((2166179349 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 5) cm_bnd_4 rho_bnd_4 cm_bnd_5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_6` 的有理区间。 -/
theorem kappa_bnd_6 : ((1292041693 / 500000000 : ℚ) : ℝ) < kappaConst 6 ∧ kappaConst 6 < ((2584083387 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 6) cm_bnd_5 rho_bnd_5 cm_bnd_6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_7` 的有理区间。 -/
theorem kappa_bnd_7 : ((749830981 / 250000000 : ℚ) : ℝ) < kappaConst 7 ∧ kappaConst 7 < ((119972957 / 40000000 : ℚ) : ℝ) :=
  kappa_mem (m := 7) cm_bnd_6 rho_bnd_6 cm_bnd_7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_8` 的有理区间。 -/
theorem kappa_bnd_8 : ((1706187629 / 500000000 : ℚ) : ℝ) < kappaConst 8 ∧ kappaConst 8 < ((3412375259 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 8) cm_bnd_7 rho_bnd_7 cm_bnd_8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_9` 的有理区间。 -/
theorem kappa_bnd_9 : ((3823580931 / 1000000000 : ℚ) : ℝ) < kappaConst 9 ∧ kappaConst 9 < ((3823580933 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 9) cm_bnd_8 rho_bnd_8 cm_bnd_9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_10` 的有理区间。 -/
theorem kappa_bnd_10 : ((2116600051 / 500000000 : ℚ) : ℝ) < kappaConst 10 ∧ kappaConst 10 < ((4233200103 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 10) cm_bnd_9 rho_bnd_9 cm_bnd_10 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_11` 的有理区间。 -/
theorem kappa_bnd_11 : ((2320717223 / 500000000 : ℚ) : ℝ) < kappaConst 11 ∧ kappaConst 11 < ((4641434447 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 11) cm_bnd_10 rho_bnd_10 cm_bnd_11 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_12` 的有理区间。 -/
theorem kappa_bnd_12 : ((2524222419 / 500000000 : ℚ) : ℝ) < kappaConst 12 ∧ kappaConst 12 < ((5048444839 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 12) cm_bnd_11 rho_bnd_11 cm_bnd_12 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_13` 的有理区间。 -/
theorem kappa_bnd_13 : ((5454362213 / 1000000000 : ℚ) : ℝ) < kappaConst 13 ∧ kappaConst 13 < ((2727181107 / 500000000 : ℚ) : ℝ) :=
  kappa_mem (m := 13) cm_bnd_12 rho_bnd_12 cm_bnd_13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_14` 的有理区间。 -/
theorem kappa_bnd_14 : ((5859294947 / 1000000000 : ℚ) : ℝ) < kappaConst 14 ∧ kappaConst 14 < ((1464823737 / 250000000 : ℚ) : ℝ) :=
  kappa_mem (m := 14) cm_bnd_13 rho_bnd_13 cm_bnd_14 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_15` 的有理区间。 -/
theorem kappa_bnd_15 : ((3131667011 / 500000000 : ℚ) : ℝ) < kappaConst 15 ∧ kappaConst 15 < ((6263334023 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 15) cm_bnd_14 rho_bnd_14 cm_bnd_15 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_16` 的有理区间。 -/
theorem kappa_bnd_16 : ((1333311351 / 200000000 : ℚ) : ℝ) < kappaConst 16 ∧ kappaConst 16 < ((1666639189 / 250000000 : ℚ) : ℝ) :=
  kappa_mem (m := 16) cm_bnd_15 rho_bnd_15 cm_bnd_16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_17` 的有理区间。 -/
theorem kappa_bnd_17 : ((7069029551 / 1000000000 : ℚ) : ℝ) < kappaConst 17 ∧ kappaConst 17 < ((441814347 / 62500000 : ℚ) : ℝ) :=
  kappa_mem (m := 17) cm_bnd_16 rho_bnd_16 cm_bnd_17 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_18` 的有理区间。 -/
theorem kappa_bnd_18 : ((747080997 / 100000000 : ℚ) : ℝ) < kappaConst 18 ∧ kappaConst 18 < ((7470809971 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 18) cm_bnd_17 rho_bnd_17 cm_bnd_18 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_19` 的有理区间。 -/
theorem kappa_bnd_19 : ((7871948321 / 1000000000 : ℚ) : ℝ) < kappaConst 19 ∧ kappaConst 19 < ((3935974161 / 500000000 : ℚ) : ℝ) :=
  kappa_mem (m := 19) cm_bnd_18 rho_bnd_18 cm_bnd_19 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_20` 的有理区间。 -/
theorem kappa_bnd_20 : ((8272488893 / 1000000000 : ℚ) : ℝ) < kappaConst 20 ∧ kappaConst 20 < ((4136244447 / 500000000 : ℚ) : ℝ) :=
  kappa_mem (m := 20) cm_bnd_19 rho_bnd_19 cm_bnd_20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_21` 的有理区间。 -/
theorem kappa_bnd_21 : ((8672470933 / 1000000000 : ℚ) : ℝ) < kappaConst 21 ∧ kappaConst 21 < ((4336235467 / 500000000 : ℚ) : ℝ) :=
  kappa_mem (m := 21) cm_bnd_20 rho_bnd_20 cm_bnd_21 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_22` 的有理区间。 -/
theorem kappa_bnd_22 : ((362877177 / 40000000 : ℚ) : ℝ) < kappaConst 22 ∧ kappaConst 22 < ((9071929427 / 1000000000 : ℚ) : ℝ) :=
  kappa_mem (m := 22) cm_bnd_21 rho_bnd_21 cm_bnd_22 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_23` 的有理区间。 -/
theorem kappa_bnd_23 : ((2367723931 / 250000000 : ℚ) : ℝ) < kappaConst 23 ∧ kappaConst 23 < ((4735447863 / 500000000 : ℚ) : ℝ) :=
  kappa_mem (m := 23) cm_bnd_22 rho_bnd_22 cm_bnd_23 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`κ_24` 的有理区间。 -/
theorem kappa_bnd_24 : ((9869398063 / 1000000000 : ℚ) : ℝ) < kappaConst 24 ∧ kappaConst 24 < ((616837379 / 62500000 : ℚ) : ℝ) :=
  kappa_mem (m := 24) cm_bnd_23 rho_bnd_23 cm_bnd_24 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 辅助引理（注记 3.3）：`U_{6}(2)` 的精确值（`Ucol` 在内核里算）。 -/
theorem U_6_2 : U 6 2 = 119 := by
  rw [U_eq_Ucol_getD 6 2 6 le_rfl]
  decide +kernel

/-- 辅助引理（注记 3.3）：`U_{72}(24)` 的精确值（`Ucol` 在内核里算）。 -/
theorem U_72_24 : U 72 24 = 276659713493101322870440455877224295394460134720 := by
  rw [U_eq_Ucol_getD 72 24 72 le_rfl]
  decide +kernel

/-- 辅助引理（注记 3.3）：`U_{20}(2)` 的精确值（`Ucol` 在内核里算）。 -/
theorem U_20_2 : U 20 2 = 288119 := by
  rw [U_eq_Ucol_getD 20 2 20 le_rfl]
  decide +kernel

/-- 辅助引理（注记 3.3）：`U_{240}(24)` 的精确值（`Ucol` 在内核里算）。 -/
theorem U_240_24 : U 240 24 = 6974522710714646320442659346624613228970634347409699210981321238802202926773022174321679950327316948402424347401373172047540083249037280 := by
  rw [U_eq_Ucol_getD 240 24 240 le_rfl]
  decide +kernel

/-! ## 论文注记 3.3 的数值说法 -/

/-- **注记 3.3**（数值）：`ρ_1 ≈ 1.46557`。 -/
theorem rho_one_approx : |rho 1 - 1.46557| < 5 / 10 ^ 6 :=
  approx_of_bounds rho_bnd_1.1 rho_bnd_1.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：`c_1 ≈ 2.20961`。 -/
theorem cm_one_approx : |cm 1 - 2.20961| < 5 / 10 ^ 6 :=
  approx_of_bounds cm_bnd_1.1 cm_bnd_1.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：`c_2 ≈ 7.84112`。 -/
theorem cm_two_approx : |cm 2 - 7.84112| < 5 / 10 ^ 6 :=
  approx_of_bounds cm_bnd_2.1 cm_bnd_2.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：`c_3 ≈ 28.97686`。 -/
theorem cm_three_approx : |cm 3 - 28.97686| < 5 / 10 ^ 6 :=
  approx_of_bounds cm_bnd_3.1 cm_bnd_3.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：`κ_1 ≈ 0.453`。 -/
theorem kappa_one_approx : |kappaConst 1 - 0.453| < 5 / 10 ^ 4 :=
  approx_of_bounds kappa_bnd_1.1 kappa_bnd_1.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：`κ_4 ≈ 1.745`。 -/
theorem kappa_four_approx : |kappaConst 4 - 1.745| < 5 / 10 ^ 4 :=
  approx_of_bounds kappa_bnd_4.1 kappa_bnd_4.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：`κ_24 ≈ 9.869`。 -/
theorem kappa_twentyfour_approx : |kappaConst 24 - 9.869| < 5 / 10 ^ 4 :=
  approx_of_bounds kappa_bnd_24.1 kappa_bnd_24.2 (by norm_num) (by norm_num)

/-- **注记 3.3**（数值）：在 `1 ≤ m ≤ 24` 内 `κ_m` 随 `m` 递增。 -/
theorem kappa_increasing : ∀ m, 1 ≤ m → m < 24 → kappaConst m < kappaConst (m + 1) := by
  intro m h1 h2
  interval_cases m
  · exact lt_trans kappa_bnd_1.2 (lt_trans (by norm_num) kappa_bnd_2.1)
  · exact lt_trans kappa_bnd_2.2 (lt_trans (by norm_num) kappa_bnd_3.1)
  · exact lt_trans kappa_bnd_3.2 (lt_trans (by norm_num) kappa_bnd_4.1)
  · exact lt_trans kappa_bnd_4.2 (lt_trans (by norm_num) kappa_bnd_5.1)
  · exact lt_trans kappa_bnd_5.2 (lt_trans (by norm_num) kappa_bnd_6.1)
  · exact lt_trans kappa_bnd_6.2 (lt_trans (by norm_num) kappa_bnd_7.1)
  · exact lt_trans kappa_bnd_7.2 (lt_trans (by norm_num) kappa_bnd_8.1)
  · exact lt_trans kappa_bnd_8.2 (lt_trans (by norm_num) kappa_bnd_9.1)
  · exact lt_trans kappa_bnd_9.2 (lt_trans (by norm_num) kappa_bnd_10.1)
  · exact lt_trans kappa_bnd_10.2 (lt_trans (by norm_num) kappa_bnd_11.1)
  · exact lt_trans kappa_bnd_11.2 (lt_trans (by norm_num) kappa_bnd_12.1)
  · exact lt_trans kappa_bnd_12.2 (lt_trans (by norm_num) kappa_bnd_13.1)
  · exact lt_trans kappa_bnd_13.2 (lt_trans (by norm_num) kappa_bnd_14.1)
  · exact lt_trans kappa_bnd_14.2 (lt_trans (by norm_num) kappa_bnd_15.1)
  · exact lt_trans kappa_bnd_15.2 (lt_trans (by norm_num) kappa_bnd_16.1)
  · exact lt_trans kappa_bnd_16.2 (lt_trans (by norm_num) kappa_bnd_17.1)
  · exact lt_trans kappa_bnd_17.2 (lt_trans (by norm_num) kappa_bnd_18.1)
  · exact lt_trans kappa_bnd_18.2 (lt_trans (by norm_num) kappa_bnd_19.1)
  · exact lt_trans kappa_bnd_19.2 (lt_trans (by norm_num) kappa_bnd_20.1)
  · exact lt_trans kappa_bnd_20.2 (lt_trans (by norm_num) kappa_bnd_21.1)
  · exact lt_trans kappa_bnd_21.2 (lt_trans (by norm_num) kappa_bnd_22.1)
  · exact lt_trans kappa_bnd_22.2 (lt_trans (by norm_num) kappa_bnd_23.1)
  · exact lt_trans kappa_bnd_23.2 (lt_trans (by norm_num) kappa_bnd_24.1)

/-- **注记 3.3**（数值）：`U_{6}(2)/(c_2 ρ_2^{6}) − 1 ≈ -0.36`（`k = 3m`）。 -/
theorem relerr_two_six : |(U 6 2 : ℝ) / (cm 2 * rho 2 ^ 6) - 1 - (-0.36)| < 5 / 10 ^ 3 := by
  have h := relerr_of_bounds (u := U 6 2) (k := 6) (t := -9 / 25) (ε := 5 / 1000) cm_bnd_2 rho_bnd_2
    (by norm_num) (by norm_num) (by rw [U_6_2]; norm_num) (by rw [U_6_2]; decide +kernel)
    (by rw [U_6_2]; decide +kernel)
  have e1 : ((-9 / 25 : ℚ) : ℝ) = -0.36 := by norm_num
  have e2 : ((5 / 1000 : ℚ) : ℝ) = 5 / 10 ^ 3 := by norm_num
  rwa [e1, e2] at h

/-- **注记 3.3**（数值）：`U_{72}(24)/(c_24 ρ_24^{72}) − 1 ≈ -0.996`（`k = 3m`）。 -/
theorem relerr_twentyfour_seventytwo : |(U 72 24 : ℝ) / (cm 24 * rho 24 ^ 72) - 1 - (-0.996)| < 5 / 10 ^ 4 := by
  have h := relerr_of_bounds (u := U 72 24) (k := 72) (t := -249 / 250) (ε := 5 / 10000) cm_bnd_24 rho_bnd_24
    (by norm_num) (by norm_num) (by rw [U_72_24]; norm_num) (by rw [U_72_24]; decide +kernel)
    (by rw [U_72_24]; decide +kernel)
  have e1 : ((-249 / 250 : ℚ) : ℝ) = -0.996 := by norm_num
  have e2 : ((5 / 10000 : ℚ) : ℝ) = 5 / 10 ^ 4 := by norm_num
  rwa [e1, e2] at h

/-- **注记 3.3**（数值）：`U_{20}(2)/(c_2 ρ_2^{20}) − 1 ≈ -0.05`（`k = 10m`）。 -/
theorem relerr_two_twenty : |(U 20 2 : ℝ) / (cm 2 * rho 2 ^ 20) - 1 - (-0.05)| < 5 / 10 ^ 3 := by
  have h := relerr_of_bounds (u := U 20 2) (k := 20) (t := -1 / 20) (ε := 5 / 1000) cm_bnd_2 rho_bnd_2
    (by norm_num) (by norm_num) (by rw [U_20_2]; norm_num) (by rw [U_20_2]; decide +kernel)
    (by rw [U_20_2]; decide +kernel)
  have e1 : ((-1 / 20 : ℚ) : ℝ) = -0.05 := by norm_num
  have e2 : ((5 / 1000 : ℚ) : ℝ) = 5 / 10 ^ 3 := by norm_num
  rwa [e1, e2] at h

/-- **注记 3.3**（数值）：`U_{240}(24)/(c_24 ρ_24^{240}) − 1 ≈ -0.41`（`k = 10m`）。 -/
theorem relerr_twentyfour_twoforty : |(U 240 24 : ℝ) / (cm 24 * rho 24 ^ 240) - 1 - (-0.41)| < 5 / 10 ^ 3 := by
  have h := relerr_of_bounds (u := U 240 24) (k := 240) (t := -41 / 100) (ε := 5 / 1000) cm_bnd_24 rho_bnd_24
    (by norm_num) (by norm_num) (by rw [U_240_24]; norm_num) (by rw [U_240_24]; decide +kernel)
    (by rw [U_240_24]; decide +kernel)
  have e1 : ((-41 / 100 : ℚ) : ℝ) = -0.41 := by norm_num
  have e2 : ((5 / 1000 : ℚ) : ℝ) = 5 / 10 ^ 3 := by norm_num
  rwa [e1, e2] at h

end A207123
