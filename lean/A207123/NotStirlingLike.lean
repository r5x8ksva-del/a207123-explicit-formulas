import A207123.OreDim

/-!
# `U` 不是 Kauers 意义下的 Stirling-like（报告 T3.8 的推论）

Kauers（*Summation algorithms for Stirling number identities*，J. Symbolic Comput. 42 (2007)，定义 3）
称一个二元序列为 Stirling-like，如果它的零化理想由一条三项算子 `u + v·N^{v₁}K^{v₂} − w·N^{w₁}K^{w₂}`
生成，且位移向量 `(v₁, v₂)`、`(w₁, w₂)` 构成 `ℤ²` 的基（行列式为 `±1`）。换句话说，三项的指数点构成
一个二倍面积为 1 的格点三角形。Stirling 数满足的三角递推都是这种形状；`U` 的递推 `L1 = 1 − E⁻¹ − X − m·X³`
有四项，三条位移 `(0,1)`、`(1,0)`、`(3,0)`（以 `(X 的次数, E⁻¹ 的次数)` 计）。

**主定理**（`relU_support_det`）：`Rel(U)` 中每个非零算子 `R`，其正规形 `Σ r_{ab}(k,m)·X^a·E^{−b}`
的支撑里有三个点 `p₀, p₁, p₂`，二倍有向面积 `det(p₁ − p₀, p₂ − p₀) ≥ 3`。

**推论**：
* `relU_card_support`：`Rel(U)` 中的非零算子在正规形里至少有三项（没有一项、两项的象限递推）。
* `not_mem_relU_of_support_subset`：若 `r ≠ 0` 的支撑含于三个点 `{p₀, p₁, p₂}`，且
  `|det(p₁ − p₀, p₂ − p₀)| ≤ 2`（Kauers 定义要求的幺模三角形是 `= 1`），则 `normOp r ∉ Rel(U)`。

**证明**：由 `RelU_eq`，`R = Q·L1`，`Q` 的正规形 `q ≠ 0`，`R` 的正规形是 `TU q`（`normOp_mul_L1`），而
`TU q (a, b) = q(a,b) − q(a,b−1) − q(a−1,b) − (m − b)·q(a−3,b)`（越界项为 0，`TU_apply`）。
取 `q` 的支撑中第二个下标的最小值 `b₀`，这一行第一个下标的最小值 `a⁻`、最大值 `a⁺`，以及第二个下标的
最大值 `B`（所在点 `(a_B, B)`）。则
* `TU q (a⁻, b₀) = q(a⁻, b₀) ≠ 0`；
* `TU q (a⁺ + 3, b₀) = −(m − b₀)·q(a⁺, b₀) ≠ 0`（系数环 `ℂ[k, m]` 是整环）；
* `TU q (a_B, B + 1) = −q(a_B, B) ≠ 0`；
三点的二倍面积是 `(a⁺ + 3 − a⁻)·(B + 1 − b₀) ≥ 3·1`。这是「`L1` 的牛顿三角形 `(0,0)`、`(3,0)`、`(0,1)`
面积为 3/2，乘积的牛顿多边形含它的平移」的组合版本。

**与 Kauers 定义的对应**（书面论证，不在 Lean 中）：若 `U` 是 Stirling-like，生成元 `T` 零化 `U`。
把自变量整体平移，使三项都只向下看，再左乘系数的公分母 `D(k, m)` 两次，就得到 `O_U` 中一个多项式系数算子：
它在一个象限上零化 `U`（在 `D ≠ 0` 的点由原式得到，在 `D = 0` 的点两边都乘了 0），支撑是原来三个指数点
经点反射与平移后的像，二倍面积仍为 `±1`；左乘非零多项式不改变正规形的支撑。这与 `not_mem_relU_of_support_subset`
矛盾。所以 `U` 不是 Kauers 意义下的 Stirling-like，Kauers 关于 Stirling-like 序列的现成结论不能直接用于 `U`。
-/

open Polynomial Finset

namespace A207123

/-- 三个格点 `p, q, r` 的二倍有向面积 `det(q − p, r − p)`。 -/
def det2 (p q r : ℕ × ℕ) : ℤ :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) - ((q.2 : ℤ) - p.2) * ((r.1 : ℤ) - p.1)

/-- 辅助引理：三个点都取自 `{p₀, p₁, p₂}` 时，二倍有向面积是 `0` 或 `±det2 p₀ p₁ p₂`。 -/
theorem det2_of_mem_triple {p0 p1 p2 x y z : ℕ × ℕ}
    (hx : x = p0 ∨ x = p1 ∨ x = p2) (hy : y = p0 ∨ y = p1 ∨ y = p2)
    (hz : z = p0 ∨ z = p1 ∨ z = p2) :
    det2 x y z = 0 ∨ det2 x y z = det2 p0 p1 p2 ∨ det2 x y z = -det2 p0 p1 p2 := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    first
      | exact Or.inr (Or.inl rfl)
      | (left; simp only [det2]; ring1)
      | (right; left; simp only [det2]; ring1)
      | (right; right; simp only [det2]; ring1)

/-- 辅助引理：`m − n ≠ 0`（`n` 为自然数）。 -/
theorem cM_sub_natCast_ne_zero (n : ℕ) : cM - (n : Coef) ≠ 0 := by
  rw [cM, ← Polynomial.C_eq_natCast]
  exact Polynomial.X_sub_C_ne_zero _

/-- 核心引理：`q ≠ 0` 时，`TU q`（即 `normOp q · L1` 的正规形）的支撑里有三个点，二倍面积至少为 3。 -/
theorem TU_three_points (q : ℕ × ℕ →₀ Coef) (hq : q ≠ 0) :
    ∃ p0 p1 p2 : ℕ × ℕ, TU q p0 ≠ 0 ∧ TU q p1 ≠ 0 ∧ TU q p2 ≠ 0 ∧ 3 ≤ det2 p0 p1 p2 := by
  classical
  have hS : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hq
  have mem : ∀ p : ℕ × ℕ, q p ≠ 0 → p ∈ q.support := fun p h => Finsupp.mem_support_iff.mpr h
  -- 第二个下标最小的点 `(a0, b0)` 与最大的点 `(a3, b3)`
  obtain ⟨⟨a0, b0⟩, hx, hxmin⟩ := q.support.exists_min_image Prod.snd hS
  obtain ⟨⟨a3, b3⟩, hw, hwmax⟩ := q.support.exists_max_image Prod.snd hS
  -- 第 `b0` 行第一个下标的最小值 `a1` 与最大值 `a2`
  have hRow : (q.support.filter fun p : ℕ × ℕ => p.2 = b0).Nonempty :=
    ⟨(a0, b0), mem_filter.mpr ⟨hx, rfl⟩⟩
  obtain ⟨⟨a1, b1⟩, hy, hymin⟩ :=
    (q.support.filter fun p : ℕ × ℕ => p.2 = b0).exists_min_image Prod.fst hRow
  obtain ⟨⟨a2, b2⟩, hz, hzmax⟩ :=
    (q.support.filter fun p : ℕ × ℕ => p.2 = b0).exists_max_image Prod.fst hRow
  simp only [mem_filter] at hy hz
  obtain ⟨hy, hb1⟩ := hy
  obtain ⟨hz, hb2⟩ := hz
  subst b1
  subst b2
  -- 支撑之外的点
  have below : ∀ a b, b < b0 → q (a, b) = 0 := by
    intro a b hb
    by_contra h
    have := hxmin _ (mem _ h)
    dsimp only at this
    omega
  have above : ∀ a b, b3 < b → q (a, b) = 0 := by
    intro a b hb
    by_contra h
    have := hwmax _ (mem _ h)
    dsimp only at this
    omega
  have rowlt : ∀ a, a < a1 → q (a, b0) = 0 := by
    intro a ha
    by_contra h
    have := hymin (a, b0) (mem_filter.mpr ⟨mem _ h, rfl⟩)
    dsimp only at this
    omega
  have rowgt : ∀ a, a2 < a → q (a, b0) = 0 := by
    intro a ha
    by_contra h
    have := hzmax (a, b0) (mem_filter.mpr ⟨mem _ h, rfl⟩)
    dsimp only at this
    omega
  have h12 : a1 ≤ a2 := by
    have := hzmax (a1, b0) (mem_filter.mpr ⟨hy, rfl⟩)
    dsimp only at this
    omega
  have h03 : b0 ≤ b3 := by
    have := hwmax (a0, b0) hx
    dsimp only at this
    omega
  have ny : q (a1, b0) ≠ 0 := Finsupp.mem_support_iff.mp hy
  have nz : q (a2, b0) ≠ 0 := Finsupp.mem_support_iff.mp hz
  have nw : q (a3, b3) ≠ 0 := Finsupp.mem_support_iff.mp hw
  refine ⟨(a1, b0), (a2 + 3, b0), (a3, b3 + 1), ?_, ?_, ?_, ?_⟩
  · -- `TU q (a⁻, b₀) = q(a⁻, b₀)`
    have e1 : (if 1 ≤ b0 then q (a1, b0 - 1) else 0) = 0 := by
      split_ifs with h
      · exact below _ _ (by omega)
      · rfl
    have e2 : (if 1 ≤ a1 then q (a1 - 1, b0) else 0) = 0 := by
      split_ifs with h
      · exact rowlt _ (by omega)
      · rfl
    have e3 : ∀ c : Coef, (if 3 ≤ a1 then c * q (a1 - 3, b0) else 0) = 0 := by
      intro c
      split_ifs with h
      · rw [rowlt (a1 - 3) (by omega), mul_zero]
      · rfl
    rw [TU_apply, e1, e2, e3]
    simpa using ny
  · -- `TU q (a⁺ + 3, b₀) = −(m − b₀)·q(a⁺, b₀)`
    have e0 : q (a2 + 3, b0) = 0 := rowgt _ (by omega)
    have e1 : (if 1 ≤ b0 then q (a2 + 3, b0 - 1) else 0) = 0 := by
      split_ifs with h
      · exact below _ _ (by omega)
      · rfl
    have e2 : q (a2 + 3 - 1, b0) = 0 := rowgt _ (by omega)
    rw [TU_apply, e0, e1, ite_eq_left (show 1 ≤ a2 + 3 by omega), e2,
      ite_eq_left (show 3 ≤ a2 + 3 by omega), Nat.add_sub_cancel]
    simp only [sub_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero (cM_sub_natCast_ne_zero _) nz
  · -- `TU q (a_B, B + 1) = −q(a_B, B)`
    have e0 : q (a3, b3 + 1) = 0 := above _ _ (by omega)
    have e2 : (if 1 ≤ a3 then q (a3 - 1, b3 + 1) else 0) = 0 := by
      split_ifs with h
      · exact above _ _ (by omega)
      · rfl
    have e3 : ∀ c : Coef, (if 3 ≤ a3 then c * q (a3 - 3, b3 + 1) else 0) = 0 := by
      intro c
      split_ifs with h
      · rw [above (a3 - 3) (b3 + 1) (by omega), mul_zero]
      · rfl
    rw [TU_apply, e0, e2, e3, ite_eq_left (show 1 ≤ b3 + 1 by omega), Nat.add_sub_cancel]
    simpa using nw
  · -- 二倍面积 `(a⁺ + 3 − a⁻)·(B + 1 − b₀) ≥ 3`
    simp only [det2]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (a2 : ℤ) - a1 by omega)
      (show (0 : ℤ) ≤ (b3 : ℤ) - b0 by omega)]

/-- **T3.8 的推论（主定理）**：`Rel(U)` 中每个非零算子 `R`，其正规形 `r`（`R = normOp r`）的支撑里有
三个点 `p₀, p₁, p₂`，二倍有向面积 `det(p₁ − p₀, p₂ − p₀) ≥ 3`。 -/
theorem relU_support_det {R : Module.End ℂ Arr} (hR : R ∈ RelU) (hR0 : R ≠ 0)
    {r : ℕ × ℕ →₀ Coef} (hr : R = normOp r) :
    ∃ p0 ∈ r.support, ∃ p1 ∈ r.support, ∃ p2 ∈ r.support, 3 ≤ det2 p0 p1 p2 := by
  rw [RelU_eq] at hR
  obtain ⟨Q, hQ, rfl⟩ := hR
  obtain ⟨q, rfl⟩ := exists_normal_form hQ
  have hq : q ≠ 0 := by
    rintro rfl
    exact hR0 (by rw [normOp_zero, zero_mul])
  rw [normOp_mul_L1] at hr
  have hqr : TU q = r :=
    sub_eq_zero.mp (normal_form_unique _ (by rw [normOp_sub, hr, sub_self]))
  subst hqr
  obtain ⟨p0, p1, p2, h0, h1, h2, hdet⟩ := TU_three_points q hq
  exact ⟨p0, Finsupp.mem_support_iff.mpr h0, p1, Finsupp.mem_support_iff.mpr h1,
    p2, Finsupp.mem_support_iff.mpr h2, hdet⟩

/-- **T3.8 的推论**：`Rel(U)` 中的非零算子在正规形里至少有三项；特别地，`U` 没有一项或两项的
象限递推。 -/
theorem relU_card_support {R : Module.End ℂ Arr} (hR : R ∈ RelU) (hR0 : R ≠ 0)
    {r : ℕ × ℕ →₀ Coef} (hr : R = normOp r) : 3 ≤ r.support.card := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, h3⟩ := relU_support_det hR hR0 hr
  have hxy : x ≠ y := fun e => by
    rw [e] at h3
    have : det2 y y z = 0 := by simp only [det2]; ring
    linarith
  have hxz : x ≠ z := fun e => by
    rw [e] at h3
    have : det2 z y z = 0 := by simp only [det2]; ring
    linarith
  have hyz : y ≠ z := fun e => by
    rw [e] at h3
    have : det2 x z z = 0 := by simp only [det2]; ring
    linarith
  calc 3 = ({x, y, z} : Finset (ℕ × ℕ)).card :=
        (Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩).symm
    _ ≤ r.support.card := Finset.card_le_card (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> assumption)

/-- **`U` 不是 Stirling-like（T3.8 的推论）**：若正规形 `r ≠ 0` 的支撑含于三个点 `{p₀, p₁, p₂}`，且
`|det(p₁ − p₀, p₂ − p₀)| ≤ 2`（Kauers 2007 定义 3 要求的幺模三角形是 `= 1`），则 `normOp r` 不在任何
象限上零化 `U`。 -/
theorem not_mem_relU_of_support_subset {r : ℕ × ℕ →₀ Coef} (hr : r ≠ 0) {p0 p1 p2 : ℕ × ℕ}
    (hs : r.support ⊆ {p0, p1, p2}) (hdet : |det2 p0 p1 p2| ≤ 2) : normOp r ∉ RelU := by
  intro hR
  have hR0 : normOp r ≠ 0 := fun h => hr (normal_form_unique r h)
  obtain ⟨x, hx, y, hy, z, hz, h3⟩ := relU_support_det hR hR0 rfl
  have mem3 : ∀ p ∈ r.support, p = p0 ∨ p = p1 ∨ p = p2 := fun p hp => by
    simpa using hs hp
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdet
  rcases det2_of_mem_triple (mem3 x hx) (mem3 y hy) (mem3 z hz) with h | h | h <;>
    rw [h] at h3 <;> linarith

end A207123
