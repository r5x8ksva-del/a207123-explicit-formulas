import A207123.OreRel

/-!
# 论文推论 5.5：有理系数的零化算子（把分母乘掉的形式）

论文推论 5.5 是在有理函数系数的 Ore 代数 `𝒪(k,m) = ℂ(k,m)⟨X, E⁻¹⟩` 里陈述的；`𝒪(k,m)` 不作用在数组上。
本文件把分母乘掉，只用多项式系数的算子（`OU`）陈述。两条与论文的对应：

* **(1)** `mul_mem_ideal_of_vanish`：设 `R ∈ OU`、`Δ ∈ ℂ[k,m]`，`R·U` 在某个象限中 `Δ ≠ 0` 的点上为 0，则
  `Δ·R = Q·L1`（`Q ∈ OU`）。论文的 `T = Σ t_{ab} X^a E^{−b}` 取公分母 `Δ`（各系数分母之积），`R := Δ·T` 的系数是
  多项式；「`T` 在象限中系数都有定义的点上零化 `U`」推出这里的假设，结论 `Δ·R = Δ²·T ∈ O·L1` 推出
  `T ∈ 𝒪(k,m)·L1`。证明同论文：`Δ·R` 在整个象限上零化 `U`（`Δ = 0` 的点上因子 `Δ` 为 0），再用 `RelU_eq`。
* **(2)** `mem_ideal_of_mul_mem_ideal`：设 `R ∈ OU`、`Δ ≠ 0`，`Δ·R = Q·L1`（`Q ∈ OU`），则 `R ∈ O·L1`。
  `𝒪(k,m)·L1` 的元素都能写成 `Δ⁻¹·Q·L1`（系数写在左边，取公分母），所以这就是 `𝒪(k,m)·L1 ∩ O = O·L1`。
  证明不用正规形：把 `R` 化约成 `R₀ + Q'·L1`（`R₀` 只含 `X`，`red_of_mem`），则 `Δ·R₀ = (Q − Δ·Q')·L1`
  在某个象限上零化 `U`；由命题 A（`pure_ann_zero`，论文引理 5.3），`Δ·R₀` 的系数全为 0，而 `ℂ[k,m]` 是整环，
  故 `R₀ = 0`。
-/

namespace A207123

/-- 辅助引理（推论 5.5）：`Δ·Σ_a r_a X^a = Σ_a (Δ·r_a) X^a`。 -/
theorem mulOp_mul_pureOp (Δ : Coef) (r : ℕ →₀ Coef) :
    mulOp Δ * pureOp r = pureOp (r.mapRange (fun p => Δ * p) (mul_zero Δ)) := by
  simp only [pureOp]
  rw [Finsupp.sum_mapRange_index (fun _ => by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun a _ => by simp only [map_mul, mul_assoc]

/-- **推论 5.5(1)**（论文，分母乘掉的形式）：`R ∈ OU` 在某个象限中 `Δ ≠ 0` 的点上零化 `U`，则 `Δ·R ∈ O·L1`。 -/
theorem mul_mem_ideal_of_vanish {R : Module.End ℂ Arr} (hR : R ∈ OU) (Δ : Coef) {k0 m0 : ℕ}
    (h : ∀ k m, k0 ≤ k → m0 ≤ m → Δ.evalEval (k : ℂ) (m : ℂ) ≠ 0 → R Uarr k m = 0) :
    ∃ Q ∈ OU, mulOp Δ * R = Q * L1 := by
  have hmem : mulOp Δ * R ∈ RelU := by
    refine ⟨mul_mem (mulOp_mem_OU Δ) hR, k0, m0, fun k m hk hm => ?_⟩
    rw [Module.End.mul_apply, mulOp_apply]
    by_cases hΔ : Δ.evalEval (k : ℂ) (m : ℂ) = 0
    · rw [hΔ, zero_mul]
    · rw [h k m hk hm hΔ, mul_zero]
  rw [RelU_eq] at hmem
  exact hmem

/-- **推论 5.5(2)**（论文，分母乘掉的形式）：`Δ ≠ 0` 且 `Δ·R ∈ O·L1`，则 `R ∈ O·L1`
（即 `𝒪(k,m)·L1 ∩ O = O·L1`）。 -/
theorem mem_ideal_of_mul_mem_ideal {R Q : Module.End ℂ Arr} (hR : R ∈ OU) (hQ : Q ∈ OU) {Δ : Coef}
    (hΔ : Δ ≠ 0) (h : mulOp Δ * R = Q * L1) : ∃ Q' ∈ OU, R = Q' * L1 := by
  obtain ⟨r, Q', hQ', rfl⟩ := red_of_mem hR
  -- `Δ·R₀ = (Q − Δ·Q')·L1` 在某个象限上零化 `U`
  have hrel : mulOp Δ * pureOp r ∈ RelU := by
    rw [RelU_eq]
    show ∃ Q'' ∈ OU, mulOp Δ * pureOp r = Q'' * L1
    refine ⟨Q - mulOp Δ * Q', sub_mem hQ (mul_mem (mulOp_mem_OU Δ) hQ'), ?_⟩
    rw [sub_mul, ← h, mul_add, mul_assoc]
    abel
  obtain ⟨-, k0, m0, hv⟩ := hrel
  rw [mulOp_mul_pureOp] at hv
  have h0 := pure_ann_zero _ k0 m0 hv
  -- 命题 A：`Δ·r_a = 0`，而 `Δ ≠ 0`
  have hr : r = 0 := by
    refine Finsupp.ext fun a => ?_
    have ha : Δ * r a = 0 := by
      have := DFunLike.congr_fun h0 a
      simpa using this
    simpa using (mul_eq_zero.mp ha).resolve_left hΔ
  exact ⟨Q', hQ', by rw [hr, pureOp_zero, zero_add]⟩

end A207123
