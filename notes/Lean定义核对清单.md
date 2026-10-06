# Lean 定义核对清单（给人读）

整理：2026-10-07（主 Agent）。用途：Lean 只检查「证明对不对」，不检查「定义是不是报告和论文说的意思」。如果某个定义写偏了，定理照样能编译通过，但证明的是另一件事。这一页把几个**承重的定义**原文抄出来，旁边写它在数学上应当是什么意思，并列出需要人确认的地方。

- **怎么用**：逐节读「Lean 原文」与「数学含义」，在「要核对的点」里打勾。全部读完约 30–45 分钟。发现对不上的，记下小节号告诉我。
- **范围**：只覆盖论文要引用的几条机器检查结论所依赖的定义：U 的定义、原题矩阵与归约（T1.0）、D-finite（T3.7(1)）、没有 k-only 递推（T3.7(2)）、象限递推的左理想（T3.8），以及新加的「不是 Stirling-like」（T3.8 的推论）。其余模块（第四轮的 15 个）的陈述已由 AI 逐条对照报告核对过，没有人核对过。
- **怎么看全文**：`py -3.14 code/main_extra/lean_statements.py Basic Reduction Multichain DFinite NonDFinite OreRel NotStirlingLike` 会抽出这些文件的全部定义与定理陈述（不含证明）。下面引的原文大多与源文件逐字相同；为了短，省略了辅助引理，少数较长的定义体用 `…` 或行尾注释代替（`mulOp`、`opX`、`opEinv`、`polyToPS2`、`AllowedRow`），以源文件为准。

## 1. U_k(m) 的定义（`lean/A207123/Basic.lean`）

**Lean 原文**

```lean
/-- 好三元组：`b = c`，或 `a ≥ max(b, c)`。 -/
def Good (a b c : ℕ) : Prop := b = c ∨ (b ≤ a ∧ c ≤ a)

/-- 高度序列合法：每个相邻三元组都是好三元组。 -/
def Legal : List ℕ → Prop
  | a :: b :: c :: t => Good a b c ∧ Legal (b :: c :: t)
  | _ => True

/-- 所有长度为 `k`、各项取值在 `{0,…,m}` 中的列表。 -/
def seqs (m : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k + 1 => (Finset.range (m + 1)).biUnion fun a => (seqs m k).image (List.cons a)

def L (k m : ℕ) : Finset (List ℕ) := (seqs m k).filter Legal

/-- `U k m = |L k m|`（任务说明中的 `U_k(m)`）。 -/
def U (k m : ℕ) : ℕ := (L k m).card
```

**数学含义**：U_k(m) = #{(h_1,…,h_k) ∈ {0,…,m}^k ：对每个 1≤j≤k−2，(a,b,c)=(h_j,h_{j+1},h_{j+2}) 满足 b=c 或 a≥max(b,c)}。

**要核对的点**
- [ ] `Good a b c` 是「b=c 或 a≥max(b,c)」：`b ≤ a ∧ c ≤ a` 就是 a≥max(b,c)。
- [ ] 三元组的方向：列表头是 h_1，所以 `a` 是三个里**最早**的那个（h_j），不是最晚的。
- [ ] `seqs m k` 恰是长 k、每项 ≤ m 的列表（已证：`mem_seqs`；`mem_L` 把 `L k m` 写成「长度为 k ∧ 每项 ≤ m ∧ Legal」）。
- [ ] 边界：k=0,1,2 时 `Legal` 恒真，所以 U_0(m)=1、U_1(m)=m+1、U_2(m)=(m+1)²；m=0 时只有全零序列，U_k(0)=1。这与论文的约定一致吗？

**旁证**：`lean/Checks.lean` 用这个定义算出了任务说明第 2 节的数据（例如 U_10(6)=323647，k=7、k=10 两行，R_k=U_k(1) 的前 10 项），都对上了。这些计算用 `native_decide`，不属于证明，只说明定义没有写偏。

## 2. 原题的矩阵与归约 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋)（`Reduction.lean`、`Multichain.lean`）

**Lean 原文**

```lean
/-- 原题中的 n×k 0/1 矩阵：`M i j` 是第 `i` 行第 `j` 列（从 0 开始编号），`true` 表示 1。 -/
abbrev Mat (n k : ℕ) := Fin n → Fin k → Bool

/-- 行规则：每一行从左到右读，任意连续三个位置都不是 001，也不是 010。 -/
def RowRule {n k : ℕ} (M : Mat n k) : Prop :=
  ∀ (i : Fin n) (j : ℕ) (h : j + 2 < k),
    ¬ (M i ⟨j, by omega⟩ = false ∧ M i ⟨j + 1, by omega⟩ = false ∧ M i ⟨j + 2, h⟩ = true) ∧
    ¬ (M i ⟨j, by omega⟩ = false ∧ M i ⟨j + 1, by omega⟩ = true ∧ M i ⟨j + 2, h⟩ = false)

/-- 列规则：每一列从上到下读，任意连续三个位置都不是 001，也不是 011。 -/
def ColRule {n k : ℕ} (M : Mat n k) : Prop :=
  ∀ (j : Fin k) (i : ℕ) (h : i + 2 < n),
    ¬ (M ⟨i, by omega⟩ j = false ∧ M ⟨i + 1, by omega⟩ j = false ∧ M ⟨i + 2, h⟩ j = true) ∧
    ¬ (M ⟨i, by omega⟩ j = false ∧ M ⟨i + 1, by omega⟩ j = true ∧ M ⟨i + 2, h⟩ j = true)

/-- `a k n`：满足行规则与列规则的 n×k 0/1 矩阵个数（OEIS A207123 的二维表）。 -/
noncomputable def a (k n : ℕ) : ℕ := Fintype.card {M : Mat n k // RowRule M ∧ ColRule M}

theorem a_eq (k n : ℕ) : a k n = U k ((n + 1) / 2) * U k (n / 2)

/-- 允许行：长 `k` 的 0/1 串，任意连续三位既不是 001 也不是 010。 -/
def AllowedRow {k : ℕ} (r : Fin k → Bool) : Prop := …（与 RowRule 的一行相同）
abbrev Lam (k : ℕ) := {r : Fin k → Bool // AllowedRow r}

theorem U_eq_multichains (k m : ℕ) : Fintype.card {c : Fin m → Lam k // Monotone c} = U k m
```

**数学含义**：A207123 的条目名称说的是 T(n,k)：n×k 的 0/1 数组，横向避开 001 与 010，纵向避开 001 与 011（原文见 `data/oeis/` 下的快照）。`a k n` 数的是 n 行 k 列的 0/1 矩阵：每行（横向）不含连续的 001、010，每列（纵向）不含连续的 001、011。`(n+1)/2`、`n/2` 是自然数除法，分别等于 ⌈n/2⌉、⌊n/2⌋。

**要核对的点**
- [ ] n 是行数、k 是列数（`Mat n k`），与论文里 a_k(n) 的下标约定一致。
- [ ] 「横向」＝在同一行里沿列号递增读，「纵向」＝在同一列里沿行号递增读；横向排除 001、010，纵向排除 001、011（`true` 表示 1）。
- [ ] 读的方向不影响计数：把每行左右翻转是「横向不含 001、010」与「横向不含 100、010」两类矩阵之间的双射，纵向同理。所以即使 OEIS 的读法与这里相反，`a k n` 的值也不变；不必为方向担心。
- [ ] `U_eq_multichains`（T1.0(c)）：`Monotone c` 是 `Fin m` 到允许行集合的单调映射，序是逐分量序（`false < true`），即 m 元多重链 x_1≤⋯≤x_m。这是 Stanley 约定下的 zeta 多项式值 Z(Λ_k, m+1)。

**旁证**：`Checks.lean` 的 `a3_values` 经 `a_eq` 算出 a_3(1..6)=6, 36, 102, 289, 612, 1296，与 OEIS A207118（3 列的那一列，快照 `data/oeis/A207118.txt`）的前 6 项一致。因为 `a_eq` 是关于 Lean 里的 `a` 的定理，这说明矩阵的定义至少在这些值上与 OEIS 相符。

## 3. D-finite（T3.7(1)，`DFinite.lean`）

**Lean 原文**

```lean
abbrev PS2 := PowerSeries (PowerSeries K)          -- K[[x]][[t]]，t 是外层变量

noncomputable def dXK (f : PS2 K) : PS2 K :=        -- ∂_x：对每个 t^m 系数求 x 导数
  PowerSeries.mk fun m => PowerSeries.derivative (R := K) (PowerSeries.coeff m f)
noncomputable def dTK (f : PS2 K) : PS2 K :=        -- ∂_t
  PowerSeries.derivative (R := PowerSeries K) f

noncomputable def polyToPS2 : Polynomial (Polynomial K) →+* PS2 K := …   -- K[x,t] ↪ K[[x,t]]

/-- `K(x,t)`：`Frac(K[[x,t]])` 中由 `K[x,t]` 的像生成的子域。 -/
noncomputable def ratFn : Subfield (FractionRing (PS2 K)) :=
  Subfield.closure
    (Set.range fun p => algebraMap (PS2 K) (FractionRing (PS2 K)) (polyToPS2 K p))

def IsDFinite (f : PS2 K) : Prop :=
  FiniteDimensional (ratFn K) (Submodule.span (ratFn K) (Set.range fun ij : ℕ × ℕ =>
    algebraMap (PS2 K) (FractionRing (PS2 K)) ((dXK K)^[ij.1] ((dTK K)^[ij.2] f))))

noncomputable def FK : PS2 K := PowerSeries.mk fun m => PowerSeries.mk fun k => (U k m : K)

theorem not_isDFinite_FK {K : Type*} [Field K] (σ : K →+* ℂ) : ¬ IsDFinite K (FK K)
```

**数学含义**：Lipshitz 1989 Def. 2.1（n=2）：f∈K[[x,t]] 是 D-finite，当且仅当 f 的全部偏导数 ∂_x^i∂_t^j f 在 Frac(K[[x,t]]) 中张成的 K(x,t)-向量空间是有限维的。F(x,t)=Σ_{k,m}U_k(m)x^k t^m。

**要核对的点**
- [ ] `IsDFinite` 与 Lipshitz 的定义一致：所有 i,j≥0 的 ∂_x^i∂_t^j f（两个导数可交换，已证 `dXK_dTK_comm`），张成空间取在分式域里，系数域是 K(x,t)。
- [ ] `ratFn K` 就是 K(x,t)：已证 `mem_ratFn_iff`（恰由「多项式 / 非零多项式」组成）与 `isFractionRing_ratFn`。
- [ ] 用 K[[x]][[t]] 代替 K[[x,t]]：两者典范同构，这一点**没有**形式化，是标准事实。
- [ ] `FK` 中 t^m 的系数是 Σ_k U_k(m)x^k（即 G_m(x)），与论文的 F 一致。
- [ ] 定理对任何能嵌入 ℂ 的域 K 成立（`σ : K →+* ℂ`），包括 ℚ 与 ℂ；特征 0 的要求由此自动满足。
- [ ] 不是空洞的定义：常数 1 是 D-finite（`isDFinite_one`）。

## 4. 没有系数只依赖 k 的象限递推（T3.7(2)，`NonDFinite.lean`）

**Lean 原文**

```lean
theorem no_k_only_recurrence (A B k0 m0 : ℕ) (p : ℕ → ℕ → ℂ[X])
    (hp : ∃ a ≤ A, ∃ b ≤ B, p a b ≠ 0) :
    ¬ ∀ k m, k0 ≤ k → m0 ≤ m → A ≤ k → B ≤ m →
      ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1), (p a b).eval (k : ℂ) * (U (k - a) (m - b) : ℂ) = 0
```

**数学含义**：不存在不全为 0 的复系数多项式 p_{ab}(k)（0≤a≤A，0≤b≤B），使 Σ_{a,b} p_{ab}(k)·U_{k−a}(m−b)=0 在某个象限 k≥k_0、m≥m_0 上成立。

**要核对的点**
- [ ] 系数只依赖 k（`p a b : ℂ[X]`，在 k 处取值），不依赖 m。这正是 T3.7(2) 说的「k-only」。
- [ ] 「不全为 0」只看求和范围内的 a≤A、b≤B（`hp`）。
- [ ] `A ≤ k`、`B ≤ m` 的要求是为了让 `k − a`、`m − b` 不出现自然数减法截断；把象限缩小不影响结论。
- [ ] 结论是「在**某个象限**上不成立」，比「在全平面上不成立」强。

## 5. 象限递推的左理想 Rel(U)=O_U·L1（T3.8，`OreRel.lean`）

**Lean 原文**

```lean
abbrev Arr := ℕ → ℕ → ℂ                         -- ℕ×ℕ 上的复数组，负下标处约定为 0
abbrev Coef := Polynomial (Polynomial ℂ)        -- ℂ[k,m]：内层变量 k，外层变量 m
noncomputable def cK : Coef := Polynomial.C Polynomial.X   -- 系数 k
noncomputable def cM : Coef := Polynomial.X                -- 系数 m

-- 乘法算子 f ↦ p(k,m)·f
noncomputable def mulOp : Coef →+* Module.End ℂ Arr  -- toFun p := fun f k m => p.evalEval k m * f k m
-- X：(X f)(k, m) = f(k − 1, m)（k = 0 时为 0）
noncomputable def opX : Module.End ℂ Arr       -- toFun f k m := if k = 0 then 0 else f (k - 1) m
-- E⁻¹：(E⁻¹ f)(k, m) = f(k, m − 1)（m = 0 时为 0）
noncomputable def opEinv : Module.End ℂ Arr    -- toFun f k m := if m = 0 then 0 else f k (m - 1)

noncomputable def OU : Subalgebra ℂ (Module.End ℂ Arr) :=
  Algebra.adjoin ℂ {mulOp cK, mulOp cM, opX, opEinv}

noncomputable def L1 : Module.End ℂ Arr := 1 - opEinv - opX - mulOp cM * opX ^ 3

noncomputable def Uarr : Arr := fun k m => (U k m : ℂ)
def VanishOn (f : Arr) (k1 m1 : ℕ) : Prop := ∀ k m, k1 ≤ k → m1 ≤ m → f k m = 0
def RelU : Set (Module.End ℂ Arr) :=
  {R | R ∈ OU ∧ ∃ k0 m0 : ℕ, VanishOn (R Uarr) k0 m0}

theorem RelU_eq : RelU = {R | ∃ Q ∈ OU, R = Q * L1}
theorem exists_normal_form {T : Module.End ℂ Arr} (hT : T ∈ OU) : ∃ r, T = normOp r
theorem normal_form_unique (r : ℕ × ℕ →₀ Coef) (h : normOp r = 0) : r = 0
```

**数学含义**：O_U=ℂ[k,m]⟨X,E⁻¹⟩，其中 X: k↦k−1，E⁻¹: m↦m−1。Rel(U) 是 O_U 中在某个象限上零化 U 的算子全体。L1·U=0 就是引理 1：U_k(m)−U_k(m−1)−U_{k−1}(m)−m·U_{k−3}(m)=0。T3.8 说 Rel(U)={Q·L1 : Q∈O_U}，即 L1 生成的左理想。

**要核对的点**
- [ ] `L1` 作用在 (k,m) 处是 f(k,m)−f(k,m−1)−f(k−1,m)−m·f(k−3,m)：`mulOp cM * opX ^ 3` 先位移、再乘以**输出点**的 m，与引理 1 的系数 m 一致（不是 m−1，也不是在输入点取值）。
- [ ] 负下标补 0 的约定只影响边界；`RelU` 只要求在某个象限上为 0，所以边界不影响结论。论文里要写清「在某个象限上零化」。
- [ ] Lean 里的 `OU` 是作用在数组上的算子构成的子代数，不是抽象的 Ore 代数。两者一致由 `exists_normal_form`（每个元素都能写成 Σ r_{ab}(k,m)X^aE^{−b}）与 `normal_form_unique`（写法唯一，即作用是忠实的）保证。
- [ ] 系数是**多项式**，不是有理函数。有理函数系数的版本（Ore 理想的「收缩」）没有形式化。
- [ ] 只有向下的位移（X、E⁻¹），没有向上的位移。向上位移的递推乘以足够高次的 X^aE^{−b} 就变成这种形式，所以不损失一般性；这一句是书面论证，不在 Lean 中。

`N` 的版本（`OreRelN.lean`）完全平行：`RelN` 把 `Uarr` 换成 `Narr`（N(k,q) 看成数组，第二个下标是 q），`LN = 1 − X − X·Y − (q − 1)·X³·(1 + Y)²`（Y 是 `opEinv`），定理 `RelN_eq : RelN = {R | ∃ Q ∈ OU, R = Q * LN}`。核对点同上，另加一条：
- [ ] `LN` 中的系数是 q−1（`mulOp (cM - 1)`），与报告 T3.8 的 L_N 一致。

## 6. U 不是 Stirling-like（T3.8 的推论，`NotStirlingLike.lean`，2026-10-07 新增）

**Lean 原文**

```lean
/-- 三个格点 `p, q, r` 的二倍有向面积 `det(q − p, r − p)`。 -/
def det2 (p q r : ℕ × ℕ) : ℤ :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) - ((q.2 : ℤ) - p.2) * ((r.1 : ℤ) - p.1)

theorem relU_support_det {R : Module.End ℂ Arr} (hR : R ∈ RelU) (hR0 : R ≠ 0)
    {r : ℕ × ℕ →₀ Coef} (hr : R = normOp r) :
    ∃ p0 ∈ r.support, ∃ p1 ∈ r.support, ∃ p2 ∈ r.support, 3 ≤ det2 p0 p1 p2

theorem relU_card_support {R : Module.End ℂ Arr} (hR : R ∈ RelU) (hR0 : R ≠ 0)
    {r : ℕ × ℕ →₀ Coef} (hr : R = normOp r) : 3 ≤ r.support.card

theorem not_mem_relU_of_support_subset {r : ℕ × ℕ →₀ Coef} (hr : r ≠ 0) {p0 p1 p2 : ℕ × ℕ}
    (hs : r.support ⊆ {p0, p1, p2}) (hdet : |det2 p0 p1 p2| ≤ 2) : normOp r ∉ RelU
```

**数学含义**：把 Rel(U) 中的算子写成正规形 Σ r_{ab}(k,m)X^aE^{−b}，它的支撑是格点集 {(a,b) : r_{ab}≠0}。定理说：每个非零的 R∈Rel(U)，支撑里都有三个点围成的三角形二倍面积 ≥3。Kauers 2007 定义 3 的 Stirling-like 要求零化理想由一条三项算子生成，且两条位移向量构成 ℤ² 的基，也就是三个指数点围成二倍面积为 1 的三角形。

**要核对的点**
- [ ] `det2 p q r` 是 det(q−p, r−p)，绝对值是三角形面积的两倍；|det2|=1 等价于两条边向量构成 ℤ² 的基。
- [ ] `normOp r` 的支撑 `r.support` 就是「出现的单项 X^aE^{−b} 的指数点」（`normal_form_unique` 保证这个支撑由算子唯一决定）。
- [ ] 从 Kauers 的定义（有理函数系数、位移可正可负、零化理想由该算子生成）到这里的定理，中间有一段**书面**论证，不在 Lean 中：平移自变量使三项只向下看，左乘公分母 D(k,m) 两次（D=0 处等式两边都是 0），得到 O_U 中在一个象限上零化 U、支撑二倍面积仍为 1 的算子，与 `not_mem_relU_of_support_subset` 矛盾。见 `NotStirlingLike.lean` 文件头。请确认这段论证对 Kauers 定义的读法是对的。（2026-10-07 主 Agent 已对照 Kauers 2007 §2.2 原文：序列定义在整个 ℤ² 上，零化子要求 Q·f≡0，比「在象限上零化」更强，所以论证适用；见 `notes/04-主Agent-U不是Stirling-like.md` §3。仍请你自己确认一次。）
- [ ] `relU_card_support` 顺带说明 U 没有一项或两项的象限递推。

## 总清单

| # | 项 | 结论 | 备注 |
|---|---|---|---|
| 1.1 | `Good` 是「b=c 或 a≥max(b,c)」 | ☐ | |
| 1.2 | 三元组方向：a 是最早的一项 | ☐ | |
| 1.3 | 边界 k≤2、m=0 的约定 | ☐ | |
| 2.1 | `Mat n k`：n 行 k 列 | ☐ | |
| 2.2 | 行规则排除 001、010，列规则排除 001、011 | ☐ | 读的方向不影响计数 |
| 2.3 | ⌈n/2⌉=(n+1)/2，⌊n/2⌋=n/2 | ☐ | |
| 2.4 | 多重链与 zeta 多项式的约定 | ☐ | |
| 3.1 | `IsDFinite` 与 Lipshitz Def. 2.1 一致 | ☐ | |
| 3.2 | K[[x]][[t]]≅K[[x,t]] 未形式化，可接受 | ☐ | |
| 3.3 | `FK` 的系数排列 | ☐ | |
| 4.1 | k-only：系数只依赖 k | ☐ | |
| 4.2 | 象限版本、下标不截断 | ☐ | |
| 5.1 | `L1` 的系数 m 在输出点取值 | ☐ | |
| 5.2 | 「在某个象限上零化」写进论文 | ☐ | |
| 5.3 | 多项式系数、只向下位移，不损失一般性 | ☐ | 后半句是书面论证 |
| 5.4 | `LN` 的系数 q−1 | ☐ | |
| 6.1 | `det2` 与「幺模」的对应 | ☐ | |
| 6.2 | Kauers 定义到 Lean 定理的书面论证 | ☐ | 不在 Lean 中 |

全部打勾，才能在论文里说「下列陈述在 Lean 中机器检查过」；有任何一项存疑，论文里对应的定理改说「证明已机器检查，陈述的忠实性由作者核对」，并把存疑处写进正文。
