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
- [x] `Good a b c` 是「b=c 或 a≥max(b,c)」：`b ≤ a ∧ c ≤ a` 就是 a≥max(b,c)。
- [x] 三元组的方向：列表头是 h_1，所以 `a` 是三个里**最早**的那个（h_j），不是最晚的。
- [x] `seqs m k` 恰是长 k、每项 ≤ m 的列表（已证：`mem_seqs`；`mem_L` 把 `L k m` 写成「长度为 k ∧ 每项 ≤ m ∧ Legal」）。
- [x] 边界：k=0,1,2 时 `Legal` 恒真，所以 U_0(m)=1、U_1(m)=m+1、U_2(m)=(m+1)²；m=0 时只有全零序列，U_k(0)=1。这与论文的约定一致吗？

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
- [x] n 是行数、k 是列数（`Mat n k`），与论文里 a_k(n) 的下标约定一致。
- [x] 「横向」＝在同一行里沿列号递增读，「纵向」＝在同一列里沿行号递增读；横向排除 001、010，纵向排除 001、011（`true` 表示 1）。
- [x] 读的方向不影响计数：把每行左右翻转是「横向不含 001、010」与「横向不含 100、010」两类矩阵之间的双射，纵向同理。所以即使 OEIS 的读法与这里相反，`a k n` 的值也不变；不必为方向担心。
- [x] `U_eq_multichains`（T1.0(c)）：`Monotone c` 是 `Fin m` 到允许行集合的单调映射，序是逐分量序（`false < true`），即 m 元多重链 x_1≤⋯≤x_m。这是 Stanley 约定下的 zeta 多项式值 Z(Λ_k, m+1)。

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
- [x] `IsDFinite` 与 Lipshitz 的定义一致：所有 i,j≥0 的 ∂_x^i∂_t^j f（两个导数可交换，已证 `dXK_dTK_comm`），张成空间取在分式域里，系数域是 K(x,t)。
- [x] `ratFn K` 就是 K(x,t)：已证 `mem_ratFn_iff`（恰由「多项式 / 非零多项式」组成）与 `isFractionRing_ratFn`。
- [x] 用 K[[x]][[t]] 代替 K[[x,t]]：两者典范同构，这一点**没有**形式化，是标准事实。
- [x] `FK` 中 t^m 的系数是 Σ_k U_k(m)x^k（即 G_m(x)），与论文的 F 一致。
- [x] 定理对任何能嵌入 ℂ 的域 K 成立（`σ : K →+* ℂ`），包括 ℚ 与 ℂ；特征 0 的要求由此自动满足。
- [x] 不是空洞的定义：常数 1 是 D-finite（`isDFinite_one`）。

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
- [x] 系数只依赖 k（`p a b : ℂ[X]`，在 k 处取值），不依赖 m。这正是 T3.7(2) 说的「k-only」。
- [x] 「不全为 0」只看求和范围内的 a≤A、b≤B（`hp`）。
- [x] `A ≤ k`、`B ≤ m` 的要求是为了让 `k − a`、`m − b` 不出现自然数减法截断；把象限缩小不影响结论。
- [x] 结论是「在**某个象限**上不成立」，比「在全平面上不成立」强。

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
- [x] `L1` 作用在 (k,m) 处是 f(k,m)−f(k,m−1)−f(k−1,m)−m·f(k−3,m)：`mulOp cM * opX ^ 3` 先位移、再乘以**输出点**的 m，与引理 1 的系数 m 一致（不是 m−1，也不是在输入点取值）。（2026-10-08 补：X 只移动 k，m 与 X 可交换，所以对 `L1` 来说输出点与输入点的 m 相同，真正要核的只是「m 而不是 m−1」；顺序要紧的是 `LN`，因为 Y 移动 q，见 5.4。`code/main_extra/sec5_6_bruteforce.py` 从定义枚举：负下标取 0 时 (L1 U)(k,m) 只在 (0,0) 与 k=2、m≥1 处非零，把 m 换成 m−1 则在 3≤k≤8、1≤m≤4 全部非零；`LN` 的系数改在输入点取值或把 q−1 换成 q，都会在 3≤k≤7 的若干点非零。）
- [x] 负下标补 0 的约定只影响边界；`RelU` 只要求在某个象限上为 0，所以边界不影响结论。论文里要写清「在某个象限上零化」。
- [x] Lean 里的 `OU` 是作用在数组上的算子构成的子代数，不是抽象的 Ore 代数。两者一致由 `exists_normal_form`（每个元素都能写成 Σ r_{ab}(k,m)X^aE^{−b}）与 `normal_form_unique`（写法唯一，即作用是忠实的）保证。
- [x] 系数是**多项式**，不是有理函数。有理函数系数的版本（Ore 理想的「收缩」）没有形式化。
- [x] 只有向下的位移（X、E⁻¹），没有向上的位移。向上位移的递推左乘足够高次的 X^aE^{−b}（即在 (k−a,m−b) 处取值）就变成这种形式，所以不损失一般性；这一句是书面论证，不在 Lean 中。

`N` 的版本（`OreRelN.lean`）完全平行：`RelN` 把 `Uarr` 换成 `Narr`（N(k,q) 看成数组，第二个下标是 q），`LN = 1 − X − X·Y − (q − 1)·X³·(1 + Y)²`（Y 是 `opEinv`），定理 `RelN_eq : RelN = {R | ∃ Q ∈ OU, R = Q * LN}`。核对点同上，另加一条：
- [x] `LN` 中的系数是 q−1（`mulOp (cM - 1)`），与报告 T3.8 的 L_N 一致。

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
- [x] `det2 p q r` 是 det(q−p, r−p)，绝对值是三角形面积的两倍；|det2|=1 等价于两条边向量构成 ℤ² 的基。
- [x] `normOp r` 的支撑 `r.support` 就是「出现的单项 X^aE^{−b} 的指数点」（`normal_form_unique` 保证这个支撑由算子唯一决定）。
- [x] 从 Kauers 的定义（有理函数系数、位移可正可负、零化理想由该算子生成）到这里的定理，中间有一段**书面**论证，不在 Lean 中：平移自变量使三项只向下看，左乘公分母 D(k,m) 两次（D=0 处等式两边都是 0），得到 O_U 中在一个象限上零化 U、支撑二倍面积仍为 1 的算子，与 `not_mem_relU_of_support_subset` 矛盾。见 `NotStirlingLike.lean` 文件头。请确认这段论证对 Kauers 定义的读法是对的。（2026-10-07 主 Agent 已对照 Kauers 2007 §2.2 原文：序列定义在整个 ℤ² 上，零化子要求 Q·f≡0，比「在象限上零化」更强，所以论证适用；见 `notes/04-主Agent-U不是Stirling-like.md` §3。仍请你自己确认一次。）
- [x] `relU_card_support` 顺带说明 U 没有一项或两项的象限递推。

## 机械核对（2026-10-08 本地）

这两项不需要人读，脚本给出结论；它们保证上面引的、论文附录 A 里引的 Lean 原文就是当前编译过的源码。

- **附录 A 与源码逐字一致**：`py -3.14 code/main_extra/check_appendix_lean.py` 把附录 A 的 alltt 块中的 TeX 记号换回 Unicode，按声明切开，压缩空白后与源码中同名声明比较：定义（def、abbrev）连定义体整段相等，定理一直比到证明开头的 `:=`（附录不抄证明）。34 条声明全部 PASS（`logs/check_appendix_lean_2026-10-08.log`）。反向测试：在副本里改 4 处（`opX_apply` 的 `k = 0` 改 `k = 1`、截掉 `L1` 定义体的末项、`fun k m` 改 `fun km`、截掉 `RelU_eq` 陈述末尾的 `* L1`），报 4 个 FAIL、退出码 1（`logs/check_appendix_lean_reverse_2026-10-08.log`）。
- **编译产物与当前源码一致（没有重新编译）**：`py -3.14 code/main_extra/check_lean_fresh.py` 检查 28 个模块（27 个加根文件）的 .olean 都晚于源码、也晚于所导入模块的 .olean；`Axioms.lean`、`Checks.lean` 最后一次运行（`logs/lean_mem.log`，UTC 2026-10-06 22:29 与 22:33）退出码 0，且开始于源码最后修改和最新 .olean 之后；那次运行的 256 条 `#print axioms` 只用到 propext、Classical.choice、Quot.sound，对全部 2675 个声明的扫描也没有其他公理（没有 sorryAx）；git 显示 `lean/` 无未提交改动。35 项全部 PASS（`logs/check_lean_fresh_2026-10-08.log`，末尾记了全部源文件的 sha256）。反向测试（scratchpad 副本，保留修改时间）：改源码时间报 2 个 FAIL，改依赖的 .olean 时间报 4 个 FAIL，在公理日志里插入 sorryAx 报 1 个 FAIL（`logs/check_lean_fresh_reverse_2026-10-08.log`）。这是时间顺序加日志的证据，不是重新编译；源码自 2026-10-06 的提交 6bac341 起没有改过。
- **2026-10-10 补形式化后（重新编译）**：`Growth.lean` 新增 `rho_mul_rho_sub_one_strictMono` 与 `normSq_lt_rho_pred_sq`（论文定理 3.2(1) 的最后两句；用到的 `rho` 定义在 `Growth.lean`，不在上面 18 项里，陈述由 AI 对照论文核对）。经 `lean/lean_one.sh` 逐个重编 Growth、根模块，重跑 `Axioms.lean`（258 条 `#print axioms`，全量扫描 2678 个声明，只有 propext、Classical.choice、Quot.sound）与 `Checks.lean`，每次启动前查过内存（峰值约 8.05–8.08 GB，最低提交余量 4.1 GB）。之后 `check_lean_fresh.py` 35 项全部 PASS（`logs/check_lean_fresh_2026-10-10.log`）。同日第二项：推论 8.15 与引理 8.12 的一部分本来就已形式化（见论文表 5 新加的两行），给 `leadingCoeff_hpoly_eq` 补一行 `#print axioms` 后重跑 `Axioms.lean`（259 条，2678 个声明，只有三条标准公理；`logs/lean_axioms_2026-10-10_cor815.log`），`check_lean_fresh.py` 35 项全部 PASS（`logs/check_lean_fresh_2026-10-10_cor815.log`）。同日第三项：新模块 `Saturated.lean`（论文推论 5.5，分母乘掉的形式；只用到上面第 5 节的 `RelU`、`OU`、`L1`、`mulOp` 与 `pureOp`，陈述由 AI 对照论文核对），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（261 条，2682 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 36 项全部 PASS（`logs/check_lean_fresh_2026-10-10_sat.log`）。同日第四项：新模块 `ThreeTerm.lean`（论文推论 5.7 与注 5.8，分母乘掉的形式；陈述只用到 `U`、`Coef` 与多项式取值 `evalEval`，`f` 是 `U` 在 ℤ² 上的任意延拓；陈述由 AI 对照论文核对，并抄进论文附录 A，由 `check_appendix_lean.py` 对照源码），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（264 条，2728 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 37 项全部 PASS（`logs/check_lean_fresh_2026-10-10_three.log`）。同日第五项：新模块 `GenFunXY.lean`（论文定理 4.4 与引理 4.5 的按 y 细化；新定义 `Gxy`（G_m(x,y) 的系数是 `Us k m s`）与 `bxy`（b_v = 1 − x − v·y·x³）由 AI 对照论文核对，`Us`、`asc`、`hc`、`vars` 沿用 `Ascent.lean`、`Formula.lean`，不在上面 18 项里），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（268 条，2778 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 38 项全部 PASS（`logs/check_lean_fresh_2026-10-10_genfun.log`）。同日第六项：新模块 `Blocks.lean`（论文定理 4.2；新定义 `Blk`、`Blk.toList`、`Blk.level`、`Blk.Valid`、`Blk.IsE`、`concatBlk`、`BlkSeq` 由 AI 对照论文定义 4.1 与定理 4.2 核对，`L`、`Legal`、`asc` 沿用已有定义），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（270 条，2882 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 39 项全部 PASS（`logs/check_lean_fresh_2026-10-10_blocks.log`）。同日第七项：新模块 `EndAscent.lean`（论文注记 5.2；新定义 `endsAsc`（最后两项 x < y）、`NA`、`NAser`、`hyp1F1`（Σ (a)_n/(b)_n·zⁿ/n!·tⁿ）由 AI 对照论文核对），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（273 条，2937 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 40 项全部 PASS（`logs/check_lean_fresh_2026-10-10_endasc.log`）。同日第八项：新模块 `RootExpansion.lean`（论文定理 3.2(2)；新定义 `Qpoly`、`sig`、`cof`、`alpha`、`geom` 由 AI 对照论文核对：`sig m` 是 `Qpoly m` 的根的集合（`Multiset.toFinset`，`card_sig` 证明恰有 3m + 1 个，即根两两不同），`alpha` 是部分分式系数，`alpha_unique` 说明它就是论文里由展开式确定的 α_m(σ)），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（276 条，2994 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 41 项全部 PASS（`logs/check_lean_fresh_2026-10-10_rootexp.log`）。同日第九项：新模块 `RootAsymp.lean`（论文定理 3.2(3)；新定义 `cm`、`tau` 由 AI 对照论文核对：`cm` 是论文 c_m 的第二个表达式，`alpha_rho` 证明它等于 α_m(ρ_m)，`cm_eq_G` 与 `hasSum_G` 给出第一个表达式；`tau` 与论文的 τ_m 逐字对应），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（279 条，3041 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 42 项全部 PASS（`logs/check_lean_fresh_2026-10-10_rootasymp.log`）。同日第十项：新模块 `AsympRemark.lean`（论文注记 3.3 的精确部分；新定义 `thetaRatio`、`kappaConst` 与论文的 θ_m、κ_m 逐字对应，由 AI 核对），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（288 条，3074 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 43 项全部 PASS（`logs/check_lean_fresh_2026-10-10_asympremark.log`）。同日第十一项：新模块 `OeisRemark.lean`（论文注记 3.5 中不靠计算的部分；新定义 `ofList`（系数表对应的多项式）、`rowOrd`（Δ_n）、`rowPoly`（∏(X − στ)）、`ColRuleAlt`（列规则 001/101，即 A207069、A207070 标题的规则）、`aAlt`（相应的矩阵个数）、`swap01`（交换前两行）由 AI 对照论文与 OEIS 标题核对；五个 OEIS 递推的陈述由脚本从快照逐字生成），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（302 条，3121 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 44 项全部 PASS（`logs/check_lean_fresh_2026-10-10_oeisremark.log`）。同日第十二项：新模块 `ThreeTermRat.lean`（论文推论 5.7 的有理函数系数原样陈述；新定义 `RatCoef`（`FractionRing Coef`，即 ℂ(k, m)）、`HasValueAt`（有理函数在一点有定义及其值：有表示 a/b 且 b 在该点不为 0，值为 a/b 在该点的值）由 AI 对照论文核对，`HasValueAt.unique` 证明值与表示无关），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（306 条，3130 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 45 项全部 PASS（`logs/check_lean_fresh_2026-10-10_threetermrat.log`）。同日第十三项：新模块 `SaturatedRat.lean`（论文推论 5.5 的有理函数系数原样陈述；新定义 `TUrat`（右乘 L1 的正规形公式，系数在 ℂ(k, m) 中，对应论文式 (4)）由 AI 对照论文核对；「T ∈ 𝒪(k,m)·L1」按正规形写成「t_{ab} = TUrat q a b」，这一描述本身（𝒪(k,m) 的正规形唯一、右乘 L1 的公式）没有形式化），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（310 条，3138 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 46 项全部 PASS（`logs/check_lean_fresh_2026-10-10_saturatedrat.log`）。同日第十四项：新模块 `OeisRows.lean`（论文注记 3.5 的行递推核对；新定义 `colStep`、`Ucol`、`rowList`、`seg`、`Uext`、`resid`、`checkWindows` 由 AI 核对，其中 `Ucol_eq`、`rowList_eq` 证明 `Ucol`、`rowList` 算的就是 U 与 a；六条 OEIS 递推的陈述由脚本从快照逐字生成），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（319 条，3255 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 47 项全部 PASS（`logs/check_lean_fresh_2026-10-10_oeisrows.log`）。同日第十五项：新模块 `AsympNumerics.lean`（论文注记 3.3 的数值，区间算术；新定义 `cmN`、`cmD`、`cmTailQ`、`cmNQ`、`cmDQ` 由 AI 核对，其中 `cm_eq_frac`、`cmNQ_cast`、`cmDQ_cast` 证明它们与 c_m 一致；「≈ x」理解为与 x 之差小于末位的半个单位），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（336 条，3454 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 48 项全部 PASS（`logs/check_lean_fresh_2026-10-10_asympnumerics.log`）。同日第十六项：新模块 `OeisRowOrders.lean`（论文注记 3.5 后半句：行递推阶的最小性与不同乘积的个数；陈述 `row_min_order_*`、`card_row_products_*` 只用 `a`、`sig`、`IsLeast` 与有限集的元素个数，新定义 `ofDig`、`digs`、`hkUnit`、`kronCheck`、`listPoly`、`IsLevel`、`lvStep`、`lvGet`、`lvAcc`、`lvCheck`、`lvEval`、`lvIter` 与数据 `rowGam2`–`rowGam7`、`rowCols2`–`rowCols7` 只在证明里用，由 AI 核对），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（360 条，3683 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 49 项全部 PASS（`logs/check_lean_fresh_2026-10-10_oeisroworders.log`）。同日第十七项：新模块 `RStirling.lean`（论文引理 4.5 最后一句；陈述用到的新定义 `IsSetPartition`（各块非空、两两不交、并为 S）、`Separates`（1,…,j 两两不同块）、`setParts`、`partCount` 承载「集合划分个数」的意思，由 AI 对照论文核对；`Allowed` 只在证明里用），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（368 条，3764 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 50 项全部 PASS（`logs/check_lean_fresh_2026-10-10_rstirling.log`）。同日第十八项：新模块 `Bijection.lean`（论文命题 4.7，双射的存在；新定义 `NAs`（L k m 中上升数为 s 且 `endsAsc` 为假的个数）由 AI 核对，陈述 `prop_bijection` 用到 `L`、`asc`、`endsAsc`、`powersetCard` 与第十七项的 `setParts`），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（374 条，3790 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 51 项全部 PASS（`logs/check_lean_fresh_2026-10-10_bijection.log`）。论文第 9 节据此改为「basic definitions」并注明后加的定义只经过 AI 对照。

## 总清单

结论列：✓ = 作者本人在数学层面核对过；AI 一致 = Claude 的 Lean→数学翻译与另一个模型的独立复核一致，作者本人尚未核对；☐ = 还没做。

第二轮（2026-10-08 本地）：GPT-6.1 Sol 改为对照论文原件（`main（署名版）.pdf`，与 `paper/main.pdf` 同一 sha256）的正文、附录 A 和对话里贴出的 Lean 源码，重核了 1.1–4.2 这 10 项，结论都是一致；它从定义出发独立暴力枚举了文中引用的数值（不是重跑 Lean）；它没有取得完整 Lean 工程，也没有重新编译，这一缺口由上面的机械核对补上。

| # | 项 | 结论 | 备注 |
|---|---|---|---|
| 1.1 | `Good` 是「b=c 或 a≥max(b,c)」 | ✓ | 2026-10-07：Claude 翻译，GPT-6.1 Sol 独立确认；作者本人已核（2026-10-08） |
| 1.2 | 三元组方向：a 是最早的一项 | ✓ | 同上。数值证据：U 的总数分不出方向（整体倒序是双射），按上升数细分分得出——`Checks.lean` 算出 U_6(3) 按上升数为 84, 238, 97，反向读应为 10, 162, 210, 37 |
| 1.3 | 边界 k≤2、m=0 的约定 | ✓ | 同上；Lean 已证 `U_of_le_two`、`U_zero_left`、`U_zero_right` |
| 2.1 | `Mat n k`：n 行 k 列 | ✓ | 同上；OEIS 例子 n=4、k=3 为 4 行 3 列 |
| 2.2 | 行规则排除 001、010，列规则排除 001、011 | ✓ | 同上。Lean 源码逐字核过：行沿列号递增读（从左往右）排除 (0,0,1)、(0,1,0)，列沿行号递增读（从上往下）排除 (0,0,1)、(0,1,1)，与论文第 1 页原句一致，不只是计数一致 |
| 2.3 | ⌈n/2⌉=(n+1)/2，⌊n/2⌋=n/2 | ✓ | 同上；n=5、6 代入验证 |
| 2.4 | 多重链与 zeta 多项式的约定 | ✓ | 同上。Stanley 约定：Z(P,r) 数 r−1 个元素的多重链（GPT 复述，未对照原书）；m=1、m=0 两处偏移检查一致；「等于 Stanley 的 Z(Λ_k,m+1)」半句不在 Lean 里。第二轮 GPT 更正了自己先前的泛化：Z(P,1)=1 只对有最小元和最大元的偏序集成立（两元反链的 zeta 多项式恒为 2）；Λ_k 有全 0 行和全 1 行，所以结论不受影响 |
| 3.1 | `IsDFinite` 与 Lipshitz Def. 2.1 一致 | ✓ | 2026-10-07：Claude 对照 Lean 源码翻译；GPT-6.1 Sol 确认翻译与论文第 11 页的定义一致，但它只看了 Claude 的转述，没看论文原页和 Lean 源码。它提的疑点「K(x,t) 如何嵌入分式域」由 Claude 对照源码答复：`polyToPS2` 是标准嵌入（已证单射），`mem_ratFn_iff`、`isFractionRing_ratFn` 说明所得子域就是 K(x,t)；作者本人已核（2026-10-08）。第二轮 GPT 已对照论文第 11 页原文与附录 A 第 24 页，结论不变 |
| 3.2 | K[[x]][[t]]≅K[[x,t]] 未形式化，可接受 | ✓ | 同上；论文附录 A 已披露这一对应未形式化，GPT 建议保留这句 |
| 3.3 | `FK` 的系数排列 | ✓ | 同上。疑点「系数下标」由 Claude 对照源码答复：`FK = mk fun m => mk fun k => U k m`，即 [x^k t^m]F = U_k(m)；「ℂ 的任何子域」与「带嵌入 σ : K → ℂ 的域」等价 |
| 4.1 | k-only：系数只依赖 k | ✓ | 2026-10-08：GPT-6.1 Sol 对照论文第 11 页定理 5.1(2)（p_{ab}∈ℂ[k]）与附录 A 第 24 页：`p : ℕ → ℕ → ℂ[X]` 按 (a,b) 选多项式、在 k 处求值，m 不进入系数；`hp` 与「不全为 0」一致；作者本人已核（2026-10-08） |
| 4.2 | 象限版本、下标不截断 | ✓ | 同上。论文要求 k_0≥A、m_0≥B（Claude 在 `main.tex` 第 496 行核实了这句原文），所以 Lean 多出的 A≤k、B≤m 自动成立；反过来，Lean 的任意阈值换成 max(k_0,A)、max(m_0,B) 即得论文允许的阈值，检查范围相同；a≤A、b≤B 保证自然数减法不截断 |
| 5.1 | `L1` 的系数 m 在输出点取值 | ✓ | 2026-10-08：GPT-6.1 Sol 对照论文第 13 页与附录 A：`Module.End` 的乘法是复合、右边先作用，所以 (L1 f)(k,m)=f(k,m)−f(k,m−1)−f(k−1,m)−m·f(k−3,m)；`lemma1` 令 K=k+3、M=m+1，恰为引理 2.5 在 K≥3、M≥1 的情形，系数 m+1 就是 M；X 只移动 k，与 m 可交换（含零边界），所以 m 放在 X³ 哪一侧都一样；枚举证据见 `sec5_6_bruteforce.py`；作者本人已核（2026-10-08） |
| 5.2 | 「在某个象限上零化」写进论文 | ✓ | 同上。`RelU` 与论文的 Rel(U) 量词位置相同（∃k0,m0 ∀k,m）；GPT 逐处查了摘要、定理 D(3)、§5.1 的定义、定理 5.4、推论 5.5、命题 5.6、推论 5.7，没有写成「在整个 ℕ² 上」的地方；有限支撑的算子把阈值取大就不读负下标，所以负下标的约定不影响 Rel(U) |
| 5.3 | 多项式系数、只向下位移，不损失一般性 | ✓ | 同上。GPT：两条正规形定理要结合生成元定义与交换规则，才推出 OU 就是 Ore 代数且作用忠实；它没看到这些辅助性质的 Lean 定理，Claude 在源码里查到：`normOp_mem`（每个正规形属于 OU）、`opX_mul_mulOp`（X·p(k,m)=p(k−1,m)·X）、`opEinv_mul_mulOp`（E⁻¹·p(k,m)=p(k,m−1)·E⁻¹）、`commute_opX_opEinv`、`commute_opX_cM`，`mulOp` 本身是环同态。含向上位移的递推要**左**乘 X^aE^{−b}（即在 (k−a,m−b) 处取值），论文第 13 页已改为 left multiplication（10-08）；推论 5.5(1) 的 Δ² 论证无缺口（两次都是左乘）。有理系数版本与「不损失一般性」仍是书面论证 |
| 5.4 | `LN` 的系数 q−1 | ✓ | 同上。展开 (1+Y)² 后与命题 2.7 逐项对应；系数在输出点取值，顺序要紧（Y·(q−1)=(q−2)·Y）；枚举：系数放到输入点或写成 q 都不成立；`RelN` 的量词结构与 `RelU` 相同 |
| 6.1 | `det2` 与「幺模」的对应 | ✓ | 同上。行列式为 ±1 当且仅当两个格向量构成 ℤ² 的基；命题 5.6 与 `relU_support_det` 都是带符号的 ≥3，Lean 先转成整数再相减；命题 5.6 末句与 `not_mem_relU_of_support_subset` 互为逆否（行列式是整数；`normal_form_unique` 给出 r≠0 与 R≠0 等价） |
| 6.2 | Kauers 定义到 Lean 定理的书面论证 | ✓ | 2026-10-10 起推论 5.7（分母乘掉、对 U 的任意延拓）已在 Lean 中（`ThreeTerm.lean`），剩下取公分母与从 Kauers 定义到「生成元零化延拓」两步仍不在 Lean 中。以下是 10-08 的核对：GPT 读了 Kauers 2007 的公开预印本（RISC 3240，2007-08-24 版），没有比对出版社排印版：论文对 §2.2 与定义 3 的转述准确；定义要求整个零化理想由三项算子生成，论文排除的是更弱的「存在这样一条递推」，所以足够；推论 5.7 各步无缺口，(s,t)↦(c−s,d−t) 连带符号的行列式都保持；不超过两项的情形补共线点即可；注记 5.8 已按建议补上象限阈值（10-08） |

2026-10-08：18 项全部「AI 一致」，没有发现不一致；作者本人还没有核对任何一项，所以还不满足下面这条。

第三轮（2026-10-08 本地清晨）：作者本人在对话中告知，已亲自核对完毕，结论全部正确（原话「作者本人已经核对完了，都是正确的」）。据此 18 项的结论改记为 ✓，各节「要核对的点」改为已勾选；上面各行备注里 AI 两轮的记录保留，作为过程。至此满足下面这条，论文第 8 节与 AI 声明相应改为「由 AI 模型与作者核对」。本清单只覆盖这 18 项；第 6 行所说其余模块的陈述仍只有 AI 核对。

全部打勾，才能在论文里说「下列陈述在 Lean 中机器检查过」；有任何一项存疑，论文里对应的定理改说「证明已机器检查，陈述的忠实性由作者核对」，并把存疑处写进正文。
