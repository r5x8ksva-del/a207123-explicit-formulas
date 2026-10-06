# 路线图：未来要做的事

整理日期：2026-10-06；2026-10-07 按 Lean 第四轮收尾更新，同日两次加固报告 ⑥ 后再更新 §2。优先级是整理者（Claude）的判断，不是定论。背景见 `报告.md`、`猜想总表.md` 和 `README.md` 的「当前状态与待办」。

## 1. Lean 第四轮收尾（2026-10-07 已完成）

- 重检了在最后一次通过之后又被改过的 HStruct、NumStruct、NearDiag。HStruct 有一处证明被 10-06 那次修改改坏，已修好并登记。
- 第四轮 15 个模块的主要定理陈述都已对照报告核对（AI 核对），其中发现 T5.3(1) 两处要 k≥1，已补进报告。
- 全量构建通过（`lean/run_lean_checks_direct.sh`；26 个模块加根模块，2649 个声明只依赖三条标准公理）。
- 已应用报告补丁 `patch_lean4.py`、`patch_lean4_fixes3.py` 并重新拼接报告；`猜想总表.md` 已去掉 † 标记。
- 收尾时发现原 `run_lean_checks.sh` 的逐模块构建从未跑通（模块名带回车符），已改正。内存紧时它每一步要先核对 Mathlib 的构建记录（7–10 分钟），所以另写了 `run_lean_checks_direct.sh`。详见 README「过程概览」第 11 条。

## 2. 报告 ⑥：原来的三处与 T2.6(ii) 已加固（2026-10-07），现在的三处待做

原来的三处都已加固，见 `notes/02-主Agent-不确定三处加固.md` 与复核报告 `notes/review/s6-*-review.md`：
- **T4.3(6) 高次系数的一般结构**：有两份路线不同的证明。r-c4ii 由 e.g.f. 闭式展开；s6-t436 由一阶 ODE 的分量递推，不用闭式，并补上了唯一性。构造法 j≤40、拟合法 j≤24 已并入 verify_all（rv3）。
- **T3.4(2) K(x) 的闭式与「I≠𝒮」**：两位复核者各自推导，s6-t342 另给一份路线不同的证明，推论加强为 1<K/Γ(−λ)<2−x，并给出 K 的符号。两套独立的高精度实现已并入 verify_all（rv3）。
- **T2.7 的推论**：读了 WZ 1992 原文，改写为 T2.7′（条件 (N1)(N2)）并自证，只用 T3.7(2)。复核者 s6-t27 审查为 confirmed。

第一次重排后排第 1 的 **T2.6(ii) 截断块部分对一切 m≥2 的统一证明**也已加固：主 Agent 不看复核者 x1 的式子从头重推（`notes/03-主Agent-T2.6(ii)重推.md`），留数闭式与 x1 的逐项一致；独立程序的精确核对已并入 verify_all（rv4，9 条，做过反向检查）。

按现在的证据再次重排的 ⑥（2026-10-07 第二次）：

| 项 | 现状 | 下一步 |
|---|---|---|
| T2.7′（2026-10-07 的新证明） | 只经一位复核者（s6-t27）审查，结论 confirmed；(N2) 依赖被加项的写法，含 C(2j,j) 一类因子的写法不在范围内 | 请第二位复核者审查；如果论文要覆盖 C(2j,j) 一类因子，再核对 s6-t27 提出的 (N2′) 与引理 F′ |
| T3.4(4)(5) 渐近展开的显式误差界、差值门槛 | 作者加一位复核者（r-c3a）；数值只能抽查；(5) 常数项部分的 Stirling 门槛这一轮没有人再核对 | 请复核者独立重推 |
| T4.3(8) 中 b_i 可约（i=4,18,48,…）的情形 | 引用 Szegő 的 Laguerre 零点定理（教科书结果，未重证，原书条款号未核对）；同余与 Laguerre 恒等式有程序核对（q≤20、q≤30） | 在笔记里补上零点定理的标准证明（正交性加变号点计数，几行），或给出原书的准确出处 |

**对论文的含义**（整理者判断）：
- 原来的三处与 T2.6(ii) 现在都可以写进正文。T2.7′ 要连同条件 (N1)(N2) 一起写。
- 现在的三处里，T2.7′ 与 T3.4(4)(5) 写进正文之前，至少再请一位复核者，或请人类专家审阅；T4.3(8) 在论文里直接引用 Szegő 即可（数学论文的常规做法）。

### 2.1 论文准备（2026-10-07 开始）

- **T3.9「U 不是 Kauers 意义下的 Stirling-like」已证明并形式化**（`notes/04-主Agent-U不是Stirling-like.md`，`lean/A207123/NotStirlingLike.lean`）。这回答了新颖性核查里最直接的质疑：T3.8 不是 Kauers 2007 例 5 的特例。从 Kauers 的定义到 Lean 定理的一步是书面论证，只有主 Agent 推导。主 Agent 已对照 Kauers 2007 §2.2 原文：Kauers 要求序列在整个 ℤ² 上被零化（Q·f≡0），比「在象限上零化」更强，所以论证适用（笔记 §3）；投稿前仍请人确认一次。
- **承重定义的人工核对**：`notes/Lean定义核对清单.md`，18 项，要人来勾。
- **英文初稿** `paper/main.tex`：结构与主要证明已写，未编译；`TODO` 列在 README「当前状态与待办」。下一步按价值排序：编译并通读 → 处理 TODO → 请一位人类专家看第 5、6 节（单和不存在、零化理想与 Stirling-like）→ 手动补完 Scholar / WoS / MathSciNet / zbMATH 检索（§5）后定稿相关工作。

## 3. 开放问题（完整清单见 `猜想总表.md` 表 B）

| # | 问题 | 现状 | 优先级 |
|---|---|---|---|
| B1 | h_k(t) 的根全为实数 | 仅数据（k≤150）；常用的根交错路线已被否定 | 高（意义最大，但没有路线） |
| B4 | 一般意义的「不存在更短公式」 | 限定形状内已证；一般情形可能写不成严格定理 | 高 |
| B2 | 两族 u 型和不存在 | 指数绝对值 ≤6000 内无；缺有限性定理 | 中高 |
| B5 | N(k,q) 整体的短公式 | 只有 N^c 完成 | 中高 |
| B10 | 模式数 M(d;σ,β) 的一般闭式 | 4 个族已证 | 中 |
| B7 | F 的 Borel 可和性 / Gevrey-1/3 | 渐近已证，缺 Gevrey 上界与解析延拓 | 中 |
| B8 | U_k 没有其他负整数零点 | k≤70 | 中 |
| B3 | 其余奇数形状的单族和不存在 | 只有浮点证据 | 中 |
| B6 | 只用一元 ₁F₁ 的整表闭式 | 没找到 | 中，计算价值低 |
| B11 | 「二阶 Euler 型」非负展开对一切 d 不存在 | d≤8 | 低–中 |
| B9 | h_k 的符号模式、h_k(−1) 闭式 | 没找到 | 低–中 |
| B12 | U_4=A326247 是否有规范结构；OEIS 只查了 k≤7 | 判断性 | 低–中 |

## 4. 可选：继续扩 Lean（整理者判断：边际价值低）

`GenFun`（T3.1–T3.3、T3.5(3)）、`Blocks`（T2.1、T2.3、T2.8(2)）、`Asymp`（T1.3(4) 渐近、T5.1）、`NoSingleSum`（T2.6）、`Patterns`（T4.2(1)）都没有开始。它们多是分析类（渐近、Laplace / Mellin、₁F₁）或穷举型结论，在 Mathlib 里成本最高。

## 5. 新颖性与外部评审（开放数据库部分已做，2026-10-07；其余待做）

**2026-10-07 更新**（详见 `notes/新颖性核查_2026-10-07.md`，数据在 `data/lit/`，手动检索清单在 `notes/新颖性核查_手动检索清单.md`）：
- 系统检索了 arXiv、OpenAlex、Crossref、StackExchange、OEIS 条目页与 16 篇种子论文的前向引用；Semantic Scholar 仍被限流（55 条里只成功 3 条）。Google Scholar（robots.txt 禁止自动化）、Web of Science、MathSciNet、Scopus（需机构登录）、zbMATH（robots.txt 禁止 Anthropic 的爬虫）**没有查**。
- 纠正 10-06 的一处说法：Dougherty-Bliss–Kauers《Hardinian Arrays》与 Dougherty-Bliss–Spahn《Rectangular Hardinian Arrays》研究的是 king-move 数组（A253026 等），**不是**本家族；它们只是同类工作与同类方法，不是先例。
- 新发现的近先例：Kauers 2007 例 5（Stirling 数的零化子恰由三角递推生成，T3.8 的骨架）、Chyzak–Kauers–Salvy 2009 例 3（Stirling 数不是 ∂-finite）、OEIS A202093 附件（Krause，2026-06-26，与 T1.0 的列规则解耦同一引理）与 A202100（He，2026-06-29）、Dougherty-Bliss–Koutschan–Ter-Saakov–Zeilberger 2024 定理 2（固定 k 的递推存在）。
- 被抢先的风险：同类 Hardin 表在 2026-06 被公开证明；2026 年另有 AI 证 OEIS 猜想的一批预印本。A207118–A207122 目前仍是 Empirical / Conjectures。T1.9 / A15 最易被抢先。
- 同日第二次 arXiv 复查（笔记 §8，`code/novelty/arxiv_recheck.py`，32 条查询，626 篇；另读了 Fried 三篇证 OEIS 猜想论文的全文）：仍没有处理本家族的文章，也没有对非 Stirling-like 递推的零化理想分类或同类的单和不存在论证；同类的 Hardin 表（A250742）2026 年已被证明，被抢先风险不变。Kauers 2007 的零化定义已对照原文（见 §2.1）。
- 待做：手动查 Google Scholar、WoS、MathSciNet、zbMATH（最先查 Kauers 2007 与 CKS 2009 的被引用）；把 Kauers 2007 §3 与 T3.8 逐点对照；找人类专家预审。

**2026-10-06 做过的初步检索**：arXiv、Crossref、OEIS 搜索与本仓库里的 OEIS 快照；Semantic Scholar 被限流、zbMATH 接口不可用，也没有全文检索（Google Scholar、MathSciNet 都没查）。

**检索到什么**
- 没有找到直接讨论这个序列族（A207118–A207123）的论文。OEIS 的相关条目 A207118–A207122、A207069 标为 Empirical；A207118、A326247 有 Colin Barker 的 Conjectures，A207069 有他的 Empirical g.f.；截至 2026-10-04 没有任何一条写着已被证明。
- **前人已有、不属于本仓库新证的内容**：
  - 引理 1 与归约 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋) 来自任务说明（提示词）；
  - U_3 的多项式及「{1..n}³ 中单调三元组」的解释：A084990（Jack Kennedy，2009）；
  - R_k 的递推与母函数：A038718（排列解释 John W. Layman，2000；g.f. Joseph Myers，2004）；
  - r-Stirling 数本身：Broder, *The r-Stirling numbers*, Discrete Math. 49 (1984) 241–259。
- **最近的已知理论（书目信息已用 Crossref 核对存在，原文没有逐篇读过）**：D-finite / holonomic 理论——Stanley, Eur. J. Combin. 1 (1980) 175–188；Lipshitz, J. Algebra 122 (1989) 353–373；Zeilberger, J. Comput. Appl. Math. 32 (1990) 321–368；Wilf–Zeilberger, Invent. Math. 108 (1992) 575–633；Chyzak–Salvy, J. Symb. Comput. 26 (1998) 187–227。Stirling 型数列的非 D-finite 性：Klazar, J. Combin. Theory Ser. A 102 (2003) 63–87。Stirling 多项式：Gessel–Stanley, J. Combin. Theory Ser. A 24 (1978) 24–33。
- 旁证：Crossref 里已有 2026 年的预印本在证明别的 OEIS 递推猜想（例如 doi:10.2139/ssrn.7230244 与 doi:10.2139/ssrn.7176239），说明「证明 OEIS 的经验递推」本身并不稀有。

**不能由此推出什么**：「没找到」不等于「前人没证」，更不等于「有价值」。

**整理者判断**：本仓库用到的方法大多是标准的（部分分式、极点论证、r-Stirling 数、D-finite / Ore 代数理论），新的主要是对象（这个具体的序列族），而不是方法。

**下一步**
- 对外宣称「首次证明」之前，需要人类专家审阅关键定理（至少 T2.4、T2.6、T3.7、T3.8、T4.1），并做一次正式的文献核对（MathSciNet / zbMATH / Google Scholar）。
- 如果要发表：arXiv 等要求人类作者对内容负责，并披露 AI 的使用。

## 6. 仓库维护

- **许可证**：尚未选定（默认保留所有权利）。公开前需要选择；`data/oeis/` 是 OEIS 条目的快照，适用 CC-BY-SA 4.0（见 `data/oeis/NOTICE.md`）。
- **绝对路径**：`code/main_extra/report_patches/patch_*.py` 等脚本里含本机绝对路径，只作历史记录，不能在别的机器上直接运行；`verify_all.py` 用相对路径。
- **中间文件**：`code/review/r-c4i/N_K*.pkl` 不入库（Python pickle，且可重新生成）；需要时先运行 `py -3.14 code/review/r-c4i/s1_build_N.py 100`（也可用 150、200）。
- **可选**：用 GitHub Actions 跑 `verify_all.py`（约 4 分钟，需要 numpy）。Lean 构建需要 elan 与 Mathlib 依赖，单个编译峰值内存 ≥ 8 GB，默认的 runner 可能不够。
- **可选**：把本文第 1–3 节的条目建成 GitHub Issues。
