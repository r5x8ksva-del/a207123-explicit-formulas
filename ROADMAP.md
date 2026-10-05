# 路线图：未来要做的事

整理日期：2026-10-06。优先级是整理者（Claude）的判断，不是定论。背景见 `报告.md`、`猜想总表.md` 和 `README.md` 的「当前状态与待办」。

## 1. 先做：Lean 第四轮收尾（有先后顺序）

1. 确认没有别的会话在改 `lean/` 下的文件（`HStruct.lean` 最后一次修改在它编译通过之后）。
2. 重编 `lean/A207123/HStruct.lean`（T5.3），用 `lean/lean_one.sh`（带内存闸门与看门狗，一次只跑一个；单个编译峰值内存 ≥ 8 GB）。通过后登记进 `lean/A207123.lean` 与 `lean/Axioms.lean`。
3. 核对 `NumStruct`、`NearDiag`、`HStruct` 等新文件的定理陈述与报告一致。Lean 只检查证明，不检查「陈述是否忠实」；目前记录里只有 `Poly`、`HNum`、`DFiniteN`、`Parity`、`Coeffs` 做过这项核对。
4. 跑全量 `lean/run_lean_checks.sh`（逐个模块串行构建，再 `Axioms.lean`、`Checks.lean`，输出写入 `logs/lean_build.log`）。
5. 应用报告补丁：`code/main_extra/report_patches/patch_lean4.py`（先加 `--dry` 只检查替换锚点）→ 正式应用 → `code/main_extra/assemble_report.py` 重拼报告。补丁里仍待补的标签：T5.3、00_head、① 第 11 条、⑥、完成度表。
6. 全部完成后，回到 `猜想总表.md` 去掉 † 标记。

## 2. 加固报告里证据最薄的三处（报告 ⑥）

| 项 | 现状 | 下一步 |
|---|---|---|
| T3.8 维数公式 | 书面证明 + 数据；Lean 形式化在 `OreDim.lean`（第四轮，待全量构建） | 核对 OreDim 的陈述；用 k≤100、q≤40 的长方形窗口复核更多盒子 |
| T3.4(2) K(x) 闭式与「I≠𝒮」 | 只经一位复核者；7 点数值核对只在日志里 | 请第二位复核者独立推导 Mellin 表示；把数值核对并入 `verify_all.py`（或改用区间算术） |
| T2.7 推论（非 proper 超几何多重和） | 依赖 Wilf–Zeilberger 1992、Zeilberger 1990，原文没读到 | 读原文并核对前提，或在本文中自证所需的封闭性质 |

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

## 5. 新颖性与外部评审（尚未做）

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
