# A207123 任务 C：U_k(m) 的显式公式、母函数与结构（2026-10-04）

这个文件夹是「任务 C」的完整工作区：最终报告、一键核对脚本，以及全部过程文件。
本任务与同目录下的 `A207123-禁止模式01矩阵计数证明/`、`A207123-全k形态定理证明/`（任务 A、B，由其他会话完成）互相独立，这里没有读写它们的文件（它们不在本仓库中）。

> **状态声明（请先读）**
> - 本仓库的数学内容由 AI（Claude）在人类指导下生成，并经 AI 复核者交叉检查，**没有经过人类专家审稿**。不少定理另有 Lean 4 + Mathlib 机器检查（有的只覆盖一部分，范围见 `猜想总表.md`），但 Lean 只检查证明，不检查「陈述是否忠实于报告」。
> - **新颖性只核实了一半**（2026-10-07）：开放数据库（arXiv、OpenAlex、Crossref、OEIS 等）已系统检索，没有找到同时处理 U_k(m) 的显式公式、最小阶、非 D-finite、零化理想分类的论文；但 T1.0 归约、固定 k 的递推存在、T3.7/T3.8 的方法都有先例（OEIS 上 Krause 2026-06 的同款引理，Kauers 2007 例 5，Chyzak–Kauers–Salvy 2009 例 3）。Google Scholar 已由你在 10-07 手动查过（清单 A 组全部，没有发现先例，见笔记 §9）；**Web of Science、MathSciNet、zbMATH 还没有查**，清单在 `notes/新颖性核查_手动检索清单.md`，结论在 `notes/新颖性核查_2026-10-07.md`。「没找到」不等于「前人没证」，请勿对外宣称「首次证明」。
> - 许可：只有代码采用 MIT（`LICENSE`）；论文、报告与笔记保留所有权利，见文末「许可与数据来源」。
> - 这是进行中的研究仓库，不是定稿：Lean 第四轮已于 2026-10-07 收尾，但没有人类专家审过；报告 ⑥ 列出最不确定的三处（2026-10-07 加固了原来的三处与随后排第 1 的 T2.6(ii)，两次重新排序），见「当前状态与待办」。

## 这是什么

研究 OEIS A207118–A207123 一族的计数问题：n×k 的 0/1 矩阵，行不含 001 与 010，列不含 001 与 011。已知 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋)，其中 U_k(m) 是高度序列 (h_1,…,h_k)∈{0,…,m}^k 的个数，要求每个相邻三元组 (a,b,c) 满足「b=c 或 a≥max(b,c)」。本仓库（「任务 C」）研究 U_k(m) 这张二维表：显式公式、母函数、D-finite 判定、近对角线、渐近与结构。

**主要结果**（等级与证据见 `报告.md`；每个猜想的结局、意义与完成度见 `猜想总表.md`）：
- 引理 1（三项递推）与任务说明里的 (C1)–(C8) 全部独立重证；
- 全正项两层显式公式（Stirling / r-Stirling 数 × 二项式），带块分解的组合解释；
- 关于 k 的最小递推阶对一切 m 恰为 3m+1；增长率与 c_m 的闭式；
- 不存在「Stirling×二项式」单和；F(x,t) 与 N(x,y) 的母函数都不是 D-finite；全部多项式系数递推恰为引理 1 生成的左理想，由此 U 不是 Kauers 意义下的 Stirling-like；
- N(k,k−d) 对 k≥2d+2 是 2d 次多项式（门槛精确）；固定 q 的分子有一般公式；
- （2026-10-08 并入论文，报告尚未更新）h_k 的根全为实数且互异，N 的每一行严格对数凹、单峰，h_k 恰有 ⌊k/3⌋ 个根大于 1；单族二项式形状 C(k+c−αs, βs+d)（α,β≥0）中只有 α+β=1 能表示 U；m≥2 时 U 不是两个 (2,1) 形状单和之和（计算机辅助证明，模 5040 的筛法加 l 进论证）；
- Lean 4 + Mathlib 形式化：原题归约、引理 1、最小阶、二项式基、显式公式、非 D-finite、左理想刻画及其维数公式、近对角线、分子结构、h_k 的结构、「不是 Stirling-like」等，共 27 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`），2675 个声明只依赖三条标准公理；各条的覆盖范围见报告标签与 `猜想总表.md`，承重定义的人工核对清单见 `notes/Lean定义核对清单.md`。
- 英文论文初稿：`paper/main.tex`（LaTeX，2026-10-07 写成完整初稿，用 Tectonic 0.17 编译通过，`paper/main.pdf` 是编译结果；文中 TODO 需要你决定或核对）。 2026-10-08 并入表 B 的 A19–A21（第 8 节、定理 6.3、第 6.2 节），现 35 页。

**如何复现**
- Python 核对：`py -3.14 verify_all.py`（约 4.5 分钟，需要 numpy），逐条打印 PASS/FAIL；最后一次全量运行 14 个模块、332 PASS、0 FAIL（本地 2026-10-08 加入表 B 的模块 tb 之后，`logs/verify_all_final.log`，485 s，峰值 431 MB；加入前的最终日志另存为 `logs/verify_all_final_2026-10-07_before_tb.log`）。想带内存保护运行（本机常有别的任务同时在跑）：`code/main_extra/run_guarded.sh logs/<输出>.log py -3.14 verify_all.py`，实测整棵进程树峰值约 0.4 GB。
- Lean：工具链 `leanprover/lean4:v4.34.1`，依赖 Mathlib `v4.34.1`（见 `lean/lakefile.toml`、`lean/lake-manifest.json`）。作者在 Windows 上用 `lean/run_lean_checks_direct.sh` 构建（逐模块 `lake build` 的版本是 `run_lean_checks.sh`），没有在别的环境验证过；单个编译峰值内存 ≥ 8 GB。`lean/.lake/`（Mathlib 依赖与编译产物，约 5–7 GB）不在仓库里，需要自己用 `lake` 获取。
- `code/review/r-c4i/N_K*.pkl` 是可重新生成的中间文件，不在仓库里，见 `ROADMAP.md` §6。

## 先看这几个

| 文件 | 内容 |
|---|---|
| `报告.md` | 最终报告：结论摘要、定理清单（陈述/证明/核对范围/等级）、推荐显式公式、失败方向、代码与输出、最不确定的三处、C-1…C-5 完成度 |
| `verify_all.py` | 一键核对：`py -3.14 verify_all.py`（空闲时约 4.5 分钟，机器负载高时更长；需要 numpy，rv2 模块没有纯 Python 回退），逐条打印 PASS/FAIL，最后给出总表；任何 FAIL 时退出码为 1 |
| `猜想总表.md` | 把所有「原本是猜想、未证或待判断」的命题分成已证明 / 尚未证明 / 已否定三张表，每条给出意义与完成度（2026-10-06 整理，2026-10-07 更新） |
| `ROADMAP.md` | 未来要做的事：报告 ⑥ 的三处（原三处与 T2.6(ii) 2026-10-07 已加固，现在的三处待做）、开放问题的优先级、新颖性与外部评审（开放数据库部分已做，其余待做）、仓库维护（Lean 第四轮已于 2026-10-07 收尾） |

## 目录

| 路径 | 内容 |
|---|---|
| `code/core.py` | 公共底座：按第 1 节原始定义实现的全部「真值」程序（参考实现 U_list、后缀和高度 DP、多重链、原题矩阵直接计数、暴力、N 的 DFS/容斥、Stirling、h_complete） |
| `code/polylib.py` | Fraction 精确多项式与截断幂级数 |
| `code/checks/check_*.py` | verify_all 调用的 13 个正式核对模块（c0 主 Agent 补充；c1 复核；c2a/c2b 显式公式；c3a/c3b 母函数与 D-finite；c4 近对角线与分子；c5a 渐近与 h_k；c5b OEIS；rv 第二轮复核的产物；rv2 复核者 x1 的两个独立脚本；rv3 报告 ⑥ 原两处所依赖的复核者脚本，来自 r-c4ii、r-c3a、s6-t436、s6-t342，2026-10-07 加入；rv4 主 Agent 独立重推 T2.6(ii) 的精确核对，不导入 core，2026-10-07 加入） |
| `code/<area>/` | 各方向的探索脚本 |
| `code/family/` | 2026-10-06 补充：OEIS 里列规则同为「竖向禁止 001、011」的 6 张 Hardin 表都满足同一归约（`check_family.py`、OEIS 只读快照与日志，见其中 README）；另外 5 张表的结构没有研究 |
| `code/novelty/` | 2026-10-07 新颖性核查的脚本：`lit_search.py`（55 条查询，经 arXiv / OpenAlex / Crossref / Semantic Scholar / StackExchange 的官方接口，只读）、`cited_by.py`（16 篇种子论文的前向引用）、`check_note_refs.py`（核对笔记里的 arXiv 号、DOI、OEIS 编号都有数据支持，做过反向检查）、`check_note_facts.py`（核对笔记里的数字与 OEIS 关键事实能由仓库数据重新证实，不联网）；`scholar_followup.py`（10-07：对你贴来的 Google Scholar 结果里新出现的几条，用 Crossref / OpenAlex 核对书目与摘要，原始返回在 `data/lit/raw_scholar_followup/`）；用法见 `data/lit/README.md` |
| `code/tableB/` | 2026-10-07 晚：表 B 新结论的精确核对——`check_b1.py`（10 条：行多项式递推、交错关系 k≤40、公因子与根 k≤60、根的分布、U_k(−j) 的变号次数、反向检查）、`check_b3.py`（5 条：Q(ξ) 中的精确事实、1800 个线性方程组、反向检查）、`check_b7.py`（5 条：递推、显式上下界 k≤300）；入口 `run_all.py`（20 条全部 PASS，峰值约 0.4 GB，约 20 秒，日志 `logs/tableB_*.log`）；`explore/` 是找交错关系时的探索脚本。2026-10-08 加入 `check_b2.py`（12 条：留数公式在 K_i 中精确成立、模 5040 的筛法与 l 进证书、m=1 与 E_2 的两族表示作正向对照、负对照）、`check_b7_borel.py`（6 条，数值佐证：边界估计、反函数、旋转射线一致、与级数比较、t<−1 时的 Gevrey 增长）、`check_b11.py`（3 条：d≤100 的计算机辅助证明与 Stirling 数的反向检查）；`run_all.py` 现在跑 6 个部分（41 条全部 PASS，约 3 分钟，主要是 check_b11）；`explore/` 里新增 B2 的纤维与筛法原型、B11 的根方差与缺陷值探索。2026-10-08 又加入 `check_b6.py`（8 条：B6 的结构定理在 13 个有理 x 上精确成立并对照原始定义 DP、算子恒等式与 Φ_1 改写、RK4 单值群与 λ 为负整数时 Ei 闭式的数值佐证、四项反向检查），`run_all.py` 加上 b6 后跑 7 个部分（49 条全部 PASS）。需要 numpy（找近似根与筛法的向量化，判定全是精确运算）。暂未登记进 verify_all（那里仍是 13 个模块、305 PASS） |
| `code/review/<reviewer>/` | 第二轮对抗性复核者的独立脚本；`s6-*` 是 2026-10-07 加固报告 ⑥ 的第三轮复核者（s6-t436、s6-t342、s6-t27）；`main-t26ii/` 是主 Agent 重推 T2.6(ii) 时写的独立核对脚本（不导入 core、不复用 x1 的脚本）；`s8-b1/`、`s8-b3/` 是 2026-10-07 晚表 B 新证明（B1、B3）的复核者脚本；`s9-b2/`、`s9-b7/` 是 2026-10-08 表 B 新证明（B2、B7 后半）的复核者脚本；`s11-b6a/`、`s11-b6b/` 是 2026-10-08 表 B 的 B6 的两位复核者脚本 |
| `code/main_extra/` | 主 Agent 的辅助脚本（最小阶逐因子检验、结果汇总）；`assemble_report.py`（拼接报告并交叉检查核对 id）；`report_patches/`（报告补丁脚本，Lean 标签补丁是 `patch_lean*.py`，第四轮的 `patch_lean4.py`、`patch_lean4_fixes3.py` 已于 2026-10-07 应用；同日加固 ⑥ 后的同步补丁是 `patch_six.py`，重推 T2.6(ii) 后的是 `patch_t26ii.py`，加入 T3.9 后的是 `patch_stirlinglike.py`，都已应用）；`check_tex.py`（没有 TeX 编译器时检查 `paper/*.tex` 的环境、括号、$、标签与文献引用，做过反向检查）；`check_paper_numbers.py`（2026-10-07：从 `core.py` 的原始定义重算论文里印出的每一个数，并解析 `paper/main.tex` 里的表格比对，做过反向检查）；`lean_statements.py`（从 Lean 文件里只抽出文档注释、定义与定理陈述，便于人工核对陈述是否忠实于报告）；`md_to_pdf.py`（2026-10-07：把 `notes/` 里的 Markdown 用本机 Edge 无头模式转成 PDF，中文用微软雅黑、链接可点；本机没有给 .md 关联打开程序，给你看的笔记用它转）；`run_guarded.sh` + `proc_watchdog.ps1`（非 Lean 任务的内存保护：机器上有 lean.exe 或内存余量不够就不启动，运行中整棵进程树超限就结束，每次记一行到 `logs/guarded_runs.log`；2026-10-07 起内存查询失败时改用备用数据源，连续 5 秒都读不到才结束；Lean 仍只走 `lean/lean_one.sh`） |
| `code/step0_baseline.py`、`step1_quickcheck.py` | 开工时的基线核对与主线推导快速核对 |
| `notes/原始任务说明.md` | 用户给出的任务原文 |
| `notes/新颖性核查_2026-10-07.md`、`notes/新颖性核查_手动检索清单.md` | 新颖性核查的结论（逐项对照、最近先例、被抢先风险、检索盲区、下一步）与给用户手动在 Google Scholar / WoS / MathSciNet / zbMATH / Scopus 里跑的检索式 |
| `notes/00-主线推导与分工.md` | 主 Agent 开工时的推导草稿与协作规则（其中两处后来被证明有误，见报告 ④） |
| `notes/01-主Agent补充.md` | c_m 闭式等补充推导 |
| `notes/02-主Agent-不确定三处加固.md` | 2026-10-07 加固报告 ⑥ 原来的三处：逐步重推 T4.3(6)、T3.4(2) 的复核证明；把 T2.7 的推论改写为 T2.7′ 并自证 |
| `notes/03-主Agent-T2.6(ii)重推.md` | 2026-10-07 主 Agent 不看复核者 x1 的式子，从头重推 T2.6(ii)（截断块部分对一切 m≥2 没有 u 型单和）：完整证明、另一条更初等的路线、与 x1 的逐项对照 |
| `notes/04-主Agent-U不是Stirling-like.md` | 2026-10-07 新增的 T3.9：Rel(U) 的非零元支撑里有二倍面积 ≥3 的三点，所以 U 不是 Kauers 意义下的 Stirling-like；证明、读 Kauers 定义时的注意点、Lean 形式化记录 |
| `notes/05-主Agent-表B-B1-h_k实根性.md` | 2026-10-07 晚：`猜想总表.md` 表 B 的 B1 的证明——h_k 的根全为实数且两两不同（换到 z=t/(1−t) 看 N 行多项式，四条交错关系在递推 n_k=(1+z)n_{k−1}+Φn_{k−3} 下封闭）；推论：N(k,·) 严格对数凹、单峰，h_k 在 (1,∞) 恰有 ⌊k/3⌋ 个根、系数恰变号 ⌊k/3⌋ 次，「不同取值个数」满足中心极限定理 |
| `notes/06-主Agent-表B-B3单族形状分类.md` | 2026-10-07 晚：表 B 的 B3 加强为完整分类——单族形状 C(k+c−αs, βs+d) 的表示对每个 m≥1 存在当且仅当 α+β=1（新步骤：纤维上全部点的乘积给出 ξ 的非零次幂为有理数的矛盾） |
| `notes/07-主Agent-表B-B7-Gevrey上界.md` | 2026-10-07 晚：表 B 的 B7 前半——f_k(t) 在单位圆盘紧子集上一致的 Gevrey-1/3 上界（常数显式）与 t∈(0,1) 的同阶下界（t<0 时的 Borel 可和性 2026-10-08 在 notes/09 证明） |
| `notes/08-主Agent-表B-B2-两族u型和.md` | 2026-10-08：表 B 的 B2 的证明——U 对每个 m≥2、截断块 E 对每个 m≥3 都没有两族 u 型表示（纤维条件与 m 无关；模 5040 的筛法加 l 进导数排除全部 (n,b)）；推论：u 型最少族数 U 为 1、2、3（m=0、1、≥2），E 为 1、2、3（m=1、2、≥3） |
| `notes/09-主Agent-表B-B7-Borel可和.md` | 2026-10-08：表 B 的 B7 后半——对每个 t<0，积分 I 解析延拓到张角 >π/3 的扇形并有一致的 Gevrey-1/3 渐近，所以 F 在 x 方向 3-可和、和就是 I；推论：每个 t<0 都有 Gevrey-1/3 上界 |
| `notes/10-主Agent-表B-B11-平移范围.md` | 2026-10-08：表 B 的 B11 的部分结果——非负展开只可能出现在平移 [d−1,3d−1]，计算机辅助证明扩到 d≤100；一般 d 为什么还证不下来 |
| `notes/11-主Agent-表B-B6-一元合流函数闭式不存在.md` | 2026-10-08：表 B 的 B6 的否定解答——固定 x 后 F 关于 t 的单值群在 t=0、1 处不是虚交换的（λ=(1−x)/x³∉Q 时），而一元 ₁F₁、不完全 Gamma 等以 t 的代数函数为自变量拼出的表达式都是虚交换的，所以整表没有这样的有限闭式；附带只含一个 Humbert Φ_1 的闭式与 λ 为负整数时的 Ei 闭式 |
| `notes/Lean定义核对清单.md` | 给人读的一页：几个承重的 Lean 定义（U、原题矩阵、D-finite、k-only 递推、Rel(U)、新加的 det2）原文与数学含义并排，列出要核对的点；Lean 只检查证明，不检查定义是不是想说的意思 |
| `paper/main.tex` | 英文论文完整初稿（LaTeX，amsart，2026-10-07）：引言与相关工作；归约、引理 1 与 N 三角；最小递推阶与两项渐近；块分解、显式公式与双射；非 D-finite、象限递推的左理想（含维数与饱和性）、不是 Stirling-like；更短公式不存在（单族单和、其他形状、proper 超几何多重和）；近对角线；Lean 表与定义附录；开放问题；AI 使用声明。证明都已写全。用 Tectonic 0.17 编译通过（`paper/main.pdf`），结构检查 `check_tex.py`、数字核对 `check_paper_numbers.py` 都通过；`TODO` 处要你决定或核对 |
| `notes/交接提示词_Lean形式化续作.md` | 第二轮 Lean 续作的交接提示词（历史文件：其中列的任务都已完成，现状见「当前状态与待办」） |
| `notes/<area>.md` | 第一轮 8 个方向的完整证明笔记 |
| `notes/review/` | 第二轮复核：`claims_<area>.md`（第一轮结论清单）与 `<reviewer>-review.md`（逐条 verdict）；第三轮审计的输出在 `logs/phase3_audit_output.json` 与 `logs/audit_*.log`；`s6-*-review.md` 是 2026-10-07 加固 ⑥ 的复核报告（T4.3(6)、T3.4(2) 的独立重推，T2.7′ 的审查）；`s8-b1-review.md`、`s8-b3-review.md` 是 2026-10-07 晚表 B 新证明（B1 实根性、B3 形状分类）的对抗性复核（都是 confirmed with minor gaps，缺口都是表述，已改）；`s9-b2-review.md`、`s9-b7-review.md` 是 2026-10-08 表 B 新证明（B2、B7 后半）的对抗性复核；`s11-b6a-review.md`、`s11-b6b-review.md` 是 2026-10-08 表 B 的 B6 的两位对抗性复核（都是 confirmed with minor gaps，意见已采纳） |
| `notes/report_parts/` | 报告的分节源文件（`报告.md` 由它们拼接） |
| `data/oeis/` | OEIS 只读快照（68 次 curl）与 `INDEX.md` 查询记录；许可与署名见 `NOTICE.md`（CC-BY-SA 4.0） |
| `data/lit/` | 新颖性文献检索的数据（原始返回、合并候选、查询审计、前向引用、精读论文的来源与哈希、2026-10-07 的 OEIS 条目页）；说明见 `data/lit/README.md`。`data/oeis/` 保持 68 个快照不动，因为 `check_c5b.py` 要求如此 |
| `lean/` | Lean 4 + Mathlib 形式化（从原始定义出发，只依赖三条标准公理）：原题归约与多重链表述（T1.0）、引理 1（T1.1）、gcd(W_m,P_m)=1 与最小递推阶恰为 3m+1（T1.3）、二项式基与 N 的三角递推（T1.4）、按上升数细化的引理 1 与两个显式公式（T2.2、T2.4）、F 不是 D-finite（T3.7(1)，含 D-finite 的定义与引理 D1）与没有 k-only 象限递推（T3.7(2)）、U 与 N 的全部多项式系数象限递推恰为 L1、L_N 生成的左理想（T3.8 的 Rel(U)=O_U·L1、Rel(N)=O_N·L_N，含饱和引理）；第四轮又新增 15 个模块（Poly、HNum、DFiniteN、NoKOnlyN、OreDim、Gosper、Growth、SmallK、Parity、NPDE、Coeffs、HGen、NumStruct、NearDiag、HStruct），2026-10-07 又加入 `NotStirlingLike`（T3.9），`lean/A207123/` 下共 27 个文件，全部登记在 `A207123.lean`；前 26 个 2026-10-07 全量构建通过，`NotStirlingLike` 之后单独编译，并重编根模块、重跑 `Axioms.lean` 与 `Checks.lean`；全量构建用 `./run_lean_checks.sh`（按依赖顺序逐个模块 `lake build +A207123.X`，再 `lake env lean Axioms.lean`、`lake env lean Checks.lean`，输出写入 `logs/lean_build.log`），内存紧时用 `./run_lean_checks_direct.sh`（同样三步，但第 1 步直接用 `lake env lean -o` 从源码逐个编译，不经 lake 的构建记录核对；2026-10-07 用的是它，约 22 分钟），单个文件一律用 `./lean_one.sh A207123/X.lean`（带内存闸门与看门狗，一次只跑一个；单个编译峰值 ≥8 GB，本机 16 GB，Lean 编译曾两度耗尽虚拟内存导致重启）；`.lake/` 下是 Mathlib 依赖与编译产物（约 5–7 GB，可整体删除后用 `lake update` 重新获取） |
| `logs/` | 全部运行日志，包括四轮工作流的原始返回值（`phase1_workflow_output.json`、`phase2_review_output.json`、`phase3_audit_output.json`、`phase4_final_audit_output.json`、`phase4b_recheck_output.json`）与 verify_all 的完整输出（`verify_all_final.log` 是 2026-10-07 加入 rv4 之后的最新一次，13 个模块 305 个 PASS，报告的核对 id 交叉检查以它为准；同日加入 rv4 之前的一次（12 个模块 296 个 PASS）另存为 `verify_all_final_2026-10-07_before_rv4.log`；2026-10-05 的一次另存为 `verify_all_final_2026-10-05.log`，其中 290 个 PASS 的 id 全部仍在新日志里；`verify_all_2026-10-07.log` 是当天早些时候修好 `c5b.snapshots` 后的那一次）；`rv3_*.log` 是 rv3 调用的复核者脚本的完整输出，`s6_red*_rv3.log` 是 rv3 的反向检查（故意改坏复核者脚本，确认会报 FAIL）；`rv4_main_t26ii.log` 是 rv4 子脚本的完整输出，`main_t26ii_check_reverse.log` 是它的反向检查（把留数闭式的常数改成 2 倍，确认报 FAIL）。注意：rv3 调用的 `r6_structure.py` 每次运行都会重写复核日志 `review_r-c4ii_r6_structure.log`，内容不变，只有 runtime 一行会变；rv2 同样会重写 `rv2_x1_*.log`；`guarded_runs.log` 记录经 `run_guarded.sh` 运行的任务（时间为 UTC）；`lean_build.log` 是最新的全量构建日志（2026-10-07，含第四轮；第三轮的另存为 `lean_build_round3_2026-10-05.log`），`lean_recheck_2026-10-07.log` 是收尾时单独重检 HStruct、NumStruct、NearDiag 的记录，`lean_mem.log` 记录每次 Lean 编译的峰值内存与退出码（该文件的时间是 UTC，本机是 UTC+8）；`lean_notstirling_run1.log`（新模块第一次编译，1 处错误）、`lean_notstirling_run2.log`（改正后通过）、`lean_root_2026-10-07.log`、`lean_axioms_2026-10-07.log`、`lean_checks_2026-10-07.log` 是 2026-10-07 加入 `NotStirlingLike.lean` 后的记录 |

## 过程概览

1. 建文件夹，跑通参考实现，用三种独立方法（高度 DP、多重链、原题直接计数）核对第 2 节数据（`logs/step0_baseline.log`）。
2. 主 Agent 独立重证引理 1，发现「块分解」与 G_m = W_m/P_m，写成 `notes/00-主线推导与分工.md`，并快速核对（`logs/step1_quickcheck.log`）。
3. 第一轮工作流：8 个方向并行（C-1 复核；C-2 代数/组合两路；C-3 母函数/D-finite 两路；C-4；C-5 渐近/OEIS 两路），各自写证明笔记与核对模块。
4. 第二轮工作流：11 个对抗性复核者逐条复核第一轮全部结论（其中两个专门深挖「单和不可能」与「非 D-finite」），并据此修正。
5. 第三轮工作流：3 个审计者分别用独立程序重算报告里的公式、核对报告与核对模块/笔记是否一致、逐项检查交付要求；据此修订报告，并把第二轮的反例与复核者 x1 的脚本并入核对（rv、rv2 模块）。
6. 第四轮工作流：最终对抗审计（5 个审计方向，各配一个反驳验证者，确认 58 条），修订后再由 2 个复查者各配验证者复查一遍；据此再修订报告（`logs/phase4_final_audit_output.json`、`logs/phase4b_recheck_output.json`，补丁脚本在 `code/main_extra/report_patches/`）。
7. 整合报告，运行 verify_all.py 做最终核对。
8. Lean 形式化（2026-10-05）：第一轮形式化引理 1、原题归约与 T2.4 主公式；第二轮扩充到 T1.0(c)、T1.3(1)(2)、T1.4、T2.2 的细化引理 1、T2.4 第二式、T3.7(1) 的 ODE 部分与 T3.7(2)（两个子 Agent 分别写了 `Recurrence.lean`、`Ascent.lean`），第三轮（同日）补完 T3.7(1) 的最后一步（D-finite 的定义与引理 D1，子 Agent 写 `DFinite.lean`），并形式化 T3.8 的 Rel(U)=O_U·L1（`OreRel.lean`）与 Rel(N)=O_N·L_N、饱和引理（`OreRelN.lean`，搬运步骤改用二项式变换 V=P·N 在数组上直接做）。报告各条等级标签已注明定理名（补丁脚本 `code/main_extra/report_patches/patch_lean.py`、`patch_lean2.py`、`patch_lean3.py`），构建与公理检查输出在 `logs/lean_build.log`。
9. Lean 第四轮（2026-10-05 至 10-07）：新增 15 个模块（见上表 `lean/` 一行）。期间 Lean 编译两度耗尽虚拟内存导致重启（本地 10-05 11:08：三个 lean.exe 同时占用 19.6 + 8.1 + 8.0 GB；22:46：单个 lean.exe 涨到 23.9 GB），之后加了串行锁、内存闸门和看门狗（`lean/lean_one.sh`、`lean_watchdog.ps1`、`mem_status.ps1`）。
10. 2026-10-06 整理：新增 `猜想总表.md`；README 与 Obsidian 项目记忆页同步到当前状态；没有移动或删除任何文件——报告、补丁脚本和 `assemble_report.py` 里有大量路径引用（核对 id、日志路径），搬动会让引用失效。
11. 2026-10-07 收尾：
    - 修好 `c5b.snapshots`（上传时加入的 NOTICE.md 让它 FAIL），带内存保护重跑 verify_all（290 PASS）；新增 `code/family/`（同列规则 6 张表的归约核对）与 `code/main_extra/run_guarded.sh`。
    - 核对第四轮剩下 10 个模块的定理陈述（全部 15 个模块都核对过了），发现 T5.3(1) 两处要 k≥1，已补；修好 HStruct 里 10-06 改坏的一处证明并登记。
    - 发现原 `run_lean_checks.sh` 的逐模块构建从未跑通（模块名带回车符，Lake 报 unknown target），已改正；内存紧时 lake 每一步核对构建记录要 7–10 分钟，另写 `run_lean_checks_direct.sh`。
    - 全量构建通过：26 个模块加根模块，2649 个声明只依赖三条标准公理。之后应用报告补丁 `patch_lean4.py`、`patch_lean4_fixes3.py`，重新拼接报告，并同步 `猜想总表.md`。
12. 2026-10-07 加固报告 ⑥ 原来的三处（`notes/02-主Agent-不确定三处加固.md`）：
    - 主 Agent 逐步重推 T4.3(6)（r-c4ii 的定理 R2）与 T3.4(2)（r-c3a 的命题 R1）的证明。
    - 三位第三轮复核者，结论都是 confirmed：
      - s6-t436 独立证明 T4.3(6)：不用 e.g.f. 闭式，并补上 R2 没写的唯一性论证；
      - s6-t342 独立推导 T3.4(2)：另给一份路线不同的证明，并把推论加强为 1<K/Γ(−λ)<2−x，给出 K 的符号；
      - s6-t27 审查新的 T2.7′。
    - 读了 Wilf–Zeilberger 1992 原文。把 T2.7 的推论改写为 T2.7′（条件 (N1)(N2)），只用 T3.7(2) 自证，不再依赖 Zeilberger 1990 与 Bernstein 消元。
    - 新增核对模块 rv3（6 条，调用 r-c4ii、r-c3a、s6-t436、s6-t342 的脚本，做过反向检查）；全量 verify_all：12 个模块 296 PASS。
    - 报告 ⑥ 重排为 T2.6(ii)、T2.7′、T3.4(4)(5)，同步补丁是 `patch_six.py`；报告引用的 238 个核对 id 全部 PASS。
    - 修好内存保护脚本的一个缺陷：内存查询失败时会被当成余量为 0，误杀任务（s6-t342 一个只用 23 MB 的任务因此被结束）。`proc_watchdog.ps1`、`lean_watchdog.ps1`、`mem_status.ps1` 改为失败时用备用数据源，连续 5 秒都读不到才结束。
13. 2026-10-07 新颖性核查（开放数据库部分）：结论在 `notes/新颖性核查_2026-10-07.md`，数据与脚本在 `data/lit/`、`code/novelty/`，见 `ROADMAP.md` §5。
14. 2026-10-07 主 Agent 独立重推 T2.6(ii)（`notes/03-主Agent-T2.6(ii)重推.md`）：
    - 不看复核者 x1 的式子，从头推出留数闭式 Res_η E_m·u′(η)=(−1)^{m−i+1}(W̃_i(η)−1)η^{−3m−3}/((m−i)!·i!·i²)，最后对照，与 x1 的逐项一致；
    - 写了不导入 core、不复用 x1 脚本的精确核对 `code/review/main-t26ii/check_t26ii.py`（9 条，反向检查按预期报 FAIL），并入 verify_all 为 rv4；全量 verify_all：13 个模块 305 PASS；
    - 报告 ⑥ 第二次重排为 T2.7′、T3.4(4)(5)、T4.3(8)，同步补丁是 `patch_t26ii.py`；报告引用的 247 个核对 id 全部 PASS。
15. 2026-10-07 接着做了另外三件事：
    - T3.9「U 不是 Kauers 意义下的 Stirling-like」：证明 Rel(U) 的非零元支撑里总有二倍面积 ≥3 的三点（`notes/04-主Agent-U不是Stirling-like.md`），在 Lean 中形式化为 `NotStirlingLike.lean`。第一次编译有 1 处错误，改正后通过；根模块重编，`Axioms.lean` 256 条全部只依赖三条标准公理，全量扫描 2675 个声明，`Checks.lean` 通过。报告补丁 `patch_stirlinglike.py`，顺带把 ① 里过时的「11 个模块」改成 13 个。
    - `notes/Lean定义核对清单.md`：承重定义的原文与数学含义并排，给你逐项打勾。
    - 英文论文初稿 `paper/main.tex`。本机没有 TeX，未编译；`code/main_extra/check_tex.py` 的结构检查通过（反向检查：故意改坏的副本报出 5 处问题）。
    - 初稿交给一个独立 Agent 对照报告逐条审查，并用自写程序数值抽查。主要定理与报告一致，抽查全部通过。它指出 7 处问题，都在证明、措辞或元信息里，已全部改正：推论 6.5 缺「位移点两两不同」（主 Agent 已先发现，同时改了报告 T3.9 与笔记）；定理 6.1 证明里 G_{−1} 的约定写错；命题 6.4 第二句重复用了 p_i；「未形式化」清单不全；「305 条精确核对」不准（少数是高精度十进制数值）；「内层和」应为「对 j 的和」；「不是 Stirling-like」少了对 Kauers 定义读法的说明。小问题也已处理：H(m,−1,j)=0、摘要补 m≥1、ρ_0=1、全局二项式约定、记号冲突、作者栏、正文去掉中文字符。
16. 2026-10-07 第二次 arXiv 复查（`notes/新颖性核查_2026-10-07.md` §8）：`code/novelty/arxiv_recheck.py` 用 arXiv 官方 API 跑了 32 条查询（19 条按日期取最新，看被抢先风险；13 条针对 T3.9、T3.8、T2.6、T2.4、T4.1），取回 626 篇，并读了 Fried 三篇证 OEIS 猜想论文的全文。没有发现处理本家族的文章；Hardin 的另一张二进制矩阵表 A250742 已在 2026 年被证明，被抢先风险不变。同时对照 Kauers 2007 §2.2 原文：他要求序列在整个 ℤ² 上被零化，比「在象限上零化」更强，所以 T3.9 的论证适用（补丁 `patch_kauers_reading.py`，论文与笔记同步改了）。记录：export.arxiv.org 的 robots.txt 写的是 `Disallow: /`，与 arXiv API 文档的指引不一致，两次检索都按 API 文档的间隔执行。

17. 2026-10-07（本地约 08:45–10:05）论文写成完整初稿（你的要求：「现在开始写论文初稿」，输出 LaTeX）：
    - `paper/main.tex` 在早上的骨架上扩成完整初稿（26 页）：梗概证明全部写全；新增两项渐近（定理 3.2）、列的最小阶的完整证明与 OEIS 行列递推（推论 3.4、注记 3.5）、块分解例子、m=1 的显式式、竖线—集合划分双射（命题 4.7）、两种等价公式（注记 4.9）、(1,2)(2,3) 形状（命题 6.3）、T2.7′（§6.2）、Gosper 不可和（命题 6.10）、Newton 系数为正（命题 7.2）、N(k,q) 表与门槛以下例外值表、Lean 定义附录。参考文献的卷号页码用 Crossref 核对补齐。报告里没有的只有推论 5.5（有理系数的零化算子也是 L₁ 的左倍式；左理想 𝒪L₁ 饱和）。
    - 编译：经你同意装了 Tectonic 0.17.0（官方 GitHub 发布的 Windows 版，SHA-256 与 GitHub 记录一致，装在 `%LOCALAPPDATA%\Programs\tectonic`，没改 PATH）。编译无错误、无溢出、无未定义引用，`paper/main.pdf` 是结果，编译日志 `logs/main_tex_2026-10-07.log`。
    - 数字核对：新脚本 `code/main_extra/check_paper_numbers.py` 从 `core.py` 的原始定义重算论文里印出的每一个数并解析 .tex 里的表格比对，26 PASS（`logs/check_paper_numbers_2026-10-07.log`）；改坏 5 个数的副本报 5 FAIL（`logs/check_paper_numbers_reverse_2026-10-07.log`）。
    - T2.7′ 的第二位复核者 s7-t27：confirmed with minor gaps，唯一的问题是适用范围有一句说过了头（反例 C(2j,j)C(m,j−k)），论文、笔记 02、报告已改正（补丁 `patch_t27_second_review.py`，重新拼接后报告引用的 247 个核对 id 全部 PASS）。记录 `notes/review/s7-t27-review.md`，脚本 `code/review/s7-t27/`。
    - 全文独立审稿（Opus 子 Agent）：没有发现数学错误；指出 Lean 表一处说过头（\|σ\|²<ρ²_{m−1} 没有形式化）、附录首句说过头、推论 5.5 原来的说法夸大（已改写成真正有内容的版本）、若干缺条件与记号冲突，全部已改。记录 `notes/review/paper-draft-review-2026-10-07.md`，脚本 `code/review/paper-draft-2026-10-07/`（在仓库里重跑，日志 `logs/review_paper-draft_*.log`）。
    - 收尾核对（本地约 10:05–10:15）：重跑 `check_tex.py`、`check_paper_numbers.py`（26 PASS）、Tectonic（编译到临时目录：26 页，日志里 0 个警告，PDF 文字与 `paper/main.pdf` 完全相同）、`assemble_report.py`（247 PASS，`报告.md` 不变）。发现 s7-t27 的 `run_t27.py`、`run_n2.py` 要带例子参数，第一次在仓库重跑时漏了（`run_n2` 的日志是空文件），已带全部参数补跑，命令写进了审稿记录；`s4b.py` 一处输出标注（应为 k≤9、m=4）改正后重跑。

18. 2026-10-07（本地约 12:20–13:00）处理你贴来的 Google Scholar 结果（清单 A 组全部）：
    - 原样保存在 `data/lit/manual_scholar_2026-10-07.md`；分类与结论写进 `notes/新颖性核查_2026-10-07.md` §9：没有找到处理本家族的文章，也没有找到对非 Stirling-like 递推做零化理想分类的文章，新颖性判断不变（有条件、中等）。新出现的几条用 `code/novelty/scholar_followup.py` 经 Crossref / OpenAlex 核对，Kitaev–Mansour–Vella 2005 在 JIS 官网核对。笔记的两个核对脚本重跑全部通过。
    - 论文：相关工作补引 Kitaev–Mansour–Vella 2005、Dougherty-Bliss–Spahn 2024、Kauers 2023 的书，Formal verification 补引 Mahboubi–Sibut-Pinote 2021（Coq 形式化 Apéry），文献检索的 `\todo` 改为「Google Scholar 已查，MathSciNet、zbMATH、WoS 待查」。`check_tex.py` 通过（21 条文献全被引用），`check_paper_numbers.py` 26 PASS，Tectonic 编译无警告，仍是 26 页。桌面的 `main.pdf` 正开在 WPS 里被锁，新版另存为桌面的 `main_最新.pdf`。
    - 本机 `.md` 没有关联打开程序，检索清单用新脚本 `code/main_extra/md_to_pdf.py` 转成 PDF 放在桌面。

## 当前状态与待办（2026-10-07）

- **研究交付物已完成**：`报告.md` + `verify_all.py`。最后一次全量验证：14 个模块、332 PASS、0 FAIL（本地 2026-10-08，加入表 B 的模块 tb 之后，`logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行，峰值 431 MB，用时 485 s；此前 13 个模块、305 PASS）；报告引用的 247 个核对 id 全部 PASS。同日早些时候修好了 `c5b.snapshots`：2026-10-06 上传 GitHub 时加入的 `data/oeis/NOTICE.md` 让它 FAIL，现在比对时排除这份许可说明，目录里多出别的文件仍会 FAIL。
- **Lean**：2026-10-07 全量构建（`lean/run_lean_checks_direct.sh`，日志 `logs/lean_build.log`）：
  - 26 个模块加根模块全部从源码编译通过，`Checks.lean` 也通过；
  - `Axioms.lean` 的 252 条 `#print axioms` 与对 2649 个声明的全量扫描，都只出现三条标准公理（依赖其他公理的 0 个；`rowRule_iff_allowed` 只用到 propext 与 Quot.sound）；
  - 每一步一次只跑一个 Lean，峰值 8.18 GB，系统提交余量最低 4.3 GB；
  - `lean/A207123/` 下没有 `sorry`、`admit`、`native_decide`、`axiom`。第三轮的日志另存为 `logs/lean_build_round3_2026-10-05.log`。
  - 之后加入 `NotStirlingLike.lean`（T3.9）：单独编译通过（峰值 8.05 GB，27 s），根模块重编，`Axioms.lean` 增至 256 条、全量扫描 2675 个声明（依赖其他公理的 0 个），`Checks.lean` 通过；其余 26 个模块没有重编，`logs/lean_build.log` 仍是加入前的全量构建记录。
- **报告已标注第四轮**：`patch_lean4.py`、`patch_lean4_fixes3.py` 已应用并重新拼接。第四轮各模块的主要定理陈述都已对照报告核对（AI 核对），其中发现 T5.3(1) 的导数公式与 n_k 都要 k≥1，已补上。
- **报告 ⑥ 原来的三处已加固**（2026-10-07，见「过程概览」第 12 条）：
  - T4.3(6) 与 T3.4(2) 现在各有两份路线不同的证明，计算与数值核对已并入 verify_all（rv3）；
  - T2.7 的推论改写为 T2.7′ 并自证。
  - 随后排第 1 的 T2.6(ii) 也已加固：两份独立推导（x1、主 Agent）加两套独立精确核对（rv2、rv4），见「过程概览」第 14 条。
  - ⑥ 按现在的证据重排为：T2.7′（新证明，两位复核者审查，未经人类核对）、T3.4(4)(5) 的分析估计、T4.3(8) 中 b_i 可约的情形（引用未重证的 Laguerre 零点定理）。
- **待办**：
  - 现在 ⑥ 的三处：
    - T2.7′ 已有第二位复核者（s7-t27，2026-10-07，confirmed with minor gaps，适用范围的一句话已改正，见 notes/review/s7-t27-review.md）；仍待人类专家审阅；如果要覆盖支撑伸到 j=0 的 C(2j,j) 一类写法，再核对 s6-t27 提出的 (N2′)；
    - T3.4(4)(5) 请复核者重推误差界与常数项部分的门槛；
    - T4.3(8) 补上 Laguerre 零点定理的标准证明，或给出 Szegő 原书的准确出处。
  - ~~按 `notes/Lean定义核对清单.md` 逐项核对承重的 Lean 定义（要人来做）~~：2026-10-08 作者本人告知已核对完 18 项、全部正确，清单已全部记 ✓；论文第 8 节与 AI 声明改为「由 AI 模型与作者核对」。清单之外其余模块的陈述仍只有 AI 核对。
  - 论文初稿 `paper/main.tex`（2026-10-07 已写全并编译）：剩 2 处 `\todo`（文献检索补完：Google Scholar 已查，剩 MathSciNet、zbMATH、WoS；AI 使用声明按投稿方要求改写）和 1 处注释里的 TODO（引理 1 的出处）；署名、通讯邮箱、仓库地址与 Lean 定义核对已于 2026-10-07、10-08 完成。原来要你决定的收录范围，初稿先这样定了，你可以改：T5.1 的两项渐近收为定理 3.2；T2.6 的补充形状只收已证明的（α≥1 且 α+β 为偶数，以及 (3,0)、(1,2)、(2,3)），浮点证据的只在注记里提；OEIS 的列与行递推收为注记 3.5；T2.7′ 连同 (N1)(N2) 写进 §6.2。改完稿子跑 `py -3.14 code/main_extra/check_tex.py paper/main.tex` 与 `py -3.14 code/main_extra/check_paper_numbers.py paper/main.tex`，再用 Tectonic 编译（`%LOCALAPPDATA%\Programs\tectonic\tectonic.exe -X compile paper/main.tex`）。
  - 人类专家审阅与正式文献核对，见 `ROADMAP.md` §5。2026-10-07 已做开放数据库部分（`notes/新颖性核查_2026-10-07.md`），同日你手动查完 Google Scholar（§9，没有发现先例）；还要你手动查 zbMATH（免费、无需登录）、Web of Science、MathSciNet（`notes/新颖性核查_手动检索清单.md`，桌面有 PDF 版），并打开 Dougherty-Bliss 2024 博士论文的 PDF 搜本家族编号（RUcore 禁止 AI 抓取，我没取）。
- **表 B 的新进展（2026-10-07 晚）**：B1（h_k 全实根且根互异）与 B3（单族形状分类，推广到 α,β≥0 的一切形状）已证明，记为 `猜想总表.md` 的 A19、A20；B7 证了一半（f_k(t) 的 Gevrey-1/3 上界与 t∈(0,1) 的同阶下界），B9 证了一部分（h_k 系数恰变号 ⌊k/3⌋ 次）。证明在 `notes/05`–`07`，核对 `py -3.14 code/tableB/run_all.py`（20 条全部 PASS），B1、B3 各有一位对抗性复核者（`notes/review/s8-b1-review.md`、`s8-b3-review.md`）。**还没有并入报告与论文**（报告 T5.3(6)、T2.6(i) 补充、T3.4(5)、④ 与论文的开放问题一节仍写着「猜想」），也没有登记进 verify_all，没有形式化。
- **表 B 并入论文（2026-10-08）**：按用户决定，A19（B1）、A20（B3）、A21（B2）写进论文，A22（B7）不进。并入前各找了第二位独立复核者（`notes/review/s10-b1-review.md`、`s10-b3-review.md`、`s10-b2-review.md`，都是 confirmed with minor gaps，意见已改进论文；s10-b2 另用模数 32760 建了一份独立证书）。核对登记进 verify_all：新模块 `code/checks/check_tb.py`（运行 `code/tableB/` 的 b1、b3、b2，27 条）；b7、b7_borel、b11 仍只在 `code/tableB/run_all.py`。`报告.md` 还没有并入这三条。
- **表 B 的新进展（2026-10-08）**：B2（两族 u 型和不存在：U 对每个 m≥2、E 对每个 m≥3）与 B7 的后半（t<0 时 F 在 x 方向 3-可和、和为积分 I）已证明，记为 `猜想总表.md` 的 A21、A22；B7 没做的两项（t∈(0,1) 的可和性、t<0 时 Gevrey 阶的下界）分出为新条目 B13，B 表现有 9 项；B11 的计算机辅助证明从 d≤8 扩到 d≤100（部分结果）。证明在 `notes/08`–`10`，核对 `py -3.14 code/tableB/run_all.py`（6 个部分 41 条全部 PASS；`check_b7_borel.py` 是数值佐证），B2、B7 各有一位对抗性复核者（`notes/review/s9-b2-review.md`、`s9-b7-review.md`）。同样**还没有并入报告与论文**（报告 T2.6(iii)、T3.4(5)、④A.4、T4.2(2) 与论文的开放问题一节仍是旧说法），没有登记进 verify_all，没有形式化。
- **表 B 的新进展（2026-10-08，B6）**：B6（只用一元 ₁F₁ / 不完全 Gamma 的整表有限闭式）已否定性解决，记为 `猜想总表.md` 的 A23。证明在 `notes/11-主Agent-表B-B6-一元合流函数闭式不存在.md`：对 λ=(1−x)/x³∉Q 的 x，f_x(t)=Σ_mG_m(x)t^m 绕 t=0 不变、绕 t=1 一圈多出 −νω（ν=2πi·x^{−3}e^{1/x³}，ω=t^λe^{−t/x³}），两圈交换次序结果不同，单值群不是虚交换的；而一元 ₁F₁、Tricomi U、Whittaker、不完全 Gamma、Ei、erf、Bessel 等以 t 的代数函数为自变量拼出的表达式，单值群都是虚交换的。附带一个只含单个 Humbert Φ_1 的闭式；λ 为负整数时反而有 Ei 闭式。核对 `code/tableB/check_b6.py`（8 条全部 PASS），两位对抗性复核者（`notes/review/s11-b6a-review.md`、`s11-b6b-review.md`，都是 confirmed with minor gaps）。同样**还没有并入报告与论文**，没有登记进 verify_all，没有形式化。
- 数学上未解的问题与完成度见 `猜想总表.md` 表 B；完整的待办与优先级见 `ROADMAP.md`。

## 许可与数据来源

- 代码采用 MIT 许可（根目录 `LICENSE`，2026-10-08 选定）：`code/`、`lean/`、`verify_all.py` 及其他脚本。
- 论文（`paper/`，另见 `paper/NOTICE.md`）、报告（`报告.md`）、笔记（`notes/`）与其余文字**不在 MIT 许可之内**，暂时保留所有权利，等选定投稿期刊后再定。
- License (English summary): the code (`code/`, `lean/`, `verify_all.py` and the other scripts) is released under the MIT License (`LICENSE`). The paper in `paper/`, the report and the notes are not covered by it; all rights reserved for now. Data in `data/oeis/` comes from the OEIS under CC BY-SA 4.0; other third-party data keeps its own terms.
- `data/oeis/` 是 OEIS 条目的只读快照，来源 <https://oeis.org>，适用 CC-BY-SA 4.0，署名与许可见 `data/oeis/NOTICE.md`。
- 没有向 OEIS 提交、发帖或联系任何人。
