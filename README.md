# A207123 任务 C：U_k(m) 的显式公式、母函数与结构（2026-10-04）

这个文件夹是「任务 C」的完整工作区：最终报告、一键核对脚本，以及全部过程文件。
本任务与同目录下的 `A207123-禁止模式01矩阵计数证明/`、`A207123-全k形态定理证明/`（任务 A、B，由其他会话完成）互相独立，这里没有读写它们的文件（它们不在本仓库中）。

> **状态声明（请先读）**
> - 本仓库的数学内容由 AI（Claude）在人类指导下生成，并经 AI 复核者交叉检查，**没有经过人类专家审稿**。不少定理另有 Lean 4 + Mathlib 机器检查（有的只覆盖一部分，范围见 `猜想总表.md`），但 Lean 只检查证明，不检查「陈述是否忠实于报告」。
> - **新颖性未经核实**：初步文献检索没有找到直接讨论这个序列族的论文，但检索工具有限，「没找到」不等于「前人没证」（见 `ROADMAP.md` §5）。请勿据此对外宣称「首次证明」。
> - 这是进行中的研究仓库，不是定稿：第四轮 Lean 形式化尚未收尾，见「当前状态与待办」。

## 这是什么

研究 OEIS A207118–A207123 一族的计数问题：n×k 的 0/1 矩阵，行不含 001 与 010，列不含 001 与 011。已知 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋)，其中 U_k(m) 是高度序列 (h_1,…,h_k)∈{0,…,m}^k 的个数，要求每个相邻三元组 (a,b,c) 满足「b=c 或 a≥max(b,c)」。本仓库（「任务 C」）研究 U_k(m) 这张二维表：显式公式、母函数、D-finite 判定、近对角线、渐近与结构。

**主要结果**（等级与证据见 `报告.md`；每个猜想的结局、意义与完成度见 `猜想总表.md`）：
- 引理 1（三项递推）与任务说明里的 (C1)–(C8) 全部独立重证；
- 全正项两层显式公式（Stirling / r-Stirling 数 × 二项式），带块分解的组合解释；
- 关于 k 的最小递推阶对一切 m 恰为 3m+1；增长率与 c_m 的闭式；
- 不存在「Stirling×二项式」单和；F(x,t) 与 N(x,y) 的母函数都不是 D-finite；全部多项式系数递推恰为引理 1 生成的左理想；
- N(k,k−d) 对 k≥2d+2 是 2d 次多项式（门槛精确）；固定 q 的分子有一般公式；
- Lean 4 + Mathlib 形式化：原题归约、引理 1、最小阶、二项式基、显式公式、非 D-finite、左理想刻画等已在第三轮全量构建中验过；第四轮的 15 个模块只单独编译过。

**如何复现**
- Python 核对：`py -3.14 verify_all.py`（约 4 分钟，需要 numpy），逐条打印 PASS/FAIL；最后一次全量运行 11 个模块、290 PASS、0 FAIL（本地 2026-10-07，`logs/verify_all_2026-10-07.log`）。想带内存保护运行（本机常有别的任务同时在跑）：`code/main_extra/run_guarded.sh logs/<输出>.log py -3.14 verify_all.py`，实测整棵进程树峰值约 0.4 GB。
- Lean：工具链 `leanprover/lean4:v4.34.1`，依赖 Mathlib `v4.34.1`（见 `lean/lakefile.toml`、`lean/lake-manifest.json`）。作者在 Windows 上用 `lean/run_lean_checks.sh` 构建，没有在别的环境验证过；单个编译峰值内存 ≥ 8 GB。`lean/.lake/`（Mathlib 依赖与编译产物，约 5–7 GB）不在仓库里，需要自己用 `lake` 获取。
- `code/review/r-c4i/N_K*.pkl` 是可重新生成的中间文件，不在仓库里，见 `ROADMAP.md` §6。

## 先看这几个

| 文件 | 内容 |
|---|---|
| `报告.md` | 最终报告：结论摘要、定理清单（陈述/证明/核对范围/等级）、推荐显式公式、失败方向、代码与输出、最不确定的三处、C-1…C-5 完成度 |
| `verify_all.py` | 一键核对：`py -3.14 verify_all.py`（空闲时约 3.5–4 分钟，机器负载高时更长；需要 numpy，rv2 模块没有纯 Python 回退），逐条打印 PASS/FAIL，最后给出总表；任何 FAIL 时退出码为 1 |
| `猜想总表.md` | 把所有「原本是猜想、未证或待判断」的命题分成已证明 / 尚未证明 / 已否定三张表，每条给出意义与完成度（2026-10-06 整理） |
| `ROADMAP.md` | 未来要做的事：Lean 第四轮收尾、报告里证据最薄的三处、开放问题的优先级、新颖性与外部评审（尚未做）、仓库维护 |

## 目录

| 路径 | 内容 |
|---|---|
| `code/core.py` | 公共底座：按第 1 节原始定义实现的全部「真值」程序（参考实现 U_list、后缀和高度 DP、多重链、原题矩阵直接计数、暴力、N 的 DFS/容斥、Stirling、h_complete） |
| `code/polylib.py` | Fraction 精确多项式与截断幂级数 |
| `code/checks/check_*.py` | verify_all 调用的 11 个正式核对模块（c0 主 Agent 补充；c1 复核；c2a/c2b 显式公式；c3a/c3b 母函数与 D-finite；c4 近对角线与分子；c5a 渐近与 h_k；c5b OEIS；rv 第二轮复核的产物；rv2 复核者 x1 的两个独立脚本） |
| `code/<area>/` | 各方向的探索脚本 |
| `code/family/` | 2026-10-06 补充：OEIS 里列规则同为「竖向禁止 001、011」的 6 张 Hardin 表都满足同一归约（`check_family.py`、OEIS 只读快照与日志，见其中 README）；另外 5 张表的结构没有研究 |
| `code/review/<reviewer>/` | 第二轮对抗性复核者的独立脚本 |
| `code/main_extra/` | 主 Agent 的辅助脚本（最小阶逐因子检验、结果汇总）；`assemble_report.py`（拼接报告并交叉检查核对 id）；`report_patches/`（报告补丁脚本，Lean 标签补丁是 `patch_lean*.py`，其中 `patch_lean4.py` 已写好但还没应用，见「当前状态与待办」）；`run_guarded.sh` + `proc_watchdog.ps1`（非 Lean 任务的内存保护：机器上有 lean.exe 或内存余量不够就不启动，运行中整棵进程树超限就结束，每次记一行到 `logs/guarded_runs.log`；Lean 仍只走 `lean/lean_one.sh`） |
| `code/step0_baseline.py`、`step1_quickcheck.py` | 开工时的基线核对与主线推导快速核对 |
| `notes/原始任务说明.md` | 用户给出的任务原文 |
| `notes/00-主线推导与分工.md` | 主 Agent 开工时的推导草稿与协作规则（其中两处后来被证明有误，见报告 ④） |
| `notes/01-主Agent补充.md` | c_m 闭式等补充推导 |
| `notes/交接提示词_Lean形式化续作.md` | 第二轮 Lean 续作的交接提示词（历史文件：其中列的任务都已完成，现状见「当前状态与待办」） |
| `notes/<area>.md` | 第一轮 8 个方向的完整证明笔记 |
| `notes/review/` | 第二轮复核：`claims_<area>.md`（第一轮结论清单）与 `<reviewer>-review.md`（逐条 verdict）；第三轮审计的输出在 `logs/phase3_audit_output.json` 与 `logs/audit_*.log` |
| `notes/report_parts/` | 报告的分节源文件（`报告.md` 由它们拼接） |
| `data/oeis/` | OEIS 只读快照（68 次 curl）与 `INDEX.md` 查询记录；许可与署名见 `NOTICE.md`（CC-BY-SA 4.0） |
| `lean/` | Lean 4 + Mathlib 形式化（从原始定义出发，只依赖三条标准公理）：原题归约与多重链表述（T1.0）、引理 1（T1.1）、gcd(W_m,P_m)=1 与最小递推阶恰为 3m+1（T1.3）、二项式基与 N 的三角递推（T1.4）、按上升数细化的引理 1 与两个显式公式（T2.2、T2.4）、F 不是 D-finite（T3.7(1)，含 D-finite 的定义与引理 D1）与没有 k-only 象限递推（T3.7(2)）、U 与 N 的全部多项式系数象限递推恰为 L1、L_N 生成的左理想（T3.8 的 Rel(U)=O_U·L1、Rel(N)=O_N·L_N，含饱和引理）；第四轮（进行中）又新增 15 个模块（Poly、HNum、DFiniteN、NoKOnlyN、OreDim、Gosper、Growth、SmallK、Parity、NPDE、Coeffs、HGen、NumStruct、NearDiag、HStruct），`lean/A207123/` 下共 26 个文件，其中 25 个登记在 `A207123.lean`；第四轮的模块只做过单独编译，还没有全量构建，HStruct 也还没登记；全量构建用 `./run_lean_checks.sh`（逐个模块串行 `lake build`，再 `lake env lean Axioms.lean`、`lake env lean Checks.lean`，输出写入 `logs/lean_build.log`），单个文件一律用 `./lean_one.sh A207123/X.lean`（带内存闸门与看门狗，一次只跑一个；单个编译峰值 ≥8 GB，本机 16 GB，Lean 编译曾两度耗尽虚拟内存导致重启）；`.lake/` 下是 Mathlib 依赖与编译产物（约 5–7 GB，可整体删除后用 `lake update` 重新获取） |
| `logs/` | 全部运行日志，包括四轮工作流的原始返回值（`phase1_workflow_output.json`、`phase2_review_output.json`、`phase3_audit_output.json`、`phase4_final_audit_output.json`、`phase4b_recheck_output.json`）与 verify_all 的完整输出（`verify_all_final.log` 是 2026-10-05 的那次，报告的核对 id 交叉检查以它为准；`verify_all_2026-10-07.log` 是修好 `c5b.snapshots` 后的最新一次，290 个 PASS 的 id 与前者完全相同）；`guarded_runs.log` 记录经 `run_guarded.sh` 运行的任务（时间为 UTC）；`lean_build.log` 是第三轮的全量构建日志，`lean_mem.log` 记录每次 Lean 编译的峰值内存与退出码（该文件的时间是 UTC，本机是 UTC+8） |

## 过程概览

1. 建文件夹，跑通参考实现，用三种独立方法（高度 DP、多重链、原题直接计数）核对第 2 节数据（`logs/step0_baseline.log`）。
2. 主 Agent 独立重证引理 1，发现「块分解」与 G_m = W_m/P_m，写成 `notes/00-主线推导与分工.md`，并快速核对（`logs/step1_quickcheck.log`）。
3. 第一轮工作流：8 个方向并行（C-1 复核；C-2 代数/组合两路；C-3 母函数/D-finite 两路；C-4；C-5 渐近/OEIS 两路），各自写证明笔记与核对模块。
4. 第二轮工作流：11 个对抗性复核者逐条复核第一轮全部结论（其中两个专门深挖「单和不可能」与「非 D-finite」），并据此修正。
5. 第三轮工作流：3 个审计者分别用独立程序重算报告里的公式、核对报告与核对模块/笔记是否一致、逐项检查交付要求；据此修订报告，并把第二轮的反例与复核者 x1 的脚本并入核对（rv、rv2 模块）。
6. 第四轮工作流：最终对抗审计（5 个审计方向，各配一个反驳验证者，确认 58 条），修订后再由 2 个复查者各配验证者复查一遍；据此再修订报告（`logs/phase4_final_audit_output.json`、`logs/phase4b_recheck_output.json`，补丁脚本在 `code/main_extra/report_patches/`）。
7. 整合报告，运行 verify_all.py 做最终核对。
8. Lean 形式化（2026-10-05）：第一轮形式化引理 1、原题归约与 T2.4 主公式；第二轮扩充到 T1.0(c)、T1.3(1)(2)、T1.4、T2.2 的细化引理 1、T2.4 第二式、T3.7(1) 的 ODE 部分与 T3.7(2)（两个子 Agent 分别写了 `Recurrence.lean`、`Ascent.lean`），第三轮（同日）补完 T3.7(1) 的最后一步（D-finite 的定义与引理 D1，子 Agent 写 `DFinite.lean`），并形式化 T3.8 的 Rel(U)=O_U·L1（`OreRel.lean`）与 Rel(N)=O_N·L_N、饱和引理（`OreRelN.lean`，搬运步骤改用二项式变换 V=P·N 在数组上直接做）。报告各条等级标签已注明定理名（补丁脚本 `code/main_extra/report_patches/patch_lean.py`、`patch_lean2.py`、`patch_lean3.py`），构建与公理检查输出在 `logs/lean_build.log`。
9. Lean 第四轮（2026-10-05，进行中）：新增 15 个模块（见上表 `lean/` 一行），其中 14 个单独编译通过并已登记，HStruct 编译通过一次但未登记。期间 Lean 编译两度耗尽虚拟内存导致重启（本地 10-05 11:08：三个 lean.exe 同时占用 19.6 + 8.1 + 8.0 GB；22:46：单个 lean.exe 涨到 23.9 GB），之后加了串行锁、内存闸门和看门狗（`lean/lean_one.sh`、`lean_watchdog.ps1`、`mem_status.ps1`）。报告补丁 `patch_lean4.py` 已写好大半，要等全量构建后才能应用。
10. 2026-10-06 整理：新增 `猜想总表.md`；README 与 Obsidian 项目记忆页同步到当前状态；没有移动或删除任何文件——报告、补丁脚本和 `assemble_report.py` 里有大量路径引用（核对 id、日志路径），搬动会让引用失效。

## 当前状态与待办（2026-10-06）

- **研究交付物已完成**：`报告.md` + `verify_all.py`。最后一次全量验证：11 个模块、290 PASS、0 FAIL（本地 2026-10-07 00:03–00:07，`logs/verify_all_2026-10-07.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行，峰值 434 MB）。在此之前，2026-10-06 上传 GitHub 时加入的 `data/oeis/NOTICE.md` 让 `c5b.snapshots` 一度 FAIL（这条检查要求该目录只有 68 个快照和 INDEX.md）；已在 `code/checks/check_c5b.py` 里把这份许可说明排除在比对之外，并确认目录里多出别的文件时仍会 FAIL。数学内容没有改动；报告引用的 232 个核对 id 在新日志里全部 PASS。
- **Lean**：第三轮全量构建（本地 2026-10-05 09:05）扫描了 1131 个声明，只依赖三条标准公理。第四轮的 15 个模块还没有全量构建。2026-10-06 检查 `lean/A207123/` 下 26 个文件：没有 `sorry`、`admit`、`native_decide`、`axiom`；`Axioms.lean` 有 216 条 `#print axioms`（不含 HStruct）。
- **HStruct.lean**（T5.3）：本地 10-06 00:03 单独编译通过一次，00:09 又被修改，尚未登记进 `A207123.lean` 和 `Axioms.lean`，需先重编。
- **报告尚未标注第四轮**：`patch_lean4.py` 要求先有含第四轮的全量构建日志；`报告.md` 自本地 10-05 12:36 起没变。
- **待办（按顺序）**：① 确认没有别的会话在用这个文件夹；② 用 `lean/lean_one.sh` 重编 HStruct，通过后登记；③ 核对 NumStruct、NearDiag、HStruct 等新文件的定理陈述与报告一致（Lean 检查不了陈述忠实性）；④ 跑全量 `lean/run_lean_checks.sh`，再 `patch_lean4.py --dry`、正式应用、`assemble_report.py`；⑤ 报告 ⑥ 的另两处最不确定项：T3.4(2) 请第二位复核者独立推导，T2.7 读到 Wilf–Zeilberger 1992 与 Zeilberger 1990 的原文。
- 数学上未解的问题与完成度见 `猜想总表.md` 表 B；完整的待办与优先级见 `ROADMAP.md`。

## 许可与数据来源

- 许可证尚未选定（默认保留所有权利），公开前需要选择，见 `ROADMAP.md` §6。
- `data/oeis/` 是 OEIS 条目的只读快照，来源 <https://oeis.org>，适用 CC-BY-SA 4.0，署名与许可见 `data/oeis/NOTICE.md`。
- 没有向 OEIS 提交、发帖或联系任何人。
