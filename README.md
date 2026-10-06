# A207123 任务 C：U_k(m) 的显式公式、母函数与结构（2026-10-04）

这个文件夹是「任务 C」的完整工作区：最终报告、一键核对脚本，以及全部过程文件。
本任务与同目录下的 `A207123-禁止模式01矩阵计数证明/`、`A207123-全k形态定理证明/`（任务 A、B，由其他会话完成）互相独立，这里没有读写它们的文件（它们不在本仓库中）。

> **状态声明（请先读）**
> - 本仓库的数学内容由 AI（Claude）在人类指导下生成，并经 AI 复核者交叉检查，**没有经过人类专家审稿**。不少定理另有 Lean 4 + Mathlib 机器检查（有的只覆盖一部分，范围见 `猜想总表.md`），但 Lean 只检查证明，不检查「陈述是否忠实于报告」。
> - **新颖性未经核实**：初步文献检索没有找到直接讨论这个序列族的论文，但检索工具有限，「没找到」不等于「前人没证」（见 `ROADMAP.md` §5）。请勿据此对外宣称「首次证明」。
> - 这是进行中的研究仓库，不是定稿：Lean 第四轮已于 2026-10-07 收尾，但没有人类专家审过；报告 ⑥ 列出最不确定的三处（2026-10-07 加固了原来的三处并重新排序），见「当前状态与待办」。

## 这是什么

研究 OEIS A207118–A207123 一族的计数问题：n×k 的 0/1 矩阵，行不含 001 与 010，列不含 001 与 011。已知 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋)，其中 U_k(m) 是高度序列 (h_1,…,h_k)∈{0,…,m}^k 的个数，要求每个相邻三元组 (a,b,c) 满足「b=c 或 a≥max(b,c)」。本仓库（「任务 C」）研究 U_k(m) 这张二维表：显式公式、母函数、D-finite 判定、近对角线、渐近与结构。

**主要结果**（等级与证据见 `报告.md`；每个猜想的结局、意义与完成度见 `猜想总表.md`）：
- 引理 1（三项递推）与任务说明里的 (C1)–(C8) 全部独立重证；
- 全正项两层显式公式（Stirling / r-Stirling 数 × 二项式），带块分解的组合解释；
- 关于 k 的最小递推阶对一切 m 恰为 3m+1；增长率与 c_m 的闭式；
- 不存在「Stirling×二项式」单和；F(x,t) 与 N(x,y) 的母函数都不是 D-finite；全部多项式系数递推恰为引理 1 生成的左理想；
- N(k,k−d) 对 k≥2d+2 是 2d 次多项式（门槛精确）；固定 q 的分子有一般公式；
- Lean 4 + Mathlib 形式化：原题归约、引理 1、最小阶、二项式基、显式公式、非 D-finite、左理想刻画及其维数公式、近对角线、分子结构、h_k 的结构等，共 26 个模块，2026-10-07 全量构建通过（2649 个声明只依赖三条标准公理）；各条的覆盖范围见报告标签与 `猜想总表.md`。

**如何复现**
- Python 核对：`py -3.14 verify_all.py`（约 4.5 分钟，需要 numpy），逐条打印 PASS/FAIL；最后一次全量运行 12 个模块、296 PASS、0 FAIL（本地 2026-10-07 加固报告 ⑥ 之后，`logs/verify_all_final.log`）。想带内存保护运行（本机常有别的任务同时在跑）：`code/main_extra/run_guarded.sh logs/<输出>.log py -3.14 verify_all.py`，实测整棵进程树峰值约 0.4 GB。
- Lean：工具链 `leanprover/lean4:v4.34.1`，依赖 Mathlib `v4.34.1`（见 `lean/lakefile.toml`、`lean/lake-manifest.json`）。作者在 Windows 上用 `lean/run_lean_checks_direct.sh` 构建（逐模块 `lake build` 的版本是 `run_lean_checks.sh`），没有在别的环境验证过；单个编译峰值内存 ≥ 8 GB。`lean/.lake/`（Mathlib 依赖与编译产物，约 5–7 GB）不在仓库里，需要自己用 `lake` 获取。
- `code/review/r-c4i/N_K*.pkl` 是可重新生成的中间文件，不在仓库里，见 `ROADMAP.md` §6。

## 先看这几个

| 文件 | 内容 |
|---|---|
| `报告.md` | 最终报告：结论摘要、定理清单（陈述/证明/核对范围/等级）、推荐显式公式、失败方向、代码与输出、最不确定的三处、C-1…C-5 完成度 |
| `verify_all.py` | 一键核对：`py -3.14 verify_all.py`（空闲时约 4.5 分钟，机器负载高时更长；需要 numpy，rv2 模块没有纯 Python 回退），逐条打印 PASS/FAIL，最后给出总表；任何 FAIL 时退出码为 1 |
| `猜想总表.md` | 把所有「原本是猜想、未证或待判断」的命题分成已证明 / 尚未证明 / 已否定三张表，每条给出意义与完成度（2026-10-06 整理，2026-10-07 更新） |
| `ROADMAP.md` | 未来要做的事：报告 ⑥ 的三处（原三处 2026-10-07 已加固，新三处待做）、开放问题的优先级、新颖性与外部评审（尚未做）、仓库维护（Lean 第四轮已于 2026-10-07 收尾） |

## 目录

| 路径 | 内容 |
|---|---|
| `code/core.py` | 公共底座：按第 1 节原始定义实现的全部「真值」程序（参考实现 U_list、后缀和高度 DP、多重链、原题矩阵直接计数、暴力、N 的 DFS/容斥、Stirling、h_complete） |
| `code/polylib.py` | Fraction 精确多项式与截断幂级数 |
| `code/checks/check_*.py` | verify_all 调用的 12 个正式核对模块（c0 主 Agent 补充；c1 复核；c2a/c2b 显式公式；c3a/c3b 母函数与 D-finite；c4 近对角线与分子；c5a 渐近与 h_k；c5b OEIS；rv 第二轮复核的产物；rv2 复核者 x1 的两个独立脚本；rv3 报告 ⑥ 原两处所依赖的复核者脚本，来自 r-c4ii、r-c3a、s6-t436、s6-t342，2026-10-07 加入） |
| `code/<area>/` | 各方向的探索脚本 |
| `code/family/` | 2026-10-06 补充：OEIS 里列规则同为「竖向禁止 001、011」的 6 张 Hardin 表都满足同一归约（`check_family.py`、OEIS 只读快照与日志，见其中 README）；另外 5 张表的结构没有研究 |
| `code/review/<reviewer>/` | 第二轮对抗性复核者的独立脚本；`s6-*` 是 2026-10-07 加固报告 ⑥ 的第三轮复核者（s6-t436、s6-t342、s6-t27） |
| `code/main_extra/` | 主 Agent 的辅助脚本（最小阶逐因子检验、结果汇总）；`assemble_report.py`（拼接报告并交叉检查核对 id）；`report_patches/`（报告补丁脚本，Lean 标签补丁是 `patch_lean*.py`，第四轮的 `patch_lean4.py`、`patch_lean4_fixes3.py` 已于 2026-10-07 应用；同日加固 ⑥ 后的同步补丁是 `patch_six.py`，也已应用）；`lean_statements.py`（从 Lean 文件里只抽出文档注释、定义与定理陈述，便于人工核对陈述是否忠实于报告）；`run_guarded.sh` + `proc_watchdog.ps1`（非 Lean 任务的内存保护：机器上有 lean.exe 或内存余量不够就不启动，运行中整棵进程树超限就结束，每次记一行到 `logs/guarded_runs.log`；2026-10-07 起内存查询失败时改用备用数据源，连续 5 秒都读不到才结束；Lean 仍只走 `lean/lean_one.sh`） |
| `code/step0_baseline.py`、`step1_quickcheck.py` | 开工时的基线核对与主线推导快速核对 |
| `notes/原始任务说明.md` | 用户给出的任务原文 |
| `notes/00-主线推导与分工.md` | 主 Agent 开工时的推导草稿与协作规则（其中两处后来被证明有误，见报告 ④） |
| `notes/01-主Agent补充.md` | c_m 闭式等补充推导 |
| `notes/02-主Agent-不确定三处加固.md` | 2026-10-07 加固报告 ⑥ 原来的三处：逐步重推 T4.3(6)、T3.4(2) 的复核证明；把 T2.7 的推论改写为 T2.7′ 并自证 |
| `notes/交接提示词_Lean形式化续作.md` | 第二轮 Lean 续作的交接提示词（历史文件：其中列的任务都已完成，现状见「当前状态与待办」） |
| `notes/<area>.md` | 第一轮 8 个方向的完整证明笔记 |
| `notes/review/` | 第二轮复核：`claims_<area>.md`（第一轮结论清单）与 `<reviewer>-review.md`（逐条 verdict）；第三轮审计的输出在 `logs/phase3_audit_output.json` 与 `logs/audit_*.log`；`s6-*-review.md` 是 2026-10-07 加固 ⑥ 的复核报告（T4.3(6)、T3.4(2) 的独立重推，T2.7′ 的审查） |
| `notes/report_parts/` | 报告的分节源文件（`报告.md` 由它们拼接） |
| `data/oeis/` | OEIS 只读快照（68 次 curl）与 `INDEX.md` 查询记录；许可与署名见 `NOTICE.md`（CC-BY-SA 4.0） |
| `lean/` | Lean 4 + Mathlib 形式化（从原始定义出发，只依赖三条标准公理）：原题归约与多重链表述（T1.0）、引理 1（T1.1）、gcd(W_m,P_m)=1 与最小递推阶恰为 3m+1（T1.3）、二项式基与 N 的三角递推（T1.4）、按上升数细化的引理 1 与两个显式公式（T2.2、T2.4）、F 不是 D-finite（T3.7(1)，含 D-finite 的定义与引理 D1）与没有 k-only 象限递推（T3.7(2)）、U 与 N 的全部多项式系数象限递推恰为 L1、L_N 生成的左理想（T3.8 的 Rel(U)=O_U·L1、Rel(N)=O_N·L_N，含饱和引理）；第四轮又新增 15 个模块（Poly、HNum、DFiniteN、NoKOnlyN、OreDim、Gosper、Growth、SmallK、Parity、NPDE、Coeffs、HGen、NumStruct、NearDiag、HStruct），`lean/A207123/` 下共 26 个文件，全部登记在 `A207123.lean`，2026-10-07 全量构建通过；全量构建用 `./run_lean_checks.sh`（按依赖顺序逐个模块 `lake build +A207123.X`，再 `lake env lean Axioms.lean`、`lake env lean Checks.lean`，输出写入 `logs/lean_build.log`），内存紧时用 `./run_lean_checks_direct.sh`（同样三步，但第 1 步直接用 `lake env lean -o` 从源码逐个编译，不经 lake 的构建记录核对；2026-10-07 用的是它，约 22 分钟），单个文件一律用 `./lean_one.sh A207123/X.lean`（带内存闸门与看门狗，一次只跑一个；单个编译峰值 ≥8 GB，本机 16 GB，Lean 编译曾两度耗尽虚拟内存导致重启）；`.lake/` 下是 Mathlib 依赖与编译产物（约 5–7 GB，可整体删除后用 `lake update` 重新获取） |
| `logs/` | 全部运行日志，包括四轮工作流的原始返回值（`phase1_workflow_output.json`、`phase2_review_output.json`、`phase3_audit_output.json`、`phase4_final_audit_output.json`、`phase4b_recheck_output.json`）与 verify_all 的完整输出（`verify_all_final.log` 是 2026-10-07 加固 ⑥ 之后的最新一次，12 个模块 296 个 PASS，报告的核对 id 交叉检查以它为准；2026-10-05 的上一次另存为 `verify_all_final_2026-10-05.log`，其中 290 个 PASS 的 id 全部仍在新日志里；`verify_all_2026-10-07.log` 是当天早些时候修好 `c5b.snapshots` 后的那一次）；`rv3_*.log` 是 rv3 调用的复核者脚本的完整输出，`s6_red*_rv3.log` 是 rv3 的反向检查（故意改坏复核者脚本，确认会报 FAIL）。注意：rv3 调用的 `r6_structure.py` 每次运行都会重写复核日志 `review_r-c4ii_r6_structure.log`，内容不变，只有 runtime 一行会变；rv2 同样会重写 `rv2_x1_*.log`；`guarded_runs.log` 记录经 `run_guarded.sh` 运行的任务（时间为 UTC）；`lean_build.log` 是最新的全量构建日志（2026-10-07，含第四轮；第三轮的另存为 `lean_build_round3_2026-10-05.log`），`lean_recheck_2026-10-07.log` 是收尾时单独重检 HStruct、NumStruct、NearDiag 的记录，`lean_mem.log` 记录每次 Lean 编译的峰值内存与退出码（该文件的时间是 UTC，本机是 UTC+8） |

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

## 当前状态与待办（2026-10-07）

- **研究交付物已完成**：`报告.md` + `verify_all.py`。最后一次全量验证：12 个模块、296 PASS、0 FAIL（本地 2026-10-07 加固报告 ⑥ 之后，`logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行，峰值 433 MB，用时 273 s）；报告引用的 238 个核对 id 全部 PASS。同日早些时候修好了 `c5b.snapshots`：2026-10-06 上传 GitHub 时加入的 `data/oeis/NOTICE.md` 让它 FAIL，现在比对时排除这份许可说明，目录里多出别的文件仍会 FAIL。
- **Lean**：2026-10-07 全量构建（`lean/run_lean_checks_direct.sh`，日志 `logs/lean_build.log`）：
  - 26 个模块加根模块全部从源码编译通过，`Checks.lean` 也通过；
  - `Axioms.lean` 的 252 条 `#print axioms` 与对 2649 个声明的全量扫描，都只出现三条标准公理（依赖其他公理的 0 个；`rowRule_iff_allowed` 只用到 propext 与 Quot.sound）；
  - 每一步一次只跑一个 Lean，峰值 8.18 GB，系统提交余量最低 4.3 GB；
  - `lean/A207123/` 下没有 `sorry`、`admit`、`native_decide`、`axiom`。第三轮的日志另存为 `logs/lean_build_round3_2026-10-05.log`。
- **报告已标注第四轮**：`patch_lean4.py`、`patch_lean4_fixes3.py` 已应用并重新拼接。第四轮各模块的主要定理陈述都已对照报告核对（AI 核对），其中发现 T5.3(1) 的导数公式与 n_k 都要 k≥1，已补上。
- **报告 ⑥ 原来的三处已加固**（2026-10-07，见「过程概览」第 12 条）：
  - T4.3(6) 与 T3.4(2) 现在各有两份路线不同的证明，计算与数值核对已并入 verify_all（rv3）；
  - T2.7 的推论改写为 T2.7′ 并自证。
  - ⑥ 按加固后的证据重排为：T2.6(ii) 截断块部分的统一证明（只有一位复核者）、T2.7′（新证明，只有一位复核者审查）、T3.4(4)(5) 的分析估计。
- **待办**：
  - 新 ⑥ 的三处：
    - T2.6(ii) 请第二位复核者重推一般 m 的论证；
    - T2.7′ 请第二位复核者审查，如果要覆盖 C(2j,j) 一类因子，再核对 s6-t27 提出的 (N2′)；
    - T3.4(4)(5) 请复核者重推误差界与常数项部分的门槛。
  - 人类专家审阅与正式文献核对，见 `ROADMAP.md` §5。
- 数学上未解的问题与完成度见 `猜想总表.md` 表 B；完整的待办与优先级见 `ROADMAP.md`。

## 许可与数据来源

- 许可证尚未选定（默认保留所有权利），公开前需要选择，见 `ROADMAP.md` §6。
- `data/oeis/` 是 OEIS 条目的只读快照，来源 <https://oeis.org>，适用 CC-BY-SA 4.0，署名与许可见 `data/oeis/NOTICE.md`。
- 没有向 OEIS 提交、发帖或联系任何人。
