你接手一个已经进行到一半的 Lean 4 形式化任务。请用中文汇报。

## 背景

工作目录：`C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\`（Windows，路径含空格和中文，Lean 在这里能正常工作）。

这是 OEIS A207118–A207123 一族的研究任务（「任务 C」）。原题：a_k(n) 是 n×k 的 0/1 矩阵个数，要求每行从左到右任意连续三位不是 001、010，每列从上到下任意连续三位不是 001、011。U_k(m) 是高度序列 (h_1..h_k)∈{0..m}^k 的个数，要求每个相邻三元组 (a,b,c) 满足「b=c 或 a≥max(b,c)」。

先读这几个文件：
- 任务原文：`notes/原始任务说明.md`（第 0 节是必须遵守的工作规则）。
- 研究报告：`报告.md`。它由 `notes/report_parts/` 下的分节拼接而成，定理编号为 T1.x–T5.x。
- 各结论的书面证明：`notes/c1.md`、`c2a.md`、`c2b.md`、`c3a.md`、`c3b.md`、`c4.md`、`c5a.md`、`c5b.md`。
- Python 核对：`py -3.14 verify_all.py`（11 个模块、290 条，全部 PASS）。

## Lean 部分已完成的工作（不要推倒重来）

Lean 项目在 `lean/`，环境为 Lean 4.34.1 + Mathlib v4.34.1，依赖已装在 `lean/.lake`。

| 文件 | 内容 |
|---|---|
| `A207123/Basic.lean` | `Good`、`Legal : List ℕ → Prop`、`seqs m k`、`L k m`、`U k m := (L k m).card`；`mem_L`、`legal_iff_getElem`；引理 1：`lemma1`（k≥3）、`lemma1_one`、`lemma1_two`、`U_zero_left`、`U_zero_right` |
| `A207123/Reduction.lean` | `Mat n k := Fin n → Fin k → Bool`、`RowRule`、`ColRule`、`a k n`；主定理 `a_eq : a k n = U k ((n+1)/2) * U k (n/2)`；工具 `LegalF`、`card_legalF`、`rowPattern_iff_good`、`build`、`heightE`、`heightO` |
| `A207123/Formula.lean` | `hc s l`（完全齐次对称多项式）、`vars j m = [m,…,j]`、`E l n = Σ_s h_s(l)·multichoose(|l|+s, n−3s)`、`E_cons`、闭式 `F`；`U_eq_F`、`hc_vars_zero`；推荐显式公式 `U_explicit`（报告 T2.4 主公式） |
| `Axioms.lean` | 对上述定理 `#print axioms`。当前全部只依赖 propext、Classical.choice、Quot.sound |
| `Checks.lean` | 用 `native_decide` 与任务数据表对照。这是计算核对，不算证明的一部分 |

## 本次要做的事（按优先级，能做多少做多少）

1. **(C3) 的二项式基与 N 的三角递推（T1.4）**
   - 用组合方式定义 N(k,q)：长 k、值域恰为 {1..q} 的合法词个数（「合法」的定义与 U 相同）。
   - 证明 U_k(m) = Σ_q N(k,q)·C(m+1,q)。
   - 证明三角递推 T1.4(2)，注意报告里写的边界约定。
   - 证明 N(k,k−1) = k²−k−4（k≥4）。
2. **T1.0(c) 多重链表述**：U_k(m) 等于允许行偏序集 Λ_k（长 k、不含 001 和 010 的 0/1 串，按逐分量序）中长度为 m 的多重链个数。可以复用 `Reduction.lean` 里「列单调矩阵 ↔ 高度向量」的工具。
3. **按上升数细化的公式**：即 T2.4 的第二式，U_k(m,s)，其中 s 是上升数。先形式化 T2.2 中按 s 细化的引理 1（边界约定以报告为准），再仿照 `Formula.lean` 的思路做。
4. **T1.3(2)**：对一切 m，gcd(W_m, P_m)=1，因此关于 k 的最小线性递推阶恰为 3m+1。在 `Polynomial ℚ` 里做；书面证明见报告 T1.3(2) 与 `notes/c1.md`。
5. **（较难，可选）T3.7**：F 不是 D-finite，或者它的推论 T3.7(2)：不存在只依赖 k 的多项式系数象限递推。先给出一个忠实的形式化陈述再动手，书面证明见 `notes/c3b.md` §3–§5。做不完就如实写清卡在哪里。

## 验收标准

- 不允许出现 `sorry`、`admit`，也不允许新增公理。每个新定理都要加进 `Axioms.lean`，`#print axioms` 只能出现那三条标准公理。`native_decide` 只能出现在 `Checks.lean` 里。
- 定理陈述要忠实于报告，不能偷偷加强假设或减弱结论。每个定理写 docstring，注明对应的报告编号。
- 如果 Lean 证明过程中发现报告的某条陈述有误或缺条件，立刻停下并报告：给出反例或缺失的条件，不要绕过去。
- 完成后要做三件事：
  - 在 `lean/` 下依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`，把输出存到 `logs/lean_build.log`。
  - 在报告对应定理的等级标签里加上「已在 Lean 中形式化：`定理名`」。要修改 `notes/report_parts/` 下的分节文件，不要直接改 `报告.md`；改完运行 `py -3.14 code/main_extra/assemble_report.py`，它会重新拼接报告并检查核对编号，退出码必须为 0。
  - 同步更新 `报告.md` 第 ⑤ 节的 Lean 表格、README 和项目记忆页 `C:\Users\Michael Song\Documents\Obsidian Vault\Codex协作\projects\A207123 任务C 显式公式与母函数.md`：先读，再局部修改，只改变化了的事实。

## 必须遵守的规则（来自任务原文）

- 每条结论标等级：【已证明】、【已验证（写明范围）】或【猜想】。不得把「数值上看起来对」写成已证明。
- 只做只读查询，不要发帖、提交，也不要联系任何人。
- 做不下去就如实写：试了什么、卡在哪里、为什么。
- 不要宣布「完全解决」。

## 环境注意事项（前一位 Agent 踩过的坑）

- Python 要用 `py -3.14`，`python` 命令是空壳。
- 经 Bash 工具传给 Python 的字符串里，反斜杠会被减半。带反斜杠的补丁先写成文件再运行。
- 迭代时用 `lake env lean A207123/文件.lean`：热启动约 30–50 秒，长时间不用后第一次可能要十几分钟（加载近 9000 个 Mathlib 文件，很可能被实时防护扫描拖慢）。`lake build` 每次都要核对全部 Mathlib 的构建记录，要 3–6 分钟，放后台跑。
- 不要运行 `lake update`，不要删除 `.lake`。改了文件，需要先 `lake build` 对应模块，下游文件才能 import 它。
- 本机可能有别的会话在跑占 CPU 的任务，计时会偏慢。这不是你的进程，不要去动。
- Lean/Mathlib 写法提示：
  - 常用引理：`Finset.card_union_of_disjoint`；`Finset.card_biUnion`（两两不交的目标要先 `rw [Function.onFun]`）；`Fin.card_filter_val_lt`；`Nat.multichoose`（用它可以避开自然数减法截断）；`Nat.stirlingSecond`。
  - 存在量词内部不能直接 `rw`，要先 `obtain` 拆开。
  - `push_neg` 已弃用，改用 `push Not`。
  - 自然数减法容易出错，可以用 `obtain ⟨r, hr⟩ : ∃ r, n - 3*s = r + 1` 这样引入新变量，并给 Pascal 递推显式传参，防止 `rw` 改错位置。
- 如果你会派子 Agent，要显式指定一个可用的模型（前一位用的是 opus，默认模型曾报错）。

## 最后的汇报

最后用中文汇报以下内容：
- 新形式化了哪些定理（定理名、对应报告编号、所在文件），以及 `#print axioms` 的输出。
- 哪些没做完、卡在哪里。
- 有没有发现报告里的错误。
- 本轮实际运行过的验证命令及其结果。
