# -*- coding: utf-8 -*-
"""Lean 形式化完成后同步报告与 README（2026-10-05）。"""
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


patch(P + '00_head.md', [
(r"- 只读查询：",
 r"- Lean 形式化（2026-10-05 补做）：引理 1（T1.1）、原题归约 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋)（T1.0 (a)(b)）与推荐显式公式（T2.4 的主公式）已在 Lean 4 + Mathlib v4.34.1 中形式化证明，从原始定义出发，`#print axioms` 只显示 Lean 的三条标准公理（propext、Classical.choice、Quot.sound），没有 sorry。这三条因此是机器检查过的证明；其余【已证明】仍是书面证明加程序核对。代码与重跑方法见 ⑤。" + "\n" +
 r"- 只读查询："),
])

patch(P + '01_summary.md', [
(r"`verify_all.py` 的 11 个模块全部 PASS（见 ⑤）。",
 r"`verify_all.py` 的 11 个模块全部 PASS（见 ⑤）。" + "\n" +
 r"11. **Lean 机器检查**：引理 1、原题归约 a_k(n)=U_k(⌈n/2⌉)U_k(⌊n/2⌋)、推荐显式公式（T2.4 主公式）已在 Lean 4 + Mathlib 中从原始定义形式化证明，只依赖标准公理（见 ⑤）。"),
])

patch(P + '02_C1.md', [
(r"**T1.0（第 1 节归约 (a)(b)(c)）【已证明】**",
 r"**T1.0（第 1 节归约 (a)(b)(c)）【已证明；(a)(b) 已在 Lean 中形式化：`A207123.a_eq`】**"),
(r"**T1.1（引理 1）【已证明】**",
 r"**T1.1（引理 1）【已证明；已在 Lean 中形式化：`A207123.lemma1`、`lemma1_one`、`lemma1_two`、`U_zero_left`、`U_zero_right`】**"),
])

patch(P + '03_C2.md', [
(r"**T2.4（推荐显式公式：全正项双和；按上升数细化）【已证明】**",
 r"**T2.4（推荐显式公式：全正项双和；按上升数细化）【已证明；主公式已在 Lean 中形式化：`A207123.U_explicit`（按上升数细化的那一式未形式化）】**"),
])

patch(P + '09_code.md', [
(r"**其他重要文件**",
 r"**Lean 形式化**（`lean/`，Lean 4.34.1 + Mathlib v4.34.1）" + "\n\n" +
 r"| 文件 | 内容 |" + "\n" +
 r"|---|---|" + "\n" +
 r"| `A207123/Basic.lean` | 按高度序列定义 `U k m`（`L k m` 的成员恰是长 k、取值 ≤ m、每个相邻三元组都好的列表；`legal_iff_getElem` 给出逐下标刻画）；引理 1：`lemma1`（k≥3）、`lemma1_one`、`lemma1_two`、`U_zero_left`、`U_zero_right` |" + "\n" +
 r"| `A207123/Reduction.lean` | 原题定义：`a k n` = 满足行规则（不含 001、010）与列规则（不含 001、011）的 n×k 0/1 矩阵个数；`a_eq : a k n = U k ((n+1)/2) * U k (n/2)` |" + "\n" +
 r"| `A207123/Formula.lean` | 推荐显式公式 `U_explicit`：第一项用 Mathlib 的第二类 Stirling 数 `Nat.stirlingSecond`，第二项的 H(m,s,j) 写成 `hc s (vars j m)`（完全齐次对称多项式 h_s 在 m,m−1,…,j 处的值）；路线是闭式 `F` 满足与引理 1 相同的递推（`U_eq_F`） |" + "\n" +
 r"| `Axioms.lean` | 对上述定理 `#print axioms`：全部只依赖 propext、Classical.choice、Quot.sound |" + "\n" +
 r"| `Checks.lean` | 用 `native_decide` 把定义与任务说明第 2 节的数据表对照（k=7、10 两行，R_1..R_10，a_3(1..6)）；这是计算核对，依赖编译器，不是证明的一部分 |" + "\n\n" +
 r"重跑：在 `lean/` 下运行 `lake build`，再运行 `lake env lean Axioms.lean` 与 `lake env lean Checks.lean`（首次需要下载 Mathlib 缓存，约 5–7 GB；之后每个文件编译约 0.5–2 分钟，冷启动时加载 Mathlib 可能要十几分钟）。输出见 `logs/lean_build.log`。" + "\n\n" +
 r"**其他重要文件**"),
])

patch(P + '10_uncertain.md', [
(r"**次一级的不确定处**",
 r"**次一级的不确定处**" + "\n" +
 r"- 除了已在 Lean 中机器检查的三条（引理 1、原题归约、T2.4 主公式），其余【已证明】都是书面证明加程序核对，由 AI 撰写和复核，没有经过人类专家审稿，也没有形式化。"),
])

patch(ROOT + r'\README.md', [
(r"| `logs/` |",
 r"| `lean/` | Lean 4 + Mathlib 形式化：引理 1、原题归约、推荐显式公式（`lake build` 后运行 `lake env lean Axioms.lean`）；`.lake/` 下是 Mathlib 依赖与编译产物（约 5–7 GB，可整体删除后用 `lake update` 重新获取） |" + "\n" +
 r"| `logs/` |"),
])
