# -*- coding: utf-8 -*-
"""Lean 形式化第二轮（2026-10-05）完成后同步报告分节。

新增形式化：T1.0(c)、T1.3(1)(2)、T1.4(1)-(4)、T2.2 的按 s 细化引理 1、T2.4 第二式、
T3.7(1) 的 ODE 部分、T3.7(2)。用法：py -3.14 code/main_extra/report_patches/patch_lean2.py
（每处替换都断言原文恰好出现一次；再运行 code/main_extra/assemble_report.py 重新拼接报告）。
"""
import sys

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


# ---------- 00_head：Lean 一段 ----------
OLD_HEAD = (r"- Lean 形式化（2026-10-05 补做）：引理 1（T1.1）、原题归约 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋)（T1.0 (a)(b)）"
            r"与推荐显式公式（T2.4 的主公式）已在 Lean 4 + Mathlib v4.34.1 中形式化证明，从原始定义出发，"
            r"`#print axioms` 只显示 Lean 的三条标准公理（propext、Classical.choice、Quot.sound），没有 sorry。"
            r"这三条因此是机器检查过的证明；其余【已证明】仍是书面证明加程序核对。代码与重跑方法见 ⑤。")
NEW_HEAD = (r"- Lean 形式化（2026-10-05 补做，同日第二轮扩充）：下列结论已在 Lean 4 + Mathlib v4.34.1 中从原始定义出发形式化证明——"
            r"原题归约 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋) 与多重链表述（T1.0 (a)(b)(c)）、引理 1（T1.1）、"
            r"G_m 的递推与闭式以及「gcd(W_m,P_m)=1、关于 k 的最小递推阶恰为 3m+1」（T1.3(1)(2)）、"
            r"二项式基与容斥式、N 的三角递推及初值更正、N(k,k)=2、N(k,k−1)=k²−k−4（T1.4）、"
            r"按上升数细化的引理 1（T2.2）、推荐显式公式及其按上升数细化的一式（T2.4）、"
            r"F 关于 x 没有多项式系数 ODE（T3.7(1) 的 ODE 部分）与不存在系数只依赖 k 的象限递推（T3.7(2)）。"
            r"`#print axioms` 只显示 Lean 的三条标准公理（propext、Classical.choice、Quot.sound），没有 sorry。"
            r"这些条目因此是机器检查过的证明；其余【已证明】仍是书面证明加程序核对"
            r"（T3.7 中 D-finite 的定义与引理 D1、T3.7(3) 没有形式化）。形式化过程中没有发现报告陈述的错误或缺条件。"
            r"代码与重跑方法见 ⑤。")
patch(P + '00_head.md', [(OLD_HEAD, NEW_HEAD)])

# ---------- 01_summary：第 11 条 ----------
patch(P + '01_summary.md', [
(r"11. **Lean 机器检查**：引理 1、原题归约 a_k(n)=U_k(⌈n/2⌉)U_k(⌊n/2⌋)、推荐显式公式（T2.4 主公式）已在 Lean 4 + Mathlib 中从原始定义形式化证明，只依赖标准公理（见 ⑤）。",
 r"11. **Lean 机器检查**：原题归约与多重链表述（T1.0）、引理 1（T1.1）、最小递推阶恰为 3m+1（T1.3）、二项式基与 N 的三角递推、N(k,k−1)=k²−k−4（T1.4）、按上升数细化的引理 1 与两个显式公式（T2.2、T2.4）、F 没有 x 方向多项式系数 ODE 与没有 k-only 象限递推（T3.7(1)(2)）已在 Lean 4 + Mathlib 中从原始定义形式化证明，只依赖标准公理（见 ⑤）。"),
])

# ---------- 02_C1：T1.0、T1.3、T1.4 ----------
patch(P + '02_C1.md', [
(r"**T1.0（第 1 节归约 (a)(b)(c)）【已证明；(a)(b) 已在 Lean 中形式化：`A207123.a_eq`】**",
 r"**T1.0（第 1 节归约 (a)(b)(c)）【已证明；已在 Lean 中形式化：(a)(b) `A207123.a_eq`；(c) `A207123.U_eq_multichains`（m 元多重链 x_1≤⋯≤x_m，逐分量序；另有 `card_Lam`：R_k=|Λ_k|=U_k(1)）】**"),
(r"(1)【已证明】(1−x−m x³)G_m=G_{m−1}+m x²",
 r"(1)【已证明；已在 Lean 中形式化：`A207123.G_zero`、`G_rec`、`P_mul_G`、`X_mul_W`】(1−x−m x³)G_m=G_{m−1}+m x²"),
(r"(2)【已证明，强于提示词】**对一切 m≥0",
 r"(2)【已证明，强于提示词；已在 Lean 中形式化：`A207123.isCoprime_W_P`、`natDegree_P`、`coeff_zero_P`、`P_recurrence`、`order_lower_bound`、`min_order`、`P_dvd_of_mul_G_poly`（递推系数取 Q；`order_lower_bound` 还允许递推只在 k≥k_0 时成立）】**对一切 m≥0"),
(r"∎（「b_4 可约是否影响」：不影响。）",
 r"∎（「b_4 可约是否影响」：不影响。）（Lean 证明在一次因子情形改用正性：b_i 的有理根 r 处 W_i(r)≥1，因而不需要 W_4(1/2) 的计算；二次、三次因子仍用 Gauss 引理与有理根定理。）"),
(r"**T1.4（(C3) 二项式基、三角递推、对角线）【已证明】**",
 r"**T1.4（(C3) 二项式基、三角递推、对角线）【已证明；已在 Lean 中形式化：(1) `A207123.U_eq_sum_N`、`N_inv`、`N_inv_zero`；(2) `N_tri`、初值 `N_init`、初值更正 `N_tri_fails_at_two`、`N_tri_one`、`N_tri_two`；(3) `N_diag`；(4) `N_subdiag`（例外 `N_three_two`）。Lean 中 (2) 由引理 1 代入二项式基后比较 C(n,r) 的系数得到（T3.5(2) 的路线），陈述与下面相同】**"),
])

# ---------- 03_C2：T2.2、T2.4 ----------
patch(P + '03_C2.md', [
(r"**T2.2（母函数，含上升数）【已证明】**",
 r"**T2.2（母函数，含上升数）【已证明；按 s 细化的引理 1 已在 Lean 中形式化：`A207123.lemma1_asc`（k≥3,s≥1）、`lemma1_asc_s0`（k≥3,s=0）、`lemma1_asc_one`、`lemma1_asc_two`、边界 `Us_zero_left`、`Us_zero_right`；母函数本身未形式化】**"),
(r"【已证明；主公式已在 Lean 中形式化：`A207123.U_explicit`（按上升数细化的那一式未形式化）】",
 r"【已证明；已在 Lean 中形式化：主公式 `A207123.U_explicit`，按上升数细化的一式 `A207123.Us_explicit`】"),
])

# ---------- 04_C3：T3.7 ----------
patch(P + '04_C3.md', [
(r"**T3.7（F 与 𝒩 都不是 D-finite）【已证明】**",
 r"**T3.7（F 与 𝒩 都不是 D-finite）【已证明；已在 Lean 中形式化：(1) 的 ODE 部分 `A207123.no_x_ODE`（系数取 C[x][[t]]）与 `no_x_ODE_poly`（系数取 C[x,t]），(2) `A207123.no_k_only_recurrence`（p_ab∈C[k]）；D-finite 的定义与引理 D1、(3) 未形式化】**"),
])

# ---------- 10_uncertain：次一级不确定处与完成度表 ----------
patch(P + '10_uncertain.md', [
(r"- 除了已在 Lean 中机器检查的三条（引理 1、原题归约、T2.4 主公式），其余【已证明】",
 r"- 除了已在 Lean 中机器检查的条目（T1.0、T1.1、T1.3(1)(2)、T1.4、T2.2 的细化引理 1、T2.4 两式、T3.7(1) 的 ODE 部分与 T3.7(2)，见 ⑤），其余【已证明】"),
(r"引理 1 与原题归约另有 Lean 形式化证明。",
 r"引理 1、原题归约与多重链表述、最小阶恰为 3m+1、N 的二项式基与三角递推（含 N(k,k−1)=k²−k−4）另有 Lean 形式化证明。"),
(r"主公式另有 Lean 形式化证明）",
 r"主公式与按上升数细化的一式另有 Lean 形式化证明）"),
(r"而是证明了 F、𝒩 都不是 D-finite，",
 r"而是证明了 F、𝒩 都不是 D-finite（其中「F 没有 x 方向多项式系数 ODE」与「没有 k-only 象限递推」另有 Lean 形式化证明），"),
])

# ---------- 09_code：⑤ 的 Lean 小节 ----------
path = P + '09_code.md'
s = open(path, encoding='utf-8').read()
a = s.index(r"**Lean 形式化**（`lean/`，Lean 4.34.1 + Mathlib v4.34.1）")
b = s.index(r"**其他重要文件**")
assert s.count(r"**Lean 形式化**") == 1 and s.count(r"**其他重要文件**") == 1
LEAN_BLOCK = r"""**Lean 形式化**（`lean/`，Lean 4.34.1 + Mathlib v4.34.1；全部从原始定义出发，没有 sorry，只依赖三条标准公理）

| 文件 | 报告编号 | 内容 |
|---|---|---|
| `A207123/Basic.lean` | T1.1 | 按高度序列定义 `U k m`（`L k m` 的成员恰是长 k、取值 ≤ m、每个相邻三元组都好的列表；`legal_iff_getElem` 给出逐下标刻画）；引理 1：`lemma1`（k≥3）、`lemma1_one`、`lemma1_two`、`U_zero_left`、`U_zero_right`；引理 1 的三类分解抽成 `L_split`（`L_split_disjoint`、`L_split_inj`），供按上升数细化复用 |
| `A207123/Reduction.lean` | T1.0(a)(b) | 原题定义：`a k n` = 满足行规则（不含 001、010）与列规则（不含 001、011）的 n×k 0/1 矩阵个数；`a_eq : a k n = U k ((n+1)/2) * U k (n/2)` |
| `A207123/Multichain.lean` | T1.0(c) | 允许行 `AllowedRow`（`rowRule_iff_allowed`：原题行规则 ⇔ 每行都是允许行）、偏序集 `Lam k`（逐分量序）；`U_eq_multichains`：U_k(m) = Λ_k 中 m 元多重链 x_1≤⋯≤x_m 的个数；`card_Lam`：R_k=\|Λ_k\|=U_k(1) |
| `A207123/Recurrence.lean` | T1.3(1)(2) | b_i、P_m、W_m（任意交换环）与 G_m；`G_rec`、`P_mul_G`（P_m·G_m=W_m）、`X_mul_W`；`isCoprime_W_P`（Q[x] 中互素：W_m≡W_i (mod b_i)，再按不可约公因子的次数用正性、Gauss 引理、有理根定理排除）、`natDegree_P`、`P_recurrence`、`order_lower_bound`、`min_order`（最小递推阶恰为 3m+1）、`P_dvd_of_mul_G_poly`（既约分母恰为 P_m） |
| `A207123/Binomial.lean` | T1.4 | 组合定义 `N k q`（`mem_NW`：长 k、合法、值域恰为 {1..q}）；`U_eq_sum_N`（二项式基：按值域分类 + 严格增映射保持合法性）、`N_inv`/`N_inv_zero`（容斥式）、`N_tri`（三角递推，k≥3）、`N_init`、`N_tri_fails_at_two`、`N_tri_one`/`N_tri_two`（初值更正与 N(−1,·)、N(−2,·) 约定）、`N_diag`、`N_subdiag` |
| `A207123/Formula.lean` | T2.4 主公式 | 推荐显式公式 `U_explicit`：第一项用 Mathlib 的第二类 Stirling 数 `Nat.stirlingSecond`，第二项的 H(m,s,j) 写成 `hc s (vars j m)`（完全齐次对称多项式 h_s 在 m,m−1,…,j 处的值）；路线是闭式 `F` 满足与引理 1 相同的递推（`U_eq_F`） |
| `A207123/Ascent.lean` | T2.2、T2.4 第二式 | 上升数 `asc`（`asc_eq_card` 逐下标刻画）、`Us k m s`（`sum_Us`：按 s 求和回到 U）；按 s 细化的引理 1：`lemma1_asc`、`lemma1_asc_s0`、`lemma1_asc_one`、`lemma1_asc_two`、`Us_zero_left`、`Us_zero_right`；`Us_explicit`（T2.4 第二式，二项式约定由守卫条件实现） |
| `A207123/NonDFinite.lean` | T3.7(1) 的 ODE 部分、T3.7(2) | `no_x_ODE`（系数取 C[x][[t]]）、`no_x_ODE_poly`（系数取 C[x,t]）、`no_k_only_recurrence`（p_ab∈C[k]）：θ=x·d/dx 或 d/dx 作用在 W/P 上的分子递推及其模 P 的最高阶系数（`Bseq_mod`、`Dseq_mod`），在 b_m 的实根 x_m∈(0,1) 处比较「最高阶极点」系数；只用正性 W_m(x_m)≥1，不依赖 T1.3(2) 的互素性 |
| `Axioms.lean` | — | 对上述 54 条定理 `#print axioms`：全部只依赖 propext、Classical.choice、Quot.sound（其中 `rowRule_iff_allowed` 只用到 propext、Quot.sound）；另对 A207123 各模块的全部 758 个声明（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个 |
| `Checks.lean` | — | 用 `native_decide` 把定义与数据对照：任务说明第 2 节（k=7、10 两行，R_1..R_10，a_3(1..6)）、(C3) 的 N 三角形 k=7、10 两行（经 `N_inv`、`U_eq_F` 计算）、U_6(3,s) 与 U_7(2,s)（经 `Us_explicit` 计算，对照 Python 按定义暴力枚举的数据）；这是计算核对，依赖编译器，不是证明的一部分 |
| `run_lean_checks.sh` | — | 依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`，输出写入 `logs/lean_build.log` |

重跑：在 `lean/` 下运行 `./run_lean_checks.sh`，或依次运行 `lake build`、`lake env lean Axioms.lean`、`lake env lean Checks.lean`（首次需要下载 Mathlib 缓存，约 5–7 GB；之后 `lake build` 每次要核对全部 Mathlib 构建记录，约 3–6 分钟，单个文件编译约 0.5–1 分钟，冷启动时加载 Mathlib 可能要十几分钟）。输出见 `logs/lean_build.log`。

"""
s = s[:a] + LEAN_BLOCK + s[b:]
open(path, 'w', encoding='utf-8').write(s)
print('patched', path[-28:], 'Lean block')
