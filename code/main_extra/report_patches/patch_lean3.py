# -*- coding: utf-8 -*-
"""Lean 形式化第三轮（2026-10-05）完成后同步报告分节。

新增形式化：T3.7(1) 的最后一步（D-finite 的定义、引理 D1、F 不是 D-finite，DFinite.lean）；
T3.8 的 Rel(U)=O_U·L1（OreRel.lean）与 Rel(N)=O_N·L_N、饱和引理 (i)(ii)（OreRelN.lean）。
用法：py -3.14 code/main_extra/report_patches/patch_lean3.py
（先运行 lean/run_lean_checks.sh；本脚本从 logs/lean_build.log 读取全量扫描的声明数，并断言
三步退出码都是 0、依赖其他公理的声明为 0 个；每处替换都断言原文恰好出现一次；
最后再运行 code/main_extra/assemble_report.py 重新拼接报告）。
"""
import re
import sys

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

# ---------- 从构建日志读取全量扫描结果 ----------
log = open(ROOT + r'\logs\lean_build.log', encoding='utf-8').read()
codes = re.findall(r'\[exit code (\d+)\]', log)
assert codes == ['0', '0', '0'], codes
m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[([^\]]*)\]；依赖其他公理的声明：(\d+) 个', log)
assert m, 'sweep line not found'
NDECL, AXS, NBAD = m.group(1), m.group(2), m.group(3)
assert NBAD == '0', NBAD
assert set(a.strip() for a in AXS.split(',')) == {'Quot.sound', 'Classical.choice', 'propext'}, AXS
NPRINT = len(re.findall(r"^'A207123\.[^']*' depends on axioms", log, flags=re.M))
assert NPRINT == 83, NPRINT
print('sweep:', NDECL, 'declarations;', NPRINT, '#print axioms lines')


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


# ---------- 00_head：Lean 一段 ----------
OLD_HEAD_A = r"- Lean 形式化（2026-10-05 补做，同日第二轮扩充）："
NEW_HEAD_A = r"- Lean 形式化（2026-10-05 补做，同日第二、三轮扩充）："
OLD_HEAD_B = (r"F 关于 x 没有多项式系数 ODE（T3.7(1) 的 ODE 部分）与不存在系数只依赖 k 的象限递推（T3.7(2)）。")
NEW_HEAD_B = (r"F 不是 D-finite（T3.7(1)，含 D-finite 的定义（Lipshitz Def. 2.1）与引理 D1，对任何系数域 K⊆C）"
              r"与不存在系数只依赖 k 的象限递推（T3.7(2)）、U 与 N 的全部多项式系数象限递推恰为 L1、L_N 生成的左理想"
              r"（T3.8 的 Rel(U)=O_U·L1、Rel(N)=O_N·L_N，含饱和引理）。")
OLD_HEAD_C = r"（T3.7 中 D-finite 的定义与引理 D1、T3.7(3) 没有形式化）。"
NEW_HEAD_C = r"（T3.7(3) 与 T3.8 的维数公式没有形式化）。"
patch(P + '00_head.md', [(OLD_HEAD_A, NEW_HEAD_A), (OLD_HEAD_B, NEW_HEAD_B), (OLD_HEAD_C, NEW_HEAD_C)])

# ---------- 01_summary：第 11 条 ----------
OLD_SUM = (r"按上升数细化的引理 1 与两个显式公式（T2.2、T2.4）、F 没有 x 方向多项式系数 ODE 与没有 k-only 象限递推"
           r"（T3.7(1)(2)）已在 Lean 4 + Mathlib 中从原始定义形式化证明")
NEW_SUM = (r"按上升数细化的引理 1 与两个显式公式（T2.2、T2.4）、F 不是 D-finite（含定义与引理 D1）与没有 k-only 象限递推"
           r"（T3.7(1)(2)）、Rel(U)=O_U·L1 与 Rel(N)=O_N·L_N（T3.8，含饱和引理）已在 Lean 4 + Mathlib 中从原始定义形式化证明")
patch(P + '01_summary.md', [(OLD_SUM, NEW_SUM)])

# ---------- 04_C3：T3.7、T3.8 标签与 T3.8 的 Lean 说明 ----------
OLD_T37 = (r"【已证明；已在 Lean 中形式化：(1) 的 ODE 部分 `A207123.no_x_ODE`（系数取 C[x][[t]]）与 `no_x_ODE_poly`"
           r"（系数取 C[x,t]），(2) `A207123.no_k_only_recurrence`（p_ab∈C[k]）；D-finite 的定义与引理 D1、(3) 未形式化】")
NEW_T37 = (r"【已证明；已在 Lean 中形式化：(1) 全部——ODE 部分 `A207123.no_x_ODE`（系数取 C[x][[t]]）与 `no_x_ODE_poly`"
           r"（系数取 C[x,t]），D-finite 的定义 `IsDFinite`（按 c3b §4 的 Lipshitz Def. 2.1，n=2）、引理 D1 "
           r"`exists_x_ODE_of_isDFinite`（另有 t 方向 `exists_t_ODE_of_isDFinite`）与「F 不是 D-finite」"
           r"`not_isDFinite_FK`（对任何系数域 K⊆C）；(2) `A207123.no_k_only_recurrence`（p_ab∈C[k]）；(3) 未形式化】")
OLD_T38 = r"**T3.8（全部多项式系数递推 = 引理 1 生成的左理想）【已证明】**"
NEW_T38 = (r"**T3.8（全部多项式系数递推 = 引理 1 生成的左理想）【已证明；Rel(U)=O_U·L1 与 Rel(N)=O_N·L_N 已在 Lean 中形式化："
           r"`A207123.RelU_eq`、`RelU_iff_mem_span`、`RelN_eq`、`RelN_iff_mem_span`（O_U、O_N 取为 C^{N×N} 上由乘 k、"
           r"乘 m（或 q）与位移 X、E^{−1}（或 Y）生成的线性算子代数，负下标补 0；`exists_normal_form`、"
           r"`normal_form_unique` 证明它就是 Ore 代数），饱和引理 (i)(ii)：`saturation_Y`、`saturation_one_add_Y`；"
           r"维数公式未形式化】**")
OLD_T38P = r"（第二轮两位复核者逐步重推了搬运恒等式、局部化与饱和引理）。"
NEW_T38P = (r"（第二轮两位复核者逐步重推了搬运恒等式、局部化与饱和引理）。"
            r"Lean 形式化（`lean/A207123/OreRel.lean`、`OreRelN.lean`）中，U 的部分按上面的约化与命题 A"
            r"（`red_of_mem`、`pure_ann_zero`）；N 的部分换了一种搬运写法：用二项式变换 (Pf)(k,m)=Σ_q C(m,q)f(k,q)，"
            r"V:=P·N 满足 V(k,m+1)=U_k(m)；由 ΔPY=YP、Pq=mΔP（Δ:=1−Y）得搬运恒等式 L1V·P=Δ·P·L_N"
            r"（L1V:=1−Y−X−(m−1)X³，Y·L1=L1V·Y），全程只出现 (1+Y) 型分母，最后用饱和引理 (ii) 剥掉，"
            r"不需要微分算子环与局部化。")
patch(P + '04_C3.md', [(OLD_T37, NEW_T37), (OLD_T38, NEW_T38), (OLD_T38P, NEW_T38P)])

# ---------- 09_code：Lean 表 ----------
OLD_NDF = (r"只用正性 W_m(x_m)≥1，不依赖 T1.3(2) 的互素性 |")
NEW_NDF = (r"只用正性 W_m(x_m)≥1，不依赖 T1.3(2) 的互素性 |" "\n"
           r"| `A207123/DFinite.lean` | T3.7(1) 的最后一步 | `IsDFinite K f`（Lipshitz Def. 2.1，n=2：f 的全部偏导数 "
           r"∂_x^i∂_t^j f 在 Frac(K[[x,t]]) 中张成的 K(x,t)-子空间有限维；K(x,t) 取为 K[x,t] 的像生成的子域，"
           r"`mem_ratFn_iff`、`isFractionRing_ratFn` 说明它就是 K(x,t)，`dXK_dTK_comm` 说明 ∂_x^i∂_t^j 穷尽全部偏导数，"
           r"`isDFinite_one` 说明定义不是恒假的）；引理 D1 `exists_x_ODE_of_isDFinite`、`exists_t_ODE_of_isDFinite`；"
           r"`not_isDFinite_FK`（任何域 K 与环同态 σ:K→C）、`not_isDFinite_Fxt`（K=C） |" "\n"
           r"| `A207123/OreRel.lean` | T3.8（U） | 算子作用在 C^{N×N} 上（负下标补 0）：乘法算子 `mulOp`、位移 `opX`、`opEinv`；"
           r"`OU` 是它们生成的子代数，Ore 交换律 `opX_mul_mulOp`、`opEinv_mul_mulOp`，正规形存在且唯一 "
           r"`exists_normal_form`、`normal_form_unique`；约化 `red_of_mem`（E^{−1}=1−X−mX³−L1）；命题 A "
           r"`pure_ann_zero`（单列情形 `col_zero`：在 b_0..b_m 各一个单根处比较最高阶极点系数，W_m 在根处非零用 "
           r"T1.3(2) 的互素性）；`RelU_eq`、`RelU_iff_mem_span` |" "\n"
           r"| `A207123/OreRelN.lean` | T3.8（N） | `LN`、`RelN`（O_N 与 O_U 是同一个 Ore 代数）；二项式变换 `opP` 与交换关系 "
           r"`opD_P_Y`（ΔPY=YP）、`P_mul_cM`（Pq=mΔP）、`opD_P_one_add`；搬运恒等式 `L1V_P`（L1V·P=Δ·P·L_N）；"
           r"`relV`（Rel(V)=O·L1V，由 `RelU_eq` 推出）；两个方向的交换引理 `exists_N_to_V`、`exists_V_to_N` 与边界消去 "
           r"`opD_pow_P_vanish`；饱和引理 `saturation_Y`、`saturation_one_add_Y`；`RelN_eq`、`RelN_iff_mem_span` |")
OLD_AX = (r"| `Axioms.lean` | — | 对上述 54 条定理 `#print axioms`：全部只依赖 propext、Classical.choice、Quot.sound"
          r"（其中 `rowRule_iff_allowed` 只用到 propext、Quot.sound）；另对 A207123 各模块的全部 758 个声明"
          r"（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个 |")
NEW_AX = (r"| `Axioms.lean` | — | 对上述 83 条定理 `#print axioms`：全部只依赖 propext、Classical.choice、Quot.sound"
          r"（其中 `rowRule_iff_allowed` 只用到 propext、Quot.sound）；另对 A207123 各模块的全部 " + NDECL + r" 个声明"
          r"（含辅助引理与自动生成的声明）做全量扫描，依赖其他公理的声明为 0 个 |")
patch(P + '09_code.md', [(OLD_NDF, NEW_NDF), (OLD_AX, NEW_AX)])

# ---------- 10_uncertain：⑥ 第 1 处、次一级第一条、完成度 C-3 ----------
s10 = open(P + '10_uncertain.md', encoding='utf-8').read()
i0 = s10.index('1. **T3.8 中 N 的版本：Rel(N)=O_N·L_N（定理 3′）。**')
i1 = s10.index('2. **T3.4(2) 的 K(x) 闭式')
OLD_U1 = s10[i0:i1]
assert OLD_U1.count('下一步：把饱和引理写成独立引理') == 1
NEW_U1 = (
    "1. **T3.8 的维数公式（U、N 两个版本）。**（原第 1 处「T3.8 中 N 的版本 Rel(N)=O_N·L_N」及其中的饱和引理已在 Lean 中"
    "形式化，见 ⑤，移出本节；T3.8 剩下没有形式化的就是这里的维数公式。）\n"
    "   为什么不确定：盒子维数 (A−2)·B·D(D+1)/2 与 (A−2)(B−1)·D(D+1)/2（及分次版）依赖角点论证与「整环 ⇒ ΛL=0 ⇒ Λ=0」的计数，"
    "只有书面证明。两位复核者（r-c3b、x2）都逐步重推过，并且独立指出了同一处问题：N 的情形「与 §6 同法」一句按字面不成立"
    "（已补正，公式不变）。数据上，verify_all 中属于 N 的 11 个盒子（c3b.C3B-E3B 8 个、c3b.C3B-E3S 3 个，其中 3 个是维数为 0 的"
    "边界情形；verify_all 的另外 11 个盒子检验的是 U 的版本），加上复核者新增的 N 盒子（r-c3b 12 个、x2 20 个），全部吻合"
    "（r-c3b 故意设计的晚起点攻击窗口除外，见下句），但数据只能检验有限个盒子。另外，N 的窗口里有大量零行，晚起点窗口会出现"
    "有限窗口伪关系，说明这类实验容易误导。\n"
    "   下一步：在 Lean 中形式化维数公式（正规形唯一性 `normal_form_unique` 与 Rel(U)、Rel(N) 的刻画已有，还缺「支撑与次数受限的"
    "关系恰为 Q·L」的角点论证与维数计数）；或用 k 方向更长的长方形窗口（例如 k≤100、q≤40）复核更多盒子，并报告非零行数。\n\n")
s10 = s10.replace(OLD_U1, NEW_U1)
open(P + '10_uncertain.md', 'w', encoding='utf-8').write(s10)
print('patched 10_uncertain (item 1)')
OLD_L2 = (r"- 除了已在 Lean 中机器检查的条目（T1.0、T1.1、T1.3(1)(2)、T1.4、T2.2 的细化引理 1、T2.4 两式、"
          r"T3.7(1) 的 ODE 部分与 T3.7(2)，见 ⑤）")
NEW_L2 = (r"- 除了已在 Lean 中机器检查的条目（T1.0、T1.1、T1.3(1)(2)、T1.4、T2.2 的细化引理 1、T2.4 两式、"
          r"T3.7(1)(2)、T3.8 的 Rel(U)=O_U·L1 与 Rel(N)=O_N·L_N，见 ⑤）")
OLD_C3 = r"（其中「F 没有 x 方向多项式系数 ODE」与「没有 k-only 象限递推」另有 Lean 形式化证明）"
NEW_C3 = (r"（其中「F 不是 D-finite」（含 D-finite 的定义与引理 D1）、「没有 k-only 象限递推」以及 Rel(U)=O_U·L1、"
          r"Rel(N)=O_N·L_N 另有 Lean 形式化证明）")
patch(P + '10_uncertain.md', [(OLD_L2, NEW_L2), (OLD_C3, NEW_C3)])
print('done')
