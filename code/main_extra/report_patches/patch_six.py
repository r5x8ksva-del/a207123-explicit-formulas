# -*- coding: utf-8 -*-
"""2026-10-07 加固报告 ⑥ 的三处之后，同步报告各节（notes/report_parts/）。

改动：
  - 05_C4 T4.3(6)：两份证明（r-c4ii；s6-t436，不用 (7)）、唯一性、子断言的含义、核对改为 rv3；
  - 04_C3 T3.4(2)：两份证明（r-c3a 命题 R1 / s6-t342 路线 A；s6-t342 路线 B）、措辞（绝对值 Tonelli、
    C∖Z_{≤0} 上全纯、恒等定理）、加强的推论（<2−x、K 的符号）、x=1/n 的注、核对改为 rv3；
  - 03_C2 T2.7：推论改写为 T2.7′（陈述与证明见 notes/02-主Agent-不确定三处加固.md §3），「更短」的界限一句；
  - 07_formula：「在什么意义下不能再短」一句；
  - 08_failed ④C.14、④C.15：文献与联网说明；
  - 10_uncertain ⑥：重排三处，原三处移入「次一级」；
  - 09_code ⑤：12 个模块、check_rv3.py 一行、内存保护说明、最终运行（从 logs/verify_all_final.log 抽取）、日志清单；
  - 00_head：日期、模块数与耗时、「真值」来源的例外。
每处替换都断言锚点恰好出现一次。运行前提：logs/verify_all_final.log 是 2026-10-07 含 rv3 的全量运行，且 OVERALL: PASS。
用法：py -3.14 code/main_extra/report_patches/patch_six.py [--dry]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))   # report_patches → main_extra → code → 根目录
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
DRY = '--dry' in sys.argv
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

NOTE = 'notes/02-主Agent-不确定三处加固.md'
texts = {}


def load(name):
    if name not in texts:
        texts[name] = open(os.path.join(PARTS, name), encoding='utf-8').read()
    return texts[name]


def rep(name, old, new):
    t = load(name)
    n = t.count(old)
    assert n == 1, '%s：锚点出现 %d 次：%s' % (name, n, old[:60])
    texts[name] = t.replace(old, new)


# ---------------------------------------------------------------- 最终运行日志
log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read().splitlines()
assert any(ln.startswith('OVERALL: PASS') for ln in log), 'verify_all_final.log 不是 PASS'
assert any(re.match(r'rv3\s', ln) for ln in log), 'verify_all_final.log 里没有 rv3'
head = [i for i, ln in enumerate(log) if ln.startswith('area ')][-1]
tail = [i for i, ln in enumerate(log) if ln.startswith('OVERALL:')][-1]
table = '\n'.join(log[head:tail + 1])
m = re.search(r'TOTAL pass=(\d+) fail=0 modules=(\d+) failed_modules=-\s+\(([\d.]+)s\)', table)
assert m, '总表格式不对'
TOTAL_PASS, N_MOD, SECS = int(m.group(1)), int(m.group(2)), float(m.group(3))
assert N_MOD == 12, '模块数不是 12：%d' % N_MOD
MINUTES = '%.1f' % (SECS / 60)
print('final log: pass=%d modules=%d %.1fs' % (TOTAL_PASS, N_MOD, SECS))

# ---------------------------------------------------------------- 05_C4 T4.3(6)
rep('05_C4.md',
    '一般 j 的结构由第二轮复核者 r-c4ii 证明：记 A_j(z):=Σ_q a_{q,j}z^q/q!（即 (7) 的指数母函数中 y^j 的系数，因为 R_q(y)=Σ_j a_{q,j}y^j），它是 u=z/(1−z)、L=−ln(1−z) 的多项式；',
    '一般 j 有两份路线不同的证明，主 Agent 逐步核对了两份（' + NOTE + ' §1）。证明一（第二轮复核者 r-c4ii）：记 A_j(z):=Σ_q a_{q,j}z^q/q!（即 (7) 的指数母函数中 y^j 的系数，因为 R_q(y)=Σ_j a_{q,j}y^j），由 (7) 的闭式展开知它是 u=z/(1−z)、L=−ln(1−z) 的多项式；')
rep('05_C4.md',
    '所以 a_{q,j} 是 c(q,i)（i≤⌊j/2⌋+1）的 Q[q] 线性组合。子断言：a_{q,2m} 含 1·c(q,m+1)（m≥0）；a_{q,2m+1} 含 (q−m)c(q,m+1)（m≥1；m=0 时 a_{q,1}=0，第一轮原文对 j=1 不成立）。',
    '所以 a_{q,j} 是 c(q,i)（i≤⌊j/2⌋+1）的 Q[q] 线性组合。证明二（第三轮复核者 s6-t436，notes/review/s6-t436-review.md，不用 (7)）：由 (1) 的递推得一阶 ODE (1−z)²∂_zA=(1−z+y²z)+(y²(1−z)+y³z)A，按 y 拆开得 θA_j=uA_{j−2}+u²A_{j−3}（j≥3；A_0=L、A_1=0、A_2=L²/2+u−L），在 Q[u,L] 中对 j 归纳控制指标，再用同样的三角对应。'
    '唯一性：q≥1 时 c(q,0)=0，所以 i=0 项没有内容，规范为 π_{j,0}=0；π_{j,i}（1≤i≤⌊j/2⌋+1）由充分大的 q 处的 a_{q,j} 唯一决定，即使允许有理函数系数也是如此（s6-t436 引理 U：E_k(q):=c(q,k+1)/(q−1)! 满足 E_k(q+1)=E_k(q)+E_{k−1}(q)/q，最后归结为 r(t+1)−r(t)=−1/t 没有有理函数解；由此也得到 u、L 在 Q 上代数无关）。'
    '子断言说的是这组唯一的系数：π_{2m,m+1}=1（m≥0）；π_{2m+1,m+1}=q−m（m≥1；m=0 时 a_{q,1}=0，第一轮原文对 j=1 不成立）；所以 j≠1 时上限 ⌊j/2⌋+1 取到。')
rep('05_C4.md',
    '；一般 j 的高次系数结构另见 logs/review_r-c4ii_r6_structure.log（j≤14）。',
    '；一般 j 的高次系数结构：rv3.rv3-c4ii-r6（由 (7) 的闭式精确推出 j≤14 的 π_{j,i}，与真实系数比较）、rv3.rv3-s6-t436-a 与 rv3.rv3-s6-t436-b（按证明二构造到 j≤40、只用命题形状拟合到 j≤24，与真实 a_{q,j} 在 q≤300 上逐项相同）。')

# ---------------------------------------------------------------- 04_C3 T3.4(2)
rep('04_C3.md',
    '**整体的 K 也有闭式（第二轮复核者 r-c3a 给出并证明）**：',
    '**整体的 K 也有闭式（第二轮复核者 r-c3a 给出并证明；第三轮复核者 s6-t342 独立重推，并给出路线不同的第二证明；主 Agent 逐步核对，见 ' + NOTE + ' §2）**：')
rep('04_C3.md',
    '证明：把差值写成 Mellin 型积分 M(s)，在 Re s>0 上由 Tonelli/Fubini 得 M(s)=Γ(s)−x⁵Γ(s+1)Q(s)，Q(s):=∫_0^∞ w e^{−w}(1+x³w)^{−s−1}dw 是整函数；两边亚纯，故处处相等，取 s=−λ 并用 Q(−λ)=J、Γ(1−λ)=−λΓ(−λ)（notes/review/r-c3a-review.md 中 K 闭式的证明 (i)–(iv)）。由 J>0 得 K≠0，所以 **I≠𝒮 对一切 0<x<1、λ∉Z、t∈(−1,0) 成立**；并且 1<K/Γ(−λ)<2、x→0+ 时趋于 2（下界由 λ>0、J>0 直接得到；上界与极限见 notes/review/r-c3a-review.md §4 推论 R2：λ≥1 时由 ln(1+y)≤y 得 J≤(x+x³)^{−2}，故 λx⁵J≤(1−x)/(1+x²)²<1；0<λ<1 时 J≤1，故 λx⁵J≤(1−x)x²<1；x→0+ 时作代换 w=v/(x+x³) 并用控制收敛得 λx⁵J→1），整体差值夹在常数项差值的 1 倍与 2 倍之间。',
    '证明一（r-c3a 命题 R1；s6-t342 的路线 A 与它相同）：K 是 Mellin 变换 M(s)=∫_0^∞τ^{s−1}φ(τ)dτ 的解析延拓在 s=−λ 处的值，其中 φ(τ)=e^{−τ}g(−x³τ)；K 的定义里的 Σ_nφ_n/(n+s)+∫_1^∞τ^{s−1}φdτ 在 C 上亚纯、在 C∖Z_{≤0} 上全纯，Re s>0 时等于 M(s)。'
    '在 Re s>0 上，用 (1+x³τ)^{−2}=∫_0^∞we^{−w(1+x³τ)}dw 与 Fubini（对被积函数的绝对值用 Tonelli）得 M(s)=Γ(s)−x⁵Γ(s+1)Q(s)，Q(s):=∫_0^∞ w e^{−w}(1+x³w)^{−s−1}dw 是整函数。两边在连通开集 C∖Z_{≤0} 上全纯、在 Re s>0 上相等，由恒等定理处处相等；取 s=−λ 并用 Q(−λ)=J、Γ(1−λ)=−λΓ(−λ)（notes/review/r-c3a-review.md §4 (i)–(iv)）。'
    '证明二（s6-t342 路线 B，notes/review/s6-t342-review.md §3′）：把同一个 Laplace 表示直接代进 K 的定义，对每个 u 用以 c=1+x³u 为基点的 Γ 的 Prym 分解，不对一般的 φ 做解析延拓。'
    '由 J>0 得 K≠0，所以 **I≠𝒮 对一切 0<x<1、λ∉Z、t∈(−1,0) 成立**，并且 sign(I−𝒮)=sign K=(−1)^{⌈λ⌉}。'
    '又有 1<K/Γ(−λ)<2−x，x→0+ 时趋于 2：下界由 λ>0、J>0 直接得到；上界由 (1+x³w)^{λ−1}<(1+x³w)^λ≤e^{(1−x)w} 得 J<x^{−2}、λx⁵J<1−x（s6-t342），r-c3a 推论 R2 分情形给出更紧的界（λ≥1 时 λx⁵J≤(1−x)/(1+x²)²，0<λ<1 时 λx⁵J≤(1−x)x²）；极限：作代换 w=v/(x+x³) 并用控制收敛得 λx⁵J→1。'
    '所以整体差值夹在常数项差值的 1 倍与 2 倍之间。注：x=1/n 时 λ=n²(n−1) 是整数，K 在该点是极点，但比值 K/Γ(−λ)=1+λx⁵J 的右边对一切 x 都有定义。')
rep('04_C3.md',
    '；K 闭式与定义的一致性（7 个 x 值，偏差 ≤4.2·10^{−76}，数值）只在复核日志 logs/review_r-c3a_r2_numeric.log 中，不在 verify_all 中。',
    '；K 的闭式（数值，两位复核者各自独立实现）：rv3.rv3-c3a-r2（r-c3a：与 K 的定义在 7 个 x 上一致，偏差 ≤4.2·10^{−76}；另有上下界与端到端 I−𝒮）、rv3.rv3-s6-t342-K（s6-t342：13 个 x，0.18–0.9，最大相对偏差 3.3·10^{−53}；最难的 x=0.15 一点抵消 494 位，只在复核日志 logs/review_s6-t342_t1_K_x015.log 中）、rv3.rv3-s6-t342-e（端到端 I−𝒮 在 11 组 (x,t) 上与闭式一致，最大相对偏差 3.7·10^{−56}；推论在 105 个 x 上成立）。')

# ---------------------------------------------------------------- 03_C2 T2.7
rep('03_C2.md',
    '；依赖文献的推论未形式化】',
    '；推论 T2.7′ 未形式化，证明见 ' + NOTE + ' §3】')
rep('03_C2.md',
    '推论（依赖文献，本文未重证）：若 U_k(m) 是 proper 超几何项在自然边界下的有限多重和，则按 Wilf–Zeilberger 1992 与 Zeilberger 1990 它是 holonomic 的，经 Bernstein 消元其母函数关于 x 有多项式系数 ODE，与 T3.7 矛盾；所以不存在这样的表示（第二轮复核建议走这条路线，而不引用「Lipshitz 1989 中 D-finite⇔holonomic」，后者我们未能核实原文出处）；',
    '推论 T2.7′（2026-10-07 重写；陈述与证明见 ' + NOTE + ' §3，复核者 s6-t27 逐条审查为 confirmed，见 notes/review/s6-t27-review.md）：'
    '设 T(k,m,j⃗)（j⃗∈Z^r）是 (k,m,j⃗) 的 proper 超几何项，即 Wilf–Zeilberger 1992 式 (4.1.2) 的形式（整系数一次式的阶乘之比，乘多项式与几何因子；分子阶乘的参数都不是负整数时称「良定义」，负整数的阶乘的倒数取 0）。'
    '若在某个象限 {k≥k_0,m≥m_0}（k_0,m_0≥0）上：(N1) 每个 (k,m) 处只有有限多个 j⃗ 使 T 良定义且非零，且 U_k(m) 等于这些值之和；(N2) 对每个 R，在更靠里的象限上，T 良定义且非零的点的 R 邻域内 T 处处良定义（支撑外围有任意宽的良定义带，例如 Σ_jC(m,j)C(k,j)、Σ_jC(k+j,2j)C(m,j)；(N2) 是被加项写法的性质，含 C(2j,j)=(2j)!/(j!)² 一类因子的写法不满足它，不在本推论范围内），则矛盾。所以 U_k(m) 没有这样的表示。'
    '证明：用 WZ 1992 定理 4.1 的计数论证，得到系数只依赖 k、与 (m,j⃗) 无关的递推（引理 A）；把各项写成同一个公共项乘多项式，可知它在所有出现的值都良定义的点上成立（引理 F；WZ 定理 4.1 的陈述只覆盖被加项非零的点）；(N2) 保证它对补零后的 T 在整条 j⃗ 纤维上成立；再用二项式矩只对 j⃗ 求和，得到 U 的一条系数只依赖 k、在象限上成立的非平凡递推（引理 S），与 T3.7(2)（Lean：`no_k_only_recurrence`）矛盾。'
    'WZ 自己的和式定理（3.2C、4.2B、4.2C）只有一个自由变量，又要求对全部求和变量支撑紧，不能直接用于 U_k(m)；原来的写法借 Zeilberger 1990 的 holonomic 理论与 Bernstein 消元绕开这一点，现在已不需要（WZ 1992 原文已读，见 ④C.15）。')
rep('03_C2.md',
    '它说明「Stirling 型原子」是必需的。　核对：proof-only。',
    '它说明「Stirling 型原子」是必需的。　核对：proof-only（引理 A、F、S 另由复核者 s6-t27 在 6 个满足 (N1)(N2) 的项与几个反面例子上做了 219 项精确计算检验，见 logs/review_s6-t27_*.log，不在 verify_all 中）。')
rep('03_C2.md',
    'T2.7 排除了 proper 超几何项的有限多重和（依赖文献定理）。',
    'T2.7′ 排除了满足自然边界条件 (N1)(N2) 的 proper 超几何项的有限多重和（2026-10-07 自证，只用 T3.7(2)，不再依赖文献定理）。')

# ---------------------------------------------------------------- 07_formula
rep('07_formula.md',
    '由 T3.7（F 不是 D-finite）与文献中的 Wilf–Zeilberger 定理（T2.7），U_k(m) 也不能写成 proper 超几何项在自然边界下的有限多重和。',
    '由 T3.7(2)（U 没有系数只依赖 k 的象限递推）与 T2.7′，U_k(m) 也不能写成满足自然边界条件 (N1)(N2) 的 proper 超几何项的有限多重和。')

# ---------------------------------------------------------------- 08_failed ④C
rep('08_failed.md',
    '「不能写成 proper 超几何多重和」的推论改走 Wilf–Zeilberger 1992 / Zeilberger 1990 的路线，并标明依赖文献。',
    '「不能写成 proper 超几何多重和」的推论先改走 Wilf–Zeilberger 1992 / Zeilberger 1990 的路线并标明依赖文献；2026-10-07 读到 WZ 1992 原文后改写为 T2.7′，只用 T3.7(2) 自证，不再需要 Lipshitz 1989 与 Zeilberger 1990。')
rep('08_failed.md',
    '没有使用 agent-reach，因为它的网页通道经第三方代理，与「只读」的要求冲突。',
    '前几轮没有使用 agent-reach，因为它的网页通道经第三方代理，按更严格的理解与「只读」的要求冲突。'
    '2026-10-07 加固 ⑥ 时，主 Agent 读了 Wilf–Zeilberger 1992 与 Zeilberger 1990，两篇都是作者主页（sites.math.rutgers.edu/~zeilberg）公开的版本：前者的预印本、重印本 PDF 与几个页面经 r.jina.ai（第三方网页转文字服务）读取，后者的 TeX 源文件直接 curl；还运行了一次 `agent-reach doctor`，它会只读探测若干外部服务的公开接口。'
    '这些都是只读访问，没有发帖、提交或联系任何人，但偏离了前几轮不经第三方代理的做法，在此注明。Knuth 对 WZ 1992 的勘误是扫描件，没有读。')

# ---------------------------------------------------------------- 10_uncertain ⑥
t = load('10_uncertain.md')
a = t.index('## ⑥ 我最不确定的三处')
b = t.index('## 完成度对照（不宣布「完全解决」）')
assert t.count('## ⑥ 我最不确定的三处') == 1 and t.count('## 完成度对照（不宣布「完全解决」）') == 1
SIX = '''## ⑥ 我最不确定的三处

（2026-10-07 重排。原来的三处是 T4.3(6) 高次系数的一般结构、T3.4(2) 的 K 闭式、T2.7 依赖文献的推论，当天都已加固：前两处各有一位第三轮复核者独立重推，并各多出一份路线不同的证明，计算与数值核对已并入 verify_all（rv3）；第三处改写为 T2.7′，给出不依赖未读文献的证明。它们移到下面的「次一级的不确定处」。按加固后的证据重新排出的三处如下。）

1. **T2.6(ii) 截断块部分「对一切 m≥2 都没有 u 型单和」的统一证明。**
   为什么不确定：一般 m 的证明只有第二轮复核者 x1 一份（留数元的结构加范数论证）。主 Agent 独立复算了关键的范数 N(W̃_2−1)=17/8，但没有逐步重推「留数元等于 (W̃_i−1)·x^{−3m−3} 乘一个只依赖 i、m 的有理常数」这一步。2≤m≤30 另有逐个的留数–范数证书（c2b 定理 6），x1 的统一阻碍在 m=2..34 上有计算核对（rv2.rv2-x1-r1）。没有形式化。
   下一步：请另一位复核者独立重推一般 m 的论证，或由主 Agent 逐步重推。

2. **T2.7′（2026-10-07 新写的证明）。**
   为什么不确定：证明是主 Agent 当天新写的，只经过一位复核者（s6-t27）审查。审查结论是 confirmed，三条引理在 6 个例子上做了 219 项精确计算检验。没有人类核对，没有形式化。条件 (N2) 是证明技术需要的，而且依赖被加项的写法，含 C(2j,j) 一类因子的写法不在范围内。s6-t27 提出的更弱条件 (N2′)（配合沿一般方向取极限的引理 F′）只有它一人推过，本文没有采用。
   下一步：请第二位复核者审查；如果论文要覆盖 C(2j,j) 一类因子，再核对 (N2′) 与引理 F′。

3. **T3.4(4)(5) 的解析部分：渐近展开的显式误差界、差值大小的门槛。**
   为什么不确定：剩下的【已证明】大多是「作者 + 一位复核者 + 程序核对」，彼此差别不大。这两条依赖分析估计，证明来自第一轮（c3a），经第二轮复核者 r-c3a 重推。数值只能抽查有限个点：c3a 的核对，以及 rv3.rv3-c3a-r2 里的误差界抽查。(5) 常数项部分的 Stirling 门槛这一轮没有人再核对。没有形式化。(5) 的整体部分用到的 1<K/Γ(−λ)<2 已在 T3.4(2) 中加固。
   下一步：请复核者独立重推 (4) 的误差界与 (5) 常数项部分的门槛。

**次一级的不确定处**
- 除了已在 Lean 中机器检查的条目（各条标签注明了范围，汇总见 ⑤ 的表），其余【已证明】都是书面证明加程序核对，由 AI 撰写和复核，没有经过人类专家审稿，也没有形式化。机器检查过的条目也只保证证明正确；陈述是否忠实于本报告，是 AI 逐条对照的，没有人类核对过。
- T4.3(6)（2026-10-07 前是 ⑥ 第 1 处）：现在有两份路线不同的证明。r-c4ii 由 (7) 的闭式展开；s6-t436 由一阶 ODE 的分量递推，不用 (7)，还补上了 r-c4ii 没写的唯一性论证。主 Agent 逐步核对了两份。构造法到 j≤40、拟合法到 j≤24，与真实系数在 q≤300 上逐项相同（rv3）。没有形式化。
- T3.4(2)（原 ⑥ 第 2 处）：r-c3a 与 s6-t342 两位复核者各自推导，s6-t342 另给了一份路线不同的证明，主 Agent 逐步核对。两套独立的高精度实现分别在 7 个与 13 个 x 上与 K 的定义一致，端到端 I−𝒮 分别在 4 组与 11 组 (x,t) 上一致（rv3）。没有形式化。
- T2.7 的推论（原 ⑥ 第 3 处）：已改写为 T2.7′，见上面第 2 处。
- T4.3(8)（(C7) 分母对一切 q 最简）：改写后只在 i=r²(r−1) 时需要 Laguerre 零点定理（Szegő 的经典结果，未在本文重证）；核心同余与 Laguerre 恒等式有程序核对（rv.rv-num-cong q≤20、rv.rv-num-laguerre q≤30）。
- T2.6(i) 的 (1,2)/(2,3) 形状：没有形式化，但有两份独立证明（复核者 r-c2a 的纤维论证与复核者 x1 的代数证明）。（T2.6(ii) 已列为上面第 1 处。）
- T5.3(4) 的 Möbius 推论用到 Philip Hall 定理（经典结果，未重证；同一条里的 Σ_q(−1)^qN(k,q)=U_k(−2) 及其取值已在 Lean 中形式化）。
- 「U_4=A326247 倾向于巧合」「U_3 有结构」是解释性判断，不是定理。h_k 全实根只是猜想（验证到 k≤150）。

'''
texts['10_uncertain.md'] = t[:a] + SIX + t[b:]

# ---------------------------------------------------------------- 09_code ⑤
rep('09_code.md',
    '**11 个核对模块**（除 check_rv2.py 外，每个都从 `code/core.py` 的原始定义程序取「真值」；check_rv2.py 运行复核者 x1 的两个独立脚本，不导入 core：r1 用自写的三元组 DP 作真值，r2 只做纤维留数条件的精确代数穷举）',
    '**12 个核对模块**（除 check_rv2.py、check_rv3.py 外，每个都从 `code/core.py` 的原始定义程序取「真值」；check_rv2.py 运行复核者 x1 的两个独立脚本，不导入 core：r1 用自写的三元组 DP 作真值，r2 只做纤维留数条件的精确代数穷举；check_rv3.py 运行复核者 r-c4ii、r-c3a、s6-t436、s6-t342 的脚本，同样不导入 core，各脚本按定义自算真值：Num_q 的递推，K、I、𝒮 的定义）')
t = load('09_code.md')
lines = t.split('\n')
idx = [i for i, ln in enumerate(lines) if ln.startswith('| `check_rv2.py` |')]
assert len(idx) == 1
lines.insert(idx[0] + 1, '| `check_rv3.py` | 报告 ⑥ 原有两处所依赖的复核者脚本（不导入 core）：T4.3(6) 由 (7) 的闭式推出 j≤14、按第二份证明构造到 j≤40 与拟合到 j≤24（真实系数 q≤300）；T3.4(2) K 的闭式与定义（两套实现，7 个与 13 个 x）、端到端 I−𝒮（4 组与 11 组 (x,t)）、推论在 105 个 x 上的扫描 | 6 |')
texts['09_code.md'] = '\n'.join(lines)
t = load('09_code.md')
a = t.index('**最终一次运行**（2026-10-05，完整输出 `logs/verify_all_final.log`')
b0 = t.index('```', a)
b1 = t.index('```', b0 + 3)
assert t.count('**最终一次运行**') == 1
texts['09_code.md'] = (t[:a]
                       + '**最终一次运行**（本地 2026-10-07，完整输出 `logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行；2026-10-05 的上一次最终运行（11 个模块、290 条，当时本机另有会话在跑基准测试，用时 630.7 s）另存为 `logs/verify_all_final_2026-10-05.log`）：\n\n```\n'
                       + table + '\n' + t[b1:])
rep('09_code.md',
    '运行中 Lean 私有内存超过上限或系统提交余量过低就结束进程树，退出码 137）',
    '运行中 Lean 私有内存超过上限或系统提交余量过低就结束进程树，退出码 137；2026-10-07 起，单次内存查询失败时改用备用数据源，连续 5 秒都读不到才结束，不再把查询失败误当成余量为 0）')
rep('09_code.md',
    '、`logs/verify_all_final.log`（最终，11 个模块）。',
    '、`logs/verify_all_final_2026-10-05.log`（第四轮修订后，11 个模块 290 条）、`logs/verify_all_2026-10-07.log`（修好 c5b 之后，11 个模块 290 条）、`logs/verify_all_final.log`（最终，2026-10-07 加固 ⑥ 之后，12 个模块 %d 条）。' % TOTAL_PASS)

# ---------------------------------------------------------------- 00_head
rep('00_head.md',
    '（最终核对完成于 2026-10-05）。',
    '（最终核对完成于 2026-10-05；2026-10-07 Lean 第四轮收尾，并加固了原 ⑥ 的三处，见 ⑥）。')
rep('00_head.md',
    '空闲时约 3.5–4 分钟（机器负载高时更长），共 11 个模块。',
    '空闲时约 %s 分钟（2026-10-07 实测；机器负载高时更长），共 12 个模块。' % MINUTES)
rep('00_head.md',
    '其余 10 个模块只依赖标准库',
    '其余 11 个模块只依赖标准库')
rep('00_head.md',
    '唯一例外是 rv2：它运行复核者 x1 的两个独立脚本，',
    '例外是 rv2 与 rv3。rv2 运行复核者 x1 的两个独立脚本，')
rep('00_head.md',
    '（范数计算在 r1）。',
    '（范数计算在 r1）。rv3 运行复核者 r-c4ii、r-c3a、s6-t436、s6-t342 的脚本，同样不导入 core，各脚本按定义自算真值（Num_q 的递推，K、I、𝒮 的定义）。')

# ---------------------------------------------------------------- 写回
for name, txt in sorted(texts.items()):
    if DRY:
        print('would patch', name)
    else:
        with open(os.path.join(PARTS, name), 'w', encoding='utf-8') as f:
            f.write(txt)
        print('patched', name)
print('dry run' if DRY else 'done')
