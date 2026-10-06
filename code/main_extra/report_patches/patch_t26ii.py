# -*- coding: utf-8 -*-
"""2026-10-07 主 Agent 独立重推 T2.6(ii) 之后，同步报告各节（notes/report_parts/）。

改动：
  - 03_C2 T2.6(ii)：两份独立推导（x1；主 Agent，notes/03-主Agent-T2.6(ii)重推.md），写出留数闭式，核对加 rv4；
  - 10_uncertain ⑥：T2.6(ii) 移入「次一级」，新 ⑥ 为 T2.7′、T3.4(4)(5)、T4.3(8)；
  - 09_code ⑤：13 个模块、check_rv4.py 一行、最终运行（从 logs/verify_all_final.log 抽取）、日志清单；
  - 00_head：加固范围、模块数与耗时、「真值」来源的例外。
每处替换都断言锚点恰好出现一次。运行前提：logs/verify_all_final.log 是含 rv4 的 13 个模块全量运行，且 OVERALL: PASS。
用法：py -3.14 code/main_extra/report_patches/patch_t26ii.py [--dry]
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

NOTE = 'notes/03-主Agent-T2.6(ii)重推.md'
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
assert any(re.match(r'rv4\s', ln) for ln in log), 'verify_all_final.log 里没有 rv4'
head = [i for i, ln in enumerate(log) if ln.startswith('area ')][-1]
tail = [i for i, ln in enumerate(log) if ln.startswith('OVERALL:')][-1]
table = '\n'.join(log[head:tail + 1])
m = re.search(r'TOTAL pass=(\d+) fail=0 modules=(\d+) failed_modules=-\s+\(([\d.]+)s\)', table)
assert m, '总表格式不对'
TOTAL_PASS, N_MOD, SECS = int(m.group(1)), int(m.group(2)), float(m.group(3))
assert N_MOD == 13, '模块数不是 13：%d' % N_MOD
m4 = re.search(r'^rv4\s+(\d+)\s+0\s', table, re.M)
assert m4 and int(m4.group(1)) == 9, 'rv4 不是 9 条 PASS'
MINUTES = '%.1f' % (SECS / 60)
print('final log: pass=%d modules=%d %.1fs' % (TOTAL_PASS, N_MOD, SECS))

# ---------------------------------------------------------------- 03_C2 T2.6(ii)
rep('03_C2.md',
    '复核者 x1 给出统一证明：E 部分在纤维 u=1/i 处的留数元等于 (W̃_i−1)·x^{−3m−3} 乘以一个只依赖 i、m 的有理常数，所以除 x 的幂次与有理常数外与 m 无关；',
    '复核者 x1 给出统一证明；2026-10-07 主 Agent 不看 x1 的式子从头重推了一遍（' + NOTE + '），两份推导得到的闭式逐项一致：'
    'E 部分的母函数是 E_m=(W_m−1)/P_m=x²Σ_{j=1}^{m} j/∏_{v=j}^{m}b_v；b_i 的三个根恰好组成纤维 u=1/i，在其中的根 η 处 b_v(η)=(i−v)η³、b_i′(η)=(2η−3)/η、u′(η)=(3−2η)/(i²η⁴)，'
    '所以 Res_η E_m·u′(η)=(−1)^{m−i+1}(W̃_i(η)−1)η^{−3m−3}/((m−i)!·i!·i²)（1≤i≤m），即留数元等于 (W̃_i−1)·x^{−3m−3} 乘以一个只依赖 i、m 的有理常数，除 x 的幂次与有理常数外与 m 无关；')
rep('03_C2.md',
    '若有 u 型单和，则留数元乘以 x 的某个幂必须是有理数，',
    '若有 u 型单和，则留数元乘以 x 的某个幂必须是有理数（b_2 在 Q 上不可约，它在三个共轭根处的值必须相同），')
rep('03_C2.md',
    'rv2.rv2-x1-r1（E 部分统一阻碍，m=2..34）、rv2.rv2-x1-r2。',
    'rv2.rv2-x1-r1（E 部分统一阻碍，m=2..34）、rv2.rv2-x1-r2；主 Agent 重推时另写的独立程序（不导入 core、不复用 x1 的脚本）：'
    'rv4.rv4-t26ii-a（E_m=(W_m−1)/P_m 对照自写 DP，m≤6、k≤30）、rv4.rv4-t26ii-b（根处的化简）、rv4.rv4-t26ii-c（留数闭式在 Q[x]/(b_i) 中精确成立，1≤i≤8、i≤m≤40）、'
    'rv4.rv4-t26ii-d1、rv4.rv4-t26ii-d2、rv4.rv4-t26ii-d3、rv4.rv4-t26ii-d4（K_2 中的范数；N((4−2x)x^n) 的 17-进赋值在 |n|≤60 上都是 1）、'
    'rv4.rv4-t26ii-e1、rv4.rv4-t26ii-e2（b_1、b_2 不可约；b_4 可约，所以证明只用 i=1、2 的纤维）。')

# ---------------------------------------------------------------- 10_uncertain ⑥
t = load('10_uncertain.md')
a = t.index('## ⑥ 我最不确定的三处')
b = t.index('**次一级的不确定处**')
assert t.count('## ⑥ 我最不确定的三处') == 1 and t.count('**次一级的不确定处**') == 1
SIX = '''## ⑥ 我最不确定的三处

（2026-10-07 两次重排。原来的三处是 T4.3(6) 高次系数的一般结构、T3.4(2) 的 K 闭式、T2.7 依赖文献的推论，当天都已加固：前两处各有一位第三轮复核者独立重推，并各多出一份路线不同的证明，计算与数值核对已并入 verify_all（rv3）；第三处改写为 T2.7′，给出不依赖未读文献的证明。第一次重排后排第 1 的 T2.6(ii)（截断块部分的统一证明），随后由主 Agent 不看复核者 x1 的式子独立重推，并写了不导入 core 的精确核对（rv4）。这四处都移到下面的「次一级的不确定处」。按现在的证据排出的三处如下。）

1. **T2.7′（2026-10-07 新写的证明）。**
   为什么不确定：证明是主 Agent 当天新写的，只经过一位复核者（s6-t27）审查。审查结论是 confirmed，三条引理在 6 个例子上做了 219 项精确计算检验。没有人类核对，没有形式化。条件 (N2) 是证明技术需要的，而且依赖被加项的写法，含 C(2j,j) 一类因子的写法不在范围内。s6-t27 提出的更弱条件 (N2′)（配合沿一般方向取极限的引理 F′）只有它一人推过，本文没有采用。
   下一步：请第二位复核者审查；如果论文要覆盖 C(2j,j) 一类因子，再核对 (N2′) 与引理 F′。

2. **T3.4(4)(5) 的解析部分：渐近展开的显式误差界、差值大小的门槛。**
   为什么不确定：剩下的【已证明】大多是「作者 + 一位复核者 + 程序核对」，彼此差别不大。这两条依赖分析估计，证明来自第一轮（c3a），经第二轮复核者 r-c3a 重推。数值只能抽查有限个点：c3a 的核对，以及 rv3.rv3-c3a-r2 里的误差界抽查。(5) 常数项部分的 Stirling 门槛这一轮没有人再核对。没有形式化。(5) 的整体部分用到的 1<K/Γ(−λ)<2 已在 T3.4(2) 中加固。
   下一步：请复核者独立重推 (4) 的误差界与 (5) 常数项部分的门槛。

3. **T4.3(8)（(C7) 分母对一切 q 最简）中 b_i 可约的情形。**
   为什么不确定：b_i 可约（i=r²(r−1)，即 i=4,18,48,…）时，二次因子的非实根处要用「α>−1 时 L_n^{(α)} 的零点都是正实数」。这是 Szegő 书中的经典结果（正交多项式零点定理的特例），本文没有重证，也没有核对原书的条款编号。证明由第二轮复核者 r-c4ii 给出，主 Agent 逐步核对；同余与 Laguerre 恒等式有程序核对（rv.rv-num-cong q≤20、rv.rv-num-laguerre q≤30），既约性本身第一轮验证到 q≤40。没有形式化（Lean 的 NumStruct 只覆盖 T4.3(1)–(3) 与 (4)(5) 的一部分）。被引用的是教科书定理，实际风险比前两处小。
   下一步：在笔记里补上这个零点定理的标准证明（正交性加变号点计数，几行），或给出原书的准确出处。

'''
texts['10_uncertain.md'] = t[:a] + SIX + t[b:]
rep('10_uncertain.md',
    '- T2.7 的推论（原 ⑥ 第 3 处）：已改写为 T2.7′，见上面第 2 处。\n',
    '- T2.7 的推论（原 ⑥ 第 3 处）：已改写为 T2.7′，见上面第 1 处。\n'
    '- T2.6(ii)（截断块部分对一切 m≥2 没有 u 型单和；2026-10-07 第一次重排后是 ⑥ 第 1 处）：现在有两份独立推导。复核者 x1 先给出；主 Agent 不看 x1 的式子从头重推（' + NOTE + '），留数闭式与 x1 的逐项一致。'
    '两套独立程序做了精确核对：rv2（x1 的脚本，m=2..34）与 rv4（主 Agent 的脚本，留数闭式 1≤i≤8、i≤m≤40，K_2 中的范数与 17-进赋值）；2≤m≤30 另有逐个的留数–范数证书（c2b 定理 6）。没有形式化。\n')
rep('10_uncertain.md',
    '- T4.3(8)（(C7) 分母对一切 q 最简）：改写后只在 i=r²(r−1) 时需要 Laguerre 零点定理（Szegő 的经典结果，未在本文重证）；核心同余与 Laguerre 恒等式有程序核对（rv.rv-num-cong q≤20、rv.rv-num-laguerre q≤30）。\n',
    '')
rep('10_uncertain.md',
    '（复核者 r-c2a 的纤维论证与复核者 x1 的代数证明）。（T2.6(ii) 已列为上面第 1 处。）',
    '（复核者 r-c2a 的纤维论证与复核者 x1 的代数证明）。')

# ---------------------------------------------------------------- 09_code ⑤
rep('09_code.md',
    '**12 个核对模块**（除 check_rv2.py、check_rv3.py 外，',
    '**13 个核对模块**（除 check_rv2.py、check_rv3.py、check_rv4.py 外，')
rep('09_code.md',
    '各脚本按定义自算真值：Num_q 的递推，K、I、𝒮 的定义）',
    '各脚本按定义自算真值：Num_q 的递推，K、I、𝒮 的定义；check_rv4.py 运行主 Agent 重推 T2.6(ii) 时写的独立脚本，不导入 core、不复用 x1 的脚本，以自写的 DP 作真值，其余是 Q[x]/(b_i) 中的精确代数）')
t = load('09_code.md')
lines = t.split('\n')
idx = [i for i, ln in enumerate(lines) if ln.startswith('| `check_rv3.py` |')]
assert len(idx) == 1
lines.insert(idx[0] + 1, '| `check_rv4.py` | 主 Agent 独立重推 T2.6(ii) 所依赖的计算（不导入 core、不复用 x1 的脚本）：E 部分母函数对照自写 DP（m≤6、k≤30）；b_i 根处的化简与留数闭式在 Q[x]/(b_i) 中精确成立（1≤i≤8、i≤m≤40）；K_2 中的范数与 17-进赋值（\\|n\\|≤60）；b_1、b_2 不可约、b_4 可约。子脚本的完整输出在 `logs/rv4_main_t26ii.log`；反向检查（把闭式常数改成 2 倍，应报 FAIL）见 `logs/main_t26ii_check_reverse.log` | 9 |')
texts['09_code.md'] = '\n'.join(lines)
t = load('09_code.md')
a = t.index('**最终一次运行**（本地 2026-10-07，完整输出 `logs/verify_all_final.log`')
b0 = t.index('```', a)
b1 = t.index('```', b0 + 3)
assert t.count('**最终一次运行**') == 1
texts['09_code.md'] = (t[:a]
                       + '**最终一次运行**（本地 2026-10-07，加入 rv4 之后，完整输出 `logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行；同日加入 rv4 之前的一次（12 个模块、296 条）另存为 `logs/verify_all_final_2026-10-07_before_rv4.log`，2026-10-05 的一次（11 个模块、290 条，当时本机另有会话在跑基准测试，用时 630.7 s）另存为 `logs/verify_all_final_2026-10-05.log`）：\n\n```\n'
                       + table + '\n' + t[b1:])
rep('09_code.md',
    '、`logs/verify_all_final.log`（最终，2026-10-07 加固 ⑥ 之后，12 个模块 296 条）。',
    '、`logs/verify_all_final_2026-10-07_before_rv4.log`（2026-10-07 加固原 ⑥ 三处之后，12 个模块 296 条）、`logs/verify_all_final.log`（最终，2026-10-07 加入 rv4 之后，%d 个模块 %d 条）。' % (N_MOD, TOTAL_PASS))

# ---------------------------------------------------------------- 00_head
rep('00_head.md',
    '2026-10-07 Lean 第四轮收尾，并加固了原 ⑥ 的三处，见 ⑥）。',
    '2026-10-07 Lean 第四轮收尾，并加固了原 ⑥ 的三处，以及随后排到第 1 位的 T2.6(ii)，见 ⑥）。')
rep('00_head.md',
    '空闲时约 4.6 分钟（2026-10-07 实测；机器负载高时更长），共 12 个模块。',
    '空闲时约 %s 分钟（2026-10-07 实测；机器负载高时更长），共 %d 个模块。' % (MINUTES, N_MOD))
rep('00_head.md',
    '其余 11 个模块只依赖标准库',
    '其余 %d 个模块只依赖标准库' % (N_MOD - 1))
rep('00_head.md',
    '例外是 rv2 与 rv3。',
    '例外是 rv2、rv3 与 rv4。')
rep('00_head.md',
    '各脚本按定义自算真值（Num_q 的递推，K、I、𝒮 的定义）。',
    '各脚本按定义自算真值（Num_q 的递推，K、I、𝒮 的定义）。rv4 运行主 Agent 重推 T2.6(ii) 时写的独立脚本，不导入 core，以自写的 DP 作真值，其余是 Q[x]/(b_i) 中的精确代数。')

# ---------------------------------------------------------------- 写回
for name, txt in sorted(texts.items()):
    if DRY:
        print('would patch', name)
    else:
        with open(os.path.join(PARTS, name), 'w', encoding='utf-8') as f:
            f.write(txt)
        print('patched', name)
print('dry run' if DRY else 'done')
