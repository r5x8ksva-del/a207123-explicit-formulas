# -*- coding: utf-8 -*-
"""表 B 并入报告（2026-10-09）的修订：采纳复核者 s16-report（notes/review/s16-report-review.md）的 22 条意见与「细节」，
并顺带改正猜想总表 B8 行与 A29(iii) 的同样问题。每处断言原文出现一次；按字节读写，保留 CRLF。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_tableB_2026-10-09_fix.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
E = {}


def add(name, old, new):
    E.setdefault(name, []).append((old, new))


# ① 摘要（问题 6、16、20）
add('notes/report_parts/01_summary.md',
    '两族 u 型和也没有（U：m≥2；E：m≥3）。一般意义的「无更短公式」原样不是数学命题，未证明。',
    '两族 u 型和也没有（U：m≥2；E：m≥3；计算机辅助）。一般意义的「无更短公式」原样不是数学命题，不能证明也不能否定。')
add('notes/report_parts/01_summary.md',
    '只用一元 ₁F₁ / 不完全 Gamma 的闭式不存在；t<0 时 F 在 x 方向 3-可和，3-和就是积分 I。',
    '整表 F 只用一元 ₁F₁ / 不完全 Gamma 的有限闭式不存在（𝒩 同样）；t<0 时 F 在 x 方向 3-可和，3-和就是积分 I。')

# 开头的等级说明（问题 21、5）
add('notes/report_parts/00_head.md',
    '【已否定】= 附反例或证明；',
    '【已否定】= 附反例或证明；【已证明（计算机辅助）】= 书面约化加有限的精确计算证书，证书写明范围；【已证明（否定）】= 证明了某类表示或闭式不存在；')
add('notes/report_parts/00_head.md',
    '凡是用 decimal 做的高精度数值检查，一律注明「数值」。',
    '凡是用 decimal 做的高精度数值检查，一律注明「数值」；表 B 补证条目（2026-10-09 并入）的核对清单里，双精度浮点的数值检查与佐证注明「数值」或「佐证」，其余是精确计算。')

# ② C-2（问题 5、6、9、10、11、18、19）
add('notes/report_parts/03_C2.md',
    '(4)【已证明；2026-10-08 补证，notes/12 §2；复核者 s12-b4，(d) 另有 s12-b4t3】',
    '(4)【已证明；2026-10-08 补证，notes/12 §2、§3；(a)–(c) 由复核者 s12-b4 复核；(d) 是复核之后加的，由 s12-b4t3 复核（m=2 的例子由 s12-b4 先给出）】')
add('notes/report_parts/03_C2.md',
    '；m≥3 时 i=3 这一项必须用三个原子（纤维 3 上的指数丢番图问题，',
    '；m≥3 时 i=3 这一项必须用三个原子（这是 U 的结论；E 不同：E 的纤维 3 不构成障碍，E_k(3) 每个 i 两个原子就够；证明：纤维 3 上的指数丢番图问题，')
add('notes/report_parts/03_C2.md', 'tb.b4-lemmaP、tb.b4-rev。', 'tb.b4-lemmaP（佐证）、tb.b4-rev。')
add('notes/report_parts/03_C2.md', 'tb.b3-fiber、tb.b3-linsys（1800 个截断方程组）', 'tb.b3-fiber（浮点示意）、tb.b3-linsys（1800 个截断方程组）')
add('notes/report_parts/03_C2.md', 'm=1 时 F3 型本身就是两族表示，所以必须 m≥2。', '')
add('notes/report_parts/03_C2.md',
    '**对每个 m≥2**，|g_i+3m+3|≤6000 时不存在',
    '**对每个 m≥2**（m=1 时 F3 型本身就是两族表示，所以必须 m≥2），|g_i+3m+3|≤6000 时不存在')
add('notes/report_parts/03_C2.md', '对所有指数的证明见上一句（2026-10-08）。', '对所有指数的证明见本条前半（2026-10-08）。')
add('notes/report_parts/03_C2.md', '即上句记号下 N_i=−g_i', '即本条开头的记号下 N_i=−g_i')
add('notes/report_parts/03_C2.md',
    '(3) N(k,q) 整体的短公式（2026-10-08 补证，notes/13、notes/14；复核者 s12-b5、s12-b4t3、s13-b5skel）：',
    '(3) N(k,q) 整体的短公式（2026-10-08 补证，notes/13、notes/14；(a)(b)(d) 由复核者 s12-b5 复核，(c) 是复核之后加的、只经 s12-b4t3（他先算出，本会话独立重算），(e) 由 s13-b5skel 复核）：')
add('notes/report_parts/03_C2.md',
    '3≤q≤300 时 N^E_q 没有（逐个 q 的证书）。',
    '3≤q≤300 时 N^E_q 没有【计算机辅助：逐个 q 的证书；s12-b5 独立复现了 3≤q≤100，101≤q≤300 只有作者这一份】。')
add('notes/report_parts/03_C2.md',
    '【未完成】标准原子下 N 的其他两层公式（q 方向换核、以 r-Stirling 数或 c_i 为原子）。',
    '【未完成】标准原子下 N 的其他两层公式（q 方向换核、以 r-Stirling 数或 c_i 为原子），以及 a≥0 的骨架型形状（不在 (e) 的范围内）。')
add('notes/report_parts/03_C2.md', 'tb.b5s-fiber1、tb.b5s-rev。', 'tb.b5s-fiber1（数值佐证）、tb.b5s-rev。')
add('notes/report_parts/03_C2.md',
    '对一般意义的「没有更短的公式」，本文没有证明。',
    '2026-10-07 晚至 10-08 又证明了：单族二项式单和在一切整数形状下都只有平凡的基变换（T2.6(i)）；两族 u 型和不存在（T2.6(iii)，计算机辅助）；以 c_i 为原子时，每个 i 一个原子不行，两个原子对 U 只在 m≤2 时可行（T2.5(4)，后者计算机辅助）。一般意义的「没有更短的公式」原样不是数学命题（不规定原子、核与系数类时单和总是存在，notes/12 命题 0），不能证明也不能否定。')

# ② C-3（问题 1、5、12、细节）
add('notes/report_parts/04_C3.md',
    '两圈交换次序结果相差 −ν(1−e^{2πiλ})ω，所以单值群不是虚交换的；',
    '两圈交换次序结果相差 −ν(1−e^{2πiλ})ω（对 γ_0^a、γ_1^b 同样成立，λ∉Q 时 e^{2πiλa}≠1），所以单值群不是虚交换的；')
add('notes/report_parts/04_C3.md',
    '，经四则、求导与代入整函数得到的表达式，单值群都是虚交换的（参数可以任意依赖 x）。',
    '，经四则、求导，以及对可全纯延拓的元素代入整函数得到的表达式（notes/11 推论 5 的类 𝓔），单值群都是虚交换的（参数可以任意依赖 x）。')
add('notes/report_parts/04_C3.md', 'tb.b6-sharp、tb.b6-qrat、tb.b6-reverse。', 'tb.b6-sharp（数值）、tb.b6-qrat（数值）、tb.b6-reverse。')
add('notes/report_parts/04_C3.md', '本条的显式误差界不在此列。', '本条的显式误差界、以及与 𝒮 的极点有关的部分不在此列。')
add('notes/report_parts/04_C3.md',
    '并在其中有一致的 Gevrey-1/3 渐近展开 F(·,t)',
    '并在其每个闭子扇形上有一致的 Gevrey-1/3 渐近展开 F(·,t)')
add('notes/report_parts/04_C3.md',
    'tb.b7-growth、tb.b7b-bdry、tb.b7b-inv、tb.b7b-real（b7b 各条多为数值佐证）、tb.b13-alg、tb.b13-wp、tb.b13-coef、tb.b13-jump、tb.b13-dom、tb.b13-geom、tb.b13-rev。',
    'tb.b7-growth（数据）、tb.b7b-bdry、tb.b7b-inv、tb.b7b-real（b7b 各条是数值佐证）、tb.b13-alg、tb.b13-wp（数值）、tb.b13-coef（数值）、tb.b13-jump（数值）、tb.b13-dom（数值）、tb.b13-geom（取样）、tb.b13-rev。')
add('notes/report_parts/04_C3.md',
    '；表 B 补证部分的核对见 (4) 末与 (5)（tb 模块）。',
    '；表 B 补证部分的核对见 (5) 末（tb 模块；T3.3(3) 的见该条）。')

# ② C-5（问题 2、3、4、5、13、14、17）
add('notes/report_parts/06_C5.md',
    '(b) j>J_k:=k(k²−k−4)/2−k+2 时 (−1)^kU_k(−j)>0（显式根界）',
    '(b) k≥4 时，j>J_k:=k(k²−k−4)/2−k+2 蕴含 (−1)^kU_k(−j)>0（显式根界；k≤3 直接验证）')
add('notes/report_parts/06_C5.md',
    '剩下 (s_k+2,J_k] 中整除 lcm(1..k) 的 71,660,856 个候选逐个判定非零',
    '然后对 (s_k,J_k] 中整除 lcm(1..k) 的 71,660,856 个 j（J_k 取 notes/15 的定义 max_qθ_q，k≥4 时就是上面的闭式；含 (c) 已排除的 s_k+1、s_k+2）逐个判定非零')
add('notes/report_parts/06_C5.md',
    '实根到整数的距离近似均匀，看不出一般的算术障碍。',
    '数据（k≤40 的 260 个实根，notes/15 观察 5）：实根到整数的距离看不出偏向，所以与 k 无关的间隔论证行不通；一般情形大概要用到 U_k(−j) 的整数性（判断，不是定理）。')
add('notes/report_parts/06_C5.md', '核对：tb.b9-truth、tb.b9-binet、tb.b9-tau', '核对：tb.b9-truth、tb.b9-binet（数值对照）、tb.b9-tau')
add('notes/report_parts/06_C5.md',
    'h_k 的根全为实数且两两不同，等价于 N 行多项式 n_k 实根。',
    'h_k 的根全为实数且两两不同，等价于 N 行多项式 n_k 只有实根、且除 −1 外都是单根。')
add('notes/report_parts/06_C5.md',
    '由三角递推得 n_k=(1+z)n_{k−1}+Φn_{k−3}（Φn=',
    '由三角递推得 n_k=(1+z)n_{k−1}+Φn_{k−3}（k≥4；Φn=')
add('notes/report_parts/06_C5.md',
    '(b)【已证明】h_k(−1)=Σ_q(−1)^{q−1}2^{k−q}N(k,q)，符号是 (−1)^{h_k 在 (−1,0) 中的根数}（由 (6)）。',
    '(b)【已证明】k≥1 时 h_k(−1)=Σ_q(−1)^{q−1}2^{k−q}N(k,q)；h_k(−1)≠0 时，符号是 (−1)^{h_k 在 (−1,0) 中的根数}（由 (6)；h_2(−1)=0，3≤k≤1000 时 h_k(−1)≠0，是计算结果）。')
add('notes/report_parts/06_C5.md',
    '核对：tb.b9-hm1、tb.b9-osc（数值佐证）、tb.b13-coef、tb.b13-jump、tb.b13-data（数值佐证）。',
    '核对：tb.b9-hm1、tb.b9-osc（数值佐证）、tb.b13-coef（数值）、tb.b13-jump（数值）、tb.b13-data（数值佐证）。')
add('notes/report_parts/06_C5.md',
    'τ_i 的增长规律（按 (5) 的证书方法写出显式估计可得 τ_i=O(i log i)，没有写成引理）',
    'τ_i 的增长规律（启发式估计表明，按 (5) 的证书方法可以得到 τ_i=O(i log i)，还需三个显式不等式，没有写成引理）')

# ④（问题 1、6、7、15、18、细节）
add('notes/report_parts/08_failed.md',
    '2026-10-09 更新：第 1–4、6 条的大部分已在表 B 的后续工作中补证，各条写明了现状）',
    '2026-10-09 更新：第 3 条已解决（否定），第 4、6 条的主要部分已补证；第 1、2 条又排除了若干类形状，核心问题仍开放；各条写明了现状）')
add('notes/report_parts/08_failed.md',
    '仍未排除：每个 i 三个不相邻原子、或平移随 m 变化而系数为闭式的写法；允许系数依赖 k',
    '仍未排除：每个 i 三个不相邻原子、或平移随 m 变化而系数为闭式的写法；核是多个二项式之积的单和、非 u 型的两族和、一般的 holonomic 多重和（T2.7′ 只排除了满足 (N1)(N2) 的 proper 超几何多重和）；允许系数依赖 k')
add('notes/report_parts/08_failed.md',
    '而一元 ₁F₁、不完全 Gamma 等拼出的表达式都是虚交换的）',
    '而一元 ₁F₁、不完全 Gamma 等按 notes/11 推论 5 的规则拼出的表达式都是虚交换的）')
add('notes/report_parts/08_failed.md',
    't<0 时都已补上（T3.4(5)）：Gevrey 上界用 Nagumo 范数（2026-10-07 晚）；',
    't<0 时都已补上（T3.4(5)）：Gevrey 上界在 |t|<1 时用 Nagumo 范数（2026-10-07 晚），对一切 t<0 由 notes/09 的推论给出；')
add('notes/report_parts/08_failed.md',
    '固定位置系数转正的门槛对 i≤40 已确定（T5.3(5)，原数据',
    '固定位置系数转正的门槛对 i≤40 已确定（T5.3(5)，计算机辅助；原数据')
add('notes/report_parts/08_failed.md',
    '最终一轮对抗审计又更正了：其余奇数形状只有浮点证据，等级由【已验证】降为【猜想】；',
    '最终一轮对抗审计又更正了：其余奇数形状只有浮点证据，等级由【已验证】降为【猜想】（2026-10-07 晚已证明，见 T2.6(i)）；')

# ⑤（问题 5）
add('notes/report_parts/09_code.md',
    '原样转印各条 PASS/FAIL；b7_borel 各条与 b6-mono、b9-osc、b13-data 是数值佐证。',
    '原样转印各条 PASS/FAIL；b7_borel 各条与 b6-mono、b9-osc、b13-data 是数值佐证，b3-fiber、b4-fiberD、b4-lemmaP、b5s-fiber1、b6-sharp、b6-qrat、b9-binet、b13-wp、b13-coef、b13-jump、b13-dom、b13-geom 是双精度的数值检查或示意（在 ② 里标了「数值」「佐证」等），其余是精确计算。')

# ⑥（问题 6、8、20、22）
add('notes/report_parts/10_uncertain.md',
    '按现在的证据排出的三处如下。）',
    '按现在的证据排出的三处如下。2026-10-09 并入的表 B 后续结论没有进前三：其中没有复核者的两处，notes/07 是标准的 Nagumo 论证、常数显式，notes/10 的平移范围引理只有几行，两处都有程序核对；只经一位复核者的 notes/17 有两轮复核与 36 条独立检查。它们放在下面「次一级的不确定处」逐条说明。）')
add('notes/report_parts/10_uncertain.md',
    '只有 T3.4(5) 第一段（notes/07）与 T4.2(2) 的 9≤d≤100 没有复核者；',
    '只有 T3.4(5)「f_k(t) 的增长」下的第一条（notes/07）与 T4.2(2) 的 9≤d≤100 没有复核者；')
add('notes/report_parts/10_uncertain.md',
    'T3.4(5) 的后两段依赖 notes/09 的解析估计，后者只有一位复核者（s9-b7）。',
    'T3.4(5)「f_k(t) 的增长」下的后两条、T3.4(4) 末的另一证明与 T5.3(7)(b) 都依赖 notes/09 的解析估计，后者只有一位复核者（s9-b7）。')
add('notes/report_parts/10_uncertain.md',
    '任意形状的「无更短公式」未完成（原样不是数学命题；',
    '任意形状的「无更短公式」原样不是数学命题，不能证明也不能否定（')
add('notes/report_parts/10_uncertain.md', '、系数转正门槛（i≤40）、', '、系数转正门槛（i≤40，计算机辅助）、')

# ③（问题 9）
add('notes/report_parts/07_formula.md',
    '一般意义下「没有更短的公式」本文没有证明。',
    '2026-10-07 晚至 10-08 又证明了几类不可能（见 ②）：单族二项式单和在一切整数形状下都只有平凡的基变换（T2.6(i)）；两族 u 型和不存在（T2.6(iii)，U：m≥2，E：m≥3，计算机辅助）；以 c_i 为原子时（T2.5(4)，上面 F4 型的原子），每个 i 一个原子不行，两个原子对 U 只在 m≤2 时可行（计算机辅助），三个相邻原子总可以，但平移与 m、i 无关时系数不是 P-递推的。一般意义下「没有更短的公式」原样不是数学命题（不规定原子、核与系数类时单和总是存在，notes/12 命题 0），不能证明也不能否定。')

# 猜想总表（复核者顺带指出）
add('猜想总表.md',
    'j>J_k=k(k²−k−4)/2−k+2 时 (−1)^kU_k(−j)>0；j=s_k+1、s_k+2 时由顶端闭式不为零；k≤300 时剩下的 71,660,856 个候选全部非零',
    'k≥4 时 j>J_k=k(k²−k−4)/2−k+2 蕴含 (−1)^kU_k(−j)>0；j=s_k+1、s_k+2 时由顶端闭式不为零；k≤300 时 (s_k,J_k] 中整除 lcm(1..k) 的 71,660,856 个候选（含 s_k+1、s_k+2；J_k 取 notes/15 的定义，k≥4 时就是这个闭式）全部非零')
add('猜想总表.md',
    '(iii) h_k(−1)=Σ_q(−1)^{q−1}2^{k−q}N(k,q)，符号是 (−1)^{h_k 在 (−1,0) 中的根数}',
    '(iii) k≥1 时 h_k(−1)=Σ_q(−1)^{q−1}2^{k−q}N(k,q)，h_k(−1)≠0 时符号是 (−1)^{h_k 在 (−1,0) 中的根数}（h_2(−1)=0）')


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    dry = '--dry' in sys.argv
    out, bad = {}, []
    # 先全部检查，有一处不唯一就一个文件也不写
    for rel, reps in E.items():
        p = os.path.join(ROOT, rel)
        raw = open(p, 'rb').read()
        crlf = raw.count(b'\r\n')
        assert crlf in (0, raw.count(b'\n')), rel
        s = raw.decode('utf-8').replace('\r\n', '\n')
        for old, new in reps:
            c = s.count(old)
            if c != 1:
                bad.append((rel, c, old[:60]))
                continue
            s = s.replace(old, new)
        out[p] = s.replace('\n', '\r\n').encode('utf-8') if crlf else s.encode('utf-8')
    for b in bad:
        print('NOT UNIQUE', b)
    assert not bad, len(bad)
    if dry:
        print('dry run ok, %d edits in %d files' % (sum(len(r) for r in E.values()), len(E)))
        return
    for p, b in out.items():
        open(p, 'wb').write(b)
    for rel, reps in E.items():
        print('%s: %d edits' % (rel, len(reps)))
    print('total edits', sum(len(r) for r in E.values()))


if __name__ == '__main__':
    main()
