# -*- coding: utf-8 -*-
"""2026-10-07 记录 T2.7′ 的第二次独立复核（复核者 s7-t27，notes/review/s7-t27-review.md），并改正一句说过了头的适用范围。

第二位复核者判 confirmed with minor gaps：引理 A、F、S 与拼接都对；唯一的问题是「含 C(2j,j) 一类因子的写法都不满足 (N2)」，
反例 C(2j,j)C(m,j−k)（支撑 k≤j≤k+m，取 Q_R={k≥R, m≥R} 满足 (N2)）。真正不满足的是在象限深处支撑仍伸到 j=0 的写法，
如 C(2j,j)C(k,j)C(m,j)。结论本身不变，只改适用范围的说法，并更新 ⑥ 第 1 处与 README、ROADMAP 的待办。
用法：py -3.14 code/main_extra/report_patches/patch_t27_second_review.py [--dry]
之后运行 py -3.14 code/main_extra/assemble_report.py 重新拼接报告。
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
DRY = '--dry' in sys.argv
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

REVIEW = 'notes/review/s7-t27-review.md'

EDITS = [
    ('notes/report_parts/03_C2.md',
     '(N2) 是被加项写法的性质，含 C(2j,j)=(2j)!/(j!)² 一类因子的写法不满足它，不在本推论范围内',
     '(N2) 是被加项写法的性质：含 (2j)! 这类分子因子、且在象限深处支撑仍伸到 j=0 的写法（如 Σ_jC(2j,j)C(k,j)C(m,j)）不满足它，'
     '不在本推论范围内；支撑远离 j=0 时这类因子无妨，例如 C(2j,j)C(m,j−k)（2026-10-07 更正：原文「含 C(2j,j) 一类因子的写法不满足它」'
     '说过了头，由第二位复核者 s7-t27 指出）'),
    ('notes/report_parts/03_C2.md',
     '复核者 s6-t27 逐条审查为 confirmed，见 notes/review/s6-t27-review.md）',
     '复核者 s6-t27 逐条审查为 confirmed，见 notes/review/s6-t27-review.md；2026-10-07 写论文时加派的第二位复核者 s7-t27 '
     '独立审查为 confirmed with minor gaps，唯一的问题是上面那句适用范围的说法，已改正，见 ' + REVIEW + '）'),
    ('notes/report_parts/10_uncertain.md',
     '   为什么不确定：证明是主 Agent 当天新写的，只经过一位复核者（s6-t27）审查。审查结论是 confirmed，三条引理在 6 个例子上做了 219 项精确计算检验。'
     '没有人类核对，没有形式化。条件 (N2) 是证明技术需要的，而且依赖被加项的写法，含 C(2j,j) 一类因子的写法不在范围内。'
     's6-t27 提出的更弱条件 (N2′)（配合沿一般方向取极限的引理 F′）只有它一人推过，本文没有采用。\n'
     '   下一步：请第二位复核者审查；如果论文要覆盖 C(2j,j) 一类因子，再核对 (N2′) 与引理 F′。',
     '   为什么不确定：证明是主 Agent 当天新写的。两位复核者先后独立审查：s6-t27 判 confirmed，三条引理在 6 个例子上做了 219 项精确计算检验；'
     's7-t27（2026-10-07 写论文时加派）判 confirmed with minor gaps，约 47.7 万次精确检验与 4 项反向检查，唯一的问题是适用范围的一句话说过了头'
     '（已改正，见 ' + REVIEW + '）。仍然没有人类核对，没有形式化。条件 (N2) 是证明技术需要的，而且依赖被加项的写法：'
     '含 (2j)! 这类因子、在象限深处支撑仍伸到 j=0 的写法不在范围内。s6-t27 提出的更弱条件 (N2′)（配合沿一般方向取极限的引理 F′）只有它一人推过，本文没有采用。\n'
     '   下一步：请人类专家审阅（论文 paper/main.tex §6.2）；如果要覆盖支撑伸到 j=0 的 C(2j,j) 一类写法，再核对 (N2′) 与引理 F′。'),
    ('notes/02-主Agent-不确定三处加固.md',
     '- 含 C(2j,j)=(2j)!/(j!)² 一类因子的项，按整数常数的写法都不满足 (N2)：支撑端点外紧挨着 (2j)! 参数为负的点。'
     '所以它们不在这条推论的范围内，尽管 s6-t27 的计算显示证明在这些例子上照样成立。',
     '- 含 (2j)! 这类分子因子的项，若在象限深处支撑仍伸到 j=0（如 C(2j,j)C(k,j)C(m,j)），按整数常数的写法不满足 (N2)：'
     '支撑端点外紧挨着 (2j)! 参数为负的点，所以它们不在这条推论的范围内，尽管 s6-t27 的计算显示证明在这些例子上照样成立。'
     '支撑远离 j=0 时这类因子无妨，例如 C(2j,j)C(m,j−k) 取 Q_R={k≥R, m≥R} 满足 (N2)。'
     '（2026-10-07 更正：原句写成「含 C(2j,j) 一类因子的项都不满足 (N2)」，第二位复核者 s7-t27 指出说过了头，见 ' + REVIEW + '。）'),
    ('README.md',
     '    - T2.7′ 请第二位复核者审查，如果要覆盖 C(2j,j) 一类因子，再核对 s6-t27 提出的 (N2′)；',
     '    - T2.7′ 已有第二位复核者（s7-t27，2026-10-07，confirmed with minor gaps，适用范围的一句话已改正，见 ' + REVIEW + '）；'
     '仍待人类专家审阅；如果要覆盖支撑伸到 j=0 的 C(2j,j) 一类写法，再核对 s6-t27 提出的 (N2′)；'),
    ('ROADMAP.md',
     '| T2.7′（2026-10-07 的新证明） | 只经一位复核者（s6-t27）审查，结论 confirmed；(N2) 依赖被加项的写法，含 C(2j,j) 一类因子的写法不在范围内 '
     '| 请第二位复核者审查；如果论文要覆盖 C(2j,j) 一类因子，再核对 s6-t27 提出的 (N2′) 与引理 F′ |',
     '| T2.7′（2026-10-07 的新证明） | 两位复核者独立审查：s6-t27 confirmed；s7-t27（10-07）confirmed with minor gaps，适用范围的一句话已改正；'
     '(N2) 依赖被加项的写法，支撑在象限深处仍伸到 j=0 的 C(2j,j) 一类写法不在范围内 '
     '| 请人类专家审阅（论文 §6.2）；如果要覆盖这类写法，再核对 s6-t27 提出的 (N2′) 与引理 F′ |'),
]

texts = {}
eols = {}
for rel, old, new in EDITS:
    path = os.path.join(ROOT, rel)
    t = texts.get(rel)
    if t is None:
        raw = open(path, 'rb').read()
        eols[rel] = '\r\n' if b'\r\n' in raw else '\n'      # keep each file's own line endings
        t = raw.decode('utf-8').replace('\r\n', '\n')
    n = t.count(old)
    assert n == 1, '%s：锚点出现 %d 次：%s' % (rel, n, old[:40])
    texts[rel] = t.replace(old, new)

for rel, t in texts.items():
    if DRY:
        print('would patch', rel, 'eol', repr(eols[rel]))
    else:
        with open(os.path.join(ROOT, rel), 'w', encoding='utf-8', newline=eols[rel]) as f:
            f.write(t)
        print('patched', rel, 'eol', repr(eols[rel]))
