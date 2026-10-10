# -*- coding: utf-8 -*-
r"""Lean 续作第三十六项（2026-10-10）：OEIS A326247（按条目的 %N/%C 定义）、U_4(m) = A326247(m+2) 与 Colin Barker 在
A326247 的三条猜想，新模块 `lean/A207123/A326247.lean`：
- 定义 `edgePairs`、`EdgeCross`、`EdgeNest`、`A326247`（既不交叉也不嵌套的边的有序对个数）；`A326247_small`：前 7 项
  与 %S 相同（内核里按定义直接数）。
- `A326247_add`：a(n) + 4·C(n,4) = C(n,2)²（坏的有序对分四类，各经坐标置换对应到 a < b < c < d，`inc4_eq`）；
  `A326247_eq_U_four`：U_4(m) = A326247(m+2)。
- Barker：`barker_A326247_formula`、`barker_A326247_rec`、`barker_A326247_gf`。
根模块加 import，Axioms 加 12 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_a326247.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；「Not formalized」一段末尾加一句：引言里 U_3、U_4 的 OEIS 等式已形式化
  （两条目按 OEIS 的定义，只经 AI 核对），U_k(1) = A038718(k+2) 没有（try_layout：39 页、无警告；第 10 节标题从
  第 29 页底移到表 5 之后）。
- paper/reviewer_guide.tex：第 2 节已形式化的清单加上引言的 OEIS 等式；只经 AI 核对的定义加上 A084990、A326247
  （2 页，只有原来就有的第 55 行 underfull）。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A15 升为 ■■■■■；A16 记 U_4 = A326247 与条目定义的等同已形式化。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_a326247.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_a326247.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '70'

PAPER = [
    (r'instead of citing the Lindeberg--Feller theorem.',
     r'instead of citing the Lindeberg--Feller theorem. Of the OEIS identities in Section~\ref{sec:intro}, '
     r'$U_3(m)=\text{A084990}(m+1)$ and $U_4(m)=\text{A326247}(m+2)$ are formalized, with both entries defined as in '
     r'the OEIS and compared with it only by AI (\lean{U\_three\_eq\_A084990}, \lean{A326247\_eq\_U\_four}); '
     r'$U_k(1)=\text{A038718}(k+2)$ is not.'),
]
PAPER_RE = [
    (r'consists of 61 files that start from', 'consists of 62 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    (r'has a negative coefficient for $k\ge3$).',
     r'has a negative coefficient for $k\ge3$), and the OEIS identities for $U_3$ and $U_4$ in Section 1.'),
    (r'the sums in Section 6.1) are in the Lean files',
     r'the sums in Section 6.1, the OEIS entries A084990 and A326247) are in the Lean files'),
]

README = [
    ('`Mobius.lean` 与 `Barker.lean`）', '`Mobius.lean`、`Barker.lean` 与 `A326247.lean`）'),
    ('共 61 个模块（', '共 62 个模块（'),
    ('与 T5.4(2) 中 Barker 在 A207118、A207069 的猜想（这两项论文没有陈述）后由 2675 增加',
     '与 T5.4(2) 中 Barker 在 A207118、A207069、A326247 的猜想（这两项论文没有陈述），以及引言里的 '
     'U_4(m) = A326247(m+2)（A326247 按条目定义）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_barker.py`。',
     '补丁 `patch_paper_2026-10-10_lean_barker.py`。第三十六项：OEIS A326247 与 Barker 在该条目的三条猜想，新模块 '
     '`A326247.lean`（按条目 %%N/%%C 定义：顶点 0..n−1 上边的有序对（可以相同）中既不交叉也不嵌套的个数，'
     '`edgePairs`、`EdgeCross`、`EdgeNest`、`A326247`；`A326247_small`：前 7 项 0, 0, 1, 9, 32, 80, 165 与 %%S 相同（内核里'
     '按定义数）；`A326247_add`：a(n) + 4·C(n,4) = C(n,2)²（坏的有序对分四类，各经坐标置换对应到 a < b < c < d < n，'
     '`inc4_eq` 由曲棍球恒等式得 C(n,4)）；`A326247_eq_U_four`：U_4(m) = A326247(m+2)（论文引言与报告 T5.4(4)）；'
     '`barker_A326247_formula`：a(n) = n(12 − 19n + 6n² + n³)/12；`barker_A326247_rec`：n > 4 时的 5 阶递推；'
     '`barker_A326247_gf`：(1 − x)⁵·Σ a(n)xⁿ = x²(1 + 4x − 3x²)）。第一次编译 split_ifs 没拆开五个 if，改成逐类 '
     'by_cases 加 ite_eq_left/ite_eq_right 后通过，再删去一个多余假设（27 s、峰值 8.1 GB）。论文第 9 节「Not formalized」'
     '一段末尾加一句：引言里 U_3、U_4 的 OEIS 等式已形式化（两条目按 OEIS 的定义，只经 AI 核对），U_k(1) = A038718(k+2) '
     '没有；审读指南同步。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_a326247.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_barker.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_barker.log`）。同日第三十六项：新模块 `A326247.lean`。新的承重定义四个，'
     '已与 A326247 条目（快照 `data/lit/oeis/A326247.txt`）的 %%N、%%C、%%t 逐条对照：`edgePairs n` 是 '
     '`((x, y), (z, t))`，`x < y`、`z < t` 都在 `{0, …, n−1}` 里（边写成 2 元子集的有序表示，两条边可以相同，与 %%t 的 '
     '`Tuples[Subsets[Range[n],{2}],2]` 一致，顶点从 0 编号不影响计数）；`EdgeCross` 是 %%C 的 `a < c < b < d` 或 '
     '`c < a < d < b`，`EdgeNest` 是 `a < c < d < b` 或 `c < a < b < d`（`a, b, c, d` 依次是 `x, y, z, t`）；`A326247 n` '
     '数两者都不成立的有序对。`A326247_small` 在内核里按定义数出前 7 项 0, 0, 1, 9, 32, 80, 165，与 %%S 相同。'
     '`inc2`、`inc3`、`inc4` 只在证明里用。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，'
     '只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_a326247.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（列方向与行方向，Barker 在 A207118、A207069 的猜想）；■■■■□（Barker 在 A326247 的猜想） |', '| ■■■■■ |'),
    ('；A326247 的三条未形式化 |',
     '；A326247 的三条（g.f.、四次多项式、5 阶递推）同日也已形式化（`A326247.lean`：A326247 按条目 %N/%C 定义为既不交叉'
     '也不嵌套的边的有序对个数，`A326247_small` 核对 %S 前 7 项，`barker_A326247_formula`、`barker_A326247_rec`、'
     '`barker_A326247_gf`） |'),
    ('| ■■■■■（多项式恒等式与 g.f.）；■■■■□（与 OEIS 条目的等同、双射） | 书面证明；代数部分 Lean：SmallK（第四轮）；',
     '| ■■■■■（多项式恒等式与 g.f.；U_3 = A084990、U_4 = A326247 与条目定义的等同）；■■■■□（R_k = A038718(k+2) 与'
     '条目定义的等同、显式双射） | 书面证明；代数部分 Lean：SmallK（第四轮；A084990 按条目 %N 的公式定义，'
     '`U_three_eq_A084990`）；U_4(m) = A326247(m+2)（A326247 按条目 %N/%C 的组合定义）2026-10-10 已形式化'
     '（`A326247.lean` 的 `A326247_eq_U_four`、`A326247_add`）；R_k = A038718(k+2) 与显式双射未形式化；'),
]


def patch(path, reps, regex=()):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    for pat, new in regex:
        found = re.findall(pat, s)
        assert len(found) == 1, (path, len(found), pat[:60])
        s = re.sub(pat, lambda _m: new, s)
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d edits' % (os.path.relpath(path, ROOT), len(reps) + len(regex)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS, ' Axioms lines:', _ax)
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER, PAPER_RE)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)
    patch(os.path.join(ROOT, '猜想总表.md'), TABLE)


if __name__ == '__main__':
    main()
