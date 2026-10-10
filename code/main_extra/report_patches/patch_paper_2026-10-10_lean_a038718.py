# -*- coding: utf-8 -*-
r"""Lean 续作第四十五项（2026-10-10）：报告 T5.4(3)——R_k = U_k(1) = A038718(k+2)（A038718 按 OEIS 条目 %N 的置换
定义）与「允许行 ↔ P_{k+2}² 中 Hamilton 路」的递归双射（猜想总表 A16），新模块 `lean/A207123/A038718.lean`：
- `A038718`：{1,…,n} 的置换 P 中 P(1) = 1、|P⁻¹(i+1) − P⁻¹(i)| ∈ {1, 2} 的个数（下标从 0 起）；
  `A038718_eq_card_hamSet`：它等于从 0 出发的 Hamilton 路数（p_i = P⁻¹(i)，路用列表表示：`IsHam`、`hamSet`）。
- `ham_cases`：n ≥ 4 时按开头分三类（0→1；0→2→1→3；其余时 1 是终点）；`ham_end_one`：以 1 结尾的路唯一，是之字形
  `zz`；`card_hamSet_add_four`、`A038718_add_four`、`A038718_rec`：a(n) = a(n−1) + a(n−3) + 1（条目 %F）；
  `A038718_one`–`A038718_four`：前 4 项 1, 1, 2, 4。
- `U_one_eq_A038718`：U_k(1) = A038718(k+2)（与 `U_one_rec` 同一递推、同一初值）。
- `rowPath`、`isHam_rowPath`、`rowPath_surj`、`rowPath_bijOn`：notes/c5b.md T6 的递归双射（1w、011w、01、0^k 四类），
  单射由满射与两边个数相同得到。
根模块加 import，Axioms 加 19 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_a038718.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；「Not formalized」一段末尾关于引言 OEIS 等式的一句改为三条都已形式化（try_layout 试过四种写法：只说「三条都已形式化」的短句让第 29 页少一行、出现 Underfull \vbox；把三条等式写出来的这一句 39 页、无警告，第 9 节仍在第 29 页，表 5 与第 10 节在第 30 页）。
- paper/reviewer_guide.tex：已形式化的清单与只经 AI 核对的定义加上 A038718。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A16 的完成度、证据与 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_a038718.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_a038718.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '79'

PAPER = [
    (r'Of the OEIS identities in Section~\ref{sec:intro}, $U_3(m)=\text{A084990}(m+1)$ and '
     r'$U_4(m)=\text{A326247}(m+2)$ are formalized, with both entries defined as in the OEIS and compared with it only '
     r'by AI (\lean{U\_three\_eq\_A084990}, \lean{A326247\_eq\_U\_four}); $U_k(1)=\text{A038718}(k+2)$ is not.',
     r'The three OEIS identities of Section~\ref{sec:intro}, $U_k(1)=\text{A038718}(k+2)$, '
     r'$U_3(m)=\text{A084990}(m+1)$ and $U_4(m)=\text{A326247}(m+2)$, are formalized, with the entries defined as in '
     r'the OEIS and compared with it only by AI (\lean{U\_one\_eq\_A038718}, \lean{U\_three\_eq\_A084990}, '
     r'\lean{A326247\_eq\_U\_four}).'),
]
PAPER_RE = [
    (r'consists of 70 files that start from', 'consists of 71 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    (r'and the OEIS identities for $U_3$ and $U_4$ in Section 1.',
     r'and the OEIS identities for $U_k(1)$, $U_3$ and $U_4$ in Section 1.'),
    (r'the OEIS entries A084990 and A326247) are in the Lean files',
     r'the OEIS entries A038718, A084990 and A326247) are in the Lean files'),
]

README = [
    ('`Laguerre.lean` 与 `NumGcd.lean`）', '`Laguerre.lean`、`NumGcd.lean` 与 `A038718.lean`）'),
    ('共 70 个模块（', '共 71 个模块（'),
    ('以及引言里的 U_4(m) = A326247(m+2)（A326247 按条目定义），',
     '以及引言里的 U_4(m) = A326247(m+2)（A326247 按条目定义）与 U_k(1) = A038718(k+2)（A038718 按条目的置换定义），'),
    ('及其证明中引用的 Laguerre 零点定理（α 为自然数）（这些论文都没有陈述）后由 2675 增加',
     '及其证明中引用的 Laguerre 零点定理（α 为自然数），T5.4(3) 中允许行与 Hamilton 路的递归双射（这些论文都没有陈述）'
     '后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_numgcd.py`。',
     '补丁 `patch_paper_2026-10-10_lean_numgcd.py`。第四十五项：报告 T5.4(3)（猜想总表 A16），新模块 `A038718.lean`'
     '（`A038718`：按条目 %%N 的置换定义——{1,…,n} 的置换 P，P(1) = 1，|P⁻¹(i+1) − P⁻¹(i)| 为 1 或 2，Lean 里下标从 0 起；'
     '`A038718_eq_card_hamSet`：令 p_i = P⁻¹(i)，它数的是 P_n² 中从 0 出发的 Hamilton 路（`IsHam`、`hamSet`，路用列表'
     '表示）；`ham_cases`：n ≥ 4 时按开头分三类——0→1、0→2→1→3、其余（这时 1 只能是终点）；`ham_end_one`：以 1 结尾的路'
     '唯一，是之字形 0, 2, 4, …, 5, 3, 1（`zz`）；`A038718_add_four`、`A038718_rec`：a(n) = a(n−1) + a(n−3) + 1（条目 '
     '%%F）；`U_one_eq_A038718`：U_k(1) = A038718(k+2)（论文引言与报告 T5.4(3)，与 `U_one_rec` 同一递推、同一初值）；'
     '`rowPath`、`rowPath_bijOn`：notes/c5b.md T6 的递归双射——1w ↦ 0·(路(w) 平移 +1)，011w ↦ 0, 2, 1·(路(w) 平移 +3)，'
     '01 ↦ 0, 2, 1, 3，全 0 行 ↦ 之字形路——是长 k 的允许行到 P_{k+2}² 中 Hamilton 路的双射，单射由满射 '
     '`rowPath_surj` 与两边个数相同得到）。编译改了一轮（`simpa` 化出的等式方向反了、长度化简缺 `length_nil`、'
     '`h.mem` 的隐式参数推不出、一处多写了 `.symm`），最终无错误、无警告（22 s、峰值 8.1 GB）。论文第 9 节「Not '
     'formalized」一段末尾关于引言 OEIS 等式的一句改为三条都已形式化；审读指南同步。Axioms %d 条，全量扫描 %s 个声明，'
     '只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_a038718.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_numgcd.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_numgcd.log`）。同日第四十五项：新模块 `A038718.lean`（报告 T5.4(3)）。新的承重'
     '定义 `A038718` 已与条目（快照 `data/oeis/A038718.txt`）的 %%N 对照：{1,…,n} 的置换 P，P(1) = 1，且对 i = 1..n−1 有 '
     '|P⁻¹(i+1) − P⁻¹(i)| 等于 1 或 2；Lean 里下标从 0 起（`σ : Equiv.Perm (Fin n)`，下标 0 处 σ 取 0，j = i + 1 时 '
     '`|σ⁻¹ j − σ⁻¹ i|` 为 1 或 2），平移下标不改变计数；条目 %%O 为 1，Lean 定义在 n = 0 时取 1，定理只用 n ≥ 1。双射'
     '定理 `rowPath_bijOn` 的陈述还用到 `hadj`（|a − b| 为 1 或 2）、`IsHam`（0, …, n−1 的排列，以 0 开头，相邻两项 '
     '`hadj`）、`hamSet`（同一集合的 Finset 写法，`mem_hamSet`）与 `rowPath`（notes/c5b.md T6「自然双射」：1w ↦ '
     '0·(路(w) 平移 +1)，011w ↦ 0, 2, 1·(路(w) 平移 +3)，01 ↦ 0, 2, 1, 3，其余 ↦ 之字形路 `zz`；笔记的顶点从 1 编号，'
     '这里从 0 编号）；`zz`、`hamA`、`hamB` 是 `rowPath` 用到的三类路，已对照。经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项'
     '全部 PASS（`logs/check_lean_fresh_2026-10-10_a038718.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（多项式恒等式与 g.f.；U_3 = A084990、U_4 = A326247 与条目定义的等同）；■■■■□（R_k = A038718(k+2) 与'
     '条目定义的等同、显式双射） |',
     '| ■■■■■（多项式恒等式与 g.f.；U_3 = A084990、U_4 = A326247、R_k = A038718(k+2) 与条目定义的等同；R_k 与 '
     'Hamilton 路的显式双射）；■■■■□（U_3、U_4 的显式保值集双射） |'),
    ('；R_k = A038718(k+2) 与显式双射未形式化；',
     '；R_k = A038718(k+2)（A038718 按条目 %N 的置换定义）与「允许行 ↔ P_{k+2}² 中从 1 出发的 Hamilton 路」的递归双射 '
     '2026-10-10 已形式化（`A038718.lean` 的 `U_one_eq_A038718`、`A038718_rec`、`rowPath_bijOn`）；U_3、U_4 的显式'
     '保值集双射未形式化（报告 T5.4(4) 已指出：两边计数是同一多项式时这类双射必然存在）；'),
]


def patched(path, reps, regex=()):
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
    return s, len(reps) + len(regex)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS, ' Axioms lines:', _ax)
    jobs = [(os.path.join(ROOT, 'paper', 'main.tex'), PAPER, PAPER_RE),
            (os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE, ()),
            (os.path.join(ROOT, 'README.md'), README, README_RE),
            (os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST, ()),
            (os.path.join(ROOT, '猜想总表.md'), TABLE, ())]
    out = [(path,) + patched(path, reps, regex) for path, reps, regex in jobs]
    for path, s, n in out:
        open(path, 'wb').write(s.encode('utf-8'))
        print('%s: %d edits' % (os.path.relpath(path, ROOT), n))


if __name__ == '__main__':
    main()
