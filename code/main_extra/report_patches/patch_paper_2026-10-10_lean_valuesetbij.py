# -*- coding: utf-8 -*-
r"""Lean 续作第五十四项（2026-10-10）：报告 T5.4(4)(5) 中 U_3、U_4 的显式保值集双射（猜想总表 A16；notes/c5b.md 的 T9、T13）。
新模块 `lean/A207123/ValueSetBij.lean`：
- `U_three_bijOn`、`bij3_values`：长 3 的合法序列 ↔ 单调三元组（非增或非减，`monoSet`）的双射 f3（非增不动；
  (a<b=c) ↦ (a,a,b)；(b<c≤a) ↦ (b,c,a)），保持取值集合；逆映射 g3（`bij3inv`）。
- `U_four_bijOn`、`bij4_values`：长 4 的合法序列 ↔ {0..m+1} 上既不交叉也不嵌套的有序边对（A326247 的对象，
  `goodPairs`，`card_goodPairs`：#goodPairs n = A326247 n）的分段双射 Φ（SSSS/ST/TS/SSE 各两段），保持取值集合；
  逆映射按 L≤/L>/R′/D1/D2 分段（`bij4inv`）。
根模块加 import，Axioms 加 6 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_valuesetbij.log 读。
论文只陈述了 U_3 = A084990、U_4 = A326247 的等式（已形式化），没有陈述双射：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A16 的状态栏与 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_valuesetbij.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_valuesetbij.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '88'

PAPER_RE = [
    (r'consists of 79 files that start from', 'consists of 80 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`OneAtomE.lean` 与 `NOneAtom.lean`）', '`OneAtomE.lean`、`NOneAtom.lean` 与 `ValueSetBij.lean`）'),
    ('共 79 个模块（', '共 80 个模块（'),
    ('，notes/13 定理 5(a)（N 的同一结论）（这些论文都没有陈述）后由 2675 增加',
     '，notes/13 定理 5(a)（N 的同一结论），报告 T5.4(4)(5) 中 U_3、U_4 的显式保值集双射（这些论文都没有陈述）后由 '
     '2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_noneatom.py`。',
     '补丁 `patch_paper_2026-10-10_lean_noneatom.py`。第五十四项：报告 T5.4(4)(5) 中 U_3、U_4 的显式保值集双射（猜想总表 '
     'A16；notes/c5b.md 的 T9、T13），新模块 `ValueSetBij.lean`（`U_three_bijOn`：f3（`bij3`：非增三元组不动；'
     '(a<b=c) ↦ (a,a,b)；(b<c≤a) ↦ (b,c,a)）是长 3 的合法序列到单调三元组（非增或非减，`monoSet`）的双射，逆映射 g3'
     '（`bij3inv`）；`U_four_bijOn`：Φ（`bij4`，区间 [x,y] 记成边 (x,y+1)，按合法 4 元组的块型 SSSS/ST/TS/SSE 各分两段）'
     '是长 4 的合法序列到 {0..m+1} 上既不交叉也不嵌套的有序边对（A326247 的对象 `goodPairs`，`card_goodPairs`：'
     '#goodPairs n = A326247 n）的双射，逆映射按区间对的类型 L≤/L>/R′/D1/D2 分段（`bij4inv`）；`bij3_values`、'
     '`bij4_values`：两个双射都保持取值集合。证明：成员关系化成坐标的不等式（`mem_L_three`、`mem_L_four`、'
     '`mem_monoSet`、`mem_goodPairs`），映射与逆映射逐段由 `omega` 验证（`Set.InvOn.bijOn`）。报告已指出这类双射在两边'
     '计数是同一多项式时必然存在，不算结构的证据。编译改了一轮（`simp only` 把 a = a 化成 True 后 `omega` 不认 '
     '`True ∧ …`，补 `true_and`；目标集合写成 Finset `goodPairs`），最终无错误、无警告（28 s、峰值 8.2 GB）。论文没有'
     '陈述这两个双射，只改第 9 节计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s '
     'PASS；补丁 `patch_paper_2026-10-10_lean_valuesetbij.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_noneatom.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_noneatom.log`）。同日第五十四项：新模块 `ValueSetBij.lean`（报告 T5.4(4)(5) '
     '的保值集双射）。新的承重定义：`monoSet m`（`seqs m 3` 中两两非增或两两非减的序列，即「单调三元组」，与 notes/c5b '
     'T8、T9 及 A084990 的条目注释一致）、`goodPairs n`（与 `A326247 n` 计数的集合逐字相同，`card_goodPairs` 由 `rfl` '
     '得到）；映射 `bij3`、`bij3inv`、`bij4`、`bij4inv` 已与 notes/c5b T9 的三段式与 T13 的八行表逐段对照（区间 [x, y] '
     '记成边 (x, y+1)）。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准'
     '公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_valuesetbij.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；R_k 与 Hamilton 路的显式双射）；■■■■□（U_3、U_4 的显式保值集双射） |',
     '；R_k 与 Hamilton 路的显式双射；U_3、U_4 的显式保值集双射） |'),
    ('；U_3、U_4 的显式保值集双射未形式化（报告 T5.4(4) 已指出：两边计数是同一多项式时这类双射必然存在）',
     '；U_3、U_4 的显式保值集双射 2026-10-10 也已形式化（`ValueSetBij.lean` 的 `U_three_bijOn`、`bij3_values`：合法三元组 '
     '↔ 单调三元组，notes/c5b T9；`U_four_bijOn`、`bij4_values`：合法 4 元组 ↔ {0..m+1} 上不交叉也不嵌套的有序边对，'
     '按块型分 8 段，notes/c5b T13；报告 T5.4(4) 已指出：两边计数是同一多项式时这类双射必然存在）'),
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
    jobs = [(os.path.join(ROOT, 'paper', 'main.tex'), [], PAPER_RE),
            (os.path.join(ROOT, 'README.md'), README, README_RE),
            (os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST, ()),
            (os.path.join(ROOT, '猜想总表.md'), TABLE, ())]
    out = [(path,) + patched(path, reps, regex) for path, reps, regex in jobs]
    for path, s, n in out:
        open(path, 'wb').write(s.encode('utf-8'))
        print('%s: %d edits' % (os.path.relpath(path, ROOT), n))


if __name__ == '__main__':
    main()
