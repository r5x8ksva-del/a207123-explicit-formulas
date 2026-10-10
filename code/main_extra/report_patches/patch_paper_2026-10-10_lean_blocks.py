# -*- coding: utf-8 -*-
r"""Lean 续作第六项（2026-10-10）：论文定理 4.2（唯一分解）与例 4.3 之后一段的上升数，新模块 `lean/A207123/Blocks.lean`：
`blocks_bijOn`（串接是从「层级弱递减、都在 {0,…,m} 中、只有最后一块可以是 E 块」的块序列全体到 ⋃_k H_k(m) 的双射，
`Set.BijOn`）、`asc_concatBlk`（好序列的上升数等于 T 块与 E 块的个数）。块 `Blk`（S、T、E）、`BlkSeq`、`concatBlk`
是新定义，由 AI 对照论文定义 4.1 与定理 4.2 核对。
根模块加 import，Axioms 加两条（共 270 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_blocks.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数 30 → 31、声明数；表 5 在定理 4.4 一行之前加定理 4.2 一行；「Not formalized」去掉块分解。
- paper/reviewer_guide.tex：第 2 节加上块分解（定理 4.2）；第 3 节第 3 条去掉定理 4.2。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_blocks.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_blocks.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '39'

ROW44 = (r'Theorem~\ref{thm:gfxy}, Lemma~\ref{lem:coef} & \lean{Gxy\_zero}, \lean{Gxy\_rec}, \lean{Gxy\_prod}, '
         r'\lean{coef\_formula\_xy}\\' '\n')
PAPER = [
    (r'consists of 30 files that start from', r'consists of 31 files that start from'),
    (r'all 2778 declarations', r'all %s declarations' % DECLS),
    (ROW44, r'Theorem~\ref{thm:blocks} & \lean{blocks\_bijOn}, \lean{asc\_concatBlk}\\' '\n' + ROW44),
    (r'Not formalized: the block decomposition (Theorem~\ref{thm:blocks}) and the bijection of '
     r'Proposition~\ref{prop:bijection} (the formal proofs',
     r'Not formalized: the bijection of Proposition~\ref{prop:bijection} (the formal proofs'),
]

GUIDE = [
    (r'Corollary 3.4, the generating function in $x$ and $y$',
     r'Corollary 3.4, the block decomposition (Theorem 4.2), the generating function in $x$ and $y$'),
    (r'(pp.~10--12):} Theorem 4.2, the identification with $r$-Stirling numbers',
     r'(pp.~10--12):} the identification with $r$-Stirling numbers'),
]

README = [
    ('共 30 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean`、'
     '`ThreeTerm.lean` 与 `GenFunXY.lean`）',
     '共 31 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean`、'
     '`ThreeTerm.lean`、`GenFunXY.lean` 与 `Blocks.lean`）'),
    ('2778 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、推论 5.5、推论 5.7、定理 4.4 与引理 4.5 的'
     '按 y 细化后由 2675 增加；',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、推论 5.5、推论 5.7、定理 4.2、定理 4.4 与'
     '引理 4.5 的按 y 细化后由 2675 增加；' % DECLS),
    ('（补丁 `patch_paper_2026-10-10_lean_genfunxy.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_genfunxy.py`）。第六项：定理 4.2（唯一分解），新模块 `Blocks.lean`：'
     '块 `Blk`（S、T、E）、`concatBlk`（串接）、`BlkSeq`（层级弱递减、都 ≤ m、只有最后一块可以是 E 块）；'
     '`blocks_bijOn`（串接是从这样的块序列到 ⋃_k H_k(m) 的双射，`Set.BijOn`）、`asc_concatBlk`（上升数等于 T 块与 E 块的'
     '个数）。证明照论文：串接都是好序列、首块由序列决定、按长度归纳构造。编译前余量只有 11.5–12.9 GB，按实测一次编译'
     '再降 9–9.5 GB 估算余地太小，没启动：`lean_one.sh` 的闸门（13 GB）第一次等满 25 分钟后放弃（exit 75），用户关掉 Ollama 后'
     '余量回到 15.5 GB 才编译（峰值 8.04 GB，最低余量 8.1 GB）。第一次编译两处 `obtain ⟨rfl, …⟩` 失败（替换后原假设重新'
     '引入、遮住了新假设），改用 `List.cons.inj` 后通过。根模块、Axioms（270 条，全量扫描 %s 个声明，只有三条'
     '标准公理）与 Checks 通过，`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_blocks.py`）。'
     % (DECLS, FRESH)),
]

CHECKLIST = [
    ('`check_lean_fresh.py` 38 项全部 PASS（`logs/check_lean_fresh_2026-10-10_genfun.log`）。',
     '`check_lean_fresh.py` 38 项全部 PASS（`logs/check_lean_fresh_2026-10-10_genfun.log`）。同日第六项：新模块 '
     '`Blocks.lean`（论文定理 4.2；新定义 `Blk`、`Blk.toList`、`Blk.level`、`Blk.Valid`、`Blk.IsE`、`concatBlk`、'
     '`BlkSeq` 由 AI 对照论文定义 4.1 与定理 4.2 核对，`L`、`Legal`、`asc` 沿用已有定义），经 `lean/lean_one.sh` 编译、'
     '重编根模块、重跑 `Axioms.lean`（270 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` '
     '%s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_blocks.log`）。' % (DECLS, FRESH)),
]


def patch(path, reps):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d edits' % (os.path.relpath(path, ROOT), len(reps)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS)
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
