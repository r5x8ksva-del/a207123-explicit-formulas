# -*- coding: utf-8 -*-
r"""Lean 续作第一项（2026-10-10，用户：「我现在还是希望跑lean，请你一个一个lean的来跑，先把最简单的lean跑完」）：
定理 3.2(1) 的最后两句已在 Lean 里证完（`lean/A207123/Growth.lean` 新增 `rho_mul_rho_sub_one_strictMono`：
|σ|²=ρ_m(ρ_m−1) 关于 m 严格增；`normSq_lt_rho_pred_sq`：|σ|²<ρ_{m−1}²）。重编 Growth 与根模块，重跑 Axioms
（258 条 #print axioms，全量扫描 2678 个声明，只有 propext、Classical.choice、Quot.sound）与 Checks，日志
`logs/lean_*_2026-10-10.log`。本补丁同步：
- paper/main.tex：表 5 里定理 3.2(1) 一行去掉「except |σ|²<ρ²_{m−1}」并补上两条新定理名；第 9 节全量扫描的声明数
  2675 → 2678；「Not formalized」去掉这条不等式。
- paper/reviewer_guide.tex：第 2 节「已机器检查」加上定理 3.2(1)；第 3 节第 5 条去掉这条不等式。
- README.md：声明数改为 2678，并记一笔这一项。
- notes/Lean定义核对清单.md：「机械核对」一节记 2026-10-10 的重编与核对。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_sigma.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

PAPER = [
    (r'Theorem~\ref{thm:asym}(1), except $|\sigma|^2<\rho_{m-1}^2$ & \lean{existsUnique\_rho}, \lean{one\_lt\_rho}, '
     r'\lean{rho\_strictMono}, \lean{normSq\_eq\_of\_root}, \lean{norm\_lt\_rho\_of\_root}, \lean{root\_P\_min}\\',
     r'Theorem~\ref{thm:asym}(1) & \lean{existsUnique\_rho}, \lean{one\_lt\_rho}, \lean{rho\_strictMono}, '
     r'\lean{normSq\_eq\_of\_root}, \lean{rho\_mul\_rho\_sub\_one\_strictMono}, \lean{normSq\_lt\_rho\_pred\_sq}, '
     r'\lean{norm\_lt\_rho\_of\_root}, \lean{root\_P\_min}\\'),
    (r'an exhaustive scan of all 2675 declarations of the development finds no other axiom.',
     r'an exhaustive scan of all 2678 declarations of the development finds no other axiom.'),
    (r'the inequality $|\sigma|^2<\rho_{m-1}^2$ in Theorem~\ref{thm:asym}(1), Theorem~\ref{thm:asym}(2)(3) and '
     r'Remark~\ref{rem:asym};',
     r'Theorem~\ref{thm:asym}(2)(3) and Remark~\ref{rem:asym};'),
]

GUIDE = [
    (r'the exact orders (Theorem 3.1), Corollary 3.4,',
     r'the exact orders (Theorem 3.1), the roots in Theorem 3.2(1), Corollary 3.4,'),
    (r'\item \textbf{Section 3:} the inequality $|\sigma|^2<\rho_{m-1}^2$ in Theorem 3.2(1), parts (2) and (3) of '
     r'Theorem 3.2 (asymptotics), and Remark 3.3.',
     r'\item \textbf{Section 3:} parts (2) and (3) of Theorem 3.2 (asymptotics) and Remark 3.3.'),
]

README = [
    ('2675 个声明只依赖三条标准公理',
     '2678 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句后由 2675 增加）'),
    ('（`notes/新颖性核查_2026-10-07.md` §10，没有发现先例）。',
     '（`notes/新颖性核查_2026-10-07.md` §10，没有发现先例）。 2026-10-10 用户要求继续做 Lean（一次只跑一个、'
     '每次先算内存够不够）：第一项把定理 3.2(1) 的最后两句形式化，`Growth.lean` 新增 '
     '`rho_mul_rho_sub_one_strictMono`（|σ|²=ρ_m(ρ_m−1) 关于 m 严格增）与 `normSq_lt_rho_pred_sq`（|σ|²<ρ²_{m−1}）；'
     '重编 Growth 与根模块，重跑 Axioms（258 条，全量扫描 2678 个声明，只有三条标准公理）与 Checks，'
     '`check_lean_fresh.py` 35 PASS（日志 `logs/lean_*_2026-10-10.log`、`logs/check_lean_fresh_2026-10-10.log`）；'
     '论文表 5、「Not formalized」与审读指南相应改动（补丁 `patch_paper_2026-10-10_lean_sigma.py`）。'),
]

CHECKLIST = [
    ('\n## 总清单',
     '- **2026-10-10 补形式化后（重新编译）**：`Growth.lean` 新增 `rho_mul_rho_sub_one_strictMono` 与 '
     '`normSq_lt_rho_pred_sq`（论文定理 3.2(1) 的最后两句；用到的 `rho` 定义在 `Growth.lean`，不在上面 18 项里，'
     '陈述由 AI 对照论文核对）。经 `lean/lean_one.sh` 逐个重编 Growth、根模块，重跑 `Axioms.lean`（258 条 '
     '`#print axioms`，全量扫描 2678 个声明，只有 propext、Classical.choice、Quot.sound）与 `Checks.lean`，'
     '每次启动前查过内存（峰值约 8.05–8.08 GB，最低提交余量 4.1 GB）。之后 `check_lean_fresh.py` 35 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10.log`）。\n\n## 总清单'),
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
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
