# -*- coding: utf-8 -*-
r"""Lean 续作第二十一项（2026-10-10）：论文推论 8.2（N 的每一行为正、严格对数凹、单峰），新模块
`lean/A207123/LogConcave.lean`：
- `prod_X_add_C_coeff_props`：正数 r_1..r_n 的 ∏(X + r_i) 的系数都是正数且严格对数凹（对因子个数归纳；论文用 Newton
  不等式，这里不用）；`root_neg_nR`（n_k 的根都是负数）、`nR_eq_prod`（n_k = N(k,k)·∏(z + r)）；
- `unimodal_of_pos_logconcave`（正的严格对数凹序列单峰）；`cor_logconcave`（推论 8.2）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_logconcave.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 5 中命题 8.10、8.11 与定理 8.1 一行之后加推论 8.2 一行；「Not formalized」
  里删去推论 8.2。
- paper/reviewer_guide.tex：第 2 节与第 3 节 Section 8 一条。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的完成度与形式化一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_logconcave.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_logconcave.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '55'

ROW_PREV = (r'\lean{realRooted\_nR}, \lean{separable\_hpoly}, \lean{thm\_realroots}\\' + '\n')
PAPER = [
    (ROW_PREV, ROW_PREV + r'Corollary~\ref{cor:logconcave} & \lean{cor\_logconcave}, '
     r'\lean{prod\_X\_add\_C\_coeff\_props}, \lean{unimodal\_of\_pos\_logconcave}\\' + '\n'),
    (r'with $c,w_a\ge0$ instead), Corollary~\ref{cor:logconcave}, the sign of $\lambda_k$',
     r'with $c,w_a\ge0$ instead), the sign of $\lambda_k$'),
]
PAPER_RE = [
    (r'consists of 46 files that start from', 'consists of 47 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('those of $h_k$ are real and simple),',
     'those of $h_k$ are real and simple), Corollary 8.2 (each row of $N$ is positive, strictly log-concave and '
     'unimodal; proved without Newton\'s inequalities),'),
    ('Not formalized: Lemmas 8.5 and 8.7(3) themselves, Corollary 8.2 and Lemma 8.12',
     'Not formalized: Lemmas 8.5 and 8.7(3) themselves and Lemma 8.12'),
]

README = [
    ('`RealRoots.lean` 与 `SimpleRoots.lean`）', '`RealRoots.lean`、`SimpleRoots.lean` 与 `LogConcave.lean`）'),
    ('共 46 个模块（', '共 47 个模块（'),
    ('h_k 的根都是实数且互不相同）后由 2675 增加',
     'h_k 的根都是实数且互不相同）、推论 8.2（N 的每一行为正、严格对数凹、单峰）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_simpleroots.py`。',
     '补丁 `patch_paper_2026-10-10_lean_simpleroots.py`。第二十一项：论文推论 8.2，新模块 `LogConcave.lean`'
     '（`prod_X_add_C_coeff_props`：正数 r_i 的 ∏(X + r_i) 的系数都是正数且严格对数凹，对因子个数归纳，不用论文的 '
     'Newton 不等式；`root_neg_nR`：n_k 的根都是负数；`nR_eq_prod`：n_k = N(k,k)·∏(z + r)；'
     '`unimodal_of_pos_logconcave`；`cor_logconcave`：N(k,1..k) 都是正数，N(k,q)² > N(k,q−1)N(k,q+1)，这一行单峰）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_logconcave.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_simpleroots.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_simpleroots.log`）。同日第二十一项：新模块 `LogConcave.lean`（论文推论 8.2；'
     '新定义 `rowProd k`（∏(z + r)，r 取 −(n_k 的根)）只在证明中用；主陈述 `cor_logconcave` 只用到 `N`），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_logconcave.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('N 的每一行单峰、对数凹 | ■■■■■（实根与单根，2026-10-10）；■■■■□（推论） |',
     'N 的每一行单峰、对数凹 | ■■■■■（实根、单根、对数凹与单峰，2026-10-10）；■■■■□（其余推论） |'),
    ('；推论（对数凹、单峰、根的分布、变号、中心极限定理）未形式化',
     '；第二十一项形式化了推论「N(k,·) 为正、严格对数凹、单峰」（论文推论 8.2，`LogConcave.lean` 的 '
     '`cor_logconcave`，不用 Newton 不等式，改为对 ∏(z + r_i) 的因子个数归纳）；根的分布、变号、中心极限定理未形式化'),
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
