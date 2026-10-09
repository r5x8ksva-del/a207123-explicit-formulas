# -*- coding: utf-8 -*-
"""论文第二轮修订（2026-10-09 晚，用户：「按照你的想法来」）：论文不再依赖中文报告与笔记里的结论。
- 决定：只在报告 / 笔记里证明的结论不写进论文（注记 6.4 的负形状、第 10 节 (1)(2) 的「报告排除了更多的类」、
  (3) 的约化、(4) 的门槛定理）；计算类的证据保留，并写明是计算、脚本在仓库（(3) 的 k<=300、(4) 的 i<=579 与常数 9.6085）。
  第 9 节、AI 声明、「Data and code」里提到报告的说法相应改掉。
- 推论 5.5 之后 Rel(N)=O L_N 一段：明说只陈述、略去证明，完整证明在 Lean（RelN_eq、finrank_relN_tot）。
- 推论 5.7 的证明里 Kauers 的生成元改用本文的移位记号 S（推论里已定义），避免与三角 N(k,q) 撞名；不写 Kauers 原文
  用什么字母（data/lit/read_papers.md 记的定义 3 写法是 N_1^{v_1}N_2^{v_2}，与原稿的 N^{v_1}K^{v_2} 不同）。
- 注记 8.16 与引言补一句零点位置：h-多项式系数非负（如 Cohen-Macaulay）时链多项式没有小于 -1 的零点，
  Brändén-Saud Maia Leite 的 TN-偏序集与 P-positive 偏序集的结果也把零点放在 [-1,0]；n_k 在 k>=3 时有 floor(k/3) 个
  零点小于 -1，所以定理 8.1 不能由这类结果推出（读过 arXiv:2412.06595v3 第 5、6 节，记录在 data/lit/read_papers.md）。
  BL26 文献条目补 arXiv 号。
每处替换断言原文出现一次；按字节读写（paper/main.tex 是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-09_reportrefs.py [tex 路径]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

REPS = [
    # --- 注记 6.4：报告里的负形状结论不写进论文
    (r' The accompanying report settles this case by a different argument (it shows $\C(x)\cap\C((v))=\C(v)$ using '
     r"L\"uroth's theorem and the Riemann--Hurwitz formula, and then bounds the absolute value of a product over a fibre): "
     r'for $m\ge1$ and all integers $\alpha,\beta$, not both $0$, a representation \eqref{eq:shapes} exists if and only if '
     r'$\beta\ge0$ and $\alpha+\beta=1$.',
     r' We do not treat this case here.'),
    # --- 推论 5.5 之后：Rel(N) 只陈述
    (r'The analogous statement for the triangle holds with $\Rel(N)=\cO\cdot L_N$, $L_N=1-X-XY-(q-1)X^3(1+Y)^2$, where $Y$ '
     r'shifts $q$, and the dimension in a box is $(A-2)(B-1)D(D+1)/2$ for $A\ge3$, $B\ge2$, $D\ge1$. Its proof transports the '
     r'problem to $U$ through the binomial transform $V(k,m)=\sum_q\binom{m}{q}N(k,q)$, which satisfies $V(k,m+1)=U_k(m)$ by '
     r'\eqref{eq:Nbasis}, and needs an additional saturation lemma for the left factors $Y$ and $1+Y$.',
     r'For the triangle we only state the analogous result: $\Rel(N)=\cO\cdot L_N$ with $L_N=1-X-XY-(q-1)X^3(1+Y)^2$, where '
     r'$Y$ shifts $q$, and the dimension in a box is $(A-2)(B-1)D(D+1)/2$ for $A\ge3$, $B\ge2$, $D\ge1$. We omit the proof. It '
     r'transports the problem to $U$ through the binomial transform $V(k,m)=\sum_q\binom{m}{q}N(k,q)$, which satisfies '
     r'$V(k,m+1)=U_k(m)$ by \eqref{eq:Nbasis}, and needs an additional saturation lemma for the left factors $Y$ and $1+Y$; '
     r'a complete proof is part of the Lean development (\lean{RelN\_eq}, \lean{finrank\_relN\_tot}; see Section~\ref{sec:lean}).'),
    # --- 推论 5.7 的证明：Kauers 的移位算子改用 S
    (r'three-term generator $u+v\,N^{v_1}K^{v_2}-w\,N^{w_1}K^{w_2}$, whose shift points',
     r'three-term generator $u+v\,S^{(v_1,v_2)}-w\,S^{(w_1,w_2)}$, whose shift points'),
    # --- 第 9 节
    # （改写后这一段有一行溢出 89pt，整段放进 sloppypar，与论文里另外两处长 Lean 名字的做法相同）
    (r'Several further results of the accompanying report are formalized as well.',
     r'\begin{sloppypar}' '\n'
     r'The development also formalizes several auxiliary results that are not stated in this paper.'),
    (r'so the formal statement is stronger.', r'so the formal statement is stronger.' '\n' r'\end{sloppypar}'),
    # --- 第 10 节
    (r' The accompanying report rules out several further classes.', ''),
    (r' The accompanying report rules out several natural single sums and one family of double sums.', ''),
    (r' The accompanying report proves this for $k\le300$ with computer assistance; for each $k$ it reduces the question to '
     r'the finitely many $j$ that divide $\operatorname{lcm}(1,\dots,k)$ and lie below an explicit bound of order $k^3$.',
     r' A computer search for $k\le300$ (scripts in the repository) found no further negative integer zeros.'),
    (r' For fixed $i$ the coefficient of $t^i$ in $h_k$ is positive for all large $k$; the notes in the repository determine '
     r'the least threshold $\tau_i$ from which on it stays positive for $i\le579$ (with computer assistance), prove '
     r'$\tau_i=O(i\log i)$, and give heuristic and numerical evidence that $\tau_i/i$ converges to an explicit constant '
     r'$\alpha^*\approx9.6085$.',
     r' Computations for $i\le579$ (scripts in the repository) suggest that for each $i$ the coefficient of $t^i$ in $h_k$ is '
     r'positive for all large $k$, and that the least $k$ from which on it stays positive grows like $\alpha^*i$ with '
     r'$\alpha^*\approx9.6085$.'),
    # --- AI 声明与 Data and code
    (r'are labelled as numerical in the accompanying report.',
     r'are labelled as numerical in the output of the verification scripts.'),
    (r'(apart from the results of the accompanying report and notes quoted in Section~\ref{sec:open}, which are checked by '
     r'their own scripts)',
     r'(apart from the computations quoted in Section~\ref{sec:open}, which have their own scripts)'),
    # --- 注记 8.16 与引言：零点位置
    (r'\cite[Chapter~II]{StanleyCCA}.' '\n' r'\end{remark}',
     r'\cite[Chapter~II]{StanleyCCA}. If the $h$-polynomial $h$ of an order complex of dimension $d-1$ has nonnegative '
     r'coefficients, as it has for Cohen--Macaulay posets, then the chain polynomial $f(z)=(1+z)^dh\bigl(z/(1+z)\bigr)$ has no '
     r'zeros in $(-\infty,-1)$, since $h>0$ on $(1,\infty)$; the general results of \cite{BL26} on TN-posets and $P$-positive '
     r'posets also place all zeros in $[-1,0]$. By the proof of Corollary~\ref{cor:hk-signs}, $n_k$ has exactly '
     r'$\lfloor k/3\rfloor$ zeros in $(-\infty,-1)$, so for $k\ge3$ Theorem~\ref{thm:realroots} does not follow from results '
     r'of this kind.' '\n' r'\end{remark}'),
    (r'a subject studied for several classes of posets in \cite{AK23,ADK24,BL26}.',
     r'a subject studied for several classes of posets in \cite{AK23,ADK24,BL26}; unlike in the results there, for $k\ge3$ '
     r'the zeros are not confined to $[-1,0]$ (Remark~\ref{rem:chains}).'),
    # --- BL26 补 arXiv 号
    (r'\emph{Adv. Math.} \textbf{487} (2026), Paper No.~110760, \url{https://doi.org/10.1016/j.aim.2025.110760}.',
     r'\emph{Adv. Math.} \textbf{487} (2026), Paper No.~110760, \url{https://doi.org/10.1016/j.aim.2025.110760}; '
     r'arXiv:2412.06595.'),
]


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    p = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'paper', 'main.tex')
    raw = open(p, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in REPS:
        c = s.count(old)
        assert c == 1, (c, old[:70])
        s = s.replace(old, new)
    assert 'accompanying report' not in s and 'notes in the repository' not in s
    open(p, 'wb').write(s.encode('utf-8'))
    print('paper/main.tex: %d edits' % len(REPS))


if __name__ == '__main__':
    main()
