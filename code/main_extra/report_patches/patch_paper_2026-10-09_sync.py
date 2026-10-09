# -*- coding: utf-8 -*-
"""论文同步（2026-10-09，用户：「推送且论文同步」）：paper/main.tex 里与项目现状不一致的几处。
- 注记 rem:othershapes：α<0、α+β>=2 的形状已在报告里解决（notes/12 定理 1，复核者 s12-b4），不再写「没有决定」；
- 第 10 节开放问题：第 5 条（负形状）已解决，删去；第 3 条（负整数零点）补上报告里 k<=300 的计算机辅助证明与一般 k 的约化
  （notes/15，A28）；第 4 条（h_k 的变号位置）补上门槛 τ_i 的结果与线性渐近的猜想（A31、B14；还没有并入报告，所以写「the notes in the repository」）；
  第 1、2 条注明报告里排除了更多的类（A24–A27）；
- 「Data and code」：verify_all 现在是 414 条（不是 332）；「重算论文里每一个数」的脚本不覆盖第 10 节引用的报告结论，写明。
每处替换断言原文出现一次；按字节读写（paper/main.tex 是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-09_sync.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

REPS = [
    (r'the comparison of coordinates in Step~2 breaks down; we have not decided whether representations exist in this case.',
     r'the comparison of coordinates in Step~2 breaks down. The accompanying report settles this case by a different argument '
     r"(it shows $\C(x)\cap\C((v))=\C(v)$ using L\"uroth's theorem and the Riemann--Hurwitz formula, and then bounds the "
     r'absolute value of a product over a fibre): for $m\ge1$ and all integers $\alpha,\beta$, not both $0$, a representation '
     r'\eqref{eq:shapes} exists if and only if $\beta\ge0$ and $\alpha+\beta=1$.'),
    (r'\item \emph{Shorter formulas.} Find a meaningful class of formulas in which the double sum of Theorem~\ref{thm:explicit} is provably shortest.',
     r'\item \emph{Shorter formulas.} Find a meaningful class of formulas in which the double sum of Theorem~\ref{thm:explicit} is provably shortest. '
     r'The accompanying report rules out several further classes.'),
    (r'\item \emph{The triangle.} Find a single or short double sum for $N(k,q)$.',
     r'\item \emph{The triangle.} Find a single or short double sum for $N(k,q)$. The accompanying report rules out several natural single sums '
     r'and one family of double sums.'),
    (r'\item \emph{Other zeros.} Show that $U_k$ has no negative integer zeros other than $-1,\dots,-\lfloor(k+2)/3\rfloor$ (verified for $k\le70$).',
     r'\item \emph{Other zeros.} Show that $U_k$ has no negative integer zeros other than $-1,\dots,-\lfloor(k+2)/3\rfloor$. '
     r'The accompanying report proves this for $k\le300$ with computer assistance; for each $k$ it reduces the question to the finitely many '
     r'$j$ that divide $\operatorname{lcm}(1,\dots,k)$ and lie below an explicit bound of order $k^3$.'),
    (r'Describe where the sign changes occur.',
     r'Describe where the sign changes occur. For fixed $i$ the coefficient of $t^i$ in $h_k$ is positive for all large $k$; the notes in the repository '
     r'determine the least threshold $\tau_i$ from which on it stays positive for $i\le579$ (with computer assistance), prove '
     r'$\tau_i=O(i\log i)$, and give heuristic and numerical evidence that $\tau_i/i$ converges to an explicit constant $\alpha^*\approx9.6085$.'),
    ('\n' + r'\item \emph{Negative shapes.} Decide whether $U_k(m)$ has representations \eqref{eq:shapes} with $\alpha<0$ and $\alpha+\beta\ge2$ (Remark~\ref{rem:othershapes}).',
     ''),
    (r'The verification scripts (332 automated checks, mostly exact; the high-precision numerical ones are labelled), a script that recomputes '
     r'every number printed in this paper from the definitions, the Lean development and the notes are available at',
     r'The verification scripts (414 automated checks, mostly exact; the high-precision numerical ones are labelled), a script that recomputes '
     r'every number printed in this paper from the definitions (apart from the results of the accompanying report and notes quoted in Section~\ref{sec:open}, '
     r"which are checked by their own scripts), the Lean development and the notes are available at"),
]


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    p = os.path.join(ROOT, 'paper', 'main.tex')
    raw = open(p, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in REPS:
        c = s.count(old)
        assert c == 1, (c, old[:70])
        s = s.replace(old, new)
    open(p, 'wb').write(s.encode('utf-8'))
    print('paper/main.tex: %d edits' % len(REPS))


if __name__ == '__main__':
    main()
