# -*- coding: utf-8 -*-
"""论文按 2026-10-09 审读意见修订（用户先答「可以」，看过改动清单与预览稿后答「都按建议」）：
- 用户的决定：全部照改（含连续模式一句、transfer-matrix 出处、非 Cohen-Macaulay 一句与新摘要）；引理 2.5 的四项递推
  是用户自己推导的，删去 TODO、不加引用；\\thanks 去掉 "and is the corresponding author"，保留本科生身份；只做本地提交。
- 清理：删去源文件里的内部注释（文件头 7 行、署名处 2 行、引理 2.5 前的 TODO）、已不用的 \\todo 宏与 xcolor、\\date 草稿日期；
  \\thanks 去掉单作者多余的 "and is the corresponding author"；MSC 分出 primary / secondary；关键词补 chain polynomials。
- 摘要重写：压到 arXiv 的 1920 字符以内（原稿约 2035 字符、315 词）。
- 新增推论 cor:negzeros（u_k 在 -1..-ceil(k/3) 为零，下一个点非零；由引理 8.12 的 deg h_k 推出），
  第 10 节开放问题 (3) 改为引用它（原稿默认了这些零点而正文只证了 u_k(-1)=0），并把 U_k 改成 u_k。
- 新增注记 rem:chains：N(k,q) 是 Lambda_k 去掉最小最大元后 (q-1) 元链的个数，n_k 是链多项式，h_k 是序复形的
  h-多项式；布尔格对应 q!S(k,q) 与 Euler 多项式；k>=3 时序复形不是 Cohen-Macaulay。引言、第 2 节各加一句指向它。
- 引言补一句连续模式的说法（Kitaev 的书），相关工作的 transfer-matrix 补标准出处 Stanley EC1 4.7 节。
- 文献：新增 ADK24、AK23、BL26、Kitaev、StanleyCCA（DOI 都经 Crossref 核对）。
每处替换断言原文出现一次；按字节读写（paper/main.tex 是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-09_review.py [tex 路径]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

ABSTRACT_NEW = (
    r'Let $a_k(n)$ be the number of $n\times k$ binary arrays in which no row contains $001$ or $010$ and no column contains '
    r'$001$ or $011$ as three consecutive entries (OEIS A207123). Splitting the rows by parity gives '
    r'$a_k(n)=U_k(\lceil n/2\rceil)\,U_k(\lfloor n/2\rfloor)$, where $U_k(m)$ counts the sequences in $\{0,\dots,m\}^k$ in which '
    r'every three consecutive entries $(a,b,c)$ satisfy $b=c$ or $a\ge\max(b,c)$; equivalently, $U_k(m)$ counts the multichains '
    r'of length $m$ in a subposet $\Lambda_k$ of the Boolean lattice. A unique factorization into blocks gives a positive '
    r'double-sum formula for $U_k(m)$ in terms of Stirling and $r$-Stirling numbers, and for each $m$ the minimal order of a '
    r'linear recurrence in $k$ is exactly $3m+1$. The bivariate generating function is not D-finite, and every '
    r'polynomial-coefficient recurrence that holds on a quadrant is a left multiple of the defining four-term recurrence; in '
    r'particular $U$ is not Stirling-like in the sense of Kauers. We also determine all binomial shapes with nonnegative '
    r'parameters in which $U_k(m)$ is a single sum; the shape of the explicit formula is not among them. The numerators '
    r'$h_k(t)$ of $\sum_mU_k(m)t^m=h_k(t)/(1-t)^{k+1}$, analogues of the Eulerian polynomials, have only real and simple zeros; '
    r'equivalently, the chain polynomials of the posets $\Lambda_k$ are real-rooted, and the rows of the associated Stirling-type '
    r'triangle are log-concave. The near-diagonal entries $N(k,k-d)$ of this triangle are polynomials in $k$ exactly from '
    r'$k=2d+2$ on. The reduction, the exact orders, the explicit formula, the non-D-finiteness, the description of the quadrant '
    r'recurrences and the near-diagonal theorem are formalized in Lean~4 with Mathlib.'
)

NEGZEROS_AND_CHAINS = (
    '\n'
    r'\begin{corollary}\label{cor:negzeros}' '\n'
    r'Let $k\ge1$ and let $u_k$ be the polynomial of Corollary~\ref{cor:poly}. Then $u_k(-j)=0$ for $1\le j\le\lceil k/3\rceil$, '
    r'and $u_k(-\lceil k/3\rceil-1)=(-1)^k\lc(h_k)\ne0$.' '\n'
    r'\end{corollary}' '\n'
    '\n'
    r'\begin{proof}' '\n'
    r'Let $s=\deg h_k=\lfloor2k/3\rfloor$ (Lemma~\ref{lem:minusone}), so that $k-s=\lceil k/3\rceil$, and write '
    r'$h_k(t)=\sum_{i=0}^{s}c_it^i$. For $m\ge0$ we have $[t^m]\,t^i(1-t)^{-k-1}=\binom{m-i+k}{k}$, where for $0\le m<i$ both '
    r'sides vanish because $i\le k$. Hence $u_k(m)=\sum_{i=0}^{s}c_i\binom{m-i+k}{k}$ as polynomials in $m$, with polynomial '
    r'binomial coefficients. For an integer $j\ge1$, $\binom{k-i-j}{k}$ is the product of the $k$ consecutive integers '
    r'$1-i-j,\dots,k-i-j$ divided by $k!$; it vanishes if $i+j\le k$ and equals $(-1)^k$ if $i+j=k+1$. For $j\le k-s$ all terms '
    r'vanish, and for $j=k-s+1$ only the term with $i=s$ remains, which is $(-1)^kc_s$.' '\n'
    r'\end{proof}' '\n'
    '\n'
    r'\begin{remark}[Chains and Eulerian polynomials]\label{rem:chains}' '\n'
    r'Let $k\ge1$, let $\mathbf 0=(0,\dots,0)$ and $\mathbf 1=(1,\dots,1)$ be the least and the greatest element of $\Lambda_k$, '
    r'and put $\bar\Lambda_k=\Lambda_k\setminus\{\mathbf 0,\mathbf 1\}$. For $w\in\{1,\dots,q\}^k$ and $1\le r<q$ let '
    r'$y_r=([w_1>r],\dots,[w_k>r])$. By the proof of Proposition~\ref{prop:reduction}, applied to the heights $w_j-1$, the word '
    r'$w$ is good if and only if $y_1,\dots,y_{q-1}\in\Lambda_k$; moreover, $w$ uses every letter $1,\dots,q$ if and only if '
    r'$\mathbf 1>y_1>\dots>y_{q-1}>\mathbf 0$, and $w$ is recovered from the $y_r$ as $w_j=1+|\{r:(y_r)_j=1\}|$. Hence $N(k,q)$ '
    r'is the number of chains with $q-1$ elements in $\bar\Lambda_k$, so $n_k$ is the chain polynomial of $\bar\Lambda_k$, and '
    r'by~\eqref{eq:hN} the polynomial $h_k(t)=(1-t)^{k-1}n_k\bigl(t/(1-t)\bigr)$ is the $h$-polynomial of the order complex of '
    r'$\bar\Lambda_k$, a simplicial complex of dimension $k-2$. For the Boolean lattice $\{0,1\}^k$ in place of $\Lambda_k$ the '
    r'same constructions give $(m+1)^k$, the numbers $q!\stirling{k}{q}$ of ordered set partitions, and the Eulerian polynomials '
    r'$A_k(t)$, which satisfy $\sum_{m\ge0}(m+1)^kt^m=A_k(t)/(1-t)^{k+1}$ \cite[Section~1.4]{StanleyEC1}. This is the precise '
    r'form of the analogy stated in the introduction. In this language, Theorem~\ref{thm:realroots} says that the chain '
    r'polynomial of $\bar\Lambda_k$ is real-rooted, as the Eulerian polynomials are \cite{Branden}; real-rootedness of chain '
    r'polynomials has been studied for several other classes of posets \cite{AK23,ADK24,BL26}. By Corollary~\ref{cor:hk-signs}, '
    r'$h_k$ has a negative coefficient for $k\ge3$, so the order complex of $\bar\Lambda_k$ is not Cohen--Macaulay for $k\ge3$ '
    r'\cite[Chapter~II]{StanleyCCA}.' '\n'
    r'\end{remark}' '\n'
)

INTRO_CHAINS = (
    r'Let $\Lambda_k\subseteq\{0,1\}^k$ be the set of binary words of length $k$ that avoid $001$ and $010$, ordered '
    r'componentwise. Then $U_k(m)$ is the number of multichains of length $m$ in $\Lambda_k$ (Proposition~\ref{prop:multichain}), '
    r'$N(k,q)$ is the number of chains with $q-1$ elements in $\Lambda_k$ without its least and greatest element, and $h_k$ is the '
    r'$h$-polynomial of the corresponding order complex; for the Boolean lattice $\{0,1\}^k$ the same constructions give '
    r'$(m+1)^k$, the numbers $q!\stirling{k}{q}$ and the Eulerian polynomials (Remark~\ref{rem:chains}). Theorem~\ref{thmF} is '
    r'thus a real-rootedness result for chain polynomials, a subject studied for several classes of posets in '
    r'\cite{AK23,ADK24,BL26}.' '\n'
    '\n'
)

REPS = [
    # --- 内部注释、不再使用的 \todo 宏（连同只为它加载的 xcolor）与草稿日期
    (r'\usepackage{xcolor}' '\n', ''),
    (r'\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}' '\n', ''),
    (r"% Sole author, who is both the first and the corresponding author (author's instruction, 7 October 2026)." '\n'
     r'% Correspondence address given by the author on 8 October 2026.' '\n', ''),
    (r'\date{Draft of 8 October 2026}' '\n\n', ''),
    ('% TODO(author): this recurrence was given in the problem statement we started from; decide on attribution.\n', ''),
    # --- \thanks、MSC、关键词
    (r'\thanks{The author is an undergraduate student in the College of Arts and Sciences at Boston University and is the corresponding author.}',
     r'\thanks{The author is an undergraduate student in the College of Arts and Sciences at Boston University.}'),
    (r'\subjclass[2020]{05A15; 05A20; 11B73; 11D61; 26C10; 33F10; 68V20}',
     r'\subjclass[2020]{Primary 05A15; Secondary 05A20, 06A07, 11B73, 26C10, 33F10, 68V20}'),
    (r'real-rooted polynomials, interlacing, formal verification}',
     r'real-rooted polynomials, chain polynomials, interlacing, formal verification}'),
    # --- 引言：连续模式、类比的指针、定理 F 之后的一段
    (r'a\ge\max(b,c).' '\n' r'\]' '\n' r'The column half of this argument',
     r'a\ge\max(b,c).' '\n' r'\]' '\n'
     r'Equivalently, $U_k(m)$ counts the words of length $k$ over the ordered alphabet $\{0,\dots,m\}$ that avoid the six '
     r'consecutive patterns $112$, $121$, $123$, $132$, $213$ and $231$ (for patterns in words see \cite{Kitaev}). '
     r'The column half of this argument'),
    (r'plays for $U$ the role that the numbers $q!\stirling{k}{q}$ of surjections play for powers:',
     r'plays for $U$ the role that the numbers $q!\stirling{k}{q}$ of surjections play for powers (Remark~\ref{rem:chains} makes this precise):'),
    ('\n' r'Consecutive polynomials $h_k$ do not have interlacing zeros',
     '\n' + INTRO_CHAINS + r'Consecutive polynomials $h_k$ do not have interlacing zeros'),
    (r'exist by a transfer-matrix argument; see Theorem~2 of Dougherty-Bliss, Koutschan, Ter-Saakov and Zeilberger \cite{DBKTZ}.',
     r'exist by the transfer-matrix method \cite[Section~4.7]{StanleyEC1}; see also Theorem~2 of Dougherty-Bliss, Koutschan, '
     r'Ter-Saakov and Zeilberger \cite{DBKTZ}.'),
    # --- 第 2 节：N 的定义处指向注记
    (r'Table~\ref{tab:N} shows the first rows.',
     r'Table~\ref{tab:N} shows the first rows. Remark~\ref{rem:chains} interprets $N(k,q)$ as a number of chains in $\Lambda_k$.'),
    # --- 第 8 节末：新推论与新注记
    (r"as in Harper's argument \cite{Harper}." '\n' r'\end{proof}' '\n',
     r"as in Harper's argument \cite{Harper}." '\n' r'\end{proof}' '\n' + NEGZEROS_AND_CHAINS),
    # --- 第 10 节开放问题 (3)
    (r'Show that $U_k$ has no negative integer zeros other than $-1,\dots,-\lfloor(k+2)/3\rfloor$.',
     r'By Corollary~\ref{cor:negzeros}, $u_k$ vanishes at $-1,\dots,-\lceil k/3\rceil$; show that it has no other negative integer zeros.'),
    # --- 文献
    (r'\begin{thebibliography}{99}' '\n\n' r'\bibitem{Branden}',
     r'\begin{thebibliography}{99}' '\n\n'
     r'\bibitem{ADK24}' '\n'
     r'C.~A. Athanasiadis, T.~Douvropoulos, K.~Kalampogia-Evangelinou, Two classes of posets with real-rooted chain polynomials, '
     r'\emph{Electron. J. Combin.} \textbf{31}(4) (2024), \#P4.16, \url{https://doi.org/10.37236/12218}.' '\n\n'
     r'\bibitem{AK23}' '\n'
     r'C.~A. Athanasiadis, K.~Kalampogia-Evangelinou, Chain enumeration, partition lattices and polynomials with only real roots, '
     r'\emph{Combin. Theory} \textbf{3}(1) (2023), \url{https://doi.org/10.5070/C63160425}.' '\n\n'
     r'\bibitem{Branden}'),
    (r'\bibitem{Broder}',
     r'\bibitem{BL26}' '\n'
     r'P.~Br\"and\'en, L.~Saud Maia Leite, Totally nonnegative matrices, chain enumeration and zeros of polynomials, '
     r'\emph{Adv. Math.} \textbf{487} (2026), Paper No.~110760, \url{https://doi.org/10.1016/j.aim.2025.110760}.' '\n\n'
     r'\bibitem{Broder}'),
    (r'\bibitem{KMV}',
     r'\bibitem{Kitaev}' '\n'
     r'S.~Kitaev, \emph{Patterns in Permutations and Words}, Monographs in Theoretical Computer Science, Springer, Heidelberg, '
     r'2011, \url{https://doi.org/10.1007/978-3-642-17333-2}.' '\n\n'
     r'\bibitem{KMV}'),
    (r'\bibitem{StanleyEC1}',
     r'\bibitem{StanleyCCA}' '\n'
     r'R.~P. Stanley, \emph{Combinatorics and Commutative Algebra}, 2nd ed., Progress in Mathematics 41, Birkh\"auser, Boston, '
     r'MA, 1996, \url{https://doi.org/10.1007/b139094}.' '\n\n'
     r'\bibitem{StanleyEC1}'),
]


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    p = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'paper', 'main.tex')
    raw = open(p, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    # 文件头的 7 行注释（\documentclass 之前）
    head, sep, rest = s.partition(r'\documentclass')
    head_lines = head.split('\n')[:-1]
    assert len(head_lines) == 7 and all(ln.startswith('%') for ln in head_lines), head_lines
    s = sep + rest
    # 摘要整段替换
    a0 = s.index(r'\begin{abstract}') + len(r'\begin{abstract}')
    a1 = s.index(r'\end{abstract}')
    assert s.count(r'\begin{abstract}') == 1
    s = s[:a0] + '\n' + ABSTRACT_NEW + '\n' + s[a1:]
    for old, new in REPS:
        c = s.count(old)
        assert c == 1, (c, old[:70])
        s = s.replace(old, new)
    assert 'TODO' not in s and r'\date{' not in s
    open(p, 'wb').write(s.encode('utf-8'))
    print('%s: header comments removed, abstract replaced, %d edits' % (p, len(REPS)))


if __name__ == '__main__':
    main()
