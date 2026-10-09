# -*- coding: utf-8 -*-
r"""论文第四轮修订（2026-10-10，用户：「按照你的想法来」，针对 GPT6.1Sol 的四条意见）。
- 新增附录 B「The recurrences of the triangle」：给出 Rel(N)=O·L_N 与 N 的维数公式（总次数与分次数两种）的完整人工证明，
  照 Lean 的路线（OreRelN.lean 的 RelN_eq，OreDim.lean 的 finrank_relN_tot / finrank_relN_gr）：二项式变换 P 把问题搬到 U，
  恒等式 ∇PY=YP、Pm=m∇P、L̃1·P=∇P·L_N（引理 B.2），两条搬运引理（B.3），边界引理（B.4），Rel(P N) 的刻画（B.5），
  左因子 1+Y 的饱和引理（B.6）。Lean 里还证了左因子 Y 的饱和引理，但主定理用不到，论文不写。
  记号避开正文已占用的字母：二项式变换写 \mathcal P（P_m 已占用），后向差分写 \nabla（Δ 在正文别处是公分母），
  单点示性函数写 \mathbf 1_{(k,m)}（e_0 在第 7 节已占用），饱和引理里的算子写 S（Λ 是偏序集）。
  引理 B.2 的恒等式另由 code/main_extra/check_appendix_relN.py 在随机整数组上精确核对（14 PASS）。
- 第 5 节 Rel(N) 一段：去掉「We omit the proof」，改为指向定理 B.1 与附录 B，并说明为什么对 U 的化约不能照搬
  （L_N 里 Y^2 的系数 -(q-1)X^3 不是单位）；原文「needs an additional saturation lemma for the left factors Y and 1+Y」
  与实际证明不符（主定理只用 1+Y 的饱和引理），改正。
- 第 9 节表 5：定理 5.4 一行拆出 N 的部分，新增定理 B.1 一行（加上已形式化的 RelN_iff_mem_span、finrank_relN_gr）。
- 引言重排主次：「Main results」只留三类主结果——固定 m 的结构（定理 A 精确阶、定理 B 显式公式）、全部递推（原定理 D，现为 C）、
  h_k 实根（原定理 F，现为 D）；N 三角那段移到定理 A 之前；新增小节「Further results」放渐近、列的最小阶与 OEIS、
  原定理 C（求和形状，现为 E）与原定理 E（近对角线，现为 F）。字母随出现顺序变化，引言定理的标签改成按内容命名
  （thmA→intro:order，thmB→intro:explicit，thmC→intro:shapes，thmD→intro:ideal，thmE→intro:neardiag，thmF→intro:roots），
  定理的陈述逐字不变（脚本断言重排前后各块拼起来与原文相同）。定理 C 之后加一句 N 的对应结论（指向定理 B.1）。
- 相关工作末尾加「What is new」一段：工具是标准的（部分分式与极点阶、Kauers 的论证框架、留数范数与 Skolem 方法、交错），
  新的是这些数组上的结论与形式化；超出直接套用的三步是块分解、把全部递推的刻画搬到三角 N（附录 B）、四条交错关系的联合归纳。
- 摘要按三项主结果重写（arXiv 上限 1920 字符，脚本断言不超）；「Organization」补两个附录。
每处替换断言原文出现一次；按字节读写（paper/main.tex 是 LF）；源文件只含 ASCII。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_relN.py [tex 路径]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

# ---------------------------------------------------------------- abstract
OLD_ABS_START = r'\begin{abstract}' '\n'
OLD_ABS_END = '\n' r'\end{abstract}'
NEW_ABS = (
    r'Let $a_k(n)$ be the number of $n\times k$ binary arrays in which no row contains $001$ or $010$ and no column '
    r'contains $001$ or $011$ as three consecutive entries (OEIS A207123). Splitting the rows by parity gives '
    r'$a_k(n)=U_k(\lceil n/2\rceil)\,U_k(\lfloor n/2\rfloor)$, where $U_k(m)$ counts the sequences in $\{0,\dots,m\}^k$ in '
    r'which every three consecutive entries $(a,b,c)$ satisfy $b=c$ or $a\ge\max(b,c)$; equivalently, $U_k(m)$ counts the '
    r'multichains of length $m$ in a subposet $\Lambda_k$ of the Boolean lattice. We prove three main results. First, for '
    r'each $m$ the minimal order of a linear recurrence in $k$ is exactly $3m+1$, and a unique factorization into blocks '
    r'gives a positive double-sum formula for $U_k(m)$ in terms of Stirling and $r$-Stirling numbers. Second, the bivariate '
    r'generating function is not D-finite, and every polynomial-coefficient recurrence that holds on a quadrant is a left '
    r'multiple of the defining four-term recurrence; the same holds for an associated Stirling-type triangle $N(k,q)$, and '
    r'$U$ is not Stirling-like in the sense of Kauers. Third, the numerators $h_k(t)$ of '
    r'$\sum_mU_k(m)t^m=h_k(t)/(1-t)^{k+1}$, analogues of the Eulerian polynomials, have only real and simple zeros; '
    r'equivalently, the chain polynomials of the posets $\Lambda_k$ are real-rooted, and the rows of $N$ are log-concave. '
    r'We also determine all binomial shapes with nonnegative parameters in which $U_k(m)$ is a single sum, and show that '
    r'the near-diagonal entries $N(k,k-d)$ are polynomials in $k$ exactly from $k=2d+2$ on. The reduction, the exact '
    r'orders, the explicit formula, the non-D-finiteness, the description of the quadrant recurrences and the near-diagonal '
    r'theorem are formalized in Lean~4 with Mathlib.'
)

# ---------------------------------------------------------------- introduction: pieces of the old "Main results"
MAIN_START = r'\subsection{Main results}' '\n'
MAIN_END = r'\subsection{Related work}' '\n'
PIECES = [  # (name, first characters of the piece); each piece runs up to the start of the next one
    ('framing', r'Let $\Lambda_k\subseteq\{0,1\}^k$ be the set of binary words'),
    ('notation', r'Throughout, $b_i(x)=1-x-ix^3$,'),
    ('thmA', r'\begin{introthm}[Exact recurrence order;'),
    ('asym', r'Theorem~\ref{thm:asym} gives the first two terms of the asymptotics:'),
    ('thmB', r'\begin{introthm}[Positive explicit formula;'),
    ('thmC', r'\begin{introthm}[Obstructions to specific summation formulas;'),
    ('thmD', r'\begin{introthm}[Non-D-finiteness and all quadrant recurrences;'),
    ('npara', r'The triangle $N(k,q)$, the number of good words of length $k$'),
    ('thmE', r'\begin{introthm}[Near-diagonal;'),
    ('thmF', r'\begin{introthm}[Real roots;'),
    ('chains', r'Since $N(k,q)$ is the number of chains with $q-1$ elements'),
    ('interlace', r'Consecutive polynomials $h_k$ do not have interlacing zeros'),
]

FRAMING_OLD = (r'the annihilator of the Stirling numbers $\stirling{n}{k}$ is generated by their triangular recurrence '
               r'\cite[Example~5]{Kauers07}, the near-diagonals $\stirling{k}{k-d}$ are polynomials in $k$ \cite{GesselStanley}, '
               r'and the Eulerian polynomials are real-rooted \cite{Branden}; compare Theorems~\ref{thmD}(3), \ref{thmE} '
               r'and~\ref{thmF}.')
FRAMING_NEW = (r'the annihilator of the Stirling numbers $\stirling{n}{k}$ is generated by their triangular recurrence '
               r'\cite[Example~5]{Kauers07}, the Eulerian polynomials are real-rooted \cite{Branden}, and the near-diagonals '
               r'$\stirling{k}{k-d}$ are polynomials in $k$ \cite{GesselStanley}; compare Theorems~\ref{thmD}(3), '
               r'\ref{thmF} and~\ref{thmE}.')

HIERARCHY = (
    r'Our main results concern the structure of $U_k(m)$ for fixed $m$ (Theorems~\ref{thmA} and~\ref{thmB}), all '
    r'recurrences satisfied by $U$ and by $N$ (Theorem~\ref{thmD}), and the zeros of the polynomials $h_k$ '
    r'(Theorem~\ref{thmF}); Section~\ref{sec:further} lists further results.' '\n\n'
)

NSENT = (
    r'For the triangle, parts (1) and (2) hold as well, and the operators in $\C[k,q]\langle X,Y\rangle$, where $Y$ is the '
    r'backward shift in $q$, that annihilate $N$ on some quadrant form the left ideal generated by '
    r'$L_N=1-X-XY-(q-1)X^3(1+Y)^2$; the dimension in~(3) becomes $(A-2)(B-1)D(D+1)/2$ for $A\ge3$, $B\ge2$, $D\ge1$ '
    r'(Section~\ref{sec:nonD} and Theorem~\ref{thm:relN}).' '\n\n'
)

FURTHER_HEAD = r'\subsection{Further results}\label{sec:further}' '\n'
COLUMNS = (
    r'By Corollary~\ref{cor:columns}, the minimal order of a linear recurrence with constant coefficients for the $k$-th '
    r'column of A207123 is $4k$; in particular, the empirical recurrences recorded in the OEIS for the columns '
    r'$k=3,\dots,7$ hold for all $n$ (Remark~\ref{rem:oeis}).' '\n\n'
)

LABELS = [('thmA', 'intro:order'), ('thmB', 'intro:explicit'), ('thmC', 'intro:shapes'), ('thmD', 'intro:ideal'),
          ('thmE', 'intro:neardiag'), ('thmF', 'intro:roots')]

# ---------------------------------------------------------------- related work: what is new
NEW_ANCHOR = r'We are not aware of previous work on the table $U_k(m)$ itself.' '\n'
WHATSNEW = (
    '\n' r'\emph{What is new.} The tools are standard: partial fractions and pole orders (Sections~\ref{sec:gf} '
    r"and~\ref{sec:nonD}), the outline of Kauers' argument for the Stirling numbers (Section~\ref{sec:nonD}), residues, "
    r"norms and Skolem's $p$-adic method (Section~\ref{sec:short}), and interlacing (Section~\ref{sec:realroots}). The "
    r'contributions are the results for these arrays and their formalization. Beyond direct applications of these tools, '
    r'the proofs need the block factorization of Section~\ref{sec:blocks}, a transfer of the description of all '
    r'recurrences from $U$ to the triangle $N$, whose generator does not allow the reduction used for $U$ '
    r'(Appendix~\ref{app:relN}), and an induction over four interlacing relations at once (Section~\ref{sec:realroots}).' '\n'
)

# ---------------------------------------------------------------- organization
ORG_OLD = (r'Section~\ref{sec:lean} describes the formalization, and Section~\ref{sec:open} lists open problems.' '\n')
ORG_NEW = (r'Section~\ref{sec:lean} describes the formalization, and Section~\ref{sec:open} lists open problems. '
           r'Appendix~\ref{app:lean} transcribes the Lean definitions, and Appendix~\ref{app:relN} proves the description '
           r'of the recurrences of $N$.' '\n')

# ---------------------------------------------------------------- section 5: the paragraph on Rel(N)
RELN_OLD = (
    r'For the triangle we only state the analogous result: $\Rel(N)=\cO\cdot L_N$ with $L_N=1-X-XY-(q-1)X^3(1+Y)^2$, '
    r'where $Y$ shifts $q$, and the dimension in a box is $(A-2)(B-1)D(D+1)/2$ for $A\ge3$, $B\ge2$, $D\ge1$. We omit '
    r'the proof. It transports the problem to $U$ through the binomial transform $V(k,m)=\sum_q\binom{m}{q}N(k,q)$, which '
    r'satisfies $V(k,m+1)=U_k(m)$ by \eqref{eq:Nbasis}, and needs an additional saturation lemma for the left factors $Y$ '
    r'and $1+Y$; a complete proof is part of the Lean development (\lean{RelN\_eq}, \lean{finrank\_relN\_tot}; see '
    r'Section~\ref{sec:lean}).'
)
RELN_NEW = (
    r'For the triangle the analogous result holds: $\Rel(N)=\cO\cdot L_N$ with $L_N=1-X-XY-(q-1)X^3(1+Y)^2$, where $Y$ '
    r'shifts $q$, and the dimension in a box is $(A-2)(B-1)D(D+1)/2$ for $A\ge3$, $B\ge2$, $D\ge1$ '
    r'(Theorem~\ref{thm:relN}). The reduction used for $U$ does not carry over, because the coefficient $-(q-1)X^3$ of '
    r'$Y^2$ in $L_N$ is not a unit. The proof in Appendix~\ref{app:relN} instead transports the problem to $U$ through '
    r'the binomial transform, $\sum_q\binom{m}{q}N(k,q)=U_k(m-1)$ for $m\ge1$ by \eqref{eq:Nbasis}, and uses a saturation '
    r'lemma for the left factor $1+Y$.'
)

# ---------------------------------------------------------------- section 9: table of formalized results
TAB_OLD = (r'Theorem~\ref{thm:ideal} & \lean{RelU\_eq}, \lean{RelU\_iff\_mem\_span}, \lean{finrank\_relU\_tot}, '
           r'\lean{finrank\_relU\_gr}; for $N$: \lean{RelN\_eq}, \lean{finrank\_relN\_tot}\\' '\n')
TAB_NEW = (r'Theorem~\ref{thm:ideal} & \lean{RelU\_eq}, \lean{RelU\_iff\_mem\_span}, \lean{finrank\_relU\_tot}, '
           r'\lean{finrank\_relU\_gr}\\' '\n'
           r'Theorem~\ref{thm:relN} & \lean{RelN\_eq}, \lean{RelN\_iff\_mem\_span}, \lean{finrank\_relN\_tot}, '
           r'\lean{finrank\_relN\_gr}\\' '\n')

# ---------------------------------------------------------------- appendix B
APP_ANCHOR = ('% =====================================================================\n'
              r'\section*{Statement on the use of AI tools}')
APPENDIX_B = r'''% =====================================================================
\section{The recurrences of the triangle}\label{app:relN}

We prove the description of $\Rel(N)$ stated after Corollary~\ref{cor:saturated}. We keep the notation of Section~\ref{sec:nonD}, write $Y=E^{-1}$, and regard the triangle as the element $N\in\mathcal A$, $(k,q)\mapsto N(k,q)$, with $N(k,q)=0$ for $q>k$. Since all functions below live in the same space $\mathcal A$, the operator of multiplication by the second coordinate is always written $m$; thus
\[
  L_N=1-X-XY-(m-1)X^3(1+Y)^2
\]
is the operator of Section~\ref{sec:nonD} with $q$ renamed $m$. As for $U$, $\Rel(N)$ is the set of $R\in\cO$ such that $RN$ vanishes on some quadrant, and for $A,B,D\ge0$ we let $V_N(A,B,D)$ be the space of $R\in\Rel(N)$ with $\Supp(R)\subseteq[0,A]\times[0,B]$ and all coefficients of total degree at most $D$.

\begin{theorem}\label{thm:relN}\leavevmode
\begin{enumerate}
\item $\Rel(N)=\cO\cdot L_N$.
\item For $A,B,D\ge0$,
\[
  \dim V_N(A,B,D)=\begin{cases}(A-2)(B-1)\,\dfrac{D(D+1)}{2}&\text{if }A\ge3,\ B\ge2,\ D\ge1,\\[1ex] 0&\text{otherwise.}\end{cases}
\]
If instead the degrees in $k$ and $m$ are bounded by $D_k$ and $D_m$, the dimension is $(A-2)(B-1)(D_k+1)D_m$ for $A\ge3$, $B\ge2$, $D_m\ge1$, and $0$ otherwise.
\end{enumerate}
\end{theorem}

The inclusion $\cO L_N\subseteq\Rel(N)$ follows as in the proof of Theorem~\ref{thm:ideal}(1), because $(L_NN)(k,m)=0$ for $k\ge3$, $m\ge1$ by Proposition~\ref{prop:Ntri}. For the converse we transport the problem to $U$. Let
\[
  (\mathcal Pf)(k,m)=\sum_{q=0}^{m}\binom{m}{q}f(k,q),\qquad \nabla=1-Y,
\]
and for $(k_1,m_1)\in\NN^2$ let $\mathbf 1_{(k_1,m_1)}\in\mathcal A$ be the indicator function of the point $(k_1,m_1)$. The maps $\mathcal P$, $\nabla$ and $1+Y$ are injective, since for fixed $k$ they are triangular in $m$ with diagonal entries $1$; $\nabla$ and $1+Y$ lie in $\cO$, while $\mathcal P$ does not. By Proposition~\ref{prop:Nbasis}, $(\mathcal PN)(k,m)=U_k(m-1)$ for $m\ge1$, and $(\mathcal PN)(k,0)=N(k,0)$ is $1$ for $k=0$ and $0$ otherwise; that is,
\begin{equation}\label{eq:PN}
  \mathcal PN=YU+\mathbf 1_{(0,0)}.
\end{equation}

\begin{lemma}\label{lem:Pid}
The following identities of linear maps of $\mathcal A$ hold for all $a\ge0$; here $p\in\C[k,m]$ and $p_\pm(k,m)=p(k,m\pm1)$.
\begin{enumerate}
\item $\mathcal P$ and $\nabla$ commute with $X$ and with $k$, and $\nabla$ commutes with $Y$.
\item $\nabla\mathcal PY=Y\mathcal P$; hence $\nabla\mathcal P(1+Y)=\mathcal P$ and $\nabla^a\mathcal P(1+Y)^a=\mathcal P$.
\item $\mathcal Pm=m\nabla\mathcal P$.
\item $\nabla p=(p-p_-)+p_-\nabla$. In particular $\nabla m=1+(m-1)\nabla$, and $\nabla^am\nabla=\bigl((m-a)\nabla+a\bigr)\nabla^a$.
\item $m\nabla^a\mathcal P=\nabla^a\mathcal P\bigl(m(1+Y)-aY\bigr)$.
\item $YL_1=\widetilde L_1Y$ and $\widetilde L_1\mathcal P=\nabla\mathcal PL_N$, where $\widetilde L_1=1-Y-X-(m-1)X^3$.
\end{enumerate}
\end{lemma}

\begin{proof}
(1) $\mathcal P$ and $Y$ act on the second coordinate only, with coefficients that do not depend on $k$, and $\nabla=1-Y$.

(2) We have $(\mathcal PYf)(k,m)=\sum_{q\ge0}\binom{m}{q+1}f(k,q)$. For $m\ge1$, Pascal's rule gives
\[
  (\nabla\mathcal PYf)(k,m)=\sum_{q\ge0}\Bigl[\binom{m}{q+1}-\binom{m-1}{q+1}\Bigr]f(k,q)=\sum_{q\ge0}\binom{m-1}{q}f(k,q)=(Y\mathcal Pf)(k,m),
\]
and for $m=0$ both sides vanish. Then $\nabla\mathcal P(1+Y)=\nabla\mathcal P+Y\mathcal P=\mathcal P$, and $\nabla^{a+1}\mathcal P(1+Y)^{a+1}=\nabla^a\bigl(\nabla\mathcal P(1+Y)\bigr)(1+Y)^a=\nabla^a\mathcal P(1+Y)^a$.

(3) The summation variable $q$ in $\mathcal P$ is the second coordinate of $f$. Since $q\binom{m}{q}=m\binom{m-1}{q-1}$, we get for $m\ge1$
\[
  (\mathcal P(mf))(k,m)=\sum_qq\binom{m}{q}f(k,q)=m\sum_q\Bigl[\binom{m}{q}-\binom{m-1}{q}\Bigr]f(k,q)=m\,(\nabla\mathcal Pf)(k,m),
\]
and for $m=0$ both sides vanish.

(4) Since $f(k,-1)=0$,
\begin{align*}
  (\nabla(pf))(k,m)&=p(k,m)f(k,m)-p(k,m-1)f(k,m-1)\\
  &=(p-p_-)(k,m)\,f(k,m)+p_-(k,m)\,(\nabla f)(k,m).
\end{align*}
For $p=m-a$ this gives $\nabla(m-a)=1+(m-a-1)\nabla$, and the last identity follows by induction on $a$: $\nabla^{a+1}m\nabla=\nabla\bigl((m-a)\nabla+a\bigr)\nabla^a=\bigl((m-a-1)\nabla+a+1\bigr)\nabla^{a+1}$.

(5) Induction on $a$. For $a=0$, (2) and (3) give $m\mathcal P=m\nabla\mathcal P(1+Y)=\mathcal Pm(1+Y)$. By (4) with $p=m+1$, $m\nabla=\nabla(m+1)-1$; using the case $a$ and $\nabla^a\mathcal P=\nabla^{a+1}\mathcal P(1+Y)$,
\[
  m\nabla^{a+1}\mathcal P=\nabla m\nabla^a\mathcal P+\nabla^{a+1}\mathcal P-\nabla^a\mathcal P=\nabla^{a+1}\mathcal P\bigl(m(1+Y)-aY+1-(1+Y)\bigr),
\]
which is the case $a+1$.

(6) $Ym=(m-1)Y$ gives $YL_1=Y-Y^2-XY-(m-1)X^3Y=\widetilde L_1Y$. By (3) and (4), $\nabla\mathcal P(m-1)=\nabla m\nabla\mathcal P-\nabla\mathcal P=(m-1)\nabla^2\mathcal P$, so by (1) and (2)
\[
  \nabla\mathcal P\,(m-1)X^3(1+Y)^2=(m-1)X^3\,\nabla^2\mathcal P(1+Y)^2=(m-1)X^3\mathcal P .
\]
Together with $\nabla\mathcal PXY=XY\mathcal P$ this gives $\nabla\mathcal PL_N=\nabla\mathcal P-X\nabla\mathcal P-XY\mathcal P-(m-1)X^3\mathcal P=\widetilde L_1\mathcal P$.
\end{proof}

\begin{lemma}\label{lem:transport}
Let $T\in\cO$.
\begin{enumerate}
\item For every $c\ge0$ there are $j\ge0$ and $M\in\cO$ such that $\nabla^j\mathcal PT=M\nabla^c\mathcal P$.
\item For every $a\ge0$ there are $c\ge0$ and $M\in\cO$ such that $T\nabla^a\mathcal P=\nabla^c\mathcal PM$.
\end{enumerate}
\end{lemma}

\begin{proof}
(1) Let $\mathcal T$ be the set of $T\in\cO$ for which the statement holds for every $c$. By Lemma~\ref{lem:Pid}, $\mathcal T$ contains the constants, $k$ and $X$ (take $j=c$ and $M=T$), $m$ (take $j=c$ and $M=(m-c)\nabla+c$, since $\nabla^c\mathcal Pm=\nabla^cm\nabla\mathcal P$), and $Y$ (take $j=c+1$ and $M=Y$, since $\nabla^{c+1}\mathcal PY=\nabla^cY\mathcal P=Y\nabla^c\mathcal P$). If $T_1,T_2\in\mathcal T$, then $T_1+T_2\in\mathcal T$: from $\nabla^{j_i}\mathcal PT_i=M_i\nabla^c\mathcal P$ we get $\nabla^{j_1+j_2}\mathcal P(T_1+T_2)=(\nabla^{j_2}M_1+\nabla^{j_1}M_2)\nabla^c\mathcal P$. Also $T_1T_2\in\mathcal T$: choose $j_2,M_2$ with $\nabla^{j_2}\mathcal PT_2=M_2\nabla^c\mathcal P$ and then $j_1,M_1$ with $\nabla^{j_1}\mathcal PT_1=M_1\nabla^{j_2}\mathcal P$; then $\nabla^{j_1}\mathcal PT_1T_2=M_1M_2\nabla^c\mathcal P$. Hence $\mathcal T=\cO$.

(2) In the same way. For the constants, $k$ and $X$ take $c=a$ and $M=T$; for $m$ take $c=a$ and $M=m(1+Y)-aY$ (Lemma~\ref{lem:Pid}(5)); for $Y$ take $c=a+1$ and $M=Y$, since $Y\nabla^a\mathcal P=\nabla^aY\mathcal P=\nabla^{a+1}\mathcal PY$. If $T_i\nabla^a\mathcal P=\nabla^{c_i}\mathcal PM_i$ for $i=1,2$, then by Lemma~\ref{lem:Pid}(2)
\[
  (T_1+T_2)\nabla^a\mathcal P=\nabla^{c_1+c_2}\mathcal P\bigl((1+Y)^{c_2}M_1+(1+Y)^{c_1}M_2\bigr),
\]
and if $T_2\nabla^a\mathcal P=\nabla^{c_2}\mathcal PM_2$ and $T_1\nabla^{c_2}\mathcal P=\nabla^{c_1}\mathcal PM_1$, then $T_1T_2\nabla^a\mathcal P=\nabla^{c_1}\mathcal PM_1M_2$.
\end{proof}

\begin{lemma}\label{lem:boundary}
Let $g\in\mathcal A$ and $n,k_0\ge0$. If $g(k,q)=0$ for all $k\ge k_0$, $q\ge n$, then $(\nabla^n\mathcal Pg)(k,m)=0$ for all $k\ge k_0$, $m\ge n$.
\end{lemma}

\begin{proof}
Fix $k\ge k_0$. Then $(\mathcal Pg)(k,m)=\varphi(m)$ for all $m\ge0$, where $\varphi(x)=\sum_{q<n}g(k,q)\binom{x}{q}$ is a polynomial of degree less than $n$; here $\binom{x}{q}=x(x-1)\cdots(x-q+1)/q!$ vanishes at $x=0,\dots,q-1$. For $m\ge n$ no negative index occurs, so $(\nabla^n\mathcal Pg)(k,m)=\sum_{i=0}^{n}(-1)^i\binom{n}{i}\varphi(m-i)$ is the $n$-th backward difference of $\varphi$ at $m$, which vanishes because $\deg\varphi<n$.
\end{proof}

\begin{lemma}\label{lem:relV}
Let $M\in\cO$. If $M(\mathcal PN)$ vanishes on some quadrant, then $M\in\cO\widetilde L_1$.
\end{lemma}

\begin{proof}
If $\Supp(M)\subseteq[0,A]\times[0,B]$, then $(M\mathbf 1_{(0,0)})(k,m)=0$ unless $k\le A$ and $m\le B$. Hence, by \eqref{eq:PN}, $(MY)U=M(\mathcal PN)-M\mathbf 1_{(0,0)}$ vanishes on a quadrant, so $MY\in\Rel(U)=\cO L_1$ by Theorem~\ref{thm:ideal}. Write $MY=QL_1$, and split the normal form of $Q$ as $Q=Q'Y+R$, where $R=\sum_ar_a(k,m)X^a$ collects the monomials free of $Y$. By Lemma~\ref{lem:Pid}(6), $MY=Q'\widetilde L_1Y+RL_1$, that is,
\[
  (M-Q'\widetilde L_1)Y=RL_1 .
\]
Right multiplication by $Y$ maps a normal form $\sum p_{ab}X^aY^b$ to $\sum p_{ab}X^aY^{b+1}$, so the left-hand side has no monomial free of $Y$. The monomials of $RL_1=R(1-X-mX^3)-RY$ free of $Y$ form $\sum_ar_a\bigl(X^a-X^{a+1}-mX^{a+3}\bigr)$; if $R\ne0$ and $a_0$ is the least $a$ with $r_a\ne0$, their coefficient of $X^{a_0}$ is $r_{a_0}\ne0$. Hence $R=0$, so $(M-Q'\widetilde L_1)Y=0$, and $M=Q'\widetilde L_1$ because right multiplication by $Y$ is injective.
\end{proof}

\begin{lemma}\label{lem:saturation}
Let $L\in\cO$. If $(1+Y)L\in\cO L_N$, then $L\in\cO L_N$.
\end{lemma}

\begin{proof}
Every $S\in\cO$ can be written as $S=(1+Y)S_1+R$ with $S_1\in\cO$ and $R$ free of $Y$: since $Yp_+=pY$ for $p\in\C[k,m]$,
\[
  pX^aY^b=(1+Y)\,p_+X^aY^{b-1}-p_+X^aY^{b-1}\qquad(b\ge1),
\]
and induction on the degree in $Y$ gives the claim. Write $(1+Y)L=SL_N$ and decompose $S$ in this way; then
\[
  RL_N=(1+Y)T,\qquad T=L-S_1L_N\in\cO .
\]
Suppose that $R=\sum_ar_a(k,m)X^a\ne0$, let $a_0$ be the least $a$ with $r_a\ne0$, let $k_1,m_1\ge0$, and put $f=\mathbf 1_{(k_1,m_1)}$. The generators of $\cO$ map functions with finite support to functions with finite support, so $g=Tf$ has finite support, and for every $k$
\[
  \sum_{m\ge0}(-1)^m\bigl((1+Y)g\bigr)(k,m)=\sum_{m\ge0}(-1)^mg(k,m)+\sum_{m\ge1}(-1)^mg(k,m-1)=0 .
\]
On the other hand, $Xf$, $XYf$ and $X^3(1+Y)^2f$ vanish at all points with $k\le k_1$, so $(L_Nf)(k,m)=f(k,m)$ for $k\le k_1$. Since $(RL_Nf)(k,m)=\sum_ar_a(k,m)(L_Nf)(k-a,m)$ and $k_1+a_0-a<k_1$ for $a>a_0$, we get $(RL_Nf)(k_1+a_0,m)=r_{a_0}(k_1+a_0,m_1)$ for $m=m_1$ and $(RL_Nf)(k_1+a_0,m)=0$ for $m\ne m_1$. Comparing the alternating sums over $m$ at $k=k_1+a_0$ gives $r_{a_0}(k_1+a_0,m_1)=0$. As $k_1,m_1\ge0$ are arbitrary, the polynomial $r_{a_0}$ vanishes on $(a_0+\NN)\times\NN$, so $r_{a_0}=0$, a contradiction. Hence $R=0$, $(1+Y)L=(1+Y)S_1L_N$, and $L=S_1L_N$ because $1+Y$ is injective.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:relN}]
(1) We have seen that $\cO L_N\subseteq\Rel(N)$. Let $L\in\Rel(N)$, say $(LN)(k,q)=0$ for $k\ge k_0$, $q\ge q_0$. By Lemma~\ref{lem:transport}(1) with $c=0$ there are $j\ge0$ and $M\in\cO$ with $\nabla^j\mathcal PL=M\mathcal P$. Put $n=q_0+j$. Then $\nabla^{q_0}M(\mathcal PN)=\nabla^n\mathcal P(LN)$ vanishes for $k\ge k_0$, $m\ge n$ by Lemma~\ref{lem:boundary}, so $\nabla^{q_0}M=Q\widetilde L_1$ for some $Q\in\cO$ by Lemma~\ref{lem:relV}. By Lemma~\ref{lem:Pid}(6),
\[
  \nabla^n\mathcal PL=\nabla^{q_0}M\mathcal P=Q\widetilde L_1\mathcal P=Q\nabla\mathcal PL_N .
\]
By Lemma~\ref{lem:transport}(2) with $a=1$ there are $c\ge0$ and $M'\in\cO$ with $Q\nabla\mathcal P=\nabla^c\mathcal PM'$. Using Lemma~\ref{lem:Pid}(2) on both sides,
\[
  \nabla^{n+c}\mathcal P(1+Y)^cL=\nabla^n\mathcal PL=\nabla^c\mathcal PM'L_N=\nabla^{n+c}\mathcal P(1+Y)^nM'L_N .
\]
Since $\nabla$ and $\mathcal P$ are injective, $(1+Y)^cL=(1+Y)^nM'L_N\in\cO L_N$, and $c$ applications of Lemma~\ref{lem:saturation} give $L\in\cO L_N$.

(2) For $Q=\sum q(a,b)X^aY^b$, the relation $Y^bm=(m-b)Y^b$ shows that the normal form of $QL_N$ is
\[
  r(a,b)=q(a,b)-q(a-1,b)-q(a-1,b-1)-\sum_{j=0}^{2}\binom{2}{j}(m-1-b+j)\,q(a-3,b-j),
\]
with $q=0$ at negative indices. Let $Q\ne0$. If $\beta^*$ is the largest $b$ with $q(\cdot,b)\ne0$ and $q(\alpha',\beta^*)\ne0$, then $r(\alpha'+3,\beta^*+2)=-(m-1-\beta^*)\,q(\alpha',\beta^*)\ne0$. If $\alpha^*$ is the largest $a$ with $q(a,\cdot)\ne0$ and $\beta'$ is the largest $b$ with $q(\alpha^*,b)\ne0$, then $r(\alpha^*+3,\beta'+2)=-(m-1-\beta')\,q(\alpha^*,\beta')\ne0$. If $e$ is the largest total degree of the coefficients of $Q$, choose $a$ such that some $q(a,b)$ has a nonzero homogeneous part $[q(a,b)]_e$ of degree $e$, and let $b_0$ be the largest such $b$; the homogeneous part of degree $e+1$ of $r(a+3,b)$ is $-m\sum_j\binom{2}{j}[q(a,b-j)]_e$, so that of $r(a+3,b_0+2)$ is $-m[q(a,b_0)]_e\ne0$. In particular right multiplication by $L_N$ is injective, and $QL_N\in V_N(A,B,D)$ if and only if $\Supp(Q)\subseteq[0,A-3]\times[0,B-2]$ and all coefficients of $Q$ have total degree at most $D-1$; the converse holds because $\Supp(L_N)\subseteq[0,3]\times[0,2]$ and the coefficients of $L_N$ have degree at most $1$. By~(1), $V_N(A,B,D)$ consists of these $QL_N$, and counting the monomials $k^im^jX^aY^b$ with $a\le A-3$, $b\le B-2$ and $i+j\le D-1$ gives the formula. For separate degree bounds, argue as in the proof of Theorem~\ref{thm:ideal}(2): the coefficients of $L_N$ and the commutation rule $Y^bm=(m-b)Y^b$ do not involve $k$, so the coefficient of the top power of $k$ in $QL_N$ is $\hat QL_N$, where $\hat Q\ne0$ collects the top $k$-coefficients of $Q$; and the degree in $m$ goes up by exactly one, by the argument just given with degrees in $m$ in place of total degrees.
\end{proof}

The proof above is a written version of the formal proof (\lean{RelN\_eq}, \lean{finrank\_relN\_tot} and \lean{finrank\_relN\_gr} in the files \lean{OreRelN.lean} and \lean{OreDim.lean}); some lemmas are organized differently there, for instance the formal proof of Lemma~\ref{lem:relV} evaluates operators at indicator functions of points instead of comparing normal forms. The identities of Lemma~\ref{lem:Pid} are also checked by exact computation on random integer arrays (script \lean{code/main\_extra/check\_appendix\_relN.py}).

'''


def split_main(block):
    """Cut the old Main results block into the named pieces; assert that nothing is lost."""
    starts = []
    for name, head in PIECES:
        c = block.count(head)
        assert c == 1, (name, c)
        starts.append((block.index(head), name))
    starts.sort()
    assert [n for _, n in starts] == [n for n, _ in PIECES], [n for _, n in starts]
    assert starts[0][0] == 0
    out = {}
    for i, (pos, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(block)
        out[name] = block[pos:end]
    assert ''.join(out[n] for n, _ in PIECES) == block
    for name in out:
        assert out[name].endswith('\n\n'), name
    return out


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    p = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'paper', 'main.tex')
    raw = open(p, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')

    # abstract
    a = s.index(OLD_ABS_START) + len(OLD_ABS_START)
    b = s.index(OLD_ABS_END, a)
    assert s.count(OLD_ABS_START) == 1
    s = s[:a] + NEW_ABS + s[b:]
    assert len(NEW_ABS) <= 1920, len(NEW_ABS)

    # introduction: rebuild "Main results" and add "Further results"
    assert s.count(MAIN_START) == 1 and s.count(MAIN_END) == 1
    i0 = s.index(MAIN_START) + len(MAIN_START)
    i1 = s.index(MAIN_END)
    pc = split_main(s[i0:i1])
    assert pc['framing'].count(FRAMING_OLD) == 1
    framing = pc['framing'].replace(FRAMING_OLD, FRAMING_NEW)
    new_main = (framing + pc['notation'] + pc['npara'] + HIERARCHY + pc['thmA'] + pc['thmB'] + pc['thmD'] + NSENT
                + pc['thmF'] + pc['chains'] + pc['interlace'] + FURTHER_HEAD + pc['asym'] + COLUMNS + pc['thmC']
                + pc['thmE'])
    s = s[:i0] + new_main + s[i1:]

    # other single replacements
    for old, new in [(NEW_ANCHOR, NEW_ANCHOR + WHATSNEW), (ORG_OLD, ORG_NEW), (RELN_OLD, RELN_NEW), (TAB_OLD, TAB_NEW),
                     (APP_ANCHOR, APPENDIX_B + APP_ANCHOR)]:
        c = s.count(old)
        assert c == 1, (c, old[:70])
        s = s.replace(old, new)

    # rename the labels of the introductory theorems
    for old, new in LABELS:
        n_lab = s.count(r'\label{%s}' % old)
        assert n_lab == 1, (old, n_lab)
        n_ref = len(re.findall(r'\\ref\{%s\}' % old, s))
        s = s.replace(r'\label{%s}' % old, r'\label{%s}' % new).replace(r'\ref{%s}' % old, r'\ref{%s}' % new)
        assert old + '}' not in s, old
        print('label %s -> %s (%d refs)' % (old, new, n_ref))

    assert all(ord(ch) < 128 for ch in s), 'non-ASCII character'
    for must in (r'\label{app:relN}', r'\label{thm:relN}', r'\label{sec:further}', r'\label{eq:PN}'):
        assert s.count(must) == 1, must
    assert 'We omit the proof' not in s
    open(p, 'wb').write(s.encode('utf-8'))
    print('paper/main.tex: abstract %d chars, intro rebuilt, appendix B added (%d bytes), %d bytes in total'
          % (len(NEW_ABS), len(APPENDIX_B.encode('utf-8')), len(s.encode('utf-8'))))


if __name__ == '__main__':
    main()
