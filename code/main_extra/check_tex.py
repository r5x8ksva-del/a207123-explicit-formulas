# -*- coding: utf-8 -*-
"""本机没有 TeX 编译器时，对 paper/*.tex 做结构检查（不能代替真正编译）。

检查：\\begin/\\end 配对与嵌套；花括号配对（忽略 \\{ \\} 与注释）；每段里 $ 的个数为偶数；\\[ \\] 配对；
\\ref/\\eqref 的标签都有 \\label，\\label 不重复；\\cite 的键都有 \\bibitem；注释之外不能有非 ASCII 字符（pdflatex 不带 CJK 宏包会报错）；
用到的自定义命令都已定义（只查本文件里 \\newcommand 定义过的那几个与常见宏包命令以外的、形如 \\xxx 的未知命令，给出提示，不判失败）。
用法：py -3.14 code/main_extra/check_tex.py paper/main.tex   （有问题时退出码 1）
"""
import re
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def strip_comments(line):
    out, i = [], 0
    while i < len(line):
        if line[i] == '\\' and i + 1 < len(line):
            out.append(line[i:i + 2])
            i += 2
            continue
        if line[i] == '%':
            break
        out.append(line[i])
        i += 1
    return ''.join(out)


def main(path):
    raw = open(path, encoding='utf-8').read().split('\n')
    lines = [strip_comments(ln) for ln in raw]
    text = '\n'.join(lines)
    problems = []

    # 环境配对
    stack = []
    for no, ln in enumerate(lines, 1):
        for m in re.finditer(r'\\(begin|end)\{([^}]*)\}', ln):
            kind, env = m.group(1), m.group(2)
            if kind == 'begin':
                stack.append((env, no))
            else:
                if not stack:
                    problems.append('第 %d 行：\\end{%s} 没有对应的 \\begin' % (no, env))
                elif stack[-1][0] != env:
                    problems.append('第 %d 行：\\end{%s} 与第 %d 行的 \\begin{%s} 不配对' % (no, env, stack[-1][1], stack[-1][0]))
                    stack.pop()
                else:
                    stack.pop()
    for env, no in stack:
        problems.append('第 %d 行：\\begin{%s} 没有结束' % (no, env))

    # 花括号
    depth = 0
    for no, ln in enumerate(lines, 1):
        i = 0
        while i < len(ln):
            c = ln[i]
            if c == '\\':
                i += 2
                continue
            if c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
                if depth < 0:
                    problems.append('第 %d 行：多出一个 }' % no)
                    depth = 0
            i += 1
    if depth != 0:
        problems.append('全文花括号不配对，差 %d 个 }' % depth)

    # $ 与 \[ \]
    paras = re.split(r'\n\s*\n', text)
    line_of_para = []
    pos = 0
    for p in paras:
        idx = text.find(p, pos)
        line_of_para.append(text.count('\n', 0, idx) + 1)
        pos = idx + len(p)
    for p, no in zip(paras, line_of_para):
        q = re.sub(r'\\\$', '', p)
        if q.count('$') % 2:
            problems.append('从第 %d 行开始的段落里 $ 的个数是奇数' % no)
        q2 = re.sub(r'\\\\(\[[^\]]*\])?', ' ', q)       # 换行命令 \\ 与 \\[1ex] 不是 \[ \]
        if len(re.findall(r'\\\[', q2)) != len(re.findall(r'\\\]', q2)):
            problems.append('从第 %d 行开始的段落里 \\[ 与 \\] 个数不等' % no)

    # 标签与引用
    labels = re.findall(r'\\label\{([^}]*)\}', text)
    dup = sorted({x for x in labels if labels.count(x) > 1})
    for x in dup:
        problems.append('标签重复：%s' % x)
    refs = set(re.findall(r'\\(?:eq)?ref\{([^}]*)\}', text))
    for x in sorted(refs - set(labels)):
        problems.append('引用了不存在的标签：%s' % x)
    cites = set()
    for m in re.finditer(r'\\cite(?:\[[^\]]*\])?\{([^}]*)\}', text):
        cites.update(k.strip() for k in m.group(1).split(','))
    items = set(re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]*)\}', text))
    for x in sorted(cites - items):
        problems.append('引用了不存在的文献：%s' % x)
    unused = sorted(items - cites)

    # 未知命令（只提示）
    defined = set(re.findall(r'\\(?:newcommand|renewcommand|DeclareMathOperator)\{?\\([A-Za-z]+)', text))
    defined |= set(re.findall(r'\\newtheorem\*?\{([A-Za-z]+)\}', text))
    used = set(re.findall(r'\\([A-Za-z]+)', text))
    known = ('''documentclass usepackage newtheorem theoremstyle renewcommand newcommand DeclareMathOperator begin end
    title author date maketitle section subsection subsubsection label ref eqref cite emph textbf texttt textcolor url
    item bibitem thebibliography abstract subjclass keywords Alph theintrothm frac dfrac binom genfrac lceil rceil lfloor
    rfloor le ge ne neq leq geq sum prod cdot cdots dots ldots infty to mapsto in notin subseteq subset cup cap sqcup bigcup
    alpha beta gamma delta varepsilon epsilon theta vartheta lambda mu nu xi pi rho varrho sigma tau phi varphi chi psi omega
    Gamma Delta Theta Lambda Xi Pi Sigma Phi Psi Omega partial nabla times pm mp backslash mathbb mathcal mathrm operatorname
    left right bigl bigr Bigl Bigr qquad quad hline toprule midrule bottomrule centering caption textit underline overline
    tilde hat bar max min gcd det deg log exp lim sup inf equiv pmod bmod mid not langle rangle ast star circ prime ell
    sqrt text mathbf boldsymbol displaystyle noindent par newline linebreak smallskip medskip bigskip vspace hspace
    enumerate itemize description tabular table align equation proof footnote today hidelinks colon setminus emptyset
    forall exists leftarrow rightarrow Leftarrow Rightarrow iff implies cong sim approx simeq propto mathfrak cal
    lVert rVert Vert vert lvert rvert ll gg lesssim gtrsim underbrace overbrace widetilde widehat nolimits limits
    stackrel overset underset substack quad dim eta bigcup backslash Lambda caption date keywords subjclass
    maketitle textbf tilde uparrow downarrow''')
    known = set(known.split()) if isinstance(known, str) else known
    unknown = sorted(c for c in used - defined - known if len(c) > 1)
    # 非 ASCII 字符（pdflatex 不带 CJK 宏包时，正文里的中文会报错；注释里的不影响编译，只提示）
    for no, (ln, rl) in enumerate(zip(lines, raw), 1):
        if any(ord(ch) > 127 for ch in ln):
            problems.append('第 %d 行（注释之外）有非 ASCII 字符，pdflatex 可能报错：%s' % (no, ''.join(sorted({ch for ch in ln if ord(ch) > 127}))))
        elif any(ord(ch) > 127 for ch in rl):
            print('提示：第 %d 行的注释里有非 ASCII 字符' % no)
    print('环境、括号、$、标签、文献：%s' % ('没有发现问题' if not problems else '%d 处问题' % len(problems)))
    for p in problems:
        print('  ' + p)
    print('标签 %d 个，引用 %d 个；文献 %d 条，引用 %d 条%s' % (
        len(labels), len(refs), len(items), len(cites), ('，未被引用：' + '、'.join(unused)) if unused else ''))
    if unknown:
        print('提示：不在内置清单里的命令（多半是宏包命令，请编译时确认）：' + ' '.join('\\' + c for c in unknown))
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else 'paper/main.tex'))
