# -*- coding: utf-8 -*-
"""从 lean/A207123/*.lean 里抽出「文档注释 + 定义全文 + 定理陈述（不含证明）」，便于人工核对陈述是否忠实于报告。

Lean 只检查证明，不检查陈述是不是报告说的意思；这一步要人读。本脚本只做抽取，不判断对错。
用法：py -3.14 code/main_extra/lean_statements.py [模块名 ...] [-o 输出.md]
  不给模块名时处理 lean/A207123/ 下全部文件；默认输出到标准输出。
规则（启发式，不是 Lean 解析器）：
  - 声明从 theorem / lemma / def / abbrev / instance / structure / inductive 开头的行算起（允许前面有 @[...] 和
    private / protected / noncomputable 等修饰词）；
  - theorem / lemma 只保留到第一个 `:=` 之前（证明不要）；
  - 定义保留全文（到下一个空行、下一条声明或 section / end 为止），因为定义本身就是陈述的一部分；
  - 紧挨在声明前面的 /-- ... -/ 文档注释一并输出。
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, 'lean', 'A207123')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b')
STOP = re.compile(r'^(?:section|end|namespace|open|variable|/-!|#|set_option|attribute)\b')


def extract(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    out, i, n = [], 0, len(lines)
    while i < n:
        m = DECL.match(lines[i])
        if not m:
            i += 1
            continue
        # 紧挨着的文档注释
        doc, j = [], i - 1
        if j >= 0 and lines[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and '/--' not in lines[k]:
                k -= 1
            if k >= 0:
                doc = lines[k:j + 1]
        kind = m.group(1)
        body, k = [], i
        if kind in ('theorem', 'lemma'):
            while k < n:
                ln = lines[k]
                if ':=' in ln:
                    body.append(ln[:ln.index(':=')].rstrip())
                    break
                body.append(ln)
                k += 1
        else:
            while k < n:
                ln = lines[k]
                if k > i and (not ln.strip() or DECL.match(ln) or STOP.match(ln) or ln.startswith('/--')):
                    break
                body.append(ln)
                k += 1
        out.append((i + 1, kind, '\n'.join(doc), '\n'.join(body).rstrip()))
        i = k + 1
    return out


def main(argv):
    target = None
    if '-o' in argv:
        p = argv.index('-o')
        target = argv[p + 1]
        argv = argv[:p] + argv[p + 2:]
    mods = argv or sorted(f[:-5] for f in os.listdir(SRC) if f.endswith('.lean'))
    chunks = ['# Lean 陈述清单（由 code/main_extra/lean_statements.py 生成；只含陈述与定义，不含证明）\n']
    for mod in mods:
        decls = extract(os.path.join(SRC, mod + '.lean'))
        chunks.append('## %s（%d 条声明）\n' % (mod, len(decls)))
        for line, kind, doc, body in decls:
            chunks.append('`lean/A207123/%s.lean:%d`（%s）\n' % (mod, line, kind))
            chunks.append('```lean\n' + (doc + '\n' if doc else '') + body + '\n```\n')
    text = '\n'.join(chunks)
    if target:
        with open(target, 'w', encoding='utf-8') as f:
            f.write(text)
        print('wrote', target, len(text), 'chars')
    else:
        sys.stdout.reconfigure(encoding='utf-8')
        print(text)


if __name__ == '__main__':
    main(sys.argv[1:])
