# -*- coding: utf-8 -*-
"""Check that every Lean name in Table 5 of paper/main.tex (\\lean{...} inside the tabular of tab:lean) is printed
by lean/Axioms.lean (`#print axioms A207123.<name>`), so the axiom check covers the table.

Usage (task C root):  py -3.14 code/main_extra/check_table5_axioms.py [paper/main.tex [lean/Axioms.lean]]
Exit code 1 if a name is missing or the table is not found.
"""
import os
import re
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def main(tex_path, axioms_path):
    tex = open(tex_path, encoding='utf-8').read()
    cap = tex.find('\\caption{Formalized results.}')
    beg = tex.rfind('\\begin{tabular}', 0, cap)
    end = tex.rfind('\\end{tabular}', 0, cap)
    if cap < 0 or beg < 0 or not beg < end:
        print('FAIL table 5 not found')
        return 1
    names = [n.replace('\\_', '_') for n in re.findall(r'\\lean\{([^}]*)\}', tex[beg:end])]
    printed = set(re.findall(r'^#print axioms A207123\.(\S+)', open(axioms_path, encoding='utf-8').read(), re.M))
    missing = [n for n in names if n not in printed]
    for n in missing:
        print('FAIL not in Axioms.lean:', n)
    print('%d Lean names in Table 5 (%d distinct); %d printed by Axioms.lean; missing: %d'
          % (len(names), len(set(names)), len(names) - len(missing), len(missing)))
    return 1 if missing or not names else 0


if __name__ == '__main__':
    a = sys.argv[1:]
    sys.exit(main(a[0] if a else os.path.join(ROOT, 'paper', 'main.tex'),
                  a[1] if len(a) > 1 else os.path.join(ROOT, 'lean', 'Axioms.lean')))
