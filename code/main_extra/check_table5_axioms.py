# -*- coding: utf-8 -*-
"""Check that every Lean name in Tables 5 and 6 of paper/main.tex (\\lean{...} inside the tabulars captioned "Formalized results") is printed
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
    # Since 2026-10-10 (21st item) the table is split into Tables 5 and 6, both captioned "Formalized results...".
    names, ntab, pos = [], 0, 0
    while True:
        cap = tex.find('\\caption{Formalized results', pos)
        if cap < 0:
            break
        beg = tex.rfind('\\begin{tabular}', 0, cap)
        end = tex.rfind('\\end{tabular}', 0, cap)
        if beg < 0 or not beg < end:
            print('FAIL no tabular before the caption at offset %d' % cap)
            return 1
        names += [n.replace('\\_', '_') for n in re.findall(r'\\lean\{([^}]*)\}', tex[beg:end])]
        ntab += 1
        pos = cap + 1
    if ntab == 0:
        print('FAIL table 5 not found')
        return 1
    print('%d tables captioned "Formalized results"' % ntab)
    printed = set(re.findall(r'^#print axioms A207123\.(\S+)', open(axioms_path, encoding='utf-8').read(), re.M))
    missing = [n for n in names if n not in printed]
    for n in missing:
        print('FAIL not in Axioms.lean:', n)
    print('%d Lean names in the tables (%d distinct); %d printed by Axioms.lean; missing: %d'
          % (len(names), len(set(names)), len(names) - len(missing), len(missing)))
    return 1 if missing or not names else 0


if __name__ == '__main__':
    a = sys.argv[1:]
    sys.exit(main(a[0] if a else os.path.join(ROOT, 'paper', 'main.tex'),
                  a[1] if len(a) > 1 else os.path.join(ROOT, 'lean', 'Axioms.lean')))
