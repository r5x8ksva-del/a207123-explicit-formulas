# -*- coding: utf-8 -*-
"""Try layout variants of paper/main.tex in a scratch folder (Tectonic), report pages, where the late sections and
the formalized-results tables land, and the TeX warnings.

Each variant is a list of (old, new) replacements applied to the current paper/main.tex; every `old` must occur
exactly once. Variants are read from a JSON file: {"name": [["old", "new"], ...], ...}.

Usage (task C root):  py -3.14 code/main_extra/try_layout.py variants.json scratch_dir
"""
import json
import os
import subprocess
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
TECT = os.path.join(os.environ['LOCALAPPDATA'], 'Programs', 'tectonic', 'tectonic.exe')
KEYS = ['8. Real roots', '9. Formal verification', 'Table 5.', 'Table 6.', '10. Open problems',
        'A. The Lean definitions', 'B. The recurrences', 'References']


def main(variants_path, scratch):
    import pymupdf
    base = open(os.path.join(ROOT, 'paper', 'main.tex'), encoding='utf-8').read()
    variants = json.load(open(variants_path, encoding='utf-8'))
    for name, reps in variants.items():
        text = base
        for old, new in reps:
            assert text.count(old) == 1, (name, text.count(old), old[:60])
            text = text.replace(old, new)
        d = os.path.join(scratch, name)
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, 'main.tex'), 'w', encoding='utf-8', newline='\n').write(text)
        r = subprocess.run([TECT, '-X', 'compile', 'main.tex'], cwd=d, capture_output=True, text=True,
                           encoding='utf-8', errors='replace')
        warns = [l for l in (r.stdout + r.stderr).splitlines()
                 if l.startswith('warning:') and 'warnings were issued' not in l]
        doc = pymupdf.open(os.path.join(d, 'main.pdf'))
        where = {}
        for i in range(doc.page_count):
            t = doc[i].get_text()
            for key in KEYS:
                if key in t:
                    where.setdefault(key, []).append(i + 1)
        print(name, 'exit', r.returncode, 'pages', doc.page_count, where, 'warnings:', len(set(warns)))
        for w in sorted(set(warns)):
            print('   ', w)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
