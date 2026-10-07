# -*- coding: utf-8 -*-
"""Check that every Lean declaration transcribed in Appendix A of paper/main.tex agrees with the current
source in lean/A207123/*.lean.

Each alltt block of the appendix is converted back from TeX to Lean's Unicode notation and split into
declarations. For each one, the source declaration of the same name is cut out (from its keyword up to the
next non-indented line) and compared after collapsing whitespace:
  * a def or abbrev must agree with the source in full, body included;
  * a theorem is transcribed without its proof, so it must agree with the source up to the `:=` that
    starts the proof.

Usage:  py -3.14 code/main_extra/check_appendix_lean.py [paper/main.tex]   (exit code 1 on any FAIL)
"""
import glob
import os
import re
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))

# TeX in the alltt blocks -> Lean source characters (longer keys first).
MAP = [
    (r'\(\NN\times\NN\)', 'ℕ × ℕ'), (r'\(\NN\)', 'ℕ'), (r'\(\C\)', 'ℂ'), (r'\(\Z\)', 'ℤ'),
    (r'\(\to_0\)', '→₀'), (r'\(\to\)', '→'), (r'\(\lor\)', '∨'), (r'\(\land\)', '∧'), (r'\(\lnot\)', '¬'),
    (r'\(\le\)', '≤'), (r'\(\ne\)', '≠'), (r'\(\forall\)', '∀'), (r'\(\exists\)', '∃'), (r'\(\notin\)', '∉'),
    (r'\(\in\)', '∈'), (r'\(\sum\)', '∑'), (r'\(\subseteq\)', '⊆'), (r'\(\langle\)', '⟨'), (r'\(\rangle\)', '⟩'),
    (r'\(\sigma\)', 'σ'), (r'\{', '{'), (r'\}', '}'),
]
DECL = re.compile(r'^(?:noncomputable\s+)?(def|abbrev|theorem)\s+([A-Za-z0-9_\']+)')


def squash(s):
    # Collapse (not delete) whitespace, so that e.g. `fun k m` and `fun km` stay different.
    return re.sub(r'\s+', ' ', s).strip()


def appendix_decls(tex):
    app = tex[tex.index(r'\section{The Lean definitions}'):]
    blocks = re.findall(r'\\begin\{alltt\}\\small\n(.*?)\\end\{alltt\}', app, re.S)
    decls = []
    for b in blocks:
        for k, v in MAP:
            b = b.replace(k, v)
        if '\\' in b:
            raise SystemExit('unconverted TeX left in the appendix: ' + b[b.index('\\'):][:40])
        # A declaration starts at column 0; its continuation lines are indented. Consecutive declarations
        # are not always separated by a blank line (e.g. Arr and Coef).
        for line in b.split('\n'):
            m = DECL.match(line)
            if m:
                decls.append([m.group(1), m.group(2), line])
            elif line.strip():
                if not decls or line[0] not in ' \t':
                    raise SystemExit('cannot read a declaration name in: ' + line[:60])
                decls[-1][2] += '\n' + line
    return [tuple(d) for d in decls]


def source_decls(name):
    """(file, line, text) for each source declaration of `name`, cut at the next non-indented line."""
    pat = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|theorem|lemma)\s+'
                     + re.escape(name) + r'(?![A-Za-z0-9_\'])', re.M)
    out = []
    for path in sorted(glob.glob(os.path.join(ROOT, 'lean', 'A207123', '*.lean'))):
        text = open(path, encoding='utf-8').read()
        for m in pat.finditer(text):
            lines = text[m.start():].split('\n')
            n = 1
            while n < len(lines) and (not lines[n].strip() or lines[n][0] in ' \t'):
                n += 1
            out.append((os.path.basename(path), text.count('\n', 0, m.start()) + 1, '\n'.join(lines[:n])))
    return out


def agrees(kind, chunk, source):
    want, have = squash(chunk), squash(source)
    if kind == 'theorem':
        return have.startswith(want) and have[len(want):].lstrip().startswith(':=')
    return have == want


def main(path):
    decls = appendix_decls(open(path, encoding='utf-8').read())
    nfail = 0
    for kind, name, chunk in decls:
        hits = source_decls(name)
        ok = [(f, line) for f, line, src in hits if agrees(kind, chunk, src)]
        if ok:
            print('PASS %-8s %-32s %s:%d' % (kind, name, ok[0][0], ok[0][1]))
        else:
            nfail += 1
            where = ', '.join('%s:%d' % (f, line) for f, line, _ in hits) or 'not found'
            print('FAIL %-8s %-32s source at %s' % (kind, name, where))
    print('%d declarations in Appendix A: %d PASS, %d FAIL' % (len(decls), len(decls) - nfail, nfail))
    return 1 if nfail else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'paper', 'main.tex')))
