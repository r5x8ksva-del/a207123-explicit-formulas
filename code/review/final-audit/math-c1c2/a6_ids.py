# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a6: every check id cited in 02_C1.md, 03_C2.md, 07_formula.md must be a PASS line
of logs/verify_all_final.log under the right module."""
import re, os, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read().splitlines()
mod = None
passes = {}
for ln in log:
    m = re.match(r'>>> check_(\w+)\.py', ln)
    if m:
        mod = m.group(1); continue
    if ln.startswith('PASS '):
        cid = ln.split()[1]
        passes.setdefault(mod, set()).add(cid)
bad = []
n = 0
for f in ('02_C1.md', '03_C2.md', '07_formula.md'):
    txt = open(os.path.join(ROOT, 'notes', 'report_parts', f), encoding='utf-8').read()
    for m in re.finditer(r'\b(c0|c1|c2a|c2b|c3a|c3b|c4|c5a|c5b|rv|rv2)\.([A-Za-z0-9_\-\.]*[A-Za-z0-9])', txt):
        md, cid = m.group(1), m.group(2)
        if cid.endswith('*') or cid == 'md':   # 'notes/c2b.md' is a file reference, not a check id
            continue
        n += 1
        cands = {cid, md + '.' + cid}
        ok = any(c in passes.get(md, set()) for c in cands)
        if not ok:
            # allow prefix wildcard like c2b.T1 (family)
            fam = [p for p in passes.get(md, set()) if p.startswith(cid) or p.startswith(md + '.' + cid)]
            if not fam:
                bad.append((f, md, cid))
print('cited ids checked:', n)
print('NOT FOUND:', bad)
print('SUMMARY a6 pass=%d fail=%d' % (int(not bad), int(bool(bad))))
