import os, re
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = os.path.join(ROOT, 'notes', 'report_parts')
names = sorted(n for n in os.listdir(P) if n.endswith('.md'))
texts = {n: open(os.path.join(P, n), encoding='utf-8').read() for n in names}
full = '\n'.join(texts[n] for n in names)

# defined theorem labels: lines starting with **T1.0（ etc.
defs = set(re.findall(r'\*\*(T\d\.\d+)（', full))
print('defined theorems:', sorted(defs))

# sub-items: within each theorem block, find "(k)【" or "(k)" at line starts
blocks = {}
order = [m for m in re.finditer(r'\*\*(T\d\.\d+)（', full)]
for i, m in enumerate(order):
    end = order[i + 1].start() if i + 1 < len(order) else len(full)
    blocks[m.group(1)] = full[m.start():end]
subs = {}
for t, b in blocks.items():
    s = set(re.findall(r'(?:^|\n|：|。|\s)\((\d)\)', b))
    subs[t] = sorted(s)
for t in sorted(subs):
    print(t, 'subitems', subs[t])

# references
refs = re.findall(r'(T\d\.\d+)((?:\(\d\))*)(?:\(([a-z])\))?', full)
bad = []
for n in names:
    for m in re.finditer(r'(T\d\.\d+)((?:\(\d\)){0,3})', texts[n]):
        t, sub = m.group(1), m.group(2)
        if t not in defs:
            bad.append((n, m.group(0), 'undefined theorem'))
            continue
        for d in re.findall(r'\((\d)\)', sub):
            if d not in subs.get(t, []):
                bad.append((n, m.group(0), 'missing subitem ' + d))
print('bad refs:')
for b in bad:
    print('  ', b)
# section refs like ④A.5, ④C, ④B.13
for n in names:
    for m in re.finditer(r'([①②③④⑤⑥])([A-C])?(?:\.(\d+))?', texts[n]):
        print('SECREF', n, m.group(0))
