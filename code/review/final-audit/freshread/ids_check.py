import os, re, sys
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = os.path.join(ROOT, 'notes', 'report_parts')
names = sorted(n for n in os.listdir(P) if n.endswith('.md'))
areas = ('c0','c1','c2a','c2b','c3a','c3b','c4','c5a','c5b','rv','rv2')
pat = re.compile(r'(?<![A-Za-z0-9_/\\])(' + '|'.join(areas) + r')\.([A-Za-z0-9][A-Za-z0-9_\-.]*[A-Za-z0-9])')


def passed_ids(log):
    s = {}
    for ln in open(log, encoding='utf-8'):
        m = re.match(r'PASS (\S+)(.*)', ln)
        if m:
            s[m.group(1)] = m.group(2)
    return s


final = passed_ids(os.path.join(ROOT, 'logs', 'verify_all_final.log'))
print('final PASS ids:', len(final))
allcited = []
for n in names:
    t = open(os.path.join(P, n), encoding='utf-8').read()
    for area, cid in pat.findall(t):
        if cid == 'md' or cid.endswith('.md'):
            continue
        allcited.append((n, area, cid))
miss = []
for n, area, cid in allcited:
    if cid in final or (area + '.' + cid) in final:
        continue
    if '..' in cid:
        stem = cid.split('..')[0].rstrip('0123456789')
        if any(p.startswith(stem) for p in final):
            continue
    miss.append((n, area, cid))
print('cited occurrences', len(allcited), 'unique', len(set((a, c) for _, a, c in allcited)))
print('missing:', miss)
cited_set = set()
for n, area, cid in allcited:
    cited_set.add(cid)
    cited_set.add(area + '.' + cid)
uncited = sorted(x for x in final if x not in cited_set)
print('uncited PASS ids in final log (%d):' % len(uncited))
for x in uncited:
    print('  ', x, '|', final[x][:160])
