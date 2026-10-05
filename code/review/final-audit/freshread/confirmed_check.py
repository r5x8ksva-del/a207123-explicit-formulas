import json, os
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = os.path.join(ROOT, 'notes', 'report_parts')
d = json.load(open(os.path.join(ROOT, 'logs', 'phase4_final_audit_output.json'), encoding='utf-8'))
conf = d['confirmed']
print('confirmed:', len(conf))
print(type(conf[0]), list(conf[0].keys()) if isinstance(conf[0], dict) else conf[0])
texts = {n: open(os.path.join(P, n), encoding='utf-8').read() for n in os.listdir(P) if n.endswith('.md')}
for i, f in enumerate(conf):
    fn = f.get('file')
    q = f.get('quote') or ''
    v = f.get('verdict', {})
    ff = v.get('final_fix') or ''
    t = texts.get(fn, '')
    still = q in t if q else None
    # check if a 25-char chunk of final_fix appears
    chunk_hits = 0
    chunks = [ff[j:j + 20] for j in range(0, max(0, len(ff) - 20), 20)]
    for c in chunks:
        if any(c in tt for tt in texts.values()):
            chunk_hits += 1
    frac = (chunk_hits / len(chunks)) if chunks else None
    print('#%02d %s quote_still=%s fix_frac=%s :: %s' % (i, fn, still, None if frac is None else round(frac, 2), q[:70].replace('\n', ' ')))
