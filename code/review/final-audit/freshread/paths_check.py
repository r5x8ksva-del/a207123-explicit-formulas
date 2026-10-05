import os, re
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = os.path.join(ROOT, 'notes', 'report_parts')
names = sorted(n for n in os.listdir(P) if n.endswith('.md'))
pat_log = re.compile(r'(logs/[A-Za-z0-9_\-./]+\.(?:log|json|txt))')
pat_bare = re.compile(r'(?<![/A-Za-z0-9_])(review_[A-Za-z0-9_\-]+\.log)')
pat_code = re.compile(r'(code/[A-Za-z0-9_\-./<>]+\.py)')
pat_notes = re.compile(r'(notes/[A-Za-z0-9_\-./<>\u4e00-\u9fff]+\.md)')
pat_data = re.compile(r'(data/[A-Za-z0-9_\-./]+)')
for n in names:
    t = open(os.path.join(P, n), encoding='utf-8').read()
    for rx, kind in ((pat_log, 'log'), (pat_code, 'code'), (pat_notes, 'notes'), (pat_data, 'data')):
        for p in sorted(set(rx.findall(t))):
            if '<' in p:
                continue
            ex = os.path.exists(os.path.join(ROOT, p.replace('/', os.sep)))
            if not ex:
                print('MISSING', n, kind, p)
    for p in sorted(set(pat_bare.findall(t))):
        ex = os.path.exists(os.path.join(ROOT, 'logs', p))
        print('BARE', n, p, 'exists_in_logs=' + str(ex))
print('done')
