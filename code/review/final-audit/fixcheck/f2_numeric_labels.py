# -*- coding: utf-8 -*-
"""只读：找出核对日志中带 decimal/numeric/float/数值 字样的检查 id，看报告中每次引用是否注明「数值」。"""
import re, os, glob
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
logs = [os.path.join(ROOT, 'logs', 'audit_a3-requirements_verify_rerun.log'),
        os.path.join(ROOT, 'logs', 'verify_all_run1.log')]
mod = None
numeric = {}
for lg in logs:
    for ln in open(lg, encoding='utf-8', errors='replace'):
        m = re.match(r'>>> check_(\w+)\.py', ln)
        if m:
            mod = m.group(1)
        m = re.match(r'(PASS|FAIL) (\S+) (.*)', ln)
        if m and mod:
            cid = m.group(2)
            if re.search(r'decimal|Decimal|\[numeric|\[NUM\]|数值|float', m.group(3)):
                numeric.setdefault(f'{mod}.{cid}', m.group(3)[:140])
rep = ''.join(open(p, encoding='utf-8').read() for p in sorted(glob.glob(os.path.join(ROOT, 'notes', 'report_parts', '*.md'))))
for cid, desc in sorted(numeric.items()):
    for mm in re.finditer(re.escape(cid) + r'(?![\w\-])', rep):
        ctx = rep[mm.end(): mm.end() + 60].replace('\n', ' ')
        pre = rep[max(0, mm.start() - 40): mm.start()].replace('\n', ' ')
        flag = 'LABELED' if '数值' in ctx[:45] else 'NO-LABEL'
        print(f'{flag:9s} {cid:28s} ...{pre[-25:]}[{cid}]{ctx[:45]}')
