# -*- coding: utf-8 -*-
import json, os
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
d = json.load(open(os.path.join(ROOT, 'logs', 'phase4_final_audit_output.json'), encoding='utf-8'))
for i, c in enumerate(d['confirmed']):
    v = c['verdict']
    print('=' * 100)
    print(f"[{i}] lens={c['lens']} file={c['file']} sev={c['severity']} vidx={v.get('index')}")
    print('QUOTE:', c['quote'])
    print('PROBLEM:', c['problem'])
    print('REASON:', v.get('reason'))
    print('FINAL_FIX:', v.get('final_fix'))
