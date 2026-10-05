# -*- coding: utf-8 -*-
import json, sys
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
d = json.load(open(ROOT + r'\logs\phase4_final_audit_output.json', encoding='utf-8'))
out = sys.stdout
for o in d['out']:
    for i, f in enumerate(o['findings']):
        v = f['verdict']
        print('=' * 100)
        print(f"[{o['lens']} #{i}] file={f['file']} sev={f['severity']} REAL={v['real']}")
        print('QUOTE:', f['quote'])
        print('PROBLEM:', f['problem'])
        print('EVIDENCE:', f['evidence'])
        print('SUGGESTED:', f['suggested_fix'])
        print('VERDICT REASON:', v['reason'])
        print('FINAL_FIX:', v['final_fix'])
print('=' * 100)
print('CONFIRMED list sample:', json.dumps(d['confirmed'][:2], ensure_ascii=False)[:2000])
