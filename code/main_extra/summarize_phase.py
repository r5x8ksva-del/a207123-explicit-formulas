# -*- coding: utf-8 -*-
"""把工作流的 JSON 结果按子任务拆成可读文本（只用于主 Agent 阅读）。"""
import json
import sys

path, area = sys.argv[1], sys.argv[2]
part = sys.argv[3] if len(sys.argv) > 3 else 'all'
data = json.load(open(path, encoding='utf-8'))
res = data['result'] if isinstance(data, dict) and 'result' in data else data
if isinstance(res, str):
    res = json.loads(res)
for r in res:
    if not (r.get("area") == area or str(res.index(r)) == area):
        continue
    if part in ('all', 'head'):
        print('### AREA', area)
        print('STAGE:', r.get('stage_conclusion'))
        print('CHECK:', r.get('check_script'), 'runtime', r.get('check_runtime_seconds'))
        print('NOTES:', r.get('notes_file'), 'OTHER:', r.get('other_files'))
        print('--- errors_found:')
        for e in r.get('errors_found_in_draft_or_prompt', []):
            print(' *', e)
        print('--- failed_directions:')
        for e in r.get('failed_directions', []):
            print(' *', e)
        print('--- uncertainties:')
        for e in r.get('uncertainties', []):
            print(' *', e)
        print('--- check tail:')
        print(r.get('check_run_output_tail'))
    if part in ('all', 'claims'):
        print('--- claims:')
        for c in r.get('claims', []):
            print('[%s] %s :: %s' % (c['level'], c['id'], c['statement']))
            print('     proof:', c['proof_summary'][:1500])
            print('     range:', c['verified_range'][:600], '| check:', c['check_id'])
