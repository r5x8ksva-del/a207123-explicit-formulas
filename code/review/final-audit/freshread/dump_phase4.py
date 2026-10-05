import json
d=json.load(open(r'logs/phase4_final_audit_output.json',encoding='utf-8'))
out=d['out']
print('confirmed type', type(d['confirmed']), len(d['confirmed']))
for o in out:
    print('=== LENS', o['lens'], 'n findings', len(o['findings']))
    for i,f in enumerate(o['findings']):
        v=f.get('verdict',{})
        print('--- #%d file=%s sev=%s real=%s' % (i, f.get('file'), f.get('severity'), v.get('real')))
        print('  QUOTE:', (f.get('quote') or '')[:300].replace('\n',' '))
        print('  PROBLEM:', (f.get('problem') or '')[:600].replace('\n',' '))
        ff = v.get('final_fix')
        if ff: print('  FINAL_FIX:', str(ff)[:500].replace('\n',' '))
        why = v.get('reason') or v.get('why') or v.get('evidence')
        if why: print('  VREASON:', str(why)[:400].replace('\n',' '))
