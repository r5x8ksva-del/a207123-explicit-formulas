# -*- coding: utf-8 -*-
"""freshread 方向（通读复查）：依次运行本目录下的只读核对脚本，汇总输出到 logs/final_audit_freshread.log。
不修改报告、笔记或代码。用法：PYTHONUTF8=1 py -3.14 code/review/final-audit/freshread/run_all.py
"""
import os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
OUT = os.path.join(ROOT, 'logs', 'final_audit_freshread.log')
SCRIPTS = [
    ('ids_check.py', '报告引用的核对 id 是否都在 logs/verify_all_final.log 中以 PASS 出现；未被引用的 PASS id'),
    ('paths_check.py', '报告引用的 logs/、code/、notes/、data/ 路径是否存在'),
    ('xref_check.py', '定理编号与子条目交叉引用是否存在'),
    ('confirmed_check.py', 'phase4 已确认的 58 条问题：原引文是否还在、修订文字是否落地'),
    ('quotes_check.py', '本方向各条发现的原文引用是否为当前文件的唯一精确子串；重跑后 verify_all_final.log 的总表与 bench 行'),
]
env = dict(os.environ, PYTHONUTF8='1')
with open(OUT, 'w', encoding='utf-8') as f:
    f.write('# freshread final audit, %s\n' % time.strftime('%Y-%m-%d %H:%M:%S'))
    for s, desc in SCRIPTS:
        f.write('\n' + '=' * 72 + '\n>>> %s ：%s\n' % (s, desc))
        p = subprocess.run([sys.executable, os.path.join(HERE, s)], cwd=ROOT, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        f.write(p.stdout.decode('utf-8', 'replace'))
        f.write('[rc=%d]\n' % p.returncode)
print('wrote', OUT)
