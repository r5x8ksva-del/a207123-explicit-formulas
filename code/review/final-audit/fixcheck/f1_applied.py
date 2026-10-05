# -*- coding: utf-8 -*-
"""只读：用 ast 解析 patch_final_audit.py 中的 (原文, 新文) 对，检查是否已落到当前 report_parts / README，
并检查 报告.md 是否等于 report_parts 的拼接（不执行补丁脚本）。"""
import ast, os, glob
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = os.path.join(ROOT, 'notes', 'report_parts')
src = open(os.path.join(ROOT, 'code', 'main_extra', 'report_patches', 'patch_final_audit.py'), encoding='utf-8').read()
tree = ast.parse(src)
calls = []
for node in ast.walk(tree):
    if isinstance(node, ast.Call) and getattr(node.func, 'id', None) == 'patch':
        target = node.args[0]
        # P + 'xx.md'  or ROOT + r'\README.md'
        if isinstance(target, ast.BinOp):
            right = target.right.value
            left = target.left.id
            path = os.path.join(P, right) if left == 'P' else ROOT + right
        pairs = [(e.elts[0].value, e.elts[1].value) for e in node.args[1].elts]
        calls.append((node.lineno, path, pairs))
calls.sort()
tot = 0
for lineno, path, pairs in calls:
    s = open(path, encoding='utf-8').read()
    for i, (a, b) in enumerate(pairs):
        tot += 1
        na, nb = s.count(a), s.count(b)
        flag = 'OK' if (nb == 1 and (na == 0 or a in b)) else 'CHECK'
        print(f"{flag} {os.path.basename(path)} pair{i+1}: old_count={na} new_count={nb}")
print('total pairs', tot)
# 拼接检查
parts = sorted(glob.glob(os.path.join(P, '*.md')))
cat_variants = {}
for sep in ['', '\n', '\n\n']:
    cat_variants[repr(sep)] = sep.join(open(p, encoding='utf-8').read() for p in parts)
rep = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read()
for k, v in cat_variants.items():
    print('concat sep', k, 'equal' if v == rep else f'diff (len {len(v)} vs {len(rep)})')
