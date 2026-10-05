# -*- coding: utf-8 -*-
"""check_rv2：把第二轮复核者 x1 的两个独立脚本纳入一键核对（它们不导入 core，只用 fractions/整数/numpy）。

  rv2-x1-r1  留数元闭式、E 部分在纤维 u=1/2 上的统一阻碍（m=2..34）、c2b 证书数值复算等
             （code/review/x1-single-sum/r1_numfield_residues.py）
  rv2-x1-r2  两族 u 型：U 纤维 1 的解在 |a|,|b|<=6000 内只有 14 组且与纤维 2 无公共解；
             E 的两项 u 型：|a|,|b|<=1500 内纤维 1、2、3 无公共解
             （code/review/x1-single-sum/r2_two_family.py，参数 6000 1500）
每个子脚本自己逐条打印 PASS/FAIL 并以「SUMMARY rX fail=0」结束；这里只检查退出码、FAIL 行与 SUMMARY 行。
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
X1 = os.path.join(ROOT, 'code', 'review', 'x1-single-sum')
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
results = []


def report(cid, ok, desc):
    results.append(ok)
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def run(script, args, tag):
    env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
    t = time.time()
    p = subprocess.run([sys.executable, os.path.join(X1, script)] + args, cwd=X1, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode('utf-8', errors='replace')
    lines = out.splitlines()
    n_pass = sum(1 for ln in lines if ln.startswith('PASS '))
    n_fail = sum(1 for ln in lines if ln.startswith('FAIL '))
    summ = [ln for ln in lines if ln.startswith('SUMMARY ')]
    ok = p.returncode == 0 and n_fail == 0 and n_pass > 0 and summ and summ[-1].endswith('fail=0')
    with open(os.path.join(ROOT, 'logs', 'rv2_%s.log' % tag), 'w', encoding='utf-8') as f:
        f.write(out)
    return ok, n_pass, time.time() - t


t0 = time.time()
ok, n, dt = run('r1_numfield_residues.py', [], 'x1_r1')
report('rv2-x1-r1', ok, '复核者 x1 的 r1：留数元闭式、E 部分纤维 u=1/2 的统一阻碍（m=2..34）、证书复算；子脚本 %d 条 PASS（%.1fs，输出 logs/rv2_x1_r1.log）' % (n, dt))
ok, n, dt = run('r2_two_family.py', ['6000', '1500'], 'x1_r2')
report('rv2-x1-r2', ok, '复核者 x1 的 r2：U 两族 |a|,|b|<=6000 无表示（m>=2），E 两项 |a|,|b|<=1500 无表示（m>=3）；子脚本 %d 条 PASS（%.1fs，输出 logs/rv2_x1_r2.log）' % (n, dt))

npass = sum(results)
nfail = len(results) - npass
print('SUMMARY rv2 pass=%d fail=%d (%.1fs)' % (npass, nfail, time.time() - t0))
sys.exit(0 if nfail == 0 else 1)
