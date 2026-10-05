# -*- coding: utf-8 -*-
"""任务 C 一键核对：依次运行 code/checks/check_*.py，汇总 PASS / FAIL。

用法（Windows）：  py -3.14 verify_all.py            # 全部
                  py -3.14 verify_all.py c1 c4      # 只跑指定模块
每个子模块逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY <area> pass=<n> fail=<n>」。
本脚本把所有行原样转印，并在最后给出总表；任何 FAIL、子模块异常退出或缺少 SUMMARY 都算失败，退出码 1。
"""
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
CHECKS = os.path.join(ROOT, 'code', 'checks')
ORDER = ['c0', 'c1', 'c2a', 'c2b', 'c3a', 'c3b', 'c4', 'c5a', 'c5b', 'rv', 'rv2']


def main(argv):
    if not sys.stdout.isatty():          # 重定向到文件/管道时统一用 UTF-8，避免 GBK 乱码
        sys.stdout.reconfigure(encoding='utf-8')
    files = sorted(f for f in os.listdir(CHECKS) if re.fullmatch(r'check_[a-z0-9_]+\.py', f))
    areas = [f[len('check_'):-3] for f in files]
    areas.sort(key=lambda a: (ORDER.index(a) if a in ORDER else len(ORDER), a))
    if argv:
        areas = [a for a in areas if a in argv]
    env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
    rows, total_pass, total_fail, bad = [], 0, 0, []
    t_all = time.time()
    for a in areas:
        path = os.path.join(CHECKS, 'check_%s.py' % a)
        t0 = time.time()
        print('=' * 72)
        print('>>> check_%s.py' % a, flush=True)
        proc = subprocess.run([sys.executable, path], cwd=ROOT, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out = proc.stdout.decode('utf-8', errors='replace')
        print(out.rstrip(), flush=True)
        dt = time.time() - t0
        n_pass = sum(1 for ln in out.splitlines() if ln.startswith('PASS '))
        n_fail = sum(1 for ln in out.splitlines() if ln.startswith('FAIL '))
        has_summary = any(ln.startswith('SUMMARY ') for ln in out.splitlines())
        ok = (proc.returncode == 0 and n_fail == 0 and has_summary and n_pass > 0)
        if not ok:
            bad.append(a)
        total_pass += n_pass
        total_fail += n_fail
        rows.append((a, n_pass, n_fail, proc.returncode, has_summary, dt, ok))
    print('=' * 72)
    print('%-6s %6s %6s %5s %8s %8s  %s' % ('area', 'pass', 'fail', 'rc', 'summary', 'secs', 'status'))
    for a, p, f, rc, hs, dt, ok in rows:
        print('%-6s %6d %6d %5d %8s %8.1f  %s' % (a, p, f, rc, 'yes' if hs else 'NO', dt, 'PASS' if ok else 'FAIL'))
    print('-' * 72)
    print('TOTAL pass=%d fail=%d modules=%d failed_modules=%s  (%.1fs)' %
          (total_pass, total_fail, len(rows), ','.join(bad) or '-', time.time() - t_all))
    print('OVERALL:', 'PASS' if not bad and rows else 'FAIL')
    return 0 if (not bad and rows) else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
