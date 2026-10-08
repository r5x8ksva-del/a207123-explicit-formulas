# -*- coding: utf-8 -*-
"""表 B 新结论的一键核对（2026-10-07；2026-10-08 加入 b2、b7_borel、b11）：依次运行 check_b1.py、check_b2.py、check_b3.py、check_b7.py、
check_b7_borel.py（数值佐证）、check_b11.py（d<=100）、check_b6.py（2026-10-08 加入；b6-mono 等几条是数值佐证）、
check_b4.py、check_b5.py（2026-10-08 加入）、check_b5_skel.py（2026-10-08 加入，notes/14）、check_b8.py、check_b9.py（2026-10-08 晚加入，
notes/15、16；默认模式）、check_b13.py（2026-10-09 加入，notes/17），汇总 PASS / FAIL。

用法（在任务 C 根目录）：  py -3.14 code/tableB/run_all.py
带内存保护：  GUARD_CAP_MB=1500 code/main_extra/run_guarded.sh logs/tableB_run_all.log py -3.14 code/tableB/run_all.py
（实测峰值约 0.4 GB；2026-10-07 的三个部分约半分钟，2026-10-08 加入的三个部分另需约 3 分钟，主要是 check_b11.py；之后加入的 b6、b4、b5、b5_skel 共约 2 分钟；2026-10-08 加入 b5_skel 后全部 10 个部分约 5 分钟；同日深夜加入 b8、b9（默认模式）后 12 个部分 101 条，约 5.5 分钟；2026-10-09 加入 b13（约 1 秒）后 13 个部分 109 条。）
格式与 verify_all.py 相同；暂未登记为 verify_all 的模块，因为报告、README、论文里写的是「13 个模块、305 PASS」，
这些结论并入报告时再把它复制为 code/checks/check_tb.py。需要 numpy（只用来求近似根，判定全部是精确运算）。
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
PARTS = ['b1', 'b2', 'b3', 'b7', 'b7_borel', 'b11', 'b6', 'b4', 'b5', 'b5_skel', 'b8', 'b9', 'b13']  # b6：2026-10-08 加入（精确部分 + RK4 数值佐证，约 15 s）
# b4、b5：2026-10-08 加入（notes/12、notes/13；b4 约 20 s、b5 约 70 s，其中 b4-two、b5-twocert 用 numpy 并导入 check_b2.py 的筛法）
# b5_skel：2026-10-08 加入（notes/14 骨架型两层和；只用标准库，几秒）
# b8、b9：2026-10-08 晚加入（notes/15、16；默认模式各约 30 s、15 s，b8 扫描 k<=150、b9 认证门槛 i<=20；
#   完整范围 k<=300、i<=40 用 check_b8.py --full、check_b9.py --full 单独运行，日志 logs/tableB_check_b8_full.log、_b9_full.log）
# b13：2026-10-09 加入（notes/17，t<0 时 f_k(t) 的精确 Gevrey 常数与 (★)；需要 numpy，约 1 s）


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1')
    rows, bad, tp, tf = [], [], 0, 0
    t_all = time.time()
    for a in PARTS:
        t0 = time.time()
        print('=' * 72)
        print('>>> check_%s.py' % a, flush=True)
        proc = subprocess.run([sys.executable, os.path.join(HERE, 'check_%s.py' % a)], cwd=ROOT, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out = proc.stdout.decode('utf-8', errors='replace')
        print(out.rstrip(), flush=True)
        n_pass = sum(1 for ln in out.splitlines() if ln.startswith('PASS '))
        n_fail = sum(1 for ln in out.splitlines() if ln.startswith('FAIL '))
        has_summary = any(ln.startswith('SUMMARY ') for ln in out.splitlines())
        ok = proc.returncode == 0 and n_fail == 0 and has_summary and n_pass > 0
        if not ok:
            bad.append(a)
        tp += n_pass
        tf += n_fail
        rows.append((a, n_pass, n_fail, proc.returncode, time.time() - t0, ok))
    print('=' * 72)
    for a, p, f, rc, dt, ok in rows:
        print('%-4s pass=%-3d fail=%-3d rc=%d %6.1fs  %s' % (a, p, f, rc, dt, 'PASS' if ok else 'FAIL'))
    print('TOTAL pass=%d fail=%d parts=%d failed=%s  (%.1fs)' % (tp, tf, len(rows), ','.join(bad) or '-',
                                                              time.time() - t_all))
    print('OVERALL:', 'PASS' if not bad else 'FAIL')
    return 0 if not bad else 1


if __name__ == '__main__':
    sys.exit(main())
