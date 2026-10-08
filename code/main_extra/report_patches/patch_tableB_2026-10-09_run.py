# -*- coding: utf-8 -*-
"""表 B 并入报告（2026-10-09）的第二步：verify_all 全量运行之后，从 logs/verify_all_final.log 与 logs/guarded_runs.log
读出总表、用时与峰值，填进 ⑤（09_code.md）与开头（00_head.md）。按字节读写，保留 CRLF。

用法（在任务 C 根目录，verify_all 跑完之后）：py -3.14 code/main_extra/report_patches/patch_tableB_2026-10-09_run.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')


def run_numbers():
    log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read().replace('\r\n', '\n')
    lines = log.split('\n')
    i0 = max(i for i, l in enumerate(lines) if l.startswith('area '))
    i1 = max(i for i, l in enumerate(lines) if l.startswith('OVERALL:'))
    block = lines[i0:i1 + 1]
    assert block[-1] == 'OVERALL: PASS'
    m = re.match(r'TOTAL pass=(\d+) fail=0 modules=14 failed_modules=-\s+\(([\d.]+)s\)', block[-2])
    assert m, block[-2]
    total, secs = int(m.group(1)), float(m.group(2))
    tb = [l for l in block if l.startswith('tb ')]
    assert len(tb) == 1
    ntb = int(tb[0].split()[1])
    g = [l for l in open(os.path.join(ROOT, 'logs', 'guarded_runs.log'), encoding='utf-8').read().split('\n')
         if 'verify_all.py > logs/verify_all_final.log' in l]
    pk = re.search(r'PEAK=(\d+)', g[-1])
    assert pk and '| exit 0 |' in g[-1], g[-1]
    return block, total, secs, ntb, int(pk.group(1))


def patch(name, reps):
    p = os.path.join(PARTS, name)
    raw = open(p, 'rb').read()
    crlf = raw.count(b'\r\n')
    assert crlf == raw.count(b'\n')
    s = raw.decode('utf-8').replace('\r\n', '\n')
    for old, new in reps:
        assert s.count(old) == 1, (name, s.count(old), old[:60])
        s = s.replace(old, new)
    out = s.replace('\n', '\r\n').encode('utf-8') if crlf else s.encode('utf-8')
    open(p, 'wb').write(out)
    print('%s: %d edits' % (name, len(reps)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    block, total, secs, ntb, peak = run_numbers()
    mins = round(secs / 60)
    print('verify_all: total=%d secs=%.1f tb=%d peak=%d MB' % (total, secs, ntb, peak))

    # ---- ⑤
    s09 = open(os.path.join(PARTS, '09_code.md'), 'rb').read().decode('utf-8').replace('\r\n', '\n')
    a = s09.index('**最终一次运行**（本地 2026-10-07，加入 rv4 之后，')
    b = s09.index('OVERALL: PASS\n```', a) + len('OVERALL: PASS\n```')
    old_run = s09[a:b]
    new_run = ('**最终一次运行**（本地 2026-10-09，表 B 并入报告、tb 模块扩到 `code/tableB/` 的 13 个部分之后，完整输出 `logs/verify_all_final.log`，'
               '经 `code/main_extra/run_guarded.sh` 带内存保护运行，整棵进程树峰值 %d MB；之前各次的日志见下面「其他重要文件」的最后一条）：\n\n```\n%s\n```'
               % (peak, '\n'.join(block)))
    patch('09_code.md', [
        ('**13 个核对模块**（除 check_rv2.py、check_rv3.py、check_rv4.py 外，',
         '**14 个核对模块**（除 check_rv2.py、check_rv3.py、check_rv4.py、check_tb.py 外，'),
        ('以自写的 DP 作真值，其余是 Q[x]/(b_i) 中的精确代数）',
         '以自写的 DP 作真值，其余是 Q[x]/(b_i) 中的精确代数；check_tb.py 依次运行 `code/tableB/` 的 13 个核对脚本，各脚本自带对照（多数对照按定义写的 DP 或已证明的递推），其余是精确代数、证书计算与少数标明的数值佐证）'),
        ('见 `logs/main_t26ii_check_reverse.log` | 9 |',
         '见 `logs/main_t26ii_check_reverse.log` | 9 |\n'
         '| `check_tb.py` | 表 B 的后续结论（猜想总表 A19–A30 与 B11 的扩展，2026-10-07 晚至 10-09；见 ② 各条标注「2026-10-0x 补证」处）：依次运行 `code/tableB/check_b1.py`、b3、b2、b7、b7_borel、b11、b6、b4、b5、b5_skel、b8、b9、b13（默认模式；b8 的 k≤300、b9 的 i≤40 用 `--full` 单独运行，日志 `logs/tableB_check_b8_full.log`、`logs/tableB_check_b9_full.log`），原样转印各条 PASS/FAIL；b7_borel 各条与 b6-mono、b9-osc、b13-data 是数值佐证。2026-10-08 只含 b1、b3、b2（27 条），2026-10-09 扩到 13 个部分 | %d |' % ntb),
        (old_run, new_run),
        ('、`logs/verify_all_final.log`（最终，2026-10-07 加入 rv4 之后，13 个模块 305 条）。',
         '、`logs/verify_all_final_2026-10-07_before_tb.log`（2026-10-07 加入 rv4 之后，13 个模块 305 条）、`logs/verify_all_2026-10-08_tableB.log`（2026-10-08 加入 tb（b1、b3、b2）之后，14 个模块 332 条）、`logs/verify_all_final.log`（最终，2026-10-09 tb 扩到 13 个部分之后，14 个模块 %d 条）。' % total),
    ])

    # ---- 开头
    patch('00_head.md', [
        ('（原始输出 logs/phase4_final_audit_output.json、logs/phase4b_recheck_output.json；见 ④B.13）。',
         '（原始输出 logs/phase4_final_audit_output.json、logs/phase4b_recheck_output.json；见 ④B.13）。2026-10-09 并入了表 B 的后续结论（2026-10-07 晚至 10-09 补证，`猜想总表.md` 的 A19–A30 与 B11 的扩展；每条有一到两位对抗性复核者，个别部分没有复核者，都在条目里注明），写在 ② 各条标注「2026-10-0x 补证」的地方，①、④、⑤、⑥ 同步更新；对应的程序核对是 verify_all 的第 14 个模块 tb。'),
        ('空闲时约 4.5 分钟（2026-10-07 实测；机器负载高时更长），共 13 个模块。',
         '约 %d 分钟（2026-10-09 实测 %d s；机器负载高时更长），共 14 个模块、%d 条检查。' % (mins, round(secs), total)),
        ('缺 numpy 时 rv2 FAIL、verify_all 退出码为 1；其余 12 个模块只依赖标准库',
         '缺 numpy 时 rv2 FAIL、verify_all 退出码为 1；tb（转印 `code/tableB/` 的 13 个核对脚本）也需要 numpy；其余 12 个模块只依赖标准库'),
    ])
    print('RUN_NUMBERS %d %d %d %d' % (total, round(secs), peak, ntb))


if __name__ == '__main__':
    main()
