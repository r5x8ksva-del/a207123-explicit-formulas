# -*- coding: utf-8 -*-
"""表 B 并入报告之后，同步 README.md、猜想总表.md 里「还没有并入报告」「报告尚未更新」等说法（2026-10-09）。

用法：py -3.14 code/main_extra/report_patches/patch_tableB_2026-10-09_docs.py <总 PASS 数> <用时秒> <峰值MB> <报告引用的核对 id 数> <tb 条数>
例：... 414 760 431 330 109
每处替换断言原文出现的次数；按字节读写（两个文件都是 LF）。README 里论文那一行属于另一个会话，不动。
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))


def patch(path, reps):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw, path
    s = raw.decode('utf-8')
    for old, new, cnt in reps:
        if isinstance(old, re.Pattern):
            s, n = old.subn(new, s)
        else:
            n = s.count(old)
            s = s.replace(old, new)
        assert n == cnt, (path, n, cnt, str(old)[:60])
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d rules ok' % (os.path.basename(path), len(reps)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    total, secs, peak, nids, ntb = (int(a) for a in sys.argv[1:6])
    mins = round(secs / 60)
    hist = '2026-10-09 已并入报告并登记进 verify_all 的 tb 模块，论文仍只并入了 A19–A21；见本节最后一条'

    # ---------------- README
    R = []
    R.append(('- Python 核对：`py -3.14 verify_all.py`（约 4.5 分钟，需要 numpy），逐条打印 PASS/FAIL；最后一次全量运行 14 个模块、332 PASS、0 FAIL（本地 2026-10-08 加入表 B 的模块 tb 之后，`logs/verify_all_final.log`，485 s，峰值 431 MB；加入前的最终日志另存为 `logs/verify_all_final_2026-10-07_before_tb.log`）。',
              '- Python 核对：`py -3.14 verify_all.py`（约 %d 分钟，需要 numpy），逐条打印 PASS/FAIL；最后一次全量运行 14 个模块、%d PASS、0 FAIL（本地 2026-10-09，tb 模块扩到 `code/tableB/` 的全部 13 个部分之后，`logs/verify_all_final.log`，%d s，峰值 %d MB；2026-10-08 只含 b1、b3、b2 时 332 PASS，日志 `logs/verify_all_2026-10-08_tableB.log`；加入 tb 前的最终日志另存为 `logs/verify_all_final_2026-10-07_before_tb.log`）。' % (mins, total, secs, peak), 1))
    R.append(('（空闲时约 4.5 分钟，机器负载高时更长；需要 numpy，rv2 模块没有纯 Python 回退）',
              '（空闲时约 %d 分钟，机器负载高时更长；需要 numpy，rv2 与 tb 模块没有纯 Python 回退）' % mins, 1))
    R.append(('verify_all 的 tb 模块只登记了其中的 b1、b3、b2',
              'verify_all 的 tb 模块 2026-10-08 只登记了其中的 b1、b3、b2，2026-10-09 并入报告时扩到全部 13 个部分（默认模式，%d 条）' % ntb, 1))
    R.append(('- **研究交付物已完成**：`报告.md` + `verify_all.py`。最后一次全量验证：14 个模块、332 PASS、0 FAIL（本地 2026-10-08，加入表 B 的模块 tb 之后，`logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行，峰值 431 MB，用时 485 s；此前 13 个模块、305 PASS）；报告引用的 247 个核对 id 全部 PASS。',
              '- **研究交付物已完成**：`报告.md` + `verify_all.py`。最后一次全量验证：14 个模块、%d PASS、0 FAIL（本地 2026-10-09，表 B 并入报告、tb 模块扩到 13 个部分之后，`logs/verify_all_final.log`，经 `code/main_extra/run_guarded.sh` 带内存保护运行，峰值 %d MB，用时 %d s；2026-10-08 为 332 PASS，此前 13 个模块、305 PASS）；报告引用的 %d 个核对 id 全部 PASS。' % (total, peak, secs, nids), 1))
    R.append(('**还没有并入报告与论文**（报告 T5.3(6)、T2.6(i) 补充、T3.4(5)、④ 与论文的开放问题一节仍写着「猜想」），也没有登记进 verify_all，没有形式化。',
              '当时**还没有并入报告与论文**（报告 T5.3(6)、T2.6(i) 补充、T3.4(5)、④ 与论文的开放问题一节仍写着「猜想」），也没有登记进 verify_all，没有形式化（%s）。' % hist, 1))
    R.append(('b7、b7_borel、b11 仍只在 `code/tableB/run_all.py`。`报告.md` 还没有并入这三条。',
              'b7、b7_borel、b11 当时仍只在 `code/tableB/run_all.py`。`报告.md` 当时还没有并入这三条（2026-10-09 已并入，tb 也扩到全部 13 个部分；见本节最后一条）。', 1))
    R.append((re.compile(r'同样\*\*还没有并入报告与论文\*\*((?:（[^）]*）)?)，没有登记进 verify_all，没有形式化。'),
              lambda m: '当时同样**还没有并入报告与论文**%s，没有登记进 verify_all，没有形式化（%s）。' % (m.group(1), hist), 6))
    old_end = '- 数学上未解的问题与完成度见 `猜想总表.md` 表 B；完整的待办与优先级见 `ROADMAP.md`。'
    R.append((old_end,
              '- **表 B 并入报告（2026-10-09）**：用户对「下一步把 A28–A30 并入报告」答「按照你的想法来」。主 Agent 发现报告连 A19–A27 也没有并入，所以把 `猜想总表.md` 的 A19–A30 与 B11 的扩展一起并入 `报告.md`：② 中 T2.5(4)（新）、T2.6(i)(iii)、T2.8(3)、T3.3(3)、T3.4(4)(5)、T4.2(2)、T5.3(2)(5)(6)(7) 改写等级，补上陈述、证明要点、复核者与核对 id；①（仍是 13 行）、④A、⑥（含完成度表）、⑤ 与开头同步。补丁脚本 `code/main_extra/report_patches/patch_tableB_2026-10-09.py`（36 处）、`patch_tableB_2026-10-09_run.py`（⑤ 与开头的运行数字）、`patch_tableB_2026-10-09_docs.py`（本 README 与猜想总表）。verify_all 的 tb 模块扩到 `code/tableB/` 的全部 13 个部分（默认模式，%d 条；b8 的 k≤300、b9 的 i≤40 仍用 `--full` 单独运行），全量运行 14 个模块、%d PASS、0 FAIL（%d s，峰值 %d MB）；`assemble_report.py` 的核对 id 交叉检查加入 tb，报告引用的 %d 个核对 id 全部 PASS。独立复核者 s16-report（`notes/review/s16-report-review.md`）逐处核对了 36 处改动。**论文没有动**：论文正文写的「332 automated checks」现在过时（verify_all 已是 %d 条），要在论文那边同步。\n' % (ntb, total, secs, peak, nids, total) + old_end, 1))
    patch(os.path.join(ROOT, 'README.md'), R)

    # ---------------- 猜想总表
    T = []
    T.append(('这几条**还没有并入报告与论文**，也没有登记进 verify_all，所以本表从这里起也记录 notes 里尚未进报告的新证明。',
              '这几条当时**还没有并入报告与论文**，也没有登记进 verify_all，所以本表从这里起也记录 notes 里尚未进报告的新证明（2026-10-09 已并入报告并登记进 verify_all 的 tb 模块；论文只并入了 A19–A21）。', 1))
    T.append(('同样**还没有并入报告与论文**，没有登记进 verify_all。',
              '当时同样**还没有并入报告与论文**，没有登记进 verify_all（2026-10-09 已并入报告并登记进 verify_all 的 tb 模块；论文只并入了 A19–A21）。', 5))
    T.append(('（报告尚未更新）', '（2026-10-09 已并入报告）', 12))
    T.append(('A30 为 2026-10-09 新增，均尚未并入报告；A19–A21 已于 2026-10-08 并入论文，A22–A30 没有并入）',
              'A30 为 2026-10-09 新增；2026-10-09 均已并入报告并登记进 verify_all 的 tb 模块；A19–A21 已于 2026-10-08 并入论文，A22–A30 没有并入论文）', 1))
    T.append(('（都是书面证明 + 核对，未形式化，尚未并入报告；', '（都是书面证明 + 核对，未形式化；2026-10-09 已并入报告；', 1))
    old_corr = 'A24–A27（B4、B5 的精确化部分，2026-10-08）也没有写进报告：T2.6 小结、T2.8(3)、④A.1、④A.2 与论文的开放问题一节仍是旧说法。'
    T.append((old_corr, old_corr + '**2026-10-09 更新**：以上这些（连同 A28–A30 与 B11 的扩展）都已并入报告：② 的 T2.5(4)（新）、T2.6(i)(iii)、T2.8(3)、T3.3(3)、T3.4(4)(5)、T4.2(2)、T5.3(2)(5)(6)(7) 改写了等级与内容，④A 的第 1–4、6 条按现状改写，⑥ 与完成度表同步；对应的程序核对是 verify_all 的 tb 模块（%d 条）。论文的开放问题一节仍是旧说法（论文只并入了 A19–A21）。' % ntb, 1))
    j_anchor = '- （2026-10-09 更新，B13）'
    i0 = open(os.path.join(ROOT, '猜想总表.md'), encoding='utf-8').read().index(j_anchor)
    T.append((j_anchor, '- （2026-10-09 更新，并入报告）表 A 的 A19–A30 与 B11 的扩展已全部并入报告与 verify_all（见「与报告的对应」）。报告里这些条目的等级按本表：计算机辅助的有限计算、没有复核者的部分（notes/07、notes/10 的 9≤d≤100）都在条目里注明。下一步若要并入论文，A22–A30 要写进论文的开放问题一节或新节，论文里的核对条数（332）也要同步。\n' + j_anchor, 1))
    assert i0 > 0
    patch(os.path.join(ROOT, '猜想总表.md'), T)


if __name__ == '__main__':
    main()
