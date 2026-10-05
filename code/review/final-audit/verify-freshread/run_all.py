# -*- coding: utf-8 -*-
"""verify-freshread：依次运行 v0_quotes.py、v1_all.py，并附逐条判定摘要，输出到 logs/final_audit_verify-freshread.log。只读。"""
import subprocess
import sys
import time

ROOT = 'C:/Users/Michael Song/Desktop/私人办公/A207123-任务C-显式公式与母函数'
HERE = ROOT + '/code/review/final-audit/verify-freshread/'
OUT = ROOT + '/logs/final_audit_verify-freshread.log'

VERDICTS = [
    (0, True, '01_summary 写「按定义直接计数只核到 k≤9」，但 c1_extended.log E3 已按 DFS 定义核 k=10,11；与 T1.4、⑥ 不一致'),
    (1, True, '④B.11「需要 k≤60」仍是 phase4 已判定无据的必要性说法；证据只说明 k≤30 不够、k≤60 足够（示例对 K=35 已矛盾）'),
    (2, True, '⑤ 总表（217.7 s）与它所指的 logs/verify_all_final.log（17:22 重跑，271.0 s）各模块耗时都不一致；PASS 数一致'),
    (3, True, '所引 6 次运行之一的 verify_all_final.log 现为 H 2.999 s、F3 3.015 s，超出「约 0.2–2.4 s」；倍数 114–1202 仍符合约 100–1000'),
    (4, True, '00_head 只写三轮；第四轮（phase4，5 个审计视角 + 逐条复核，58 条确认）在 ④B.13 被提到但无交代，phase3/phase4 原始输出未被引用'),
    (5, True, 'T1.0（c1_extended E2）与 T4.2（c4_explore9b_d4）的扩展范围来自第一轮脚本，无日志路径；T3.4(5) Gevrey 数据来自 r-c3a 亦无路径；00_head 的来源描述不全'),
    (6, True, 'c5a-roots、c5a-cm-repr 含 decimal 数值部分（日志 [numeric]），核对行未注「数值」，违反 00_head 规则'),
    (7, True, 'T5.3(1) 标【已证明】但无证明也无笔记指针；全部断言独立重算 k≤30 成立；证明在 c5a §4.1/§4.6/§4.7'),
    (8, True, 'α′、β*、α*、β′、q_{ab} 在报告中未定义（只在 c3b §6），且 q_{α*b} 与 N 的下标 q 同名'),
    (9, True, '摘要第 7 条无主语，紧接「F 与 N」，可读成对 N 也成立；N 的关系理想由 L_N 生成'),
    (10, False, '零检验形状对与目标数列无关（E、U 的示例对完全相同），「m=5,6 各有 59/1024 个」按 m 计数是准确的'),
    (11, False, '(iv) 的形状公式把 α、β、γ、δ、ε、ζ 就地写明，不存在误读成 (i) 记号的可能；属记号风格'),
    (12, True, 'm_1、m_2 在报告中未定义（c5b 笔记 T4 中为 ⌈n/2⌉、⌊n/2⌋），E 在 T3.8 是 m 方向移位'),
    (13, True, 'ar5iv、Wikipedia 读的是其他文献正文与页面，不是 Lipshitz 1989 的元数据；Semantic Scholar 读到的是引言'),
]


def main():
    with open(OUT, 'w', encoding='utf-8') as f:
        f.write('# final_audit_verify-freshread  %s\n' % time.strftime('%Y-%m-%d %H:%M:%S'))
        f.write('# 对抗性复核 freshread 的 14 条发现（只读；脚本在 code/review/final-audit/verify-freshread/）\n')
        for script in ['v0_quotes.py', 'v1_all.py']:
            f.write('\n######## %s ########\n' % script)
            f.flush()
            r = subprocess.run([sys.executable, HERE + script], capture_output=True, text=True, encoding='utf-8',
                               env={**__import__('os').environ, 'PYTHONUTF8': '1'})
            f.write(r.stdout)
            if r.stderr:
                f.write('\n[stderr]\n' + r.stderr)
            f.write('\n[rc=%d]\n' % r.returncode)
        f.write('\n######## 判定摘要 ########\n')
        for i, real, why in VERDICTS:
            f.write('#%d real=%s  %s\n' % (i, real, why))
    print(open(OUT, encoding='utf-8').read()[-3000:])


if __name__ == '__main__':
    main()
