# -*- coding: utf-8 -*-
"""check_rv3：把报告 ⑥ 前两处所依赖的复核者计算核对纳入一键核对（2026-10-07 加固 ⑥ 时加入）。

  rv3-c4ii-r6  T4.3(6) 高次系数的一般结构：由 T4.3(7) 的闭式精确算出 A_j ∈ Q[u,L]（j<=14），
               核对指标界、三角化得到的 π_{j,i} 与真实系数（q<=60）、两个子断言、表 6
               （复核者 r-c4ii 的 code/review/r-c4ii/r6_structure.py）
  rv3-c3a-r2   T3.4(2) K 的闭式 K=Γ(−λ)[1+λx⁵J]：与 K 的定义在 7 个 x 上比较、上下界、
               端到端 I−𝒮 与闭式比较等，decimal 高精度数值（复核者 r-c3a 的 code/review/r-c3a/r2_numeric.py）
  rv3-s6-t436-a  第三轮复核者 s6-t436 的独立证明所用的核对（code/review/s6-t436/）：t1 锚点、t2 证明里各引理的
               逐式核对、t4 T4.3(7) 闭式到 z^30（含阴性对照）
  rv3-s6-t436-b  同一复核者的结构核对：t3 按证明的构造法求 π_{j,i}（j<=40）并与真实 a_{q,j}（q<=300）比较，
               只用命题形状的拟合法 j<=24 与构造法逐系数相同；t5 与表 6 比较；t6 与 r-c4ii 日志里的 j=9..14 比较
  rv3-s6-t342-K  第三轮复核者 s6-t342 的数值核对（code/review/s6-t342/，自写 decimal 与求积，不复用 r-c3a 的实现）：
               K 的定义与闭式在 13 个 x（0.18..0.9，含抵消约 240 位的 x=0.18）上比较；x=0.15 一点要 564 位、约 50 s，
               只留在复核日志 logs/review_s6-t342_t1_K_x015.log
  rv3-s6-t342-e  同一复核者：端到端 I−𝒮 与闭式在 11 组 (x,t) 上比较；推论 1<K/Γ(−λ)<2−x、K 的符号在 105 个 x 上扫描
子脚本都不导入 core，只用 Python 标准库。r-c4ii、r-c3a 的脚本逐条打印 PASS/FAIL 并以「SUMMARY … fail=0」结束；
s6-t436 的脚本逐条打印「[OK ] …」或「[BAD] …」，最后一行是 ALL_OK 或 SOME_BAD；s6-t342 的脚本打印 PASS/FAIL
（t3 的表格把 PASS/FAIL 写在行尾），最后一行是「SUMMARY tN: … FAIL=0 …」。
这里只检查退出码与这些标记行，子脚本的完整输出写进 logs/rv3_<tag>.log。
"""
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
REVIEW = os.path.join(ROOT, 'code', 'review')
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
results = []


def report(cid, ok, desc):
    results.append(ok)
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


ENV = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONUTF8='1', PYTHONDONTWRITEBYTECODE='1')


def run(subdir, script, args, tag):
    env = ENV
    t = time.time()
    p = subprocess.run([sys.executable, os.path.join(REVIEW, subdir, script)] + args,
                       cwd=os.path.join(REVIEW, subdir), env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode('utf-8', errors='replace')
    lines = out.splitlines()
    n_pass = sum(1 for ln in lines if ln.startswith('PASS '))
    n_fail = sum(1 for ln in lines if ln.startswith('FAIL '))
    summ = [ln for ln in lines if ln.startswith('SUMMARY ')]
    ok = p.returncode == 0 and n_fail == 0 and n_pass > 0 and bool(summ) and summ[-1].rstrip().endswith('fail=0')
    with open(os.path.join(ROOT, 'logs', 'rv3_%s.log' % tag), 'w', encoding='utf-8') as f:
        f.write(out)
    return ok, n_pass, n_fail, time.time() - t


def run_okbad(subdir, scripts, tag):
    """s6-t436 格式：逐条「[OK ] …」/「[BAD] …」，最后一行 ALL_OK / SOME_BAD。
    这些脚本按根目录的相对路径读日志（t6 读 logs/review_r-c4ii_r6_structure.log），所以 cwd 取根目录。"""
    env = ENV
    t = time.time()
    outs, ok, n_ok, n_bad = [], True, 0, 0
    for script, args in scripts:
        p = subprocess.run([sys.executable, os.path.join(REVIEW, subdir, script)] + args, cwd=ROOT, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out = p.stdout.decode('utf-8', errors='replace')
        lines = [ln for ln in out.splitlines() if ln.strip()]
        k_ok = sum(1 for ln in lines if ln.startswith('[OK ]'))
        k_bad = sum(1 for ln in lines if ln.startswith('[BAD]'))
        good = p.returncode == 0 and k_bad == 0 and k_ok > 0 and bool(lines) and lines[-1].startswith('ALL_OK')
        ok = ok and good
        n_ok += k_ok
        n_bad += k_bad
        outs.append('### %s %s（退出码 %d）\n%s' % (script, ' '.join(args), p.returncode, out))
    with open(os.path.join(ROOT, 'logs', 'rv3_%s.log' % tag), 'w', encoding='utf-8') as f:
        f.write('\n'.join(outs))
    return ok, n_ok, n_bad, time.time() - t


def run_summary(subdir, scripts, tag):
    """s6-t342 格式：PASS/FAIL 写在行首（t3 的表格写在行尾），最后一行「SUMMARY tN: … FAIL=0 …」。"""
    t = time.time()
    outs, ok, n_ok, n_bad = [], True, 0, 0
    for script, args in scripts:
        p = subprocess.run([sys.executable, os.path.join(REVIEW, subdir, script)] + args,
                           cwd=os.path.join(REVIEW, subdir), env=ENV,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out = p.stdout.decode('utf-8', errors='replace')
        lines = [ln.rstrip() for ln in out.splitlines() if ln.strip()]
        # PASS/FAIL 作为独立的词出现（t3 的表格行在 PASS 后面还可能跟一段说明）；SUMMARY 行里的「FAIL=0」不算
        k_ok = sum(1 for ln in lines if re.search(r'(^|\s)PASS(\s|$)', ln))
        k_bad = sum(1 for ln in lines if re.search(r'(^|\s)FAIL(\s|$)', ln))
        summ = [ln for ln in lines if ln.startswith('SUMMARY ')]
        good = (p.returncode == 0 and k_bad == 0 and k_ok > 0 and bool(summ)
                and ' FAIL=0 ' in summ[-1] + ' ' and lines[-1] == summ[-1])
        ok = ok and good
        n_ok += k_ok
        n_bad += k_bad
        outs.append('### %s %s（退出码 %d）\n%s' % (script, ' '.join(args), p.returncode, out))
    with open(os.path.join(ROOT, 'logs', 'rv3_%s.log' % tag), 'w', encoding='utf-8') as f:
        f.write('\n'.join(outs))
    return ok, n_ok, n_bad, time.time() - t


t0 = time.time()
ok, n, nf, dt = run('r-c4ii', 'r6_structure.py', [], 'c4ii_r6')
report('rv3-c4ii-r6', ok, 'T4.3(6)：由 T4.3(7) 的闭式精确算出 A_j∈Q[u,L]（j<=14），指标界 ι<=⌊j/2⌋+1、'
       '三角化得到的 Σπ_{j,i}(q)c(q,i) 在 q<=60 上等于真实系数、两个子断言、与表 6（j<=8）一致；'
       '子脚本 %d 条 PASS、%d 条 FAIL（%.1fs，输出 logs/rv3_c4ii_r6.log）' % (n, nf, dt))
ok, n, nf, dt = run_okbad('s6-t436', [('t1_anchor.py', []), ('t2_lemmas.py', []), ('t4_closed_form.py', ['30'])],
                          's6_t436_a')
report('rv3-s6-t436-a', ok, 'T4.3(6) 第二份独立证明（s6-t436，由一阶 ODE 的分量递推 θA_j=uA_{j−2}+u²A_{j−3}，不用 T4.3(7)）'
       '的逐式核对：锚点、各引理、T4.3(7) 闭式到 z^30；%d 条 OK、%d 条 BAD（%.1fs，输出 logs/rv3_s6_t436_a.log）'
       % (n, nf, dt))
ok, n, nf, dt = run_okbad('s6-t436', [('t3_structure.py', ['24']), ('t5_table6.py', []), ('t6_compare_rc4ii.py', [])],
                          's6_t436_b')
report('rv3-s6-t436-b', ok, 'T4.3(6)：按 s6-t436 证明的构造法求 π_{j,i}（j<=40）与真实 a_{q,j}（q<=300）逐项相同，'
       '只用命题形状的拟合法（j<=24）与构造法逐系数相同，子断言、表 6、r-c4ii 的 j=9..14 都一致；'
       '%d 条 OK、%d 条 BAD（%.1fs，输出 logs/rv3_s6_t436_b.log）' % (n, nf, dt))
ok, n, nf, dt = run('r-c3a', 'r2_numeric.py', [], 'c3a_r2')
report('rv3-c3a-r2', ok, 'T3.4(2)：K 的定义与闭式 Γ(−λ)[1+λx⁵J] 在 7 个 x 上一致、1<K/Γ(−λ)<2、'
       '端到端 I−𝒮 与闭式一致（decimal 高精度，数值）；子脚本 %d 条 PASS、%d 条 FAIL（%.1fs，输出 logs/rv3_c3a_r2.log）'
       % (n, nf, dt))
ok, n, nf, dt = run_summary('s6-t342', [('t1_K_def_vs_closed.py', [','.join(str(i) for i in range(1, 14))])],
                            's6_t342_K')
report('rv3-s6-t342-K', ok, 'T3.4(2)：K 的定义（级数+尾积分）与闭式 Γ(−λ)[1+λx⁵J] 在 13 个 x（0.18..0.9）上一致，'
       '另核对路线 B 的两半与 K 的符号（s6-t342 自写 decimal 与求积，数值）；%d 条 PASS、%d 条 FAIL（%.1fs，'
       '输出 logs/rv3_s6_t342_K.log）' % (n, nf, dt))
ok, n, nf, dt = run_summary('s6-t342', [('t2_end_to_end.py', []), ('t3_corollary.py', [])], 's6_t342_e')
report('rv3-s6-t342-e', ok, 'T3.4(2)：端到端 I−𝒮（I 求积、𝒮 精确有理部分和）与闭式在 11 组 (x,t) 上一致；'
       '推论 1<K/Γ(−λ)<2−x 与 K 的符号在 105 个 x 上成立（数值）；%d 条 PASS、%d 条 FAIL（%.1fs，'
       '输出 logs/rv3_s6_t342_e.log）' % (n, nf, dt))

npass = sum(results)
nfail = len(results) - npass
print('SUMMARY rv3 pass=%d fail=%d (%.1fs)' % (npass, nfail, time.time() - t0))
sys.exit(0 if nfail == 0 else 1)
