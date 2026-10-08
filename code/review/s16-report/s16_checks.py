# -*- coding: utf-8 -*-
"""s16-report 复核的辅助核对（2026-10-09）。只读：不改任何已有文件。只用标准库与 numpy。

用法（任务 C 根目录）：
  GUARD_CAP_MB=1500 code/main_extra/run_guarded.sh logs/review_s16-report_checks.log py -3.14 code/review/s16-report/s16_checks.py

各条打印 PASS/FAIL/INFO：
  s16-replay   把 patch_tableB_2026-10-09.py 的 36 处替换作用在 HEAD 版本上，结果与工作区逐字相同（7 个文件）
  s16-sum      ① 的条目数与行数
  s16-ids      报告引用的 tb.* id 都出现在 run_all 日志与 verify_all 的 tb 段里
  s16-tau      报告里的 τ_1..τ_40 与 notes/16、logs/tableB_check_b9_full.log 一致
  s16-atoms    T2.5(4)(d) 的 U_k(2) 两原子例子（k=0、k>=2）与 T2.8(3)(c) 的 N(k,3) 例子（k>=1）
  s16-b8-k4    T5.3(2)(b)「j>J_k 时 (-1)^k U_k(-j)>0」：k<=3 时不成立（需要 k>=4），4<=k<=30 时在 (J_k, J_k+60] 上成立
  s16-b8-count (s_k,J_k] 与 (s_k+2,J_k] 中整除 lcm(1..k) 的 j 的个数（k<=300）；(s_k,J_k] 的整数总数
  s16-b9-second 次高项与首项的符号关系（3<=k<=240）
  s16-hm1      h_2(-1)=0；h_k(-1) 的两种算法一致（k<=60）
  s16-tau-sanity τ_i（i<=26）在 k<=240 上与 h_{k,i} 的符号一致（只是有限范围的旁证）
"""
import importlib.util
import math
import os
import re
import subprocess
import sys
from fractions import Fraction

import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
N_PASS = N_FAIL = 0


def report(ok, cid, msg):
    global N_PASS, N_FAIL
    if ok:
        N_PASS += 1
    else:
        N_FAIL += 1
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg))


def read_text(path):
    with open(path, 'rb') as f:
        return f.read().decode('utf-8').replace('\r\n', '\n')


# ------------------------------------------------------------------ s16-replay
def check_replay():
    p = os.path.join(ROOT, 'code', 'main_extra', 'report_patches', 'patch_tableB_2026-10-09.py')
    spec = importlib.util.spec_from_file_location('patch_tb_1009', p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)          # 只执行模块顶层（add 调用），不调用 main()
    E = mod.E
    total = sum(len(v) for v in E.values())
    msgs = []
    ok_all = True
    for name, reps in E.items():
        head = subprocess.run(['git', 'show', 'HEAD:notes/report_parts/' + name], cwd=ROOT,
                              stdout=subprocess.PIPE, check=True).stdout.decode('utf-8').replace('\r\n', '\n')
        s = head
        for old, new in reps:
            c = s.count(old)
            if c != 1:
                ok_all = False
                msgs.append('%s: old 出现 %d 次（%s…）' % (name, c, old[:30]))
            s = s.replace(old, new)
        cur = read_text(os.path.join(PARTS, name))
        same = (s == cur)
        ok_all &= same
        msgs.append('%s:%d处%s' % (name, len(reps), '' if same else '（与工作区不同）'))
    report(ok_all and total == 36, 's16-replay', '替换共 %d 处；%s' % (total, '；'.join(msgs)))


# ------------------------------------------------------------------ s16-sum
def check_summary():
    s = read_text(os.path.join(PARTS, '01_summary.md'))
    lines = s.split('\n')
    while lines and lines[-1] == '':
        lines.pop()
    items = [ln for ln in lines if re.match(r'^\d+\. ', ln)]
    nonempty = [ln for ln in lines if ln.strip()]
    report(len(items) <= 15 and len(nonempty) <= 15, 's16-sum',
           '① 共 %d 行（非空 %d 行，含标题），编号条目 %d 条；最长一条 %d 字符' %
           (len(lines), len(nonempty), len(items), max(len(x) for x in items)))


# ------------------------------------------------------------------ s16-ids
def ids_from_log(path, start_marker=None, end_marker=None):
    txt = read_text(path)
    if start_marker is not None:
        i = txt.index(start_marker)
        j = txt.index(end_marker, i)
        txt = txt[i:j]
    return set(m.group(1) for m in re.finditer(r'^(?:PASS|FAIL) (\S+)', txt, re.M))


def check_ids():
    rep = ''
    for fn in sorted(os.listdir(PARTS)):
        if re.match(r'^\d\d_.*\.md$', fn):
            rep += read_text(os.path.join(PARTS, fn))
    cited = set(m.group(1) for m in re.finditer(r'tb\.([A-Za-z0-9][A-Za-z0-9_-]*[A-Za-z0-9])', rep))
    cited.discard('py')                     # 「check_tb.py」里的 tb.py
    cited.discard('log')                    # 09_code.md 里的文件名「…_before_tb.log」
    run_all = ids_from_log(os.path.join(ROOT, 'logs', 'tableB_run_all_2026-10-09_b13.log'))
    va = ids_from_log(os.path.join(ROOT, 'logs', 'verify_all_final.log'), '>>> check_tb.py', 'SUMMARY tb ')
    miss1 = sorted(cited - run_all)
    miss2 = sorted(cited - va)
    uncited = sorted(run_all - cited)
    report(not miss1 and not miss2, 's16-ids',
           '报告引用 %d 个 tb id；run_all 日志 %d 个、verify_all tb 段 %d 个；缺失 %s / %s；日志里有而报告没引用的：%s' %
           (len(cited), len(run_all), len(va), miss1, miss2, uncited))


# ------------------------------------------------------------------ s16-tau
def check_tau():
    c5 = read_text(os.path.join(PARTS, '06_C5.md'))
    m = re.search(r'依次为 ([0-9, ]+)（第一轮', c5)
    rep = [int(x) for x in m.group(1).split(',')]
    n16 = read_text(os.path.join(ROOT, 'notes', '16-主Agent-表B-B9-符号模式与门槛.md'))
    m2 = re.search(r'τ_1,…,τ_40 依次是\n\s*([0-9, ]+)。', n16)
    notes = [int(x) for x in m2.group(1).split(',')]
    lg = read_text(os.path.join(ROOT, 'logs', 'tableB_check_b9_full.log'))
    m3 = re.search(r'τ_1\.\.τ_40 = \[([0-9, ]+)\]', lg)
    log = [int(x) for x in m3.group(1).split(',')]
    report(rep == notes == log and len(rep) == 40, 's16-tau',
           '报告 %d 个、notes/16 %d 个、full 日志 %d 个，三者%s' %
           (len(rep), len(notes), len(log), '相同' if rep == notes == log else '不同'))
    return rep


# ------------------------------------------------------------------ 基本数列
def good(a, b, c):
    return b == c or a >= max(b, c)


def U_brute(k, m):
    """按定义的转移 DP（状态 = 最后两个值）。"""
    if k == 0:
        return 1
    if k == 1:
        return m + 1
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for _ in range(k - 2):
        nxt = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    nxt[(b, c)] = nxt.get((b, c), 0) + v
        cnt = nxt
    return sum(cnt.values())


def U_table(K, M):
    """U_k(m)（0<=k<=K，0<=m<=M）：G_m(1-x-m x^3)=G_{m-1}+m x^2，G_{-1}=1。"""
    U = [[0] * (M + 1) for _ in range(K + 1)]
    prev = [1 if k == 0 else 0 for k in range(K + 1)]      # U_k(-1)=[k=0]
    for m in range(M + 1):
        for k in range(K + 1):
            v = prev[k] + (U[k - 1][m] if k >= 1 else 0) + (m * U[k - 3][m] if k >= 3 else 0) + (m if k == 2 else 0)
            U[k][m] = v
        prev = [U[k][m] for k in range(K + 1)]
    return U


def c_seq(i, nmax):
    """c_i(n)=[x^n]1/(1-x-i x^3)，n<0 时为 0。返回函数。"""
    c = [0] * (nmax + 1)
    for n in range(nmax + 1):
        c[n] = (1 if n == 0 else 0) + (c[n - 1] if n >= 1 else 0) + (i * c[n - 3] if n >= 3 else 0)

    def f(n):
        return c[n] if n >= 0 else 0
    return f


def N_table(U, K):
    """N(k,q)=sum_{i=1}^{q}(-1)^{q-i}C(q,i)U_k(i-1)（k>=1）；N(0,0)=1。"""
    N = [[0] * (K + 1) for _ in range(K + 1)]
    N[0][0] = 1
    for k in range(1, K + 1):
        for q in range(1, k + 1):
            N[k][q] = sum((-1) ** (q - i) * math.comb(q, i) * U[k][i - 1] for i in range(1, q + 1))
    return N


def gbinom(n, q):
    """整值多项式 C(n,q)，n 可为负。"""
    if q < 0:
        return 0
    num = 1
    for t in range(q):
        num *= (n - t)
    return num // math.factorial(q)


# ------------------------------------------------------------------ s16-atoms
def check_atoms(U):
    ok_brute = all(U[k][m] == U_brute(k, m) for k in range(0, 10) for m in range(0, 4))
    c1 = c_seq(1, 80)
    c2 = c_seq(2, 80)
    bad_U2 = [k for k in range(0, 41)
              if Fraction(U[k][2]) != Fraction(1, 2) - Fraction(1, 4) * c1(k + 10) + Fraction(1, 4) * c1(k - 4)
              + Fraction(5, 2) * c2(k + 3) + 6 * c2(k - 2)]
    bad_U1 = [k for k in range(0, 41) if U[k][1] != c1(k + 3) + c1(k - 2) - 1]
    N = N_table(U, 40)
    bad_N3 = [k for k in range(1, 41)
              if Fraction(N[k][3]) != Fraction(13, 2) - c1(k + 8) - 2 * c1(k - 2) + Fraction(5, 2) * c2(k + 3) + 6 * c2(k - 2)]
    ok = ok_brute and bad_U2 == [1] and bad_N3 == [] and bad_U1 == []
    report(ok, 's16-atoms', 'U 递推 = 定义 DP（k<=9,m<=3）：%s；U_k(2) 两原子式不成立的 k（0..40）：%s（报告写「k=0 与 k>=2」）；'
           'N(k,3) 两原子式不成立的 k（1..40）：%s；R_k=c_1(k+3)+c_1(k-2)-1 不成立的 k：%s' % (ok_brute, bad_U2, bad_N3, bad_U1))
    return N


# ------------------------------------------------------------------ s16-b8-k4
def U_neg(Nrow, k, j):
    """U_k(-j)=sum_q N(k,q) C(1-j,q)。"""
    return sum(Nrow[q] * gbinom(1 - j, q) for q in range(0, k + 1))


def Jk(k):
    return k * (k * k - k - 4) // 2 - k + 2


def check_b8_k4(U):
    N = N_table(U, 30)
    fails_small = []
    for k in (1, 2, 3):
        for j in range(max(1, Jk(k) + 1), Jk(k) + 11):
            v = (-1) ** k * U_neg(N[k], k, j)
            if v <= 0:
                fails_small.append((k, j, v))
    ok_big = all((-1) ** k * U_neg(N[k], k, j) > 0 for k in range(4, 31) for j in range(Jk(k) + 1, Jk(k) + 61))
    s3 = U_neg(N[3], 3, 3)
    report(ok_big and len(fails_small) > 0, 's16-b8-k4',
           'k<=3 时 j>J_k 而 (-1)^k U_k(-j)<=0 的例子（k,j,值）：%s（J_1,J_2,J_3=%d,%d,%d；U_3(-3)=%d）；4<=k<=30、J_k<j<=J_k+60 全部 >0：%s'
           % (fails_small[:6], Jk(1), Jk(2), Jk(3), s3, ok_big))


# ------------------------------------------------------------------ s16-b8-count
def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(sieve[p * p::p]))
    return [p for p in range(n + 1) if sieve[p]]


def divisors_upto(k, X):
    arr = np.array([1], dtype=np.int64)
    for p in primes_upto(k):
        pe = 1
        parts = [arr]
        while pe * p <= k:
            pe *= p
            t = arr * pe
            parts.append(t[t <= X])
        arr = np.concatenate(parts)
    return arr


def theta_max(Nrow, k):
    """J_k 的原始定义 max_q θ_q，θ_q=(q+1)N(k,q)/N(k,q+1)-q+1（notes/15 定理 3 的证明；k>=4 时等于闭式）。"""
    return max((q + 1) * Fraction(Nrow[q], Nrow[q + 1]) - q + 1 for q in range(1, k))


def check_b8_count(U):
    N = N_table(U, 12)
    jdef = {k: theta_max(N[k], k) for k in range(2, 13)}
    agree = all(jdef[k] == Jk(k) for k in range(4, 13))
    tot_a = tot_b = tot_c = 0      # (s_k,J_k] 中的约数；(s_k+2,J_k] 中的约数；(s_k,J_k] 的整数个数
    tot_a4 = tot_c4 = 0
    for k in range(1, 301):
        s = (k + 2) // 3
        if k <= 3:
            J = int(math.floor(jdef[k])) if k >= 2 else -1     # k=3：max θ=5，而闭式给 2
        else:
            J = Jk(k)
        if J <= s:
            continue
        d = divisors_upto(k, J)
        a = int(np.count_nonzero(d > s))
        b = int(np.count_nonzero(d > s + 2))
        tot_a += a
        tot_b += b
        tot_c += J - s
        if k >= 4:
            tot_a4 += a
            tot_c4 += J - s
    ok = agree and tot_a == 71660856 and tot_c == 1014588733
    report(ok, 's16-b8-count',
           'J_k 取 max θ（4<=k<=12 与闭式一致：%s；J_2=%s，J_3=%s，闭式 J_3=%d）。(s_k,J_k] 中整除 lcm(1..k) 的 j：%d（k>=4 部分 %d）；'
           '(s_k+2,J_k] 中：%d（少 %d 个，即 298 个 k 各少 s_k+1、s_k+2 两个）；(s_k,J_k] 的整数共 %d（k>=4 部分 %d）'
           % (agree, jdef[2], jdef[3], Jk(3), tot_a, tot_a4, tot_b, tot_a - tot_b, tot_c, tot_c4))


# ------------------------------------------------------------------ h_k 系数
def h_coeffs(U, k):
    """h_{k,i}=sum_{r<=i}(-1)^r C(k+1,r) U_k(i-r)，i=0..floor(2k/3)+1。"""
    d = (2 * k) // 3
    out = []
    for i in range(d + 2):
        out.append(sum((-1) ** r * math.comb(k + 1, r) * U[k][i - r] for r in range(i + 1)))
    return out


def check_b9(U, tau):
    K = len(U) - 1
    H = {k: h_coeffs(U, k) for k in range(0, K + 1)}
    bad = []
    lead_bad = []
    for k in range(3, K + 1):
        h = H[k]
        d = (2 * k) // 3
        if h[d + 1] != 0 or h[d] == 0:
            bad.append(('deg', k))
            continue
        if (h[d] > 0) != ((k // 3) % 2 == 0):
            lead_bad.append(k)
        same = (h[d] > 0) == (h[d - 1] > 0)
        if k % 3 == 0:
            exp_same = False
        elif k % 3 == 2:
            exp_same = True
        else:
            exp_same = (k >= 166)
        if h[d - 1] == 0 or same != exp_same:
            bad.append(k)
    report(not bad and not lead_bad, 's16-b9-second',
           '3<=k<=%d：deg、首项符号 (-1)^floor(k/3) 与次高项符号规律（k≡0 异号、k≡2 同号、k≡1 时 k<=163 异号、k>=166 同号）的例外：%s / %s'
           % (K, bad[:10], lead_bad[:10]))
    # h_k(-1)
    N = N_table(U, 60)
    hm = {}
    ok2 = True
    for k in range(1, 61):
        h = H[k]
        v1 = sum(c * (-1) ** i for i, c in enumerate(h))
        v2 = sum((-1) ** (q - 1) * 2 ** (k - q) * N[k][q] for q in range(1, k + 1))
        hm[k] = v1
        ok2 &= (v1 == v2)
    zeros = [k for k in range(1, 61) if hm[k] == 0]
    report(ok2 and zeros == [2], 's16-hm1',
           'h_k(-1) 两种算法一致（1<=k<=60）：%s；1<=k<=60 中 h_k(-1)=0 的 k：%s（报告 T5.3(7)(b) 的符号式没写「h_k(-1)≠0 时」）'
           % (ok2, zeros))
    # τ_i 的有限范围旁证
    bad3 = []
    for i in range(1, 27):
        t = tau[i - 1]
        if t > K:
            continue
        def hk(k):
            return H[k][i] if i < len(H[k]) else 0
        if not (hk(t - 1) <= 0 and all(hk(k) > 0 for k in range(t, K + 1))):
            bad3.append(i)
    report(not bad3, 's16-tau-sanity', '1<=i<=26：h_{τ_i-1,i}<=0 且 τ_i<=k<=%d 时 h_{k,i}>0 的例外：%s（有限范围，只是旁证）'
           % (K, bad3))


def main():
    check_replay()
    check_summary()
    check_ids()
    tau = check_tau()
    U = U_table(240, 240)
    check_atoms(U)
    check_b8_k4(U)
    check_b8_count(U)
    check_b9(U, tau)
    R = math.sqrt(4 + math.pi ** 2)
    print('INFO R(-1)=sqrt(4+pi^2)=%.6f，8/R=%.6f' % (R, 8 / R))
    print('SUMMARY s16 pass=%d fail=%d' % (N_PASS, N_FAIL))


if __name__ == '__main__':
    main()
