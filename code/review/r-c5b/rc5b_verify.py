# -*- coding: utf-8 -*-
"""r-c5b：对 c5b 全部 35 条结论的独立复核脚本（离线，只读 data/oeis 快照；不导入 core/polylib/check_c5b）。

运行：py -3.14 code/review/r-c5b/rc5b_verify.py
输出：每项一行 PASS/FAIL <id> <说明>，最后 SUMMARY。
"""
import os
import re
import sys
import time
from collections import defaultdict
from fractions import Fraction
from itertools import product, combinations, permutations
from math import comb, factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rc5b_lib as L  # noqa: E402

try:
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass

T0 = time.time()
RES = []


def check(cid, fn):
    t = time.time()
    try:
        ok, msg = fn()
    except Exception as ex:  # noqa
        import traceback
        ok, msg = False, 'EXC %r %s' % (ex, traceback.format_exc().splitlines()[-3:])
    RES.append((cid, ok))
    print('%s %s [%.1fs] %s' % ('PASS' if ok else 'FAIL', cid, time.time() - t, msg))
    sys.stdout.flush()


E = L.all_entries()
COLS = {3: 'A207118', 4: 'A207119', 5: 'A207120', 6: 'A207121', 7: 'A207122'}
ROWS = {2: 'A207069', 3: 'A207070', 4: 'A207124', 5: 'A207125', 6: 'A207126', 7: 'A207127'}


def emp_line(aid):
    ls = [l for l in E[aid]['F'] if l.startswith('Empirical: a(n)') or l.startswith('Empirical: a(n) =')]
    assert len(ls) == 1, (aid, ls)
    return ls[0]


# ---------------------------------------------------------------------------
def v01():
    rows = []
    with open(os.path.join(L.LOGDIR, 'c5b_fetch.log'), encoding='utf-8') as f:
        for line in f:
            p = line.rstrip('\n').split('\t')
            rows.append(p)
    assert all(len(p) == 5 for p in rows)
    urls = [p[4] for p in rows]
    kinds = defaultdict(int)
    for u in urls:
        if re.fullmatch(r'https://oeis\.org/search\?q=id:A\d{6}&fmt=text', u):
            kinds['entry'] += 1
        elif re.fullmatch(r'https://oeis\.org/A\d{6}/b\d{6}\.txt', u):
            kinds['bfile'] += 1
        elif re.fullmatch(r'https://oeis\.org/search\?q=-?\d+(,-?\d+)+&fmt=text', u):
            kinds['seq'] += 1
        elif re.fullmatch(r'https://oeis\.org/search\?q=A207123(&start=10)?&fmt=text', u):
            kinds['ref'] += 1
        else:
            kinds['other'] += 1
    sizes_ok = all(os.path.getsize(os.path.join(L.OEIS, p[1])) == int(p[3]) for p in rows)
    files = sorted(x for x in os.listdir(L.OEIS) if x != 'INDEX.md')
    ok = (len(rows) == 68 and len(set(urls)) == 68 and all(p[2] == '200' for p in rows) and sizes_ok
          and sorted(p[1] for p in rows) == files and dict(kinds) == {'entry': 13, 'bfile': 16, 'seq': 37, 'ref': 2})
    ts = sorted(p[0] for p in rows)
    return ok, '日志 %d 行、%d 个不同 URL、类型 %s、全 200、大小一致、文件集合一致；时间 %s..%s' % (
        len(rows), len(set(urls)), dict(kinds), ts[0], ts[-1])


def v02():
    want = {'A207117': 1, 'A207118': 1, 'A207119': 1, 'A207120': 1, 'A207121': 1, 'A207122': 1,
            'A207123': 1, 'A207124': 1, 'A207125': 1, 'A207126': 1, 'A207127': 1, 'A207069': 1,
            'A207070': 1, 'A038718': 1, 'A084990': 0, 'A326247': 0, 'A002620': 0, 'A030179': 0,
            'A077949': 0, 'A077974': 0, 'A084386': 0}
    got = {a: L.entry_offset(E[a]) for a in want}
    return got == want, '21 个条目 %%O 首项 = 预期；got=%s' % ({a: got[a] for a in got if got[a] != want[a]} or 'all match')


def v03():
    tot = 0
    fail_transposed = 0
    for aid, kfix in [('A207118', 3), ('A207119', 4), ('A207120', 5), ('A207121', 6), ('A207122', 7), ('A207123', None)]:
        lines = E[aid].get('e', [])
        i = 0
        while i < len(lines):
            mm = re.match(r'Some solutions for n=(\d+)(?: k=(\d+))?', lines[i])
            if not mm:
                i += 1
                continue
            n = int(mm.group(1))
            k = int(mm.group(2)) if mm.group(2) else kfix
            blk = lines[i + 1:i + 1 + n]
            parts = [re.split(r'\.\.\.\.+', l.strip().strip('.')) for l in blk]
            ns = len(parts[0])
            for j in range(ns):
                arr = [[int(d) for d in re.findall(r'[01]', parts[r][j])] for r in range(n)]
                assert all(len(r) == k for r in arr), (aid, arr)
                okr = all(not L.has3(r, L.H_FORB) for r in arr)
                okc = all(not L.has3([arr[r][c] for r in range(n)], L.V_FORB) for c in range(k))
                assert okr and okc, (aid, arr)
                # 转置读法（行用列规则、列用行规则）是否会失败
                okr2 = all(not L.has3(r, L.V_FORB) for r in arr)
                okc2 = all(not L.has3([arr[r][c] for r in range(n)], L.H_FORB) for c in range(k))
                if not (okr2 and okc2):
                    fail_transposed += 1
                tot += 1
            i += 1 + n
    return tot == 30, '%%e 样例 %d 个全部满足「行禁001/010、列禁001/011」；其中 %d 个在「互换行列规则」读法下不合法（样例对方向有区分力）' % (tot, fail_transposed)


def v04():
    for k, aid in COLS.items():
        bf = L.read_bfile('b%s.txt' % aid[1:])
        assert [n for n, _ in bf] == list(range(1, 211))
        assert all(v == L.a_val(k, n) for n, v in bf), aid
        d = L.entry_data(E[aid])
        assert d == [v for _, v in bf[:len(d)]]
    return True, 'k=3..7 的 b 文件 n=1..210 = U_k(ceil(n/2))U_k(floor(n/2))（自写前缀和高度 DP）；数据段为 b 文件前缀'


def v05():
    cnt = 0
    for k, aid in COLS.items():
        bf = dict(L.read_bfile('b%s.txt' % aid[1:]))
        lst = L.a_rowpair_list(24, k)
        for n in range(1, 25):
            assert lst[n] == bf[n], (k, n)
            cnt += 1
        for n in range(1, 8):
            if n * k <= 16:
                assert L.a_brute(n, k) == bf[n], (k, n)
                cnt += 1
    return True, '自写逐行转移 a_rowpair（k=3..7, n=1..24）与暴力 a_brute（n*k<=16）共 %d 个值 = b 文件' % cnt


def v06():
    bf = L.read_bfile('b207123.txt')
    vals = [v for _, v in bf]
    assert len(vals) == 545
    T = {}
    pos = 0
    s = 2
    while pos < len(vals):
        for n in range(1, s):          # 反对角线 n+k=s，n 递增
            if pos < len(vals):
                T[(n, s - n)] = vals[pos]
                pos += 1
        s += 1
    assert all(v == L.a_val(k, n) for (n, k), v in T.items())
    # 反方向解码会失败吗？
    T2 = {}
    pos = 0
    s = 2
    while pos < len(vals):
        for k in range(1, s):
            if pos < len(vals):
                T2[(s - k, k)] = vals[pos]
                pos += 1
        s += 1
    rev_bad = sum(1 for (n, k), v in T2.items() if v != L.a_val(k, n))
    C = E['A207123']['C']
    i0 = C.index('Table starts')
    for r in range(8):
        nums = [int(x) for x in re.findall(r'\d+', C[i0 + 1 + r])]
        assert nums == [L.a_val(c, r + 1) for c in range(1, 11)]
    c2 = 0
    for (n, k), v in T.items():
        if n <= 9 and k <= 6:
            assert L.a_rowpair(n, k) == v
            c2 += 1
    maxs = max(n + k for (n, k) in T)
    return True, ('A207123 b 文件 545 项（n 递增读反对角线，n+k<=%d）全部 = a_k(n)；反方向解码有 %d 项不符（读法有区分力）；%%C 8x10 表一致；'
                  '%d 项另与 a_rowpair 一致' % (maxs, rev_bad, c2))


def v07():
    bf = L.read_bfile('b207117.txt')
    assert [n for n, _ in bf] == list(range(1, 20))
    assert all(v == L.a_val(n, n) for n, v in bf)
    for n in range(1, 7):
        assert L.a_rowpair(n, n) == dict(bf)[n]
    return True, 'A207117 b 文件 n=1..19 = a_n(n)；n<=6 另与 a_rowpair 一致'


def v08():
    for n, aid in ROWS.items():
        bf = L.read_bfile('b%s.txt' % aid[1:])
        assert [k for k, _ in bf] == list(range(1, 211))
        assert all(v == L.a_val(k, n) for k, v in bf), aid
        for k in range(1, 7):
            assert L.a_rowpair(n, k) == dict(bf)[k]
    return True, '第 2..7 行 b 文件 k=1..210 = a_k(n)；k<=6 另与 a_rowpair 一致'


def v09():
    b69 = dict(L.read_bfile('b207069.txt'))
    b70 = dict(L.read_bfile('b207070.txt'))
    for k in range(1, 9):
        o2 = L.a_rowpair(2, k, L.V_FORB_OTHER)
        o3 = L.a_rowpair(3, k, L.V_FORB_OTHER)
        assert o2 == b69[k] == L.a_rowpair(2, k)
        assert o3 == b70[k] == L.a_rowpair(3, k)
    # 证明中的恒等：3 行两边都等于 R_k * U_k(2)
    assert all(b70[k] == L.U(k, 1) * L.U(k, 2) for k in range(1, 211))
    assert L.a_brute(4, 1, L.V_FORB_OTHER) == 8 and L.a_brute(4, 1) == 9
    # 「从 4 行起不同」对每个 n>=4 都成立：k=1 时另一规则为 2n，本题为 floor((n+2)^2/4)
    for n in range(2, 15):
        o, s = L.a_brute(n, 1, L.V_FORB_OTHER), L.a_brute(n, 1)
        assert o == 2 * n and s == (n + 2) ** 2 // 4
        assert (o == s) == (n <= 3)
    d45 = [(L.a_rowpair(4, k, L.V_FORB_OTHER), L.a_rowpair(4, k)) for k in range(1, 5)]
    nm = E['A207069']['N'][0] + E['A207070']['N'][0]
    assert nm.count('0 0 1 and 1 0 1 vertically') == 2
    return True, '另一规则（纵禁 001/101）2xk、3xk（k<=8）直接数 = b 文件 = 本题；3 行 = R_k*U_k(2)（k<=210）；4x1：8 vs 9；4xk(k<=4) 两规则 %s' % d45


def v10():
    d1 = L.entry_data(E['A002620'])
    d2 = L.entry_data(E['A030179'])
    assert E['A030179']['N'][0].startswith('Quarter-squares squared: A002620^2')
    assert all(L.a_val(1, n) == d1[n + 2] == (n + 2) ** 2 // 4 for n in range(1, len(d1) - 2))
    assert all(L.a_val(2, n) == d2[n + 2] for n in range(1, len(d2) - 2))
    return True, '第1列 = A002620(n+2)（n<=%d）、第2列 = A030179(n+2)（n<=%d，名称即 A002620^2）' % (len(d1) - 3, len(d2) - 3)


def v11():
    msg = []
    for k, aid in COLS.items():
        c = L.parse_recurrence(emp_line(aid))
        e = len(c)
        assert e == 4 * k
        # 特征多项式 x^e - sum c_i x^(e-i)，按降幂比较
        ch = [1] + [-x for x in c]                     # 降幂
        tgt = [1]
        for _ in range(2 * k + 1):
            tgt = L.pmul(tgt, [1, -1])                 # 这里用「降幂」表示也可，(x-1) 降幂为 [1,-1]
        for _ in range(2 * k - 1):
            tgt = L.pmul(tgt, [1, 1])
        assert ch == tgt, aid
        # 先验：每个奇偶类上是 <=2k 次多项式（T1）——数值确认 (2k+1) 阶差分为 0（j<=60）
        for par in (0, 1):
            seq = [L.a_val(k, 2 * j + par) for j in range(0, 61)]
            for _ in range(2 * k + 1):
                seq = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
            assert all(x == 0 for x in seq)
        N = 300
        a = [None] + [L.a_val(k, n) for n in range(1, N + 1)]
        assert all(a[n] == sum(c[i - 1] * a[n - i] for i in range(1, e + 1)) for n in range(e + 1, N + 1))
        # 最小性：e×e Hankel（a(1..2e-1)）非奇异 => 最小阶 = e
        assert L.hankel_nonsingular(a[1:], e)
        assert c[-1] != 0
        msg.append('k=%d:e=%d' % (k, e))
    return True, ('列 Empirical 递推：特征多项式 = (x-1)^(2k+1)(x+1)^(2k-1)；奇偶类 (2k+1) 阶差分为 0；在自算 a(1..300) 上成立（>= e+4k+2 个位置，'
                  '配合 T3 即对一切 n 成立）；e×e Hankel 行列式模两大素数非零 => 最小阶 = e；c_e != 0 => 任一尾段最小阶也为 e。' + ','.join(msg))


def v12():
    msg = []
    for n, aid in ROWS.items():
        c = L.parse_recurrence(emp_line(aid))
        e = len(c)
        m1, m2 = (n + 1) // 2, n // 2
        d = (m1 + 1) ** 2 * (m2 + 1) ** 2
        N = e + 1 + d + 5
        a = [None] + [L.U(k, m1) * L.U(k, m2) for k in range(1, N + 1)]
        assert all(a[k] == sum(c[i - 1] * a[k - i] for i in range(1, e + 1)) for k in range(e + 1, N + 1)), aid
        assert L.hankel_nonsingular(a[1:], e), aid
        assert c[-1] != 0
        msg.append('%s:e=%d,d=%d,核到k=%d' % (aid, e, d, N))
    return True, '行 Empirical 递推在 k=e+1..e+1+d(+5) 上成立（d=(m1+1)^2(m2+1)^2 为 Kronecker 积先验阶），Hankel 非奇异 => 最小；' + '; '.join(msg)


def v13():
    F = E['A207118']['F']
    gf = [l for l in F if l.startswith('G.f.:')][0]
    mm = re.match(r'G\.f\.: x\*\((.*)\) / \(\(1 - x\)\^7\*\(1 \+ x\)\^5\)\.$', gf)
    num = L.parse_poly(mm.group(1), 'x')
    D = [1]
    for _ in range(7):
        D = L.pmul(D, [1, -1])
    for _ in range(5):
        D = L.pmul(D, [1, 1])
    NN = 160
    A = [0] + [L.a_val(3, n) for n in range(1, NN)]
    prod_ = L.series_mul(D, A, NN)
    assert prod_ == ([0] + num + [0] * NN)[:NN]
    U3 = L.lagrange([0, 1, 2, 3], [L.U(3, m) for m in range(4)])
    assert all(L.peval(U3, m) == L.U(3, m) for m in range(0, 40))
    h = Fraction(1, 2)
    Ev = L.pmul(L.pcompose(U3, [0, h]), L.pcompose(U3, [0, h]))
    Od = L.pmul(L.pcompose(U3, [-h, h]), L.pcompose(U3, [h, h]))
    pe = [l for l in F if l.endswith('for n even.')][0]
    po = [l for l in F if l.endswith('for n odd.')][0]
    pe = L.pscale(L.parse_poly(re.match(r'a\(n\) = \((.*)\) / 576 for n even\.', pe).group(1), 'n'), Fraction(1, 576))
    po = L.pscale(L.parse_poly(re.match(r'a\(n\) = \((.*)\) / 576 for n odd\.', po).group(1), 'n'), Fraction(1, 576))
    assert L.ptrim(Ev) == L.ptrim(pe) and L.ptrim(Od) == L.ptrim(po)
    return True, 'A207118 Barker：(1-x)^7(1+x)^5*Σa_3(n)x^n = x*num（到 x^159）；偶/奇 n 多项式与 U_3(n/2)^2、U_3((n-1)/2)U_3((n+1)/2) 系数全等（U_3 由自算 DP 插值）'


def v14():
    F = E['A207069']['F']
    gf = [l for l in F if l.startswith('Empirical g.f.:')][0]
    mm = re.match(r'Empirical g\.f\.: x\*\((.*?)\) / \((.*)\)\. - _Colin Barker_', gf)
    num = L.parse_poly(mm.group(1), 'x')
    facs = re.findall(r'\(([^()]*)\)', '(' + mm.group(2) + ')')
    D = [1]
    for f_ in facs:
        D = L.pmul(D, L.parse_poly(f_, 'x'))
    c = L.parse_recurrence(emp_line('A207069'))
    assert D == L.ptrim([1] + [-x for x in c])
    NN = 160
    A = [0] + [L.U(k, 1) ** 2 for k in range(1, NN)]
    assert L.series_mul(D, A, NN) == ([0] + num + [0] * NN)[:NN]
    # 根的解释：f=y^3-y^2-1；平方根所满足 z^3-z^2-2z-1；倒数满足 y^3+y-1；对应 x 因子
    import numpy as np
    r = np.roots([1, -1, 0, -1])
    sq = np.poly(r ** 2)
    inv = np.poly(1 / r)
    ok = np.allclose(sq, [1, -1, -2, -1]) and np.allclose(inv, [1, 0, 1, -1])
    # 两两之积 rho_i rho_j (i<j) = 1/rho_l
    pr = sorted([r[0] * r[1], r[0] * r[2], r[1] * r[2]], key=lambda z: (z.real, z.imag))
    iv = sorted(list(1 / r), key=lambda z: (z.real, z.imag))
    ok = ok and np.allclose(pr, iv)
    return ok, 'A207069 Barker g.f.：分母 = 1-Σc_i x^i，D*ΣR_k^2 x^k = x*num（到 x^159）；数值（numpy，容差 1e-8）确认 1-x-2x^2-x^3 <-> rho_i^2、1+x^2-x^3 <-> rho_i rho_j = 1/rho_l'


def ham_count(n):
    """P_n^2 中从 1 出发的 Hamilton 路数（DFS）。"""
    if n == 1:
        return 1
    used = [False] * (n + 2)
    used[1] = True
    cnt = 0

    def rec(x, depth):
        nonlocal cnt
        if depth == n:
            cnt += 1
            return
        for y in (x - 2, x - 1, x + 1, x + 2):
            if 1 <= y <= n and not used[y]:
                used[y] = True
                rec(y, depth + 1)
                used[y] = False
    rec(1, 1)
    return cnt


def ham_paths(n):
    res = []
    path = [1]
    used = {1}

    def rec():
        if len(path) == n:
            res.append(tuple(path))
            return
        x = path[-1]
        for y in (x - 2, x - 1, x + 1, x + 2):
            if 1 <= y <= n and y not in used:
                used.add(y)
                path.append(y)
                rec()
                path.pop()
                used.discard(y)
    rec()
    return res


def v15():
    bf = L.read_bfile('b038718.txt')
    assert [n for n, _ in bf] == list(range(1, 6024))
    Rcol = L.U_col(1, 6025)
    assert bf[0][1] == 1 and all(v == Rcol[n - 2] for n, v in bf[1:])
    assert all(Rcol[k] == Rcol[k - 1] + Rcol[k - 3] + 1 for k in range(3, 6022))
    # 原始置换定义 n<=9；Hamilton 路 DFS n<=18
    for n in range(1, 10):
        c = 0
        for rest in permutations(range(2, n + 1)):
            P = (1,) + rest
            inv = {v: i for i, v in enumerate(P, 1)}
            if all(abs(inv[i + 1] - inv[i]) in (1, 2) for i in range(1, n)):
                c += 1
        assert c == bf[n - 1][1] == ham_count(n)
    for n in range(10, 19):
        assert ham_count(n) == bf[n - 1][1]
    # 引理中的三分法计数：(α)/(β)/(γ) 分别为 H(n-1)、H(n-3)、1（n=4..12，直接按首两步分类数）
    for n in range(4, 13):
        P = ham_paths(n)
        al = sum(1 for p in P if p[1] == 2)
        be = sum(1 for p in P if p[1] == 3 and p[2] == 2)
        ga = sum(1 for p in P if p[1] == 3 and p[2] != 2)
        assert (al, be, ga) == (ham_count(n - 1), ham_count(n - 3), 1), n
        assert [p for p in P if p[1] == 3 and p[2] != 2][0][-1] == 2
    # 子引理：P_N^2 中从 1 到 2 的 Hamilton 路唯一（N=2..13）
    for Nn in range(2, 14):
        P = [p for p in ham_paths(Nn) if p[-1] == 2]
        assert len(P) == 1
    return True, 'b038718 n=1..6023：a(1)=1、a(n)=R_{n-2}；R 递推 k<=6021；置换定义 n<=9 = Hamilton 路 DFS = b 文件，DFS 到 n<=18；三分法 (α,β,γ)=(H(n-1),H(n-3),1) 在 n=4..12 直接计数成立；1->2 Hamilton 路唯一（N<=13）'


def row_to_path(w):
    k = len(w)
    n = k + 2
    if all(x == 0 for x in w):
        return tuple(list(range(1, n + 1, 2)) + list(range(2, n + 1, 2))[::-1])
    if w[0] == 1:
        return (1,) + tuple(v + 1 for v in row_to_path(w[1:]))
    assert w[0] == 0 and w[1] == 1
    if k == 2:
        return (1, 3, 2, 4)
    assert w[2] == 1
    return (1, 3, 2) + tuple(v + 3 for v in row_to_path(w[3:]))


def v16():
    for k in range(0, 13):
        rows = L.allowed_rows(k) if k else ((),)
        img = [row_to_path(tuple(w)) for w in rows]
        P = set(ham_paths(k + 2))
        assert len(set(img)) == len(rows) and set(img) == P, k
        # 0^k 对应唯一以 2 结尾的路
        z = row_to_path(tuple([0] * k))
        assert z[-1] == 2 and sum(1 for p in P if p[-1] == 2) == 1
    return True, '允许行 -> Hamilton 路的递归映射（自写实现）对 k=0..12 是双射，像 = DFS 全体；0^k 的像是唯一以 2 结尾的路'


def v17():
    NN = 300
    R = L.U_col(1, NN)[:NN]
    D = L.pmul([1, -1], [1, -1, 0, -1])
    g1 = L.series_div([1, 0, 1, -1], D, NN)
    g2 = L.series_div([1, -1, 1], D, NN)
    ok = g1 == R and g2 == [1] + R[:NN - 1] and g2[1] == 1 != R[1]
    # 提示词列出的 2,4,6,9,... 若从 x^0 起：(2-x^3)/D
    g3 = L.series_div([2, 0, 0, -1], D, NN)
    ok = ok and g3 == R[1:NN] + [g3[-1]] and D == [1, -2, 1, -1, 1]
    gtxt = [l for l in E['A038718']['F'] if l.startswith('G.f.:')][0]
    ok = ok and '(1 -x +x^2)/(1-2*x+x^2-x^3+x^4)' in gtxt
    return ok, 'ΣR_k x^k = (1+x^2-x^3)/D，(1-x+x^2)/D = 1+xΣR_k x^k（到 x^299）；若把列出的 2,4,6,... 从 x^0 起算则 g.f. 为 (2-x^3)/D——提示词的式子只有作为「A038718 条目所印 g.f.」才对'


def v18():
    for k in range(1, 10):
        Nk = L.N_dfs(k)
        assert Nk.get(k, 0) >= 1
        col = [L.U(k, m) for m in range(0, 21)]
        assert all(col[m] == sum(v * comb(m + 1, q) for q, v in Nk.items()) for m in range(21))
        assert L.N_from_values(k, col) == {q: Nk.get(q, 0) for q in range(1, k + 1)}
    # (b) 归约：三元组条件 = 逐行字面检查（m<=12）
    for m in range(0, 13):
        for a, b, c in product(range(m + 1), repeat=3):
            assert L.legal(a, b, c) == L.legal_literal(a, b, c, m)
    # 字面 DP / 前缀和 DP / 多重链 三者一致
    for m in range(0, 7):
        s1 = L.U_slow(m, 12, literal=True)
        assert s1 == L.U_col(m, 12)
    for k in range(1, 8):
        for m in range(0, 6):
            assert L.U_multichain(k, m) == L.U(k, m)
    # T1'：链数
    for k in range(1, 10):
        P = sorted(L.allowed_rows(k), key=sum)
        bot, top = tuple([0] * k), tuple([1] * k)
        assert P[0] == bot and top in P
        f = {x: defaultdict(int) for x in P}
        f[bot][0] = 1
        for i, x in enumerate(P):
            for y in P[:i]:
                if y != x and all(u <= v for u, v in zip(y, x)):
                    for q, v in f[y].items():
                        f[x][q + 1] += v
        assert dict(f[top]) == L.N_dfs(k), k
    return True, 'T1：N 用自写 DFS（k<=9），U_k(m)=ΣN(k,q)C(m+1,q) 在 m<=20 成立、容斥反演一致；(b) 三元组条件与逐行字面检查在 m<=12 全等；字面 DP=前缀和 DP（m<=6,k<=12）；多重链=DP（k<=7,m<=5）；T1′ 链数=N（k<=9）'


def v19():
    U3 = L.lagrange([0, 1, 2, 3], [L.U(3, m) for m in range(4)])
    tgt = L.pscale(L.pmul([1, 1], [3, 5, 1]), Fraction(1, 3))
    alt = L.padd(L.pscale(L.pmul(L.pmul([3, 1], [2, 1]), [1, 1]), Fraction(1, 3)), [-1, -1])  # 2C(m+3,3)-(m+1)
    a84 = L.pscale([0, -1, 3, 1], Fraction(1, 3))
    ok = L.ptrim(U3) == L.ptrim(tgt) == L.ptrim(alt) == L.ptrim(L.pcompose(a84, [1, 1]))
    bf = L.read_bfile('b084990.txt')
    ok = ok and [n for n, _ in bf] == list(range(0, 1001)) and all(3 * v == n * (n * n + 3 * n - 1) for n, v in bf)
    ok = ok and all(v == L.U(3, n - 1) for n, v in bf[1:150])
    for n in range(0, 26):
        mono = sum(1 for t in product(range(1, n + 1), repeat=3) if t[0] <= t[1] <= t[2] or t[0] >= t[1] >= t[2])
        ok = ok and mono == bf[n][1]
    ok = ok and E['A084990']['N'][0] == 'a(n) = n*(n^2+3*n-1)/3.'
    return ok, 'U_3 = (m+1)(m^2+5m+3)/3 = 2C(m+3,3)-(m+1) = A084990(m+1)（多项式全等；b 文件 n<=1000；DP n<=149；单调三元组暴力 n<=25）'


def f3(t):
    a, b, c = t
    if a >= b >= c:
        return t
    if b == c and a < b:
        return (a, a, b)
    if b < c <= a:
        return (b, c, a)
    raise ValueError(t)


def g3(t):
    x, y, z = t
    if x >= y >= z:
        return t
    if x == y < z:
        return (x, z, z)
    if x < y <= z:
        return (z, x, y)
    raise ValueError(t)


def v20():
    for m in range(0, 26):
        dom = [t for t in product(range(m + 1), repeat=3) if L.legal(*t)]
        cod = {t for t in product(range(m + 1), repeat=3) if t[0] >= t[1] >= t[2] or t[0] <= t[1] <= t[2]}
        img = [f3(t) for t in dom]
        assert len(dom) == L.U(3, m) and len(set(img)) == len(dom) and set(img) == cod
        assert all(set(f3(t)) == set(t) and g3(f3(t)) == t for t in dom)
        assert all(f3(g3(t)) == t and L.legal(*g3(t)) for t in cod)
    return True, 'f3 与逆 g3（自写）对 m<=25 互逆、双射、保持取值集合'


def upper_cover_profile(P):
    le = lambda x, y: all(u <= v for u, v in zip(x, y))
    prof = []
    for x in P:
        ups = [y for y in P if y != x and le(x, y)]
        covers = [y for y in ups if not any(z != y and le(z, y) for z in ups)]
        prof.append(len(covers))
    return sorted(prof)


def chains(P):
    P = sorted(set(P), key=sum)
    k = len(P[0])
    bot, top = tuple([0] * k), tuple([1] * k)
    f = {x: defaultdict(int) for x in P}
    f[bot][0] = 1
    for i, x in enumerate(P):
        for y in P[:i]:
            if y != x and all(u <= v for u, v in zip(y, x)):
                for q, v in f[y].items():
                    f[x][q + 1] += v
    return dict(f[top])


def v21():
    P3 = list(L.allowed_rows(3))
    Q3 = [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1), (0, 0, 1), (0, 1, 1)]
    ok = chains(P3) == chains(Q3) == {1: 1, 2: 4, 3: 2}
    ok = ok and upper_cover_profile(P3) != upper_cover_profile(Q3)
    # Q3 的多重链 = 单调三元组（高度坐标：各行都在 Q3 中）
    for m in range(0, 9):
        cntQ = sum(1 for h in product(range(m + 1), repeat=3)
                   if all(tuple(int(t <= x) for x in h) in Q3 for t in range(1, m + 1)))
        mono = sum(1 for h in product(range(m + 1), repeat=3) if h[0] >= h[1] >= h[2] or h[0] <= h[1] <= h[2])
        ok = ok and cntQ == mono == L.U(3, m)
    Q4 = [(0, 0, 0, 0), (1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 0), (1, 1, 1, 1), (0, 0, 0, 1), (0, 0, 1, 1), (0, 1, 1, 1)]
    ok = ok and chains(Q4) == {1: 1, 2: 6, 3: 6, 4: 2} and L.N_dfs(4) == {1: 1, 2: 7, 3: 8, 4: 2}
    tri = sum(1 for h in product((0, 1), repeat=4) if all(h[i] <= h[i + 1] <= h[i + 2] or h[i] >= h[i + 1] >= h[i + 2] for i in range(2)))
    ok = ok and tri == 10 and 2 * comb(5, 4) - 2 == 8 and L.U(4, 1) == 9
    # 「k-2 条边」字样：k=2 时 0 条边 -> 1；「k/2 条边」k=2 -> C(m+2,2)。两种读法都 != U_2
    ok = ok and all(1 != L.U(2, m) and comb(m + 2, 2) != L.U(2, m) for m in range(1, 10))
    return ok, ('P3、Q3 链数同为 (1,4,2)，上覆盖数分布不同 %s vs %s（不同构）；Q3 多重链 = 单调三元组 = U_3（m<=8）；Q4 链数 (1,6,6,2)≠(1,7,8,2)；'
                '相邻三元组单调 k=4,m=1 为 10；「k−2 条边」若字面理解（k=2 时 0 条边）计数为 1，若理解为 k/2 条边为 C(m+2,2)，均 ≠ U_2' %
                (upper_cover_profile(P3), upper_cover_profile(Q3)))


def v22():
    U4 = L.lagrange(list(range(5)), [L.U(4, m) for m in range(5)])
    ok = all(L.peval(U4, m) == L.U(4, m) for m in range(0, 40))
    f1 = L.pscale(L.pmul(L.pmul([1, 1], [2, 1]), [6, 11, 1]), Fraction(1, 12))
    C2 = L.pscale(L.pmul([2, 1], [1, 1]), Fraction(1, 2))         # C(m+2,2)
    C4 = L.pscale(L.pmul(L.pmul([2, 1], [1, 1]), L.pmul([0, 1], [-1, 1])), Fraction(1, 24))  # C(m+2,4)
    f2 = L.padd(L.pmul(C2, C2), L.pscale(C4, -4))
    binb = L.ptrim([0])
    for q, v in {1: 1, 2: 7, 3: 8, 4: 2}.items():
        p = [Fraction(1)]
        for i in range(q):
            p = L.pmul(p, [Fraction(1 - i), Fraction(1)])
        binb = L.padd(binb, L.pscale(p, Fraction(v, factorial(q))))
    ok = ok and L.ptrim(U4) == L.ptrim(f1) == L.ptrim(f2) == L.ptrim(binb)
    ok = ok and L.peval(U4, -1) == 0 and L.peval(U4, -2) == 0
    bf = L.read_bfile('b326247.txt')
    ok = ok and [n for n, _ in bf] == list(range(0, 41)) and all(v == L.peval(U4, n - 2) for n, v in bf)
    ok = ok and all(v == L.U(4, n - 2) for n, v in bf[2:])
    # Barker 三条
    F = E['A326247']['F']
    bk = L.pscale(L.pmul([0, 1], [12, -19, 6, 1]), Fraction(1, 12))
    ok = ok and any('a(n) = (n*(12 - 19*n + 6*n^2 + n^3)) / 12.' == l for l in F)
    ok = ok and L.ptrim(bk) == L.ptrim(L.pcompose(U4, [-2, 1]))
    D5 = [1]
    for _ in range(5):
        D5 = L.pmul(D5, [1, -1])
    A = [int(L.peval(bk, n)) for n in range(0, 200)]
    ok = ok and L.series_mul(D5, A, 200) == [0, 0, 1, 4, -3] + [0] * 195
    c = L.parse_recurrence([l for l in F if l.startswith('a(n) = 5*a(n-1)')][0])
    ok = ok and c == [5, -10, 10, -5, 1] and all(A[n] == sum(c[i - 1] * A[n - i] for i in range(1, 6)) for n in range(5, 200))
    # 附注（供 c5b-35 讨论）：两边在 C(m+2,j) 基下系数同为 (j=2,3,4) -> (1,6,2)；A326247 侧按端点个数直接数
    ok = ok and all(L.U(4, m) == comb(m + 2, 2) + 6 * comb(m + 2, 3) + 2 * comb(m + 2, 4) for m in range(0, 30))
    for n in range(0, 12):
        Es = list(combinations(range(n), 2))
        byend = defaultdict(int)
        for x in Es:
            for y in Es:
                if not bad_pair(x, y):
                    byend[len(set(x) | set(y))] += 1
        ok = ok and byend.get(2, 0) == comb(n, 2) and byend.get(3, 0) == 6 * comb(n, 3) and byend.get(4, 0) == 2 * comb(n, 4)
    return ok,'U_4 = (m+1)(m+2)(m^2+11m+6)/12 = C(m+2,2)^2-4C(m+2,4) = 二项式基(1,7,8,2)（多项式全等，DP m<=39）；b326247 n=0..40；Barker 的多项式、g.f.、5 阶递推（n>4）均由闭式推出'


def bad_pair(e1, e2):
    a, b = e1
    c, d = e2
    return (a < c < b < d) or (c < a < d < b) or (a < c < d < b) or (c < a < b < d)


def v23():
    C = E['A326247']['C'][0]
    assert 'a < c < b < d or c < a < d < b' in C and 'a < c < d < b or c < a < b < d' in C
    bf = dict(L.read_bfile('b326247.txt'))
    for n in range(0, 15):
        Es = list(combinations(range(1, n + 1), 2))
        cnt = sum(1 for x in Es for y in Es if not bad_pair(x, y))
        assert cnt == comb(n, 2) ** 2 - 4 * comb(n, 4)
        if n in bf:
            assert cnt == bf[n]
    E3 = list(combinations(range(1, 4), 2))
    unord = sum(1 for i in range(3) for j in range(i, 3) if not bad_pair(E3[i], E3[j]))
    ex = [l.strip() for l in E['A326247']['e']]
    t = ' '.join(E['A326247']['t'])
    ok = unord == 6 and '{12,13}' in ex and '{13,12}' in ex and 'Tuples[' in t
    ok = ok and 'nestQ[stn_]:=' in t and '!nesXQ[#]' in t and 'nesXQ[stn_]' not in t
    return ok, 'A326247：按 %C 暴力数有序对 n<=14 = C(n,2)^2-4C(n,4) = b 文件；无序 n=3 为 6；%e 同列 {12,13}、{13,12}；%t 用 Tuples、调用未定义的 nesXQ（定义的是 nestQ）'


def type4(h):
    h1, h2, h3, h4 = h
    if h1 >= h2 >= h3 >= h4:
        return 'SSSS'
    if h1 >= h3 == h4 > h2:
        return 'ST'
    if h2 == h3 > h1 and h4 <= h3:
        return 'TS'
    if h1 >= h2 >= h4 > h3:
        return 'SSE'
    return None


def Phi(h):
    """按笔记 §5 表格逐行实现（独立重写）。返回两区间 ([x1,y1],[x2,y2])。"""
    h1, h2, h3, h4 = h
    t = type4(h)
    if t == 'SSSS' and h2 == h3:
        return ((h4, h3), (h4, h1))
    if t == 'SSSS':
        return ((h2, h1), (h4, h3))
    if t == 'ST':
        v, a, w = h1, h2, h3
        return ((a, v), (a, w)) if w < v else ((a, w), (a, a))
    if t == 'TS':
        a, v, w = h1, h2, h4
        return ((a, v), (w, v)) if w != a else ((v, v), (a, v))
    if t == 'SSE':
        v, w, a, j = h
        return ((a, j), (w, v)) if j < w else ((a, a), (j, v))
    raise ValueError(h)


def v24():
    for m in range(0, 13):
        dom = [h for h in product(range(m + 1), repeat=4) if L.legal(*h[:3]) and L.legal(*h[1:])]
        assert len(dom) == L.U(4, m)
        assert all(type4(h) is not None for h in dom)
        # 类型引理反方向：四类中的元组都合法
        allh = list(product(range(m + 1), repeat=4))
        assert all((type4(h) is not None) == (L.legal(*h[:3]) and L.legal(*h[1:])) for h in allh)
        img = {}
        for h in dom:
            I1, I2 = Phi(h)
            assert 0 <= I1[0] <= I1[1] <= m and 0 <= I2[0] <= I2[1] <= m
            assert {I1[0], I1[1], I2[0], I2[1]} == set(h)
            e = ((I1[0], I1[1] + 1), (I2[0], I2[1] + 1))
            assert e not in img
            img[e] = h
        Es = list(combinations(range(0, m + 2), 2))
        tgt = {(x, y) for x in Es for y in Es if not bad_pair(x, y)}
        assert set(img) == tgt, m
    return True, 'Φ（按笔记表格自写）对 m<=12：定义域 = U_4(m) 个合法元组（类型引理双向成立），像落在 {0..m+1} 的有序边对且两两不同、恰为不交叉不嵌套全体，保持取值集合'


def v25():
    def rows_of(h, m):
        return [tuple(int(t <= x) for x in h) for t in range(1, m + 1)]

    def acc(h):
        x1, y1, x2, y2 = h
        if not (x1 <= y1 and x2 <= y2):
            return False
        return not bad_pair((x1, y1 + 1), (x2, y2 + 1))
    ok = acc((0, 1, 1, 1)) and acc((0, 0, 0, 1)) and not acc((0, 1, 1, 2))
    ok = ok and rows_of((0, 1, 1, 2), 2) == [rows_of((0, 1, 1, 1), 1)[0], rows_of((0, 0, 0, 1), 1)[0]]
    # 区间模型计数仍 = U_4（作为对照）
    ok = ok and all(sum(1 for h in product(range(m + 1), repeat=4) if acc(h)) == L.U(4, m) for m in range(0, 9))
    return ok, '反例成立：(0,1,1,1)、(0,0,0,1) 可接受，(0,1,1,2) 的两行恰为它们的行却交叉；区间模型计数 = U_4（m<=8）'


def Nrow(k):
    if k == 0:
        return {0: 1}
    col = [L.U(k, m) for m in range(k)]
    return L.N_from_values(k, col)


def search_terms_and_result(name):
    txt = L.read_snapshot(name)
    q = re.search(r'^Search: seq:(.*)$', txt, re.M).group(1)
    terms = [int(x) for x in q.split(',')]
    if re.search(r'^No results\.', txt, re.M):
        return terms, 0, []
    tot = int(re.search(r'^Showing \d+-\d+ of (\d+)', txt, re.M).group(1))
    ids = re.findall(r'^%I (A\d{6})', txt, re.M)
    return terms, tot, ids


def cseq(i, n):
    c = []
    for t in range(n):
        c.append(1 if t < 3 else c[t - 1] + i * c[t - 3])
    return c


def expected_searches():
    W = {}
    for k in (5, 6, 7):
        for m0 in (0, 1, 2):
            W['search_U%d_m%d.txt' % (k, m0)] = [L.U(k, m) for m in range(m0, m0 + 8)]
    W['search_U3_m0.txt'] = [L.U(3, m) for m in range(0, 9)]
    W['search_U3_m2.txt'] = [L.U(3, m) for m in range(2, 11)]
    W['search_U4_m0.txt'] = [L.U(4, m) for m in range(0, 9)]
    W['search_U4_m2.txt'] = [L.U(4, m) for m in range(2, 11)]
    W['search_R.txt'] = [L.U(k, 1) for k in range(1, 13)]
    W['search_Uk2.txt'] = [L.U(k, 2) for k in range(2, 12)]
    W['search_Uk3.txt'] = [L.U(k, 3) for k in range(2, 12)]
    W['search_Uk4.txt'] = [L.U(k, 4) for k in range(2, 12)]
    W['search_Udiag.txt'] = [L.U(k, k) for k in range(0, 10)]
    NR = {k: Nrow(k) for k in range(0, 14)}
    W['search_Nflat.txt'] = [NR[k][q] for k in range(1, 7) for q in range(1, k + 1)]
    W['search_Nflat_rev.txt'] = [NR[k][q] for k in range(1, 7) for q in range(k, 0, -1)]
    W['search_Nflat_q0.txt'] = [1] + [x for k in range(1, 6) for x in [0] + [NR[k][q] for q in range(1, k + 1)]]
    W['search_Nrowsum.txt'] = [sum(NR[k].values()) for k in range(1, 11)]
    W['search_Nkk1.txt'] = [NR[k][k - 1] for k in range(4, 14)]
    W['search_Nkk2.txt'] = [NR[k][k - 2] for k in range(4, 13)]
    W['search_Nkk3.txt'] = [NR[k][k - 3] for k in range(5, 13)]
    W['search_Nk2.txt'] = [NR[k][2] for k in range(2, 13)]
    W['search_Nk3.txt'] = [NR[k][3] for k in range(3, 13)]
    hf = []
    for k in range(3, 8):
        ser = [L.U(k, m) for m in range(0, 40)]
        fac = [1]
        for _ in range(k + 1):
            fac = L.pmul(fac, [1, -1])
        h = L.series_mul(ser, fac, 40)
        assert all(x == 0 for x in h[k + 1:])
        hf += L.ptrim(h[:k + 1])
    W['search_hflat.txt'] = hf
    nf = []
    for q in range(3, 6):
        KK = 45
        ser = [0] * KK
        for k in range(0, KK):
            if k >= q:
                col = [L.U(k, m) for m in range(q)]
                s = 0
                for i in range(1, q + 1):
                    s += (-1) ** (q - i) * comb(q, i) * col[i - 1]
                ser[k] = s
        P = [1]
        for i in range(0, q):
            P = L.pmul(P, [1, -1, 0, -i])
        num = L.series_mul(ser, P, KK)
        assert all(x == 0 for x in num[3 * q - 1:KK]), q      # (C7)：分子是 3q-2 次多项式（q=5 时核到 x^44）
        nf += num[q:3 * q - 1]
    W['search_C7num.txt'] = nf
    W['search_c2.txt'] = cseq(2, 14)
    W['search_c3.txt'] = cseq(3, 14)

    def Uz(k, m):
        return 1 if k == 0 else L.U(k, m)

    def ad(kmin, mmin, lo, hi, inc):
        out = []
        for s in range(lo, hi + 1):
            cells = [(k, s - k) for k in range(kmin, s - mmin + 1)]
            out += [Uz(k, m) for k, m in (cells if inc else cells[::-1])]
        return out
    W['search_Utab_k1m1_kinc.txt'] = ad(1, 1, 4, 7, True)
    W['search_Utab_k1m1_kdec.txt'] = ad(1, 1, 4, 7, False)
    W['search_Utab_k1m0_kinc.txt'] = ad(1, 0, 4, 6, True)
    W['search_Utab_k1m0_kdec.txt'] = ad(1, 0, 4, 6, False)
    W['search_Utab_k0m0_kinc.txt'] = ad(0, 0, 4, 6, True)
    W['search_Utab_k0m0_kdec.txt'] = ad(0, 0, 4, 6, False)
    return W


W_CACHE = {}


def v26():
    W = W_CACHE.setdefault('W', expected_searches())
    out = []
    for k in (5, 6, 7):
        for m0 in (0, 1, 2):
            fn = 'search_U%d_m%d.txt' % (k, m0)
            terms, tot, ids = search_terms_and_result(fn)
            assert terms == W[fn] and tot == 0, fn
            out.append(fn)
    return True, '9 个 U_5/U_6/U_7 窗口：搜索项 = 自算值，快照均为 No results'


def v27():
    W = W_CACHE.setdefault('W', expected_searches())
    names = [n for n in W if n not in ('search_U3_m0.txt', 'search_U3_m2.txt', 'search_U4_m0.txt', 'search_U4_m2.txt',
                                       'search_R.txt', 'search_c2.txt', 'search_c3.txt') and not re.match(r'search_U[567]_', n)]
    for fn in names:
        terms, tot, ids = search_terms_and_result(fn)
        assert terms == W[fn] and tot == 0, (fn, terms, W[fn])
    # N(k,k-1)=k^2-k-4 延长
    NR = {k: Nrow(k) for k in range(4, 31)}
    assert all(NR[k][k - 1] == k * k - k - 4 for k in range(4, 31))
    return len(names) == 21, '%d 个其余无命中搜索：搜索项 = 自算值（N 用容斥，q=5 时 (C7) 分子多项式性另核到 x^44），均 No results；另 N(k,k-1)=k^2-k-4 核到 k<=30' % len(names)


def v28():
    W = W_CACHE.setdefault('W', expected_searches())
    ok = True
    for fn, want in (('search_R.txt', ['A038718']), ('search_U3_m0.txt', ['A084990']), ('search_U3_m2.txt', ['A084990']),
                     ('search_U4_m0.txt', ['A326247']), ('search_U4_m2.txt', ['A326247']),
                     ('search_c2.txt', ['A077949', 'A077974']), ('search_c3.txt', ['A084386'])):
        terms, tot, ids = search_terms_and_result(fn)
        ok = ok and terms == W[fn] and tot == len(want) and sorted(ids) == want
    t1 = L.read_snapshot('search_ref_A207123.txt')
    t2 = L.read_snapshot('search_ref_A207123_p2.txt')
    ids = re.findall(r'^%I (A\d{6})', t1, re.M) + re.findall(r'^%I (A\d{6})', t2, re.M)
    tots = re.findall(r'^Showing \d+-\d+ of (\d+)', t1, re.M) + re.findall(r'^Showing \d+-\d+ of (\d+)', t2, re.M)
    ok = ok and sorted(ids) == ['A2071%02d' % i for i in range(17, 28)] and set(tots) == {'11'}
    return ok, '有命中的 7 次搜索（R、U_3x2、U_4x2、c_2、c_3）结果与声称一致；反向引用 A207123 共 11 个 = A207117..A207127'


def v29():
    d49 = L.entry_data(E['A077949'])
    d74 = L.entry_data(E['A077974'])
    d86 = L.entry_data(E['A084386'])
    ok = d49 == cseq(2, len(d49)) and d86 == cseq(3, len(d86)) and d74 == [(-1) ** n * v for n, v in enumerate(cseq(2, len(d74)))]
    for v in (1, 2, 3, 4):
        cs = cseq(v, 12)
        for n in range(0, 10 if v <= 3 else 9):
            cnt = 0
            for w in product(range(v + 1), repeat=n):
                if all(w[i] == v or (i + 2 < n and w[i + 1] == v and w[i + 2] == v) for i in range(n)):
                    assert all(L.legal(w[i], w[i + 1], w[i + 2]) for i in range(n - 2))
                    cnt += 1
            ok = ok and cnt == cs[n] == sum(comb(n - 2 * i, i) * v ** i for i in range(0, n // 3 + 1))
    return ok, 'c_2=A077949、c_3=A084386、A077974=(-1)^n c_2（数据段）；块解释 c_v(n)=Σ_i C(n-2i,i)v^i 在 v=1..4、n<=9 穷举成立且这些序列全合法'


def v30():
    C = E['A077949']['C']
    ok = any(l.startswith('Number of compositions of n into parts 1 and two sorts of parts 2.') for l in C)
    d = L.entry_data(E['A077949'])

    def comp(n, parts):
        f = [1] + [0] * n
        for s in range(1, n + 1):
            f[s] = sum(mult * f[s - p] for p, mult in parts if p <= s)
        return f[n]
    ok = ok and comp(2, [(1, 1), (2, 2)]) == 3 and d[2] == 1
    ok = ok and [comp(n, [(1, 1), (3, 2)]) for n in range(len(d))] == d
    return ok, 'A077949 注释（parts 2）在 n=2 给 3 而数据为 1；改为 parts 3 时与整个数据段（%d 项）相符' % len(d)


def negvals(K, J):
    """用引理 1 的多项式恒等向下递推：V[m][k] = U_k(m)，m=0,-1,..,-J（k=-2..K）。"""
    cur = {k: 1 for k in range(0, K + 1)}
    cur[-1], cur[-2] = 1, 0
    V = {0: dict(cur)}
    for m in range(0, -J, -1):          # 由 U(.,m) 求 U(.,m-1)
        nxt = {-1: 1, -2: 0, 0: 1}
        for k in range(1, K + 1):
            nxt[k] = cur[k] - cur[k - 1] - m * cur[k - 3]
        V[m - 1] = nxt
        cur = nxt
    return V


def v31():
    # (1) 二项式基（自算 N，k<=40）给出的多项式值 vs 引理 1 向下递推
    K1 = 40
    V = negvals(K1, K1 + 2)
    for k in range(1, K1 + 1):
        col = [L.U(k, m) for m in range(k)]
        Nk = L.N_from_values(k, col)
        for j in range(1, K1 + 2):
            x = -j + 1                     # C(m+1,q) 在 m=-j 处 = C(1-j, q)（广义二项式）
            val = 0
            for q, v in Nk.items():
                g = 1
                for i in range(q):
                    g *= (x - i)
                val += v * g // factorial(q)
            assert val == V[-j][k], (k, j)
    # (2) 零点与 j!
    for k in range(1, K1 + 1):
        zs = [j for j in range(1, K1 + 2) if V[-j][k] == 0]
        assert zs == list(range(1, (k + 2) // 3 + 1)), (k, zs)
    for j in range(1, 14):
        assert V[-j - 1][3 * j] == factorial(j)
    # (3) Moebius（按定义）= U_k(-2)
    mus = []
    for k in range(1, 12):
        P = sorted(L.allowed_rows(k), key=sum)
        mu = {}
        for x in P:
            if x == P[0]:
                mu[x] = 1
            else:
                mu[x] = -sum(mu[y] for y in mu if all(u <= v for u, v in zip(y, x)))
        top = tuple([1] * k)
        assert mu[top] == V[-2][k], k
        mus.append(mu[top])
    return True, '二项式基多项式值 = 引理1向下递推值（k<=40, m=-1..-41）；零点集合 = {-1..-floor((k+2)/3)}（k<=40）；U_{3j}(-j-1)=j!（j<=13）；Moebius 按定义 k=1..11: %s = U_k(-2)' % mus


def v32():
    K = 150
    V = negvals(K, K + 2)
    bad = []
    for k in range(1, K + 1):
        zs = [j for j in range(1, K + 2) if V[-j][k] == 0]
        if zs != list(range(1, (k + 2) // 3 + 1)):
            bad.append((k, zs))
    return not bad, ('引理1向下递推：k<=150 时 U_k 在窗口 -1..-151 内的零点恰为 -1..-floor((k+2)/3)%s'
                     '（注意：这只是窗口检查，不覆盖更远的负实根；「全部负整数零点」的严格有限验证见 rc5b_negzeros_exact.py，k<=70）'
                     % ('' if not bad else ' 反例 %s' % bad[:3]))


def v33():
    forms = {3: ([1], [3, 5, 1], 3), 4: ([1, 2], [6, 11, 1], 12), 5: ([1, 2], [30, 77, 32, 1], 60),
             6: ([1, 2], [180, 603, 410, 66, 1], 360), 7: ([1, 2, 3], [420, 1618, 1103, 113, 1], 2520)}
    for k, (lin, rest, den) in forms.items():
        p = [Fraction(1)]
        for a in lin:
            p = L.pmul(p, [a, 1])
        p = L.pscale(L.pmul(p, rest), Fraction(1, den))
        assert len(p) == k + 1
        assert all(L.peval(p, m) == L.U(k, m) for m in range(0, 30)), k
    return True, 'U_3..U_7 的因式分解式均为 k 次，且在 m=0..29 与自算 DP 一致'


def v34():
    import numpy as np
    msg = []
    ok = True
    for n, aid in ROWS.items():
        c = L.parse_recurrence(emp_line(aid))
        e = len(c)
        m1, m2 = (n + 1) // 2, n // 2
        s1, s2 = 3 * m1 + 1, 3 * m2 + 1
        pe = s2 * (s2 + 1) // 2 + s2 * (s1 - s2)
        pp = factorial(m2) ** (s2 + 1) * factorial(m2) ** (s1 - s2) * (factorial(m1) // factorial(m2)) ** s2
        ok = ok and e == pe and c[-1] == (-1) ** (e + 1) * pp
        # 数值：根集 S_m，所有乘积是否互不相同（容差 1e-7）
        def S(m):
            rs = [1.0 + 0j]
            for i in range(1, m + 1):
                rs += list(np.roots([1, -1, 0, -i]))
            return rs
        A, B = S(m1), S(m2)
        prods = []
        seen = set()
        for i, x in enumerate(A):
            for j, y in enumerate(B):
                key = tuple(sorted([('A', i), ('B', j)]))
                prods.append(x * y)
        # 去掉由 S_{m2} ⊆ S_{m1} 造成的重复（x*y 与 y*x）
        uniq = []
        for z in prods:
            if not any(abs(z - u) < 1e-7 for u in uniq):
                uniq.append(z)
        ok = ok and len(uniq) == pe
        msg.append('%s:e=%d,预言%d,数值互异乘积%d' % (aid, e, pe, len(uniq)))
    return ok, '（观察，非证明）' + '; '.join(msg)


ALL = [('r.c5b-01', v01), ('r.c5b-02', v02), ('r.c5b-03', v03), ('r.c5b-04', v04), ('r.c5b-05', v05), ('r.c5b-06', v06),
       ('r.c5b-07', v07), ('r.c5b-08', v08), ('r.c5b-09', v09), ('r.c5b-10', v10), ('r.c5b-11', v11), ('r.c5b-12', v12),
       ('r.c5b-13', v13), ('r.c5b-14', v14), ('r.c5b-15', v15), ('r.c5b-16', v16), ('r.c5b-17', v17), ('r.c5b-18', v18),
       ('r.c5b-19', v19), ('r.c5b-20', v20), ('r.c5b-21', v21), ('r.c5b-22', v22), ('r.c5b-23', v23), ('r.c5b-24', v24),
       ('r.c5b-25', v25), ('r.c5b-26', v26), ('r.c5b-27', v27), ('r.c5b-28', v28), ('r.c5b-29', v29), ('r.c5b-30', v30),
       ('r.c5b-31', v31), ('r.c5b-32', v32), ('r.c5b-33', v33), ('r.c5b-34', v34)]

if __name__ == '__main__':
    only = sys.argv[1:]
    for cid, fn in ALL:
        if only and cid not in only:
            continue
        check(cid, fn)
    npass = sum(1 for _, ok in RES if ok)
    print('SUMMARY r-c5b pass=%d fail=%d time=%.1fs' % (npass, len(RES) - npass, time.time() - T0))
    sys.exit(0 if npass == len(RES) else 1)
