# -*- coding: utf-8 -*-
"""check_c5b：C-5「OEIS 只读查询与巧合还是结构」的正式核对模块。

离线运行：只读 data/oeis/ 下的快照（由 code/c5b/fetch.sh 用 curl 一次性抓取），不联网。
所有比较都用精确整数 / Fraction；本模块没有任何浮点运算。
U_k(m)、a_k(n) 一律由 core 中按原始定义写成的程序计算：
  U_fast_column / U_fast_table（高度 DP，第 1 节 (b) 的直接实现）、U_multichain（多重链）、
  a_direct（原题：行禁 001/010、列禁 001/011 的逐行转移，列三元组字面检查）、a_brute（暴力）、
  N_brute（按定义 DFS 枚举合法词）。
输出：每条结论一行 PASS/FAIL <id> <描述>，最后一行 SUMMARY c5b pass=<n> fail=<n>。
"""
import os
import re
import sys
import time
from fractions import Fraction
from itertools import product, combinations, permutations

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
ROOT = os.path.dirname(CODE)
OEIS = os.path.join(ROOT, 'data', 'oeis')
LOG = os.path.join(ROOT, 'logs', 'c5b_fetch.log')
sys.path.insert(0, CODE)

from core import (good, U_fast_column, U_fast_table, U_multichain, a_direct, a_brute,  # noqa: E402
                  N_brute, N_from_U, binom, allowed_rows, row_ok, col_ok)
from polylib import padd, psub, pmul, pscale, trim, P_poly, series_mul, series_inv  # noqa: E402

try:  # 统一用 UTF-8 输出，避免 Windows 控制台代码页导致中文乱码
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass

T_START = time.time()
NPASS = 0
NFAIL = 0


def report(cid, ok, desc):
    global NPASS, NFAIL
    if ok:
        NPASS += 1
    else:
        NFAIL += 1
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc))
    sys.stdout.flush()


def run(cid, fn):
    try:
        ok, desc = fn()
    except Exception as e:  # 任何异常都算 FAIL
        import traceback
        tb = traceback.format_exc().strip().splitlines()[-3:]
        ok, desc = False, 'exception: %r | %s' % (e, ' / '.join(tb))
    report(cid, bool(ok), desc)


# ---------------------------------------------------------------------------
# 快照解析
# ---------------------------------------------------------------------------
def read(name):
    with open(os.path.join(OEIS, name), encoding='utf-8') as f:
        return f.read()


LINE_RE = re.compile(r'^%([A-Za-z]) (A\d{6})(?: (.*))?$')
_ENTRY_CACHE = {}


def entries(name):
    """解析一个 fmt=text 快照，返回 {A号: {'lines': {tag: [...]}, 'data': [...], 'offset': int}}。"""
    if name in _ENTRY_CACHE:
        return _ENTRY_CACHE[name]
    out = {}
    for line in read(name).splitlines():
        m = LINE_RE.match(line)
        if not m:
            continue
        tag, aid, rest = m.group(1), m.group(2), m.group(3) or ''
        e = out.setdefault(aid, {'lines': {}})
        e['lines'].setdefault(tag, []).append(rest)
    for aid, e in out.items():
        L = e['lines']
        data = ''.join(L.get('S', []) + L.get('T', []) + L.get('U', []))
        e['data'] = [int(x) for x in data.split(',') if x.strip()]
        e['offset'] = int(L.get('O', ['0'])[0].split(',')[0])
    _ENTRY_CACHE[name] = out
    return out


def entry(aid):
    """在所有快照中找条目 aid（条目原文快照优先）。"""
    fn = aid + '.txt'
    if os.path.exists(os.path.join(OEIS, fn)):
        es = entries(fn)
        if aid in es:
            return es[aid]
    for fn in sorted(os.listdir(OEIS)):
        if fn.startswith('search_') and fn.endswith('.txt'):
            es = entries(fn)
            if aid in es:
                return es[aid]
    raise KeyError(aid)


def search_info(name):
    """返回 (查询串, 结果总数, A号列表)。"""
    txt = read(name)
    q = re.search(r'^Search: (.*)$', txt, re.M).group(1).strip()
    if re.search(r'^No results\.', txt, re.M):
        return q, 0, []
    m = re.search(r'^Showing (\d+)-(\d+) of (\d+)', txt, re.M)
    ids = re.findall(r'^%I (A\d{6})', txt, re.M)
    return q, int(m.group(3)), ids


def query_terms(q):
    assert q.startswith('seq:'), q
    return [int(x) for x in q[4:].split(',')]


def bfile(name):
    out = []
    for line in read(name).splitlines():
        s = line.strip()
        if not s or s.startswith('#'):
            continue
        n, v = s.split()[:2]
        out.append((int(n), int(v)))
    return out


def parse_rec(text):
    """'... a(n) = 2*a(n-1) +4*a(n-2) ... +a(n-12)[.| for n>..]' -> [c_1..c_e]（a(n)=sum c_i a(n-i)）。"""
    rhs = text.split('a(n) =', 1)[1].split(' for ')[0]
    coef = {}
    rest = rhs
    for m in re.finditer(r'([+-]?)\s*(\d*)\s*\*?\s*a\(n-(\d+)\)', rhs):
        sign = -1 if m.group(1) == '-' else 1
        c = int(m.group(2)) if m.group(2) else 1
        lag = int(m.group(3))
        assert lag not in coef
        coef[lag] = sign * c
        rest = rest.replace(m.group(0), ' ', 1)
    assert re.fullmatch(r'[\s.]*', rest), 'unparsed: %r' % rest[:80]
    e = max(coef)
    return [coef.get(i, 0) for i in range(1, e + 1)]


def parse_poly(s, var='x'):
    """'6 + 24*x + 6*x^2 - 4*x^5' -> 系数列表（升幂，int）。"""
    s = s.replace(' ', '')
    if s[0] not in '+-':
        s = '+' + s
    pat = re.compile(r'([+-])(\d*)(?:\*?(%s)(?:\^(\d+))?)?' % var)
    pos = 0
    coef = {}
    while pos < len(s):
        m = pat.match(s, pos)
        assert m and m.end() > pos, 'bad poly at %r' % s[pos:]
        sign = -1 if m.group(1) == '-' else 1
        digits, xv, ex = m.group(2), m.group(3), m.group(4)
        assert digits or xv, 'empty term in %r' % s
        c = int(digits) if digits else 1
        e = (int(ex) if ex else 1) if xv else 0
        coef[e] = coef.get(e, 0) + sign * c
        pos = m.end()
    d = max(coef)
    return trim([coef.get(i, 0) for i in range(d + 1)])


def formula_lines(aid, tag='F'):
    return entry(aid)['lines'].get(tag, [])


def find_formula(aid, prefix):
    for l in formula_lines(aid):
        if l.startswith(prefix):
            return l
    raise KeyError((aid, prefix))


# ---------------------------------------------------------------------------
# 由原始定义计算的量
# ---------------------------------------------------------------------------
_COLS = {}


def ucol(m, K):
    """[U_0(m),...,U_K(m)]（高度 DP），带缓存。"""
    c = _COLS.get(m)
    if c is None or len(c) < K + 1:
        c = U_fast_column(m, max(K, 2))
        _COLS[m] = c
    return c


def a_val(k, n):
    """a_k(n) = U_k(ceil(n/2)) U_k(floor(n/2))（归约 (a)，在 col-direct/table 等处与 a_direct 对照）。"""
    return ucol((n + 1) // 2, k)[k] * ucol(n // 2, k)[k]


def binom_poly(q, shift):
    """C(m+shift, q) 作为 m 的多项式（Fraction 系数）。"""
    p = [Fraction(1)]
    for i in range(q):
        p = pmul(p, [Fraction(shift - i), Fraction(1)])
    from math import factorial
    return pscale(p, Fraction(1, factorial(q)))


def pcompose(p, q):
    r = []
    for c in reversed(p):
        r = padd(pmul(r, q), [c])
    return trim(r)


def peval(p, x):
    r = Fraction(0)
    for c in reversed(p):
        r = r * x + c
    return r


def U_poly_from_N(k):
    """sum_q N(k,q) C(m+1,q)，N 用 N_brute（按定义 DFS）。"""
    Nk = N_brute(k)
    p = []
    for q, v in Nk.items():
        p = padd(p, pscale(binom_poly(q, 1), Fraction(v)))
    return trim(p), Nk


def berlekamp_massey(seq):
    s = [Fraction(x) for x in seq]
    C = [Fraction(1)]
    B = [Fraction(1)]
    L, m, b = 0, 1, Fraction(1)
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            if i < len(C):
                d += C[i] * s[n - i]
        if d == 0:
            m += 1
            continue
        coef = d / b
        Tm = C[:]
        need = len(B) + m
        if len(C) < need:
            C = C + [Fraction(0)] * (need - len(C))
        for i, x in enumerate(B):
            C[i + m] -= coef * x
        if 2 * L <= n:
            L, B, b, m = n + 1 - L, Tm, d, 1
        else:
            m += 1
    C = C[:L + 1] + [Fraction(0)] * max(0, L + 1 - len(C))
    return L, C


def rec_holds(a, c, n):
    """a 为 1 起标的序列（a[0] 占位），检查 a(n) = sum_i c_i a(n-i)。"""
    return a[n] == sum(ci * a[n - i] for i, ci in enumerate(c, 1) if ci)


COL_IDS = {3: 'A207118', 4: 'A207119', 5: 'A207120', 6: 'A207121', 7: 'A207122'}
ROW_IDS = {2: 'A207069', 3: 'A207070', 4: 'A207124', 5: 'A207125', 6: 'A207126', 7: 'A207127'}


# ---------------------------------------------------------------------------
# 各条核对
# ---------------------------------------------------------------------------
def chk_snapshots():
    rows = []
    with open(LOG, encoding='utf-8') as f:
        for line in f:
            p = line.rstrip('\n').split('\t')
            if len(p) >= 5:
                rows.append(p)
    urls = [p[4] for p in rows]
    names = [p[1] for p in rows]
    ok = len(rows) == 68 and len(set(urls)) == len(urls) and all(p[2] == '200' for p in rows)
    for p in rows:
        path = os.path.join(OEIS, p[1])
        ok = ok and os.path.exists(path) and os.path.getsize(path) == int(p[3]) > 0
    files = sorted(fn for fn in os.listdir(OEIS) if fn != 'INDEX.md')
    ok = ok and sorted(names) == files
    idx = read('INDEX.md')
    ok = ok and all(('`%s`' % n) in idx and u in idx for n, u in zip(names, urls))
    oeis_only = all(u.startswith('https://oeis.org/') for u in urls)
    return ok and oeis_only, ('%d 个快照、%d 个不同 URL（每个只取一次）、全部 HTTP 200、全部来自 https://oeis.org/、'
                              '文件大小与日志一致、INDEX.md 逐条列出' % (len(rows), len(set(urls))))


def chk_offsets():
    want = {'A207117': 1, 'A207118': 1, 'A207119': 1, 'A207120': 1, 'A207121': 1, 'A207122': 1,
            'A207123': 1, 'A207124': 1, 'A207125': 1, 'A207126': 1, 'A207127': 1, 'A207069': 1,
            'A207070': 1, 'A038718': 1, 'A084990': 0, 'A326247': 0, 'A002620': 0, 'A030179': 0,
            'A077949': 0, 'A077974': 0, 'A084386': 0}
    got = {a: entry(a)['offset'] for a in want}
    bad = {a: (got[a], want[a]) for a in want if got[a] != want[a]}
    return not bad, '%d 个条目的 %%O offset 与预期一致（A2071xx/A207069/A207070/A038718 为 1；A084990/A326247/A002620/A030179/A077949/A077974/A084386 为 0）%s' % (
        len(want), '' if not bad else ' 不一致: %r' % bad)


def chk_examples():
    """条目 %e 中 Hardin 给出的样例数组都满足我们对定义的读法（行禁 001/010，列禁 001/011）。"""
    total = 0
    for aid, kfix in [('A207118', 3), ('A207119', 4), ('A207120', 5), ('A207121', 6), ('A207122', 7),
                      ('A207123', None)]:
        lines = entry(aid)['lines'].get('e', [])
        i = 0
        while i < len(lines):
            m = re.match(r'Some solutions for n=(\d+)(?: k=(\d+))?', lines[i])
            if not m:
                i += 1
                continue
            n = int(m.group(1))
            k = int(m.group(2)) if m.group(2) else kfix
            block = lines[i + 1:i + 1 + n]
            chunks = [re.split(r'\.{3,}', l.strip('.')) for l in block]
            ns = len(chunks[0])
            assert all(len(c) == ns for c in chunks)
            for j in range(ns):
                arr = [tuple(int(d) for d in re.findall(r'\d', chunks[r][j])) for r in range(n)]
                assert all(len(r) == k for r in arr), (aid, arr)
                assert all(row_ok(r) for r in arr), (aid, arr)
                assert all(col_ok(tuple(arr[r][c] for r in range(n))) for c in range(k)), (aid, arr)
                total += 1
            i += 1 + n
    return total >= 30, '条目 A207118..A207123 的 %%e 样例数组共 %d 个，全部满足 core.row_ok（行禁 001/010）与 core.col_ok（列禁 001/011），确认方向读法一致' % total


def chk_col_data():
    for k, aid in COL_IDS.items():
        bf = bfile('b' + aid[1:] + '.txt')
        assert [n for n, _ in bf] == list(range(1, 211)), aid
        assert all(v == a_val(k, n) for n, v in bf), aid
        d = entry(aid)['data']
        assert d == [v for _, v in bf[:len(d)]], aid
    return True, 'A207118..A207122（k=3..7）b 文件 n=1..210 全部 = U_k(ceil(n/2))·U_k(floor(n/2))（高度 DP）；条目数据段 = b 文件前缀'


def chk_col_direct():
    cnt = 0
    for k, aid in COL_IDS.items():
        bf = dict(bfile('b' + aid[1:] + '.txt'))
        for n in range(1, 21):
            assert a_direct(n, k) == bf[n], (k, n)
            cnt += 1
        for n in range(1, 6):
            if n * k <= 14:
                assert a_brute(n, k) == bf[n], (k, n)
                cnt += 1
    return True, 'OEIS b 文件与原题定义直接计数一致：a_direct（行转移、列三元组字面检查）k=3..7、n=1..20，及 a_brute（2^(nk) 暴力）n*k<=14；共 %d 个值' % cnt


def chk_table():
    bf = bfile('b207123.txt')
    assert [n for n, _ in bf] == list(range(1, 546))
    vals = [v for _, v in bf]
    pos = 0
    s = 1
    T = {}
    while pos < len(vals):
        for i in range(1, s + 1):
            if pos >= len(vals):
                break
            T[(i, s + 1 - i)] = vals[pos]        # 第 i 行（n=i）、第 s+1-i 列（k）
            pos += 1
        s += 1
    for (n, k), v in T.items():
        assert v == a_val(k, n), (n, k)
    # 条目 %C 的 Table starts（8 行 x 10 列）
    C = entry('A207123')['lines']['C']
    i0 = C.index('Table starts')
    tab = [[int(x) for x in re.findall(r'\d+', C[i0 + 1 + r])] for r in range(8)]
    for r in range(8):
        assert len(tab[r]) == 10
        for c in range(10):
            assert tab[r][c] == a_val(c + 1, r + 1), (r, c)
    # 与原题定义直接计数对照（小范围）
    cnt = 0
    for (n, k), v in T.items():
        if n <= 10 and k <= 6:
            assert a_direct(n, k) == v
            cnt += 1
    return True, ('A207123 b 文件 545 项按反对角线（同一反对角线内行号 n 递增）解码为 T(n,k)=a_k(n)，n+k<=34 全部与高度 DP 一致；'
                  '%%C 表 8x10 一致；其中 n<=10、k<=6 的 %d 项与 a_direct 一致' % cnt)


def chk_diag():
    bf = bfile('b207117.txt')
    assert [n for n, _ in bf] == list(range(1, 20))
    assert all(v == a_val(n, n) for n, v in bf)
    d = entry('A207117')['data']
    assert d == [v for _, v in bf[:len(d)]]
    for n in range(1, 8):
        assert a_direct(n, n) == dict(bf)[n]
    return True, 'A207117（A207123 对角线）b 文件 n=1..19 = a_n(n)（高度 DP），n<=7 与 a_direct 一致'


def chk_rows():
    for n, aid in ROW_IDS.items():
        bf = bfile('b' + aid[1:] + '.txt')
        assert [k for k, _ in bf] == list(range(1, 211)), aid
        assert all(v == a_val(k, n) for k, v in bf), aid
        d = entry(aid)['data']
        assert d == [v for _, v in bf[:len(d)]], aid
        for k in range(1, 8):
            assert a_direct(n, k) == dict(bf)[k], (aid, k)
    return True, ('A207069/A207070/A207124/A207125/A207126/A207127（A207123 第 2..7 行）b 文件 k=1..210 = a_k(n)（n=2..7，高度 DP 乘积），'
                  'k<=7 与 a_direct 一致；条目数据段 = b 文件前缀')


def chk_rows23_def():
    """A207069/A207070 的定义是「竖直方向禁 001 与 101」（与本题的 001/011 不同）；直接按其定义数 2 行、3 行。"""
    def count_other(nrows, k):
        rows = allowed_rows(k)
        bad = {(0, 0, 1), (1, 0, 1)}
        c = 0
        for rs in product(rows, repeat=nrows):
            okk = True
            for j in range(k):
                col = [r[j] for r in rs]
                for i in range(nrows - 2):
                    if tuple(col[i:i + 3]) in bad:
                        okk = False
                        break
                if not okk:
                    break
            if okk:
                c += 1
        return c
    name69 = entry('A207069')['lines']['N'][0]
    name70 = entry('A207070')['lines']['N'][0]
    assert '0 0 1 and 1 0 1 vertically' in name69 and '0 0 1 and 1 0 1 vertically' in name70
    b69 = dict(bfile('b207069.txt'))
    b70 = dict(bfile('b207070.txt'))
    for k in range(1, 9):
        assert count_other(2, k) == b69[k] == a_direct(2, k)
        assert count_other(3, k) == b70[k] == a_direct(3, k)
    assert count_other(4, 1) == 8 and a_direct(4, 1) == 9          # 4 行起两个问题不同
    return True, ('A207069/A207070 名称里的竖直规则是「禁 001 与 101」；按该定义直接数 2xk、3xk 数组（k<=8）= 各自 b 文件 = 本题 a_direct(2,k)、a_direct(3,k)；'
                  '故 A207123 的「Row 2 is A207069 / Row 3 is A207070」数值上成立（一般性证明见 notes）；4 行时两问题已不同（k=1：另一规则 8，本题 9）')


def chk_col12():
    d2620 = entry('A002620')['data']
    d30179 = entry('A030179')['data']
    n1 = len(d2620) - 2
    n2 = len(d30179) - 2
    ok = all(a_val(1, n) == d2620[n + 2] for n in range(1, n1))
    ok = ok and all(a_val(2, n) == d30179[n + 2] for n in range(1, n2))
    nm = entry('A030179')['lines']['F']
    ok = ok and any('a(n) = floor(n^2/4)^2.' in l for l in nm)
    return ok, ('A207123 第 1 列 a_1(n) = A002620(n+2)（n=1..%d）、第 2 列 a_2(n) = A030179(n+2)（n=1..%d，条目公式 floor(n^2/4)^2）与条目数据段一致' % (n1 - 1, n2 - 1))


def chk_emp_col():
    msgs = []
    for k, aid in COL_IDS.items():
        c = parse_rec(find_formula(aid, 'Empirical'))
        e = len(c)
        assert e == 4 * k, (aid, e)
        # (i) 特征多项式 = (x-1)^(2k+1) (x+1)^(2k-1)
        charp = [0] * (e + 1)
        charp[e] = 1
        for i, ci in enumerate(c, 1):
            charp[e - i] = -ci
        target = [1]
        for _ in range(2 * k + 1):
            target = pmul(target, [-1, 1])
        for _ in range(2 * k - 1):
            target = pmul(target, [1, 1])
        assert trim(charp) == trim(target), aid
        # (ii) b 文件全部项
        bf = dict(bfile('b' + aid[1:] + '.txt'))
        a = [0] + [bf[n] for n in range(1, 211)]
        assert all(rec_holds(a, c, n) for n in range(e + 1, 211)), aid
        # (iii) 证明所需的有限检查：a_k(n) 在每个奇偶类上是 n 的 <=2k 次多项式 => (E^2-1)^(2k+1) 零化（d=4k+2）
        d = 4 * k + 2
        N = e + d
        a2 = [0] + [a_val(k, n) for n in range(1, N + 1)]
        assert all(rec_holds(a2, c, n) for n in range(e + 1, N + 1)), aid
        # (iv) 最小性：精确 BM（序列满足 <=e 阶递推，前 2e 项足够）
        L, Cb = berlekamp_massey(a2[1:2 * e + 1])
        assert L == e and [int(-x) for x in Cb[1:]] == c, (aid, L)
        msgs.append('k=%d:%d阶' % (k, e))
    return True, ('A207118..A207122 的 Empirical 递推（%s）：特征多项式恰为 (x-1)^(2k+1)(x+1)^(2k-1)；在 b 文件 n<=210 上成立；'
                  '在计算值 a_k(1..8k+2) 上成立（配合拟多项式零化子 (x^2-1)^(2k+1) 即为对一切 n 的证明）；精确 BM 给出最小阶 4k 且多项式相同' % ', '.join(msgs))


def chk_emp_row():
    msgs = []
    for n, aid in ROW_IDS.items():
        c = parse_rec(find_formula(aid, 'Empirical'))
        e = len(c)
        m1, m2 = (n + 1) // 2, n // 2
        dbound = (m1 + 1) ** 2 * (m2 + 1) ** 2       # (U_k(m1)U_k(m2))_{k>=2} 满足 <= dbound 阶递推（转移矩阵的 Kronecker 积）
        bf = dict(bfile('b' + aid[1:] + '.txt'))
        a = [0] + [bf[k] for k in range(1, 211)]
        assert all(rec_holds(a, c, kk) for kk in range(e + 1, 211)), aid
        N = e + 1 + dbound
        K = N + 2
        u1 = ucol(m1, K)
        u2 = ucol(m2, K)
        a2 = [0] + [u1[k] * u2[k] for k in range(1, N + 1)]
        assert all(rec_holds(a2, c, kk) for kk in range(e + 1, N + 1)), aid
        L, Cb = berlekamp_massey(a2[1:2 * e + 1])
        assert L == e and [int(-x) for x in Cb[1:]] == c, (aid, L)
        msgs.append('%s(行%d):%d阶,界%d,核到k=%d' % (aid, n, e, dbound, N))
    return True, ('A207123 第 2..7 行的 Empirical 递推全部成立：b 文件 k<=210 上成立；且在计算值上核到 k=e+1+d（d=(m1+1)^2(m2+1)^2 为转移矩阵 Kronecker 积给出的先验阶界），'
                  '据此对一切 k 成立；精确 BM 证明这些递推阶数最小。明细：' + '; '.join(msgs))


def chk_barker_207118():
    F = formula_lines('A207118')
    gf = [l for l in F if l.startswith('G.f.:')][0]
    m = re.match(r'G\.f\.: x\*\((.*)\) / \(\(1 - x\)\^7\*\(1 \+ x\)\^5\)\.$', gf)
    num = parse_poly(m.group(1))
    D = [1]
    for _ in range(7):
        D = pmul(D, [1, -1])
    for _ in range(5):
        D = pmul(D, [1, 1])
    N = 120
    A = [0] + [a_val(3, n) for n in range(1, N)]
    prod = series_mul(D, A, N)
    want = [0] + num + [0] * (N - 1 - len(num))
    assert prod == want[:N]
    ev = [l for l in F if l.endswith('for n even.')][0]
    od = [l for l in F if l.endswith('for n odd.')][0]
    pe = parse_poly(re.match(r'a\(n\) = \((.*)\) / 576 for n even\.', ev).group(1), 'n')
    po = parse_poly(re.match(r'a\(n\) = \((.*)\) / 576 for n odd\.', od).group(1), 'n')
    pe = pscale([Fraction(x) for x in pe], Fraction(1, 576))
    po = pscale([Fraction(x) for x in po], Fraction(1, 576))
    U3, _ = U_poly_from_N(3)
    half = Fraction(1, 2)
    E = pmul(pcompose(U3, [0, half]), pcompose(U3, [0, half]))            # U_3(n/2)^2
    O = pmul(pcompose(U3, [-half, half]), pcompose(U3, [half, half]))     # U_3((n-1)/2) U_3((n+1)/2)
    assert trim(E) == trim(pe) and trim(O) == trim(po)
    bf = dict(bfile('b207118.txt'))
    assert all(peval(pe if n % 2 == 0 else po, n) == bf[n] for n in range(1, 211))
    return True, ('A207118 中 Barker 的三条猜想：g.f. 分子与 (1-x)^7(1+x)^5·sum a_3(n)x^n 精确一致（系数到 x^119，>=x^13 全为 0）；'
                  '偶/奇 n 的六次多项式与 U_3(n/2)^2、U_3((n-1)/2)U_3((n+1)/2) 作为多项式恒等（U_3 由 N_brute 的二项式基给出）；b 文件 n<=210 吻合')


def chk_barker_207069():
    F = formula_lines('A207069')
    gf = [l for l in F if l.startswith('Empirical g.f.:')][0]
    m = re.match(r'Empirical g\.f\.: x\*\((.*?)\) / \((.*)\)\. - _Colin Barker_', gf)
    num = parse_poly(m.group(1))
    facs = re.findall(r'\(([^()]*)\)', '(' + m.group(2) + ')')
    D = [1]
    for f in facs:
        D = pmul(D, parse_poly(f))
    c = parse_rec(find_formula('A207069', 'Empirical: a(n)'))
    e = len(c)
    recip = [1] + [-x for x in c]                    # 1 - sum c_i x^i
    assert trim(D) == trim(recip)
    N = 150
    u1 = ucol(1, N)
    A = [0] + [u1[k] ** 2 for k in range(1, N)]
    prod = series_mul(D, A, N)
    assert prod == ([0] + num + [0] * N)[:N]
    # 分母因子的根解释（精确多项式恒等）：f(y)=y^3-y^2-1；f(y)f(-y) = -(z^3-z^2-2z-1)|_{z=y^2}（根的平方）；
    # -y^3 f(1/y) = y^3+y-1（根的倒数）；对应的 x 因子 1-x-2x^2-x^3、1+x^2-x^3 恰在分母中
    f = [-1, 0, -1, 1]
    fneg = [c * (-1) ** i for i, c in enumerate(f)]
    sq = [-1, 0, -2, 0, -1, 0, 1]                    # z^3-z^2-2z-1 在 z=y^2 处
    assert trim(pmul(f, fneg)) == trim([-c for c in sq])
    assert [-c for c in f[::-1]] == [-1, 1, 0, 1]     # y^3+y-1（升幂）
    assert [1, -1, -2, -1] in [parse_poly(x) for x in facs] and [1, 0, 1, -1] in [parse_poly(x) for x in facs]
    return True, ('A207069 中 Barker 的经验 g.f.：分母四因子之积 = 1 - sum c_i x^i（与 10 阶经验递推一致），分子与 D·sum R_k^2 x^k 精确一致（到 x^149）；'
                  '因递推已证（见 c5b.emp-row），该 g.f. 成立；分母因子 1-x-2x^2-x^3、1+x^2-x^3 分别对应 rho_i^2、1/rho_l（y^3-y^2-1 的根的平方、倒数，精确多项式恒等）')


def chk_R_data():
    bf = bfile('b038718.txt')
    assert [n for n, _ in bf] == list(range(1, 6024))
    col = ucol(1, 6021)
    ok = bf[0][1] == 1 and all(v == col[n - 2] for n, v in bf[1:])
    R = col
    ok = ok and all(R[k] == R[k - 1] + R[k - 3] + 1 for k in range(3, 6022))
    d = entry('A038718')['data']
    ok = ok and d == [v for _, v in bf[:len(d)]]
    return ok, ('A038718 offset=1：b 文件 n=1..6023 中 a(1)=1，且 a(n)=U_{n-2}(1)=R_{n-2}（n>=2，高度 DP m=1），即 R_k=A038718(k+2)（k=0..6021；提示词的 a(k+2) 正确）；'
                'R_k=R_{k-1}+R_{k-3}+1 在 3<=k<=6021 成立')


def ham_paths(n):
    """P_n^2（|i-j|<=2）中从 1 出发的 Hamilton 路（DFS，只走合法步）。"""
    res = []
    path = [1]
    used = {1}

    def dfs():
        if len(path) == n:
            res.append(tuple(path))
            return
        x = path[-1]
        for y in (x - 2, x - 1, x + 1, x + 2):
            if 1 <= y <= n and y not in used:
                used.add(y)
                path.append(y)
                dfs()
                path.pop()
                used.discard(y)
    dfs()
    return res


def row_to_path(w):
    """允许行（长 k）-> P_{k+2}^2 中从 1 出发的 Hamilton 路（按两边相同的递归分解）。"""
    k = len(w)
    n = k + 2
    if all(x == 0 for x in w):
        odds = list(range(1, n + 1, 2))
        evens = list(range(2, n + 1, 2))
        return tuple(odds + evens[::-1])           # 1,3,5,...,6,4,2：唯一以 2 结尾的路
    if w[0] == 1:
        return (1,) + tuple(v + 1 for v in row_to_path(w[1:]))
    if w[:2] == (0, 1):
        if k == 2:
            return (1, 3, 2, 4)
        assert w[2] == 1
        return (1, 3, 2) + tuple(v + 3 for v in row_to_path(w[3:]))
    raise ValueError(w)


def chk_R_def():
    bf = dict(bfile('b038718.txt'))
    for n in range(1, 10):                       # A038718 的原始定义：置换 P，P(1)=1，|P^-1(i+1)-P^-1(i)| in {1,2}
        cnt = 0
        for rest in permutations(range(2, n + 1)):
            P = (1,) + rest
            inv = [0] * (n + 1)
            for pos, val in enumerate(P, 1):
                inv[val] = pos
            if all(abs(inv[i + 1] - inv[i]) in (1, 2) for i in range(1, n)):
                cnt += 1
        assert cnt == bf[n], n
        assert len(ham_paths(n)) == cnt
    for k in range(0, 11):
        rows = allowed_rows(k) if k > 0 else ((),)
        img = [row_to_path(tuple(w)) for w in rows]
        assert len(set(img)) == len(img) == len(rows)
        assert set(img) == set(ham_paths(k + 2)), k
    return True, ('A038718 的原始定义（P(1)=1 且相邻值位置差为 1 或 2 的置换 = P_n^2 中从 1 出发的 Hamilton 路）按置换暴力数 n<=9 = b 文件；'
                  '允许行 -> Hamilton 路的递归映射（全 0 行<->以 2 结尾的之字形路；1w<->1→2·路(w)；011w<->1→3→2→4·路(w)）对 k=0..10 是双射')


def chk_R_gf():
    N = 200
    R = ucol(1, N)[:N]
    D = pmul([1, -1], [1, -1, 0, -1])
    g1 = series_mul([1, 0, 1, -1], series_inv(D, N), N)           # (1+x^2-x^3)/((1-x)(1-x-x^3))
    g2 = series_mul([1, -1, 1], series_inv(D, N), N)              # (1-x+x^2)/((1-x)(1-x-x^3))
    ok = [int(x) for x in g1] == R
    ok = ok and [int(x) for x in g2] == [1] + R[:N - 1]           # = 1 + x * sum R_k x^k
    ok = ok and int(g2[1]) != R[1]                                 # 若把它当作 sum R_k x^k，x^1 系数 1 != R_1 = 2
    gtxt = find_formula('A038718', 'G.f.:')
    ok = ok and '(1 -x +x^2)/(1-2*x+x^2-x^3+x^4)' in gtxt and D == [1, -2, 1, -1, 1]
    return ok, ('sum_{k>=0} R_k x^k = (1+x^2-x^3)/((1-x)(1-x-x^3))（到 x^199）；提示词与 A038718 条目里的 (1-x+x^2)/((1-x)(1-x-x^3)) = 1 + x·sum R_k x^k'
                '（按 OEIS 下标 = sum_n A038718(n+1) x^n），不是 sum R_k x^k 本身；分母 (1-x)(1-x-x^3)=1-2x+x^2-x^3+x^4 正确')


def chk_binom_basis():
    T = U_fast_table(8, 15)
    for k in range(1, 9):
        Nk = N_brute(k)
        for m in range(0, 16):
            assert T[k][m] == sum(v * binom(m + 1, q) for q, v in Nk.items()), (k, m)
    for k in range(1, 7):
        for m in range(0, 5):
            assert U_multichain(k, m) == T[k][m]
    return True, '工具定理 U_k(m) = sum_q N(k,q) C(m+1,q)：N 用 N_brute（按定义 DFS），对 1<=k<=8、0<=m<=15 与高度 DP 一致；高度 DP 与多重链定义 k<=6、m<=4 一致'


def chk_U3():
    bf = bfile('b084990.txt')
    assert [n for n, _ in bf] == list(range(0, 1001))
    assert entry('A084990')['lines']['N'][0] == 'a(n) = n*(n^2+3*n-1)/3.'
    ok = all(v * 3 == n * (n * n + 3 * n - 1) for n, v in bf)
    ok = ok and all(v == ucol(n - 1, 3)[3] for n, v in bf[1:122]) and bf[0][1] == 0
    for n in range(0, 21):
        mono = sum(1 for t in product(range(1, n + 1), repeat=3) if t[0] <= t[1] <= t[2] or t[0] >= t[1] >= t[2])
        ok = ok and mono == bf[n][1]
    U3, N3 = U_poly_from_N(3)
    ok = ok and N3 == {1: 1, 2: 4, 3: 2}
    target = pscale(pmul([1, 1], [3, 5, 1]), Fraction(1, 3))                  # (m+1)(m^2+5m+3)/3
    a084990 = pscale([0, -1, 3, 1], Fraction(1, 3))                             # n(n^2+3n-1)/3
    ok = ok and trim(U3) == trim(target) and trim(pcompose(a084990, [1, 1])) == trim(target)
    ok = ok and peval(U3, -1) == 0
    return ok, ('U_3(m)=A084990(m+1)：N(3,.)=(1,4,2)（DFS）给出 U_3(m)=(m+1)(m^2+5m+3)/3，与条目定义 n(n^2+3n-1)/3 在 n=m+1 处多项式恒等；'
                'b 文件 n=0..1000 = 该多项式，n=1..121 = 高度 DP 的 U_3(n-1)；条目注释「[n]^3 中单调三元组」按暴力 n<=20 成立')


def f3(t):
    a, b, c = t
    if a >= b >= c:
        return (a, b, c)
    if b == c:
        return (a, a, b)
    return (b, c, a)


def chk_bij3():
    for m in range(0, 21):
        L = [t for t in product(range(m + 1), repeat=3) if good(*t)]
        img = [f3(t) for t in L]
        mono = {t for t in product(range(m + 1), repeat=3) if t[0] >= t[1] >= t[2] or t[0] <= t[1] <= t[2]}
        assert len(L) == ucol(m, 3)[3]
        assert len(set(img)) == len(img) and set(img) == mono
        assert all(set(f3(t)) == set(t) for t in L)
    return True, '草稿 §3 的 U_3 双射（非增不动；(a<b=c)->(a,a,b)；(b<c<=a)->(b,c,a)）对 m<=20 是「合法三元组 -> 单调三元组」的双射且保持取值集合'


def chains_count(elems):
    """有界偏序集（0/1 元组，逐分量序）中从全 0 到全 1、恰好 q 步的链数 b_q。"""
    elems = sorted(set(elems), key=sum)
    k = len(elems[0])
    bot, top = tuple([0] * k), tuple([1] * k)
    le = lambda x, y: all(a <= b for a, b in zip(x, y))
    # f[x][q] = 从 bot 到 x 恰 q 步的链数
    f = {x: {} for x in elems}
    f[bot][0] = 1
    order = elems                    # 按重量排序即为线性扩张
    for i, x in enumerate(order):
        if x == bot:
            continue
        for y in order[:i]:
            if y != x and le(y, x):
                for q, v in f[y].items():
                    f[x][q + 1] = f[x].get(q + 1, 0) + v
    return {q: v for q, v in f[top].items()}


def multichains(elems, m):
    if m == 0:
        return 1
    le = lambda x, y: all(a <= b for a, b in zip(x, y))
    E = list(elems)
    f = [1] * len(E)
    for _ in range(m - 1):
        f = [sum(f[i] for i in range(len(E)) if le(E[j], E[i])) for j in range(len(E))]
    return sum(f)


def chk_zeta3():
    P3 = list(allowed_rows(3))
    Q3 = [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1), (0, 0, 1), (0, 1, 1)]   # 非增行 ∪ 非减行
    bP, bQ = chains_count(P3), chains_count(Q3)
    ok = bP == bQ == {1: 1, 2: 4, 3: 2} == N_brute(3)
    for m in range(0, 9):
        ok = ok and multichains(Q3, m) == 2 * binom(m + 3, 3) - (m + 1) == U_multichain(3, m)
    le = lambda x, y: all(a <= b for a, b in zip(x, y))
    iso = False
    for perm in permutations(range(6)):
        if all(le(P3[i], P3[j]) == le(Q3[perm[i]], Q3[perm[j]]) for i in range(6) for j in range(6)):
            iso = True
            break
    ok = ok and not iso
    for k in range(1, 8):
        ok = ok and chains_count(list(allowed_rows(k))) == N_brute(k)
    Q4 = [(0, 0, 0, 0), (1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 0), (1, 1, 1, 1), (0, 0, 0, 1), (0, 0, 1, 1), (0, 1, 1, 1)]
    ok = ok and chains_count(Q4) == {1: 1, 2: 6, 3: 6, 4: 2} != N_brute(4)
    ok = ok and multichains(Q4, 1) == 8 != U_multichain(4, 1) == 9
    # 其他「自然推广」在小 k 处即失效（笔记 §6）
    ok = ok and 2 * binom(1 + 4, 4) - (1 + 1) == 8                                   # 单调 4 元组，m=1
    tri_mono = sum(1 for h in product(range(2), repeat=4)
                   if all((h[i] <= h[i + 1] <= h[i + 2]) or (h[i] >= h[i + 1] >= h[i + 2]) for i in range(2)))
    ok = ok and tri_mono == 10                                                       # 每个相邻三元组单调，m=1,k=4
    ok = ok and binom(1 + 2, 2) == 3 != U_multichain(2, 1) == 4                      # 「k/2 条边」族在 k=2 处
    return ok, ('U_3 的结构解释：允许行偏序集 P_3 与「单调行」偏序集 Q_3（两条 4 元链粘合首尾）链数向量同为 (1,4,2)=N(3,.)，Q_3 的多重链 = 单调三元组（m<=8），'
                '但 P_3 与 Q_3 不同构（720 个双射穷举）；且 N(k,q) = P_k 中 0->1 的 q 步链数（k<=7）；k=4 的单调行偏序集链数 (1,6,6,2) != N(4,.)，单调 4 元组 != U_4；'
                '「每个相邻三元组单调」在 m=1,k=4 为 10 != 9，「k/2 条边」族在 k=2 为 C(3,2)=3 != 4')


def chk_U4():
    bf = bfile('b326247.txt')
    assert [n for n, _ in bf] == list(range(0, 41))
    ok = all(v == ucol(n - 2, 4)[4] for n, v in bf[2:]) and bf[0][1] == 0 and bf[1][1] == 0
    U4, N4 = U_poly_from_N(4)
    ok = ok and N4 == {1: 1, 2: 7, 3: 8, 4: 2}
    ok = ok and peval(U4, -1) == 0 and peval(U4, -2) == 0            # 对应 A326247(1)=A326247(0)=0
    closed = psub(pmul(binom_poly(2, 2), binom_poly(2, 2)), pscale(binom_poly(4, 2), Fraction(4)))   # C(m+2,2)^2-4C(m+2,4)
    ok = ok and trim(U4) == trim(closed)
    ok = ok and all(v == binom(n, 2) ** 2 - 4 * binom(n, 4) for n, v in bf)
    F = formula_lines('A326247')
    ok = ok and any('a(n) = (n*(12 - 19*n + 6*n^2 + n^3)) / 12.' in l for l in F)
    ok = ok and any('G.f.: x^2*(1 + 4*x - 3*x^2) / (1 - x)^5.' in l for l in F)
    barker = pscale(pmul([0, 1], [12, -19, 6, 1]), Fraction(1, 12))
    nclosed = pcompose(closed, [-2, 1])                                   # 换成 n=m+2 的多项式
    ok = ok and trim(barker) == trim(nclosed)
    factored = pscale(pmul(pmul([0, 1], [-1, 1]), [-12, 7, 1]), Fraction(1, 12))   # n(n-1)(n^2+7n-12)/12
    ok = ok and trim(factored) == trim(nclosed)
    D5 = [1]
    for _ in range(5):
        D5 = pmul(D5, [1, -1])
    A = [v for _, v in bf]
    ok = ok and series_mul(D5, A, 41)[:41] == ([0, 0, 1, 4, -3] + [0] * 41)[:41]
    rec = parse_rec([l for l in F if l.startswith('a(n) = 5*a(n-1)')][0])
    ok = ok and rec == [5, -10, 10, -5, 1]
    ok = ok and all(A[n] == sum(c * A[n - i] for i, c in enumerate(rec, 1)) for n in range(5, 41))
    return ok, ('U_4(m)=A326247(m+2)：N(4,.)=(1,7,8,2)（DFS）给出的 U_4 与 C(m+2,2)^2-4C(m+2,4) 多项式恒等；b 文件 n=2..40 = 高度 DP 的 U_4(n-2)，n=0,1 处 0 = 多项式在 m=-2,-1 的值；'
                'Barker 的多项式、g.f.、5 阶递推三条猜想均与闭式一致（闭式由定义证明，见 c5b.A326247-def）')


def crossing_or_nesting(e1, e2):
    a, b = e1
    c, d = e2
    cross = (a < c < b < d) or (c < a < d < b)
    nest = (a < c < d < b) or (c < a < b < d)
    return cross or nest


def chk_A326247_def():
    C = entry('A326247')['lines']['C'][0]
    assert C == 'Two edges {a,b}, {c,d} are crossing if a < c < b < d or c < a < d < b, and nesting if a < c < d < b or c < a < b < d.'
    bf = dict(bfile('b326247.txt'))
    for n in range(0, 13):
        E = list(combinations(range(1, n + 1), 2))
        ordered = sum(1 for e1 in E for e2 in E if not crossing_or_nesting(e1, e2))
        assert ordered == bf[n] == binom(n, 2) ** 2 - 4 * binom(n, 4), n
    E3 = list(combinations(range(1, 4), 2))
    unordered3 = sum(1 for i in range(len(E3)) for j in range(i, len(E3)) if not crossing_or_nesting(E3[i], E3[j]))
    ex = [l.strip() for l in entry('A326247')['lines']['e']]
    ok = unordered3 == 6 and bf[3] == 9 and '{12,13}' in ex and '{13,12}' in ex
    t = ' '.join(entry('A326247')['lines']['t'])
    typo = ('nesXQ' in t) and ('nestQ[stn_]' in t) and ('nesXQ[stn_]' not in t)
    return ok and typo, ('A326247 按 %C 的交叉/嵌套条件暴力数「边的有序对（可相同）」n<=12 = b 文件 = C(n,2)^2-4C(n,4)；按无序多重集理解 n=3 只有 6 个（数据为 9，%e 同时列出 {12,13} 与 {13,12}），'
                         '故条目实际计数有序对；另 %t 中调用的 nesXQ 与定义的 nestQ 名字不一致（疑似笔误）')


def type4(h):
    h1, h2, h3, h4 = h
    if h1 >= h2 >= h3 >= h4:
        return 'SSSS'
    if h3 == h4 > h2 and h1 >= h3:
        return 'ST'
    if h2 == h3 > h1 and h4 <= h3:
        return 'TS'
    if h1 >= h2 >= h4 > h3:
        return 'SSE'
    return None


def Phi(h):
    h1, h2, h3, h4 = h
    t = type4(h)
    if t == 'SSSS':
        return ((h2, h1), (h4, h3)) if h3 < h2 else ((h4, h3), (h4, h1))
    if t == 'ST':
        v, a, w = h1, h2, h3
        return ((a, v), (a, w)) if w < v else ((a, w), (a, a))
    if t == 'TS':
        a, v, w = h1, h2, h4
        return ((a, v), (w, v)) if w != a else ((v, v), (a, v))
    if t == 'SSE':
        v, w, a, j = h1, h2, h3, h4
        return ((a, j), (w, v)) if j < w else ((a, a), (j, v))
    raise ValueError(h)


def Phi_inv(I1, I2):
    (x1, y1), (x2, y2) = I1, I2
    if x1 == x2:
        x = x1
        if y1 <= y2:
            return (y2, y1, y1, x)                       # L<=  -> SSSS(h2=h3)
        return (y1, x, y2, y2) if x < y2 else (y1, x, y1, y1)     # L> -> ST
    if y1 == y2:
        y = y1
        return (x1, y, y, x2) if x1 < y else (x2, y, y, x2)       # R' -> TS
    if y1 < x2:
        return (y2, x2, x1, y1) if x1 < y1 else (y2, x2, x1, x2)  # D1 -> SSE
    if y2 < x1:
        return (y1, x1, y2, x2)                          # D2 -> SSSS(h2>h3)
    raise ValueError((I1, I2))


def interval_class(I1, I2):
    (x1, y1), (x2, y2) = I1, I2
    if x1 == x2:
        return 'L'
    if y1 == y2:
        return "R'"
    if y1 < x2:
        return 'D1'
    if y2 < x1:
        return 'D2'
    return None


def chk_bij4():
    for m in range(0, 11):
        L = [h for h in product(range(m + 1), repeat=4) if good(h[0], h[1], h[2]) and good(h[1], h[2], h[3])]
        assert len(L) == ucol(m, 4)[4]
        img = set()
        for h in L:
            t = type4(h)
            assert t is not None
            I1, I2 = Phi(h)
            assert 0 <= I1[0] <= I1[1] <= m and 0 <= I2[0] <= I2[1] <= m
            cls = interval_class(I1, I2)
            assert cls == {'SSSS': ('D2' if h[2] < h[1] else 'L'), 'ST': 'L', 'TS': "R'", 'SSE': 'D1'}[t]
            assert {I1[0], I1[1], I2[0], I2[1]} == set(h)
            assert Phi_inv(I1, I2) == h
            e = ((I1[0], I1[1] + 1), (I2[0], I2[1] + 1))
            assert not crossing_or_nesting(*e)
            img.add(e)
        assert len(img) == len(L)
        E = list(combinations(range(0, m + 2), 2))
        objs = {(e1, e2) for e1 in E for e2 in E if not crossing_or_nesting(e1, e2)}
        assert img == objs
    return True, ('U_4 的显式双射 Φ（SSSS/ST/TS/SSE 四类块型 -> 区间对 L/R\'/D1/D2，再 [x,y]->边{x,y+1}）对 m<=10 穷举：'
                  '像是 {0..m+1} 上不交叉不嵌套的有序边对全体（A326247(m+2) 的对象），单射、保持取值集合、逆映射 Φ^-1 逐点验证')


def chk_nonrowposet():
    """A326247 的区间模型不是任何「行集合」的多重链模型；本题与单调三元组都是。"""
    def rows_of(h, m):
        return [tuple(int(t <= x) for x in h) for t in range(1, m + 1)]

    def admissible(h):
        x1, y1, x2, y2 = h
        return x1 <= y1 and x2 <= y2 and interval_class((x1, y1), (x2, y2)) is not None
    m = 2
    good_rows = set()
    for mm in range(1, 4):
        for h in product(range(mm + 1), repeat=4):
            if admissible(h):
                good_rows.update(rows_of(h, mm))
    bad = (0, 1, 1, 2)                       # 区间 [0,1],[1,2]：交叉
    ok = (not admissible(bad)) and all(r in good_rows for r in rows_of(bad, m))
    ok = ok and admissible((0, 1, 1, 1)) and admissible((0, 0, 0, 1))
    # 对照：合法 4 元组 <=> 每一行都是允许行（归约 (b) 的多重链刻画），m<=4 穷举
    A4 = set(allowed_rows(4))
    for mm in range(0, 5):
        for h in product(range(mm + 1), repeat=4):
            lg = good(h[0], h[1], h[2]) and good(h[1], h[2], h[3])
            ok = ok and (lg == all(r in A4 for r in rows_of(h, mm)))
    return ok, ('区间模型（A326247）不是任何行集合的多重链模型：交叉的 (x1,y1,x2,y2)=(0,1,1,2) 的两行 (0,1,1,1)、(0,0,0,1) 都出现在可接受元组里；'
                '而合法 4 元组 <=> 各行均为允许行（m<=4 穷举）。故 U_4=A326247 不能解释为两个行偏序集同构/同链数')


def chk_k567():
    T = U_fast_table(7, 12)
    out = []
    for k in (5, 6, 7):
        for m0 in (0, 1, 2):
            q, tot, ids = search_info('search_U%d_m%d.txt' % (k, m0))
            terms = query_terms(q)
            assert terms == T[k][m0:m0 + 8], (k, m0)
            assert tot == 0
            out.append('U_%d(%d..%d)' % (k, m0, m0 + 7))
    return True, 'k=5,6,7 无类似对应：' + '、'.join(out) + ' 的搜索项 = 高度 DP 值，OEIS 快照均为 No results'


def chk_nohit_other():
    K = 13
    T = U_fast_table(K, K)
    NN = {k: [N_from_U(T, k, q) for q in range(0, k + 1)] for k in range(0, K + 1)}
    for k in range(1, 9):
        br = N_brute(k)
        assert [br.get(q, 0) for q in range(1, k + 1)] == NN[k][1:], k
    assert all(NN[k][2] == T[k][1] - 2 for k in range(2, K + 1))              # N(k,2) = R_k - 2
    assert all(NN[k][k - 1] == k * k - k - 4 for k in range(4, K + 1))        # N(k,k-1) = k^2-k-4（表头所写，k=4..13）
    want = {}
    want['search_Uk2.txt'] = [T[k][2] for k in range(2, 12)]
    want['search_Uk3.txt'] = [T[k][3] for k in range(2, 12)]
    want['search_Uk4.txt'] = [T[k][4] for k in range(2, 12)]
    want['search_Udiag.txt'] = [T[k][k] for k in range(0, 10)]
    flat, flatr, q0 = [], [], [1]
    for k in range(1, 7):
        flat += NN[k][1:]
        flatr += NN[k][1:][::-1]
    for k in range(1, 6):
        q0 += NN[k]
    want['search_Nflat.txt'] = flat
    want['search_Nflat_rev.txt'] = flatr
    want['search_Nflat_q0.txt'] = q0
    want['search_Nrowsum.txt'] = [sum(NN[k]) for k in range(1, 11)]
    want['search_Nkk1.txt'] = [NN[k][k - 1] for k in range(4, 14)]
    want['search_Nkk2.txt'] = [NN[k][k - 2] for k in range(4, 13)]
    want['search_Nkk3.txt'] = [NN[k][k - 3] for k in range(5, 13)]
    want['search_Nk2.txt'] = [NN[k][2] for k in range(2, 13)]
    want['search_Nk3.txt'] = [NN[k][3] for k in range(3, 13)]
    hfl = []
    for k in range(3, 8):
        ser = [T[k][m] for m in range(K + 1)]
        fac = [1]
        for _ in range(k + 1):
            fac = pmul(fac, [1, -1])
        h = series_mul(ser, fac, K + 1)          # 前 K+1 个系数是精确的（fac 为多项式）
        assert all(x == 0 for x in h[k + 1:K + 1]), k
        hfl += trim(h[:k + 1])
    want['search_hflat.txt'] = hfl
    numfl = []
    for q in range(3, 6):
        ser = [N_from_U(T, k, q) for k in range(K + 1)]
        num = series_mul(ser, P_poly(q - 1), K + 1)
        assert all(x == 0 for x in num[3 * q - 1:K + 1])
        numfl += num[q:3 * q - 1]
    want['search_C7num.txt'] = numfl

    def U(k, m):
        return 1 if k == 0 else T[k][m]

    def antidiag(kmin, mmin, lo, hi, inc):
        out = []
        for s in range(lo, hi + 1):
            cells = [(k, s - k) for k in range(kmin, s - mmin + 1)]
            if not inc:
                cells = cells[::-1]
            out += [U(k, m) for k, m in cells]
        return out
    want['search_Utab_k1m1_kinc.txt'] = antidiag(1, 1, 4, 7, True)
    want['search_Utab_k1m1_kdec.txt'] = antidiag(1, 1, 4, 7, False)
    want['search_Utab_k1m0_kinc.txt'] = antidiag(1, 0, 4, 6, True)
    want['search_Utab_k1m0_kdec.txt'] = antidiag(1, 0, 4, 6, False)
    want['search_Utab_k0m0_kinc.txt'] = antidiag(0, 0, 4, 6, True)
    want['search_Utab_k0m0_kdec.txt'] = antidiag(0, 0, 4, 6, False)
    for fn, w in want.items():
        q, tot, ids = search_info(fn)
        assert query_terms(q) == w, fn
        assert tot == 0, fn
    return True, ('其余 %d 个无命中搜索（U_k(2)/U_k(3)/U_k(4) 关于 k、对角线 U_k(k)、N 三角三种展平、行和、N(k,k-1..k-3)、N(k,2)、N(k,3)、h_k 系数、(C7) 分子、U 表六种反对角线展平）：'
                  '搜索项与由 core 重算的序列逐项一致（N 用容斥并与 DFS k<=8 对照；另核 N(k,2)=R_k-2、N(k,k-1)=k^2-k-4 于 k<=13），快照均为 No results' % len(want))


def chk_hits():
    T = U_fast_table(4, 12)
    R = ucol(1, 13)
    q, tot, ids = search_info('search_R.txt')
    ok = query_terms(q) == R[1:13] and tot == 1 and ids == ['A038718']
    for m0, rng in ((0, range(0, 9)), (2, range(2, 11))):
        q, tot, ids = search_info('search_U3_m%d.txt' % m0)
        ok = ok and query_terms(q) == [T[3][m] for m in rng] and tot == 1 and ids == ['A084990']
        q, tot, ids = search_info('search_U4_m%d.txt' % m0)
        ok = ok and query_terms(q) == [T[4][m] for m in rng] and tot == 1 and ids == ['A326247']

    def cseq(i, n):
        c = []
        for t in range(n):
            c.append(1 if t < 3 else c[t - 1] + i * c[t - 3])
        return c
    q, tot, ids = search_info('search_c2.txt')
    ok = ok and query_terms(q) == cseq(2, 14) and tot == 2 and sorted(ids) == ['A077949', 'A077974']
    q, tot, ids = search_info('search_c3.txt')
    ok = ok and query_terms(q) == cseq(3, 14) and tot == 1 and ids == ['A084386']
    q1, tot1, ids1 = search_info('search_ref_A207123.txt')
    q2, tot2, ids2 = search_info('search_ref_A207123_p2.txt')
    ok = ok and tot1 == tot2 == 11 and sorted(ids1 + ids2) == ['A2071%02d' % i for i in range(17, 28)]
    return ok, ('有命中的搜索：R_k -> 仅 A038718；U_3(0..8)、U_3(2..10) -> 仅 A084990；U_4(0..8)、U_4(2..10) -> 仅 A326247；c_2 -> A077949（及带号版 A077974）；c_3 -> A084386；'
                '引用 A207123 的条目共 11 个 = A207117..A207127；各搜索项与 core 重算值一致')


def chk_c2c3():
    def cseq(i, n):
        c = []
        for t in range(n):
            c.append(1 if t < 3 else c[t - 1] + i * c[t - 3])
        return c
    d49 = entry('A077949')['data']
    d74 = entry('A077974')['data']
    d86 = entry('A084386')['data']
    ok = d49 == cseq(2, len(d49)) and d86 == cseq(3, len(d86))
    ok = ok and d74 == [(-1) ** n * v for n, v in enumerate(cseq(2, len(d74)))]
    ok = ok and entry('A077949')['lines']['N'][0] == 'Expansion of 1/(1-x-2*x^3).'
    ok = ok and 'G.f.: 1/(1-x-3*x^3).' in entry('A084386')['lines']['F']
    # 块解释：长 n、取值 {0..v}、每个 <v 的位置后面紧跟两个 v 的序列（B_v^* 中的词）
    for v in (2, 3):
        cs = cseq(v, 10)
        for n in range(0, 9):
            cnt = 0
            for w in product(range(v + 1), repeat=n):
                if all(w[i] == v or (i + 2 < n and w[i + 1] == v and w[i + 2] == v) for i in range(n)):
                    assert all(good(w[i], w[i + 1], w[i + 2]) for i in range(n - 2))
                    cnt += 1
            ok = ok and cnt == cs[n]
    return ok, ('c_2=A077949、c_3=A084386（条目定义即 1/(1-x-2x^3)、1/(1-x-3x^3)，数据段逐项一致），A077974=(-1)^n c_2(n)；'
                '组合解释：c_v(n) = 只由第 v 层块 [v]、[a,v,v] 组成的合法序列数（v=2,3，n<=8 穷举，且这些序列都合法）')


def chk_A077949_comment():
    C = entry('A077949')['lines']['C']
    assert 'Number of compositions of n into parts 1 and two sorts of parts 2. - _Joerg Arndt_, Aug 29 2013' in C
    d = entry('A077949')['data']

    def compositions(n, parts):
        if n == 0:
            return 1
        return sum(mult * compositions(n - p, parts) for p, mult in parts if p <= n)
    as_stated = [compositions(n, [(1, 1), (2, 2)]) for n in range(0, 15)]
    as_3 = [compositions(n, [(1, 1), (3, 2)]) for n in range(0, 15)]
    ok = as_stated[2] == 3 != d[2] == 1 and as_3 == d[:15]
    return ok, ('A077949 的注释「compositions of n into parts 1 and two sorts of parts 2」与数据不符（n=2 时为 3，数据为 1）；改成「two sorts of parts 3」则 n<=14 全符（只记录，不提交）')


def chk_negzeros():
    """引理 1 的多项式形式 => U_k(-j)=0（1<=j<=floor((k+2)/3)）与 U_{3j}(-j-1)=j!；mu_{P_k}(0,1)=U_k(-2)。"""
    from math import factorial
    K = 30
    T = U_fast_table(K, K)

    def U(k, m):
        if k == -2:
            return 0
        if k in (-1, 0):
            return 1
        if m == -1:
            return 0
        return T[k][m]
    for k in range(1, K + 1):                      # 引理 1（计数形式，作为证明中用到的事实的数值复核）
        for m in range(0, K + 1):
            assert U(k, m) == U(k, m - 1) + U(k - 1, m) + m * U(k - 3, m), (k, m)

    def gb(x, q):
        r = 1
        for i in range(q):
            r *= (x - i)
        return r // factorial(q)
    NN = {k: [N_from_U(T, k, q) for q in range(0, k + 1)] for k in range(1, K + 1)}

    def Upoly(k, x):                               # 二项式基给出的多项式在整数 x 处的值
        return 1 if k == 0 else sum(NN[k][q] * gb(x + 1, q) for q in range(1, k + 1))
    for k in range(1, K + 1):
        zs = [j for j in range(1, K + 2) if Upoly(k, -j) == 0]
        assert zs == list(range(1, (k + 2) // 3 + 1)), (k, zs)
    for j in range(1, 11):
        assert Upoly(3 * j, -j - 1) == factorial(j)
    le = lambda x, y: all(a <= b for a, b in zip(x, y))
    for k in range(1, 10):
        E = sorted(allowed_rows(k), key=sum)
        mu = {E[0]: 1}
        for x in E[1:]:
            mu[x] = -sum(v for y, v in mu.items() if le(y, x))
        top = tuple([1] * k)
        alt = sum((-1) ** q * NN[k][q] for q in range(1, k + 1))
        assert mu[top] == Upoly(k, -2) == alt, k
    return True, ('引理 1（k<=30、m<=30 与高度 DP 一致）；U_k 在负整数处的零点恰为 m=-1..-floor((k+2)/3)（1<=k<=30 且 j<=31 的窗口；「至少这些」已证；「恰好」的严格有限验证见 rv-negzeros）；'
                  'U_{3j}(-j-1)=j!（j<=10，已证）；mu_{P_k}(0,1)=U_k(-2)=sum_q (-1)^q N(k,q)（按定义算 Moebius 函数，k<=9）')


def chk_polys():
    """笔记里写出的 U_3..U_7 因式分解形式（T1 保证 U_k 是 k 次多项式，故 k+1 个点即可确定；这里核 m=0..12）。"""
    forms = {
        3: ([1], [3, 5, 1], 3),                       # (m+1)(m^2+5m+3)/3
        4: ([1, 2], [6, 11, 1], 12),                  # (m+1)(m+2)(m^2+11m+6)/12
        5: ([1, 2], [30, 77, 32, 1], 60),             # (m+1)(m+2)(m^3+32m^2+77m+30)/60
        6: ([1, 2], [180, 603, 410, 66, 1], 360),     # (m+1)(m+2)(m^4+66m^3+410m^2+603m+180)/360
        7: ([1, 2, 3], [420, 1618, 1103, 113, 1], 2520),
    }
    for k, (lin, rest, den) in forms.items():
        for m in range(0, 13):
            v = 1
            for a in lin:
                v *= (m + a)
            v *= sum(c * m ** i for i, c in enumerate(rest))
            assert v % den == 0 and v // den == ucol(m, 7)[k], (k, m)
    U4 = [binom(m + 2, 2) ** 2 - 4 * binom(m + 2, 4) for m in range(13)]
    assert U4 == [ucol(m, 7)[4] for m in range(13)]
    return True, ('U_3=(m+1)(m^2+5m+3)/3，U_4=(m+1)(m+2)(m^2+11m+6)/12，U_5=(m+1)(m+2)(m^3+32m^2+77m+30)/60，'
                  'U_6=(m+1)(m+2)(m^4+66m^3+410m^2+603m+180)/360，U_7=(m+1)(m+2)(m+3)(m^4+113m^3+1103m^2+1618m+420)/2520：m=0..12 与高度 DP 一致（k 次多项式，点数足够即恒等）')


def chk_root_products():
    """行递推的阶与常数项 = 「特征根两两之积」的预言值（根集 S_m = {1} ∪ {y^3=y^2+i 的根, i=1..m}，取自 (C2)）。"""
    from math import factorial
    msgs = []
    for n, aid in ROW_IDS.items():
        c = parse_rec(find_formula(aid, 'Empirical'))
        e = len(c)
        m1, m2 = (n + 1) // 2, n // 2
        s1, s2 = 3 * m1 + 1, 3 * m2 + 1
        pred_e = s2 * (s2 + 1) // 2 + s2 * (s1 - s2)
        P1, P2 = factorial(m1), factorial(m2)
        pred_prod = P2 ** (s2 + 1) * P2 ** (s1 - s2) * (P1 // P2) ** s2
        assert e == pred_e, (aid, e, pred_e)
        assert c[-1] == (-1) ** (e + 1) * pred_prod, (aid, c[-1], pred_prod)
        msgs.append('%s:%d阶,|常数项|=%d' % (aid, e, pred_prod))
    return True, ('（与 (C2) 的一致性检验）第 2..7 行最小递推的阶 10/22/28/49/55/85 与末项系数，恰等于「U_k(m1)、U_k(m2) 的特征根两两之积」的个数与乘积：' + '; '.join(msgs))


CHECKS = [
    ('c5b.snapshots', chk_snapshots),
    ('c5b.offsets', chk_offsets),
    ('c5b.examples', chk_examples),
    ('c5b.col-data', chk_col_data),
    ('c5b.col-direct', chk_col_direct),
    ('c5b.table', chk_table),
    ('c5b.diag', chk_diag),
    ('c5b.rows', chk_rows),
    ('c5b.rows23-def', chk_rows23_def),
    ('c5b.col12', chk_col12),
    ('c5b.emp-col', chk_emp_col),
    ('c5b.emp-row', chk_emp_row),
    ('c5b.barker-207118', chk_barker_207118),
    ('c5b.barker-207069', chk_barker_207069),
    ('c5b.R-data', chk_R_data),
    ('c5b.R-def', chk_R_def),
    ('c5b.R-gf', chk_R_gf),
    ('c5b.binom-basis', chk_binom_basis),
    ('c5b.U3', chk_U3),
    ('c5b.bij3', chk_bij3),
    ('c5b.zeta3', chk_zeta3),
    ('c5b.U4', chk_U4),
    ('c5b.A326247-def', chk_A326247_def),
    ('c5b.bij4', chk_bij4),
    ('c5b.nonrowposet', chk_nonrowposet),
    ('c5b.k567-nohit', chk_k567),
    ('c5b.nohit-other', chk_nohit_other),
    ('c5b.hits', chk_hits),
    ('c5b.c2c3', chk_c2c3),
    ('c5b.A077949-comment', chk_A077949_comment),
    ('c5b.negzeros', chk_negzeros),
    ('c5b.polys', chk_polys),
    ('c5b.root-products', chk_root_products),
]

if __name__ == '__main__':
    for cid, fn in CHECKS:
        run(cid, fn)
    print('SUMMARY c5b pass=%d fail=%d' % (NPASS, NFAIL))
    sys.exit(0 if NFAIL == 0 else 1)
