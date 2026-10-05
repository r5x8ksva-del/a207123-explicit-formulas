# -*- coding: utf-8 -*-
"""r-c5b 独立复核工具库。

刻意不导入 code/core.py、code/polylib.py、code/checks/check_c5b.py，全部按原题定义重写：
  * 行规则：每行（从左到右）任意连续三位不是 001、010；
  * 列规则：每列（从上到下）任意连续三位不是 001、011。
只用整数 / Fraction（Hankel 行列式用大素数模算术，只用于证明「非奇异」）。
"""
import os
import re
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
OEIS = os.path.join(ROOT, 'data', 'oeis')
LOGDIR = os.path.join(ROOT, 'logs')

H_FORB = {(0, 0, 1), (0, 1, 0)}      # 行（横向）禁止
V_FORB = {(0, 0, 1), (0, 1, 1)}      # 列（纵向）禁止
V_FORB_OTHER = {(0, 0, 1), (1, 0, 1)}  # A207069/A207070 名称中的纵向规则


def has3(bits, forb):
    return any(tuple(bits[i:i + 3]) in forb for i in range(len(bits) - 2))


@lru_cache(maxsize=None)
def allowed_rows(k):
    return tuple(r for r in product((0, 1), repeat=k) if not has3(r, H_FORB))


# ---------------------------------------------------------------------------
# 计数：直接按矩阵定义
# ---------------------------------------------------------------------------
def a_brute(n, k, vforb=V_FORB):
    """2^(nk) 暴力：行禁 H_FORB，列禁 vforb。"""
    c = 0
    for cells in product((0, 1), repeat=n * k):
        rows = [cells[i * k:(i + 1) * k] for i in range(n)]
        if any(has3(r, H_FORB) for r in rows):
            continue
        if any(has3([rows[i][j] for i in range(n)], vforb) for j in range(k)):
            continue
        c += 1
    return c


def a_rowpair_list(N, k, vforb=V_FORB):
    """[a(0),...,a(N)]：与 a_rowpair 相同的逐行转移，一次算出 n<=N。"""
    rows = allowed_rows(k)
    R = len(rows)
    out = [1, R]
    ok = {}
    for i in range(R):
        for j in range(R):
            ok[(i, j)] = [l for l in range(R)
                          if not any((rows[i][c], rows[j][c], rows[l][c]) in vforb for c in range(k))]
    cur = {(i, j): 1 for i in range(R) for j in range(R)}
    out.append(sum(cur.values()))
    for _ in range(3, N + 1):
        nxt = defaultdict(int)
        for (i, j), v in cur.items():
            for l in ok[(i, j)]:
                nxt[(j, l)] += v
        cur = nxt
        out.append(sum(cur.values()))
    return out[:N + 1]


def a_rowpair(n, k, vforb=V_FORB):
    """逐行转移（状态 = 最后两行），纵向三元组逐列字面检查。与 core.a_direct 独立编写。"""
    rows = allowed_rows(k)
    R = len(rows)
    if n == 0:
        return 1
    if n == 1:
        return R
    ok = {}
    for i in range(R):
        for j in range(R):
            lst = []
            for l in range(R):
                if not any((rows[i][c], rows[j][c], rows[l][c]) in vforb for c in range(k)):
                    lst.append(l)
            ok[(i, j)] = lst
    cur = {(i, j): 1 for i in range(R) for j in range(R)}
    for _ in range(n - 2):
        nxt = defaultdict(int)
        for (i, j), v in cur.items():
            for l in ok[(i, j)]:
                nxt[(j, l)] += v
        cur = nxt
    return sum(cur.values())


# ---------------------------------------------------------------------------
# U_k(m)：高度向量
# ---------------------------------------------------------------------------
def legal_literal(a, b, c, m):
    """按「第 t 行 = ([t<=a],[t<=b],[t<=c])」逐行检查 001/010。"""
    for t in range(1, m + 1):
        if (int(t <= a), int(t <= b), int(t <= c)) in H_FORB:
            return False
    return True


def legal(a, b, c):
    """归约 (b) 的三元组条件（已在 m<=12 与 legal_literal 全等核对）。"""
    return b == c or a >= max(b, c)


def U_slow(m, K, literal=False):
    """O(m^3)/步 的直接 DP：[U_0(m),...,U_K(m)]。literal=True 时三元组用逐行字面检查。"""
    vals = range(m + 1)
    out = [1, m + 1]
    if K >= 2:
        cnt = {(a, b): 1 for a in vals for b in vals}
        out.append(len(cnt))
        f = (lambda a, b, c: legal_literal(a, b, c, m)) if literal else legal
        trans = {(a, b): [c for c in vals if f(a, b, c)] for a in vals for b in vals}
        for _ in range(3, K + 1):
            new = defaultdict(int)
            for (a, b), v in cnt.items():
                for c in trans[(a, b)]:
                    new[(b, c)] += v
            cnt = new
            out.append(sum(cnt.values()))
    return out[:K + 1]


def U_col(m, K):
    """快速版（自己写的前缀和）：g[b][c] = sum_{a 合法} f[a][b]；b==c 时全体 a，否则 a>=max(b,c)。"""
    n = m + 1
    out = [1, n]
    if K < 2:
        return out[:K + 1]
    f = [[1] * n for _ in range(n)]   # f[a][b]
    out.append(n * n)
    for _ in range(3, K + 1):
        g = [[0] * n for _ in range(n)]
        for b in range(n):
            col = [f[a][b] for a in range(n)]
            tail = [0] * (n + 1)          # tail[t] = sum_{a>=t} col[a]
            for a in range(n - 1, -1, -1):
                tail[a] = tail[a + 1] + col[a]
            for c in range(n):
                g[b][c] = tail[0] if b == c else tail[max(b, c)]
        f = g
        out.append(sum(sum(r) for r in f))
    return out


_UC = {}


def U(k, m):
    """U_k(m)，m>=0，k>=0（缓存列）。"""
    col = _UC.get(m)
    if col is None or len(col) <= k:
        col = U_col(m, max(2 * k, 16))
        _UC[m] = col
    return col[k]


def a_val(k, n):
    return U(k, (n + 1) // 2) * U(k, n // 2)


def U_multichain(k, m):
    if m == 0:
        return 1
    rows = allowed_rows(k)
    le = [[all(x <= y for x, y in zip(r, s)) for s in rows] for r in rows]
    f = [1] * len(rows)                 # f[j] = 以 rows[j] 为最小元的长 t 多重链个数
    for _ in range(m - 1):
        f = [sum(f[i] for i in range(len(rows)) if le[j][i]) for j in range(len(rows))]
    return sum(f)


# ---------------------------------------------------------------------------
# N(k,q)：按定义 DFS（值域恰为 {0..q-1} 的合法词）
# ---------------------------------------------------------------------------
def N_dfs(k):
    res = defaultdict(int)
    if k == 0:
        return {0: 1}
    seq = []

    def rec():
        if len(seq) == k:
            s = set(seq)
            if s == set(range(len(s))):
                res[len(s)] += 1
            return
        for v in range(k):
            if len(seq) >= 2 and not legal(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return dict(res)


def N_from_values(k, Ulist):
    """容斥：N(k,q) = sum_i (-1)^(q-i) C(q,i) U_k(i-1)，Ulist[m] = U_k(m)，U_k(-1)=0 (k>=1)。"""
    out = {}
    for q in range(1, k + 1):
        s = 0
        for i in range(1, q + 1):
            s += (-1) ** (q - i) * comb(q, i) * Ulist[i - 1]
        out[q] = s
    return out


# ---------------------------------------------------------------------------
# 多项式（Fraction，升幂）
# ---------------------------------------------------------------------------
def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return ptrim(r)


def pscale(p, c):
    return ptrim([c * a for a in p])


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = r * x + c
    return r


def pcompose(p, q):
    r = []
    for c in reversed(p):
        r = padd(pmul(r, q), [c])
    return r


def lagrange(xs, ys):
    """返回插值多项式（Fraction 升幂系数）。"""
    n = len(xs)
    res = []
    for i in range(n):
        num = [Fraction(1)]
        den = Fraction(1)
        for j in range(n):
            if j != i:
                num = pmul(num, [Fraction(-xs[j]), Fraction(1)])
                den *= (xs[i] - xs[j])
        res = padd(res, pscale(num, Fraction(ys[i]) / den))
    return ptrim(res)


def series_mul(a, b, n):
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j in range(min(len(b), n - i)):
                r[i + j] += x * b[j]
    return r


def series_div(num, den, n):
    """num/den 的前 n 项（den[0] = ±1，整数）。"""
    assert den[0] in (1, -1)
    num = list(num) + [0] * n
    den = list(den) + [0] * n
    out = []
    for i in range(n):
        s = num[i] - sum(den[j] * out[i - j] for j in range(1, i + 1) if den[j])
        out.append(s // den[0] if den[0] == 1 else -s)
    return out


# ---------------------------------------------------------------------------
# OEIS 快照解析（自写）
# ---------------------------------------------------------------------------
def read_snapshot(name):
    with open(os.path.join(OEIS, name), encoding='utf-8') as f:
        return f.read()


def parse_entries(name):
    out = {}
    for line in read_snapshot(name).splitlines():
        mm = re.match(r'^%(\w) (A\d{6}) ?(.*)$', line)
        if not mm:
            continue
        tag, aid, rest = mm.groups()
        out.setdefault(aid, defaultdict(list))[tag].append(rest)
    return out


def all_entries():
    """合并全部快照里的条目（同一条目出现多次时，以 id: 条目快照优先）。"""
    res = {}
    names = sorted(os.listdir(OEIS))
    prim = [n for n in names if re.match(r'^A\d{6}\.txt$', n)]
    sec = [n for n in names if n.startswith('search_')]
    for n in sec + prim:          # 后写覆盖：条目快照优先
        for aid, e in parse_entries(n).items():
            res[aid] = e
    return res


def entry_data(e):
    s = ''.join(e.get('S', []) + e.get('T', []) + e.get('U', []))
    return [int(x) for x in s.split(',') if x.strip()]


def entry_offset(e):
    return int(e['O'][0].split(',')[0])


def read_bfile(name):
    out = []
    for line in read_snapshot(name).splitlines():
        s = line.strip()
        if not s or s.startswith('#'):
            continue
        a, b = s.split()[:2]
        out.append((int(a), int(b)))
    return out


def parse_recurrence(line):
    """'Empirical: a(n) = 2*a(n-1) +4*a(n-2) ... [.]' -> [c_1..c_e]，要求右边被完全解析。"""
    rhs = line.split('a(n) =', 1)[1]
    rhs = re.split(r'\sfor\s', rhs)[0]
    s = rhs.replace(' ', '').rstrip('.')
    pos = 0
    coef = {}
    pat = re.compile(r'([+-]?)(\d*)\*?a\(n-(\d+)\)')
    while pos < len(s):
        mm = pat.match(s, pos)
        if not mm or mm.end() == pos:
            raise ValueError('cannot parse at %r' % s[pos:pos + 40])
        sg = -1 if mm.group(1) == '-' else 1
        c = int(mm.group(2)) if mm.group(2) else 1
        lag = int(mm.group(3))
        if lag in coef:
            raise ValueError('dup lag %d' % lag)
        coef[lag] = sg * c
        pos = mm.end()
    e = max(coef)
    return [coef.get(i, 0) for i in range(1, e + 1)]


def parse_poly(s, var):
    s = s.replace(' ', '')
    if s[0] not in '+-':
        s = '+' + s
    pat = re.compile(r'([+-])(\d*)(\*?%s(\^(\d+))?)?' % var)
    pos = 0
    coef = defaultdict(int)
    while pos < len(s):
        mm = pat.match(s, pos)
        if not mm or mm.end() == pos:
            raise ValueError(s[pos:])
        sg = -1 if mm.group(1) == '-' else 1
        _sgn, digits, vpart, _, ex = mm.groups()
        if not digits and not vpart:
            raise ValueError('empty term')
        c = int(digits) if digits else 1
        e = (int(ex) if ex else 1) if vpart else 0
        coef[e] += sg * c
        pos = mm.end()
    return ptrim([coef.get(i, 0) for i in range(max(coef) + 1)])


# ---------------------------------------------------------------------------
# 模 p 行列式（只用于证明非奇异：det mod p != 0 => det != 0）
# ---------------------------------------------------------------------------
P61 = (1 << 61) - 1


def det_mod(M, p=P61):
    A = [[x % p for x in row] for row in M]
    n = len(A)
    det = 1
    for c in range(n):
        piv = None
        for r in range(c, n):
            if A[r][c]:
                piv = r
                break
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det = det * A[c][c] % p
        inv = pow(A[c][c], p - 2, p)
        for r in range(c + 1, n):
            if A[r][c]:
                f = A[r][c] * inv % p
                A[r] = [(x - f * y) % p for x, y in zip(A[r], A[c])]
    return det % p


def hankel_nonsingular(seq, e):
    """seq[0..2e-2] 构成的 e×e Hankel 矩阵在两个大素数下的行列式是否非零。"""
    H = [[seq[i + j] for j in range(e)] for i in range(e)]
    for p in (P61, (1 << 89) - 1):
        if det_mod(H, p) != 0:
            return True
    return False
