# -*- coding: utf-8 -*-
"""r-c2a 复核脚本 1：完全独立地（不导入 core / polylib / c2a_lib）重新实现
  (a) 原题定义：n x k 0/1 矩阵直接计数（行禁 001/010，列禁 001/011）；
  (b) 高度序列定义的 U_k(m)：朴素 O(k m^3) DP 与后缀和 DP；
  (c) c2a 声称的全部显式形式 F1(Theta) F2(H) F3 F4 F5 F6(Gamma 三角) F7(全正三重和)、
      Gamma 的级数除法、G_m = W_m/P_m、N(k,q) 反演式；
并在比 c2a 更大的范围内对照 (b)。只用 Python 整数。
"""
import sys
import time
from math import comb, factorial
from itertools import product

T0 = time.time()
RES = []


def rep(tag, ok, msg):
    RES.append(bool(ok))
    print(('PASS ' if ok else 'FAIL ') + tag + ' ' + msg, flush=True)


def C(a, b):
    """约定：0 除非 0 <= b <= a。"""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


# ---------------------------------------------------------------- (a) 原题直接计数
def row_ok(r):
    for i in range(len(r) - 2):
        t = r[i:i + 3]
        if t == (0, 0, 1) or t == (0, 1, 0):
            return False
    return True


def a_matrix(n, k):
    rows = [r for r in product((0, 1), repeat=k) if row_ok(r)]
    if n == 0:
        return 1
    if n == 1:
        return len(rows)

    def col3(x, y, z):
        # 列从上到下 (x_j, y_j, z_j) 不能是 001 或 011（字面检查）
        return all((x[j], y[j], z[j]) not in ((0, 0, 1), (0, 1, 1)) for j in range(k))
    R = len(rows)
    nxt = {(p, q): [s for s in range(R) if col3(rows[p], rows[q], rows[s])] for p in range(R) for q in range(R)}
    cur = {(p, q): 1 for p in range(R) for q in range(R)}
    for _ in range(n - 2):
        new = {}
        for (p, q), v in cur.items():
            for s in nxt[(p, q)]:
                new[(q, s)] = new.get((q, s), 0) + v
        cur = new
    return sum(cur.values())


def a_brute(n, k):
    cnt = 0
    for cells in product((0, 1), repeat=n * k):
        rows = [cells[i * k:(i + 1) * k] for i in range(n)]
        if not all(row_ok(tuple(r)) for r in rows):
            continue
        good = True
        for j in range(k):
            col = [rows[i][j] for i in range(n)]
            for i in range(n - 2):
                t = (col[i], col[i + 1], col[i + 2])
                if t == (0, 0, 1) or t == (0, 1, 1):
                    good = False
                    break
            if not good:
                break
        if good:
            cnt += 1
    return cnt


# ---------------------------------------------------------------- (b) 高度序列定义
def legal3(a, b, c):
    # 题面 1(b)：第 r 行在三列上的取值 ([r<=a],[r<=b],[r<=c])，禁 001、010
    # 这里直接按「存在某行 r in 1..M 使该行为 001 或 010」字面判定，而不是用化简后的条件
    for r in range(1, max(a, b, c) + 1):
        t = (int(r <= a), int(r <= b), int(r <= c))
        if t == (0, 0, 1) or t == (0, 1, 0):
            return False
    return True


def U_naive(k, m):
    """朴素 DP：状态 = 最后两个高度，转移时逐个检查 legal3（字面行规则）。"""
    if k == 0:
        return 1
    if k == 1:
        return m + 1
    ok = [[[legal3(a, b, c) for c in range(m + 1)] for b in range(m + 1)] for a in range(m + 1)]
    cnt = [[1] * (m + 1) for _ in range(m + 1)]
    for _ in range(k - 2):
        new = [[0] * (m + 1) for _ in range(m + 1)]
        for a in range(m + 1):
            for b in range(m + 1):
                v = cnt[a][b]
                if v:
                    row = ok[a][b]
                    for c in range(m + 1):
                        if row[c]:
                            new[b][c] += v
        cnt = new
    return sum(map(sum, cnt))


def U_column_fast(m, K):
    """后缀和 DP（自写）：b==c 时对 a 全求和，否则对 a>=max(b,c) 求和。"""
    out = [1]
    if K >= 1:
        out.append(m + 1)
    if K >= 2:
        n = m + 1
        cnt = [[1] * n for _ in range(n)]
        out.append(n * n)
        for _ in range(3, K + 1):
            new = [[0] * n for _ in range(n)]
            for b in range(n):
                suf = [0] * (n + 1)
                for a in range(n - 1, -1, -1):
                    suf[a] = suf[a + 1] + cnt[a][b]
                for c in range(n):
                    new[b][c] = suf[0] if b == c else suf[max(b, c)]
            cnt = new
            out.append(sum(map(sum, cnt)))
    return out


# ---------------------------------------------------------------- 原子
def stirling2(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


def hfun(s, lo, hi):
    """h_s(lo..hi)，直接按「单项式和」的 DP：逐个变量加入。"""
    row = [1] + [0] * s
    for v in range(lo, hi + 1):
        for t in range(1, s + 1):
            row[t] = row[t] + v * row[t - 1]
    return row[s] if s >= 0 else 0


def c_expl(i, n):
    if n < 0:
        return 0
    return sum(C(n - 2 * l, l) * i ** l for l in range(n // 3 + 1))


def c_rec_table(I, N):
    """c_i(n) 用 1/(1-x-i x^3) 的递推 c(n) = c(n-1) + i c(n-3)。"""
    tab = []
    for i in range(I + 1):
        c = [0] * (N + 1)
        for n in range(N + 1):
            c[n] = (1 if n == 0 else 0) + (c[n - 1] if n >= 1 else 0) + (i * c[n - 3] if n >= 3 else 0)
        tab.append(c)
    return tab


# ---------------------------------------------------------------- 主程序
# (a) 原题 vs 高度序列：a_k(n) = U_k(ceil(n/2)) U_k(floor(n/2))
ok = True
for k in range(1, 7):
    for n in range(0, 13):
        lhs = a_matrix(n, k)
        rhs = U_naive(k, (n + 1) // 2) * U_naive(k, n // 2)
        ok = ok and lhs == rhs
ok_b = all(a_brute(n, k) == a_matrix(n, k) for k in range(1, 4) for n in range(0, 6) if n * k <= 16)
rep('anchor_matrix', ok and ok_b, 'own direct matrix count a_k(n) == U_naive(ceil)U_naive(floor), k<=6, n<=12; own 2^(nk) brute == transfer (nk<=16)')

# (b) 朴素 DP vs 后缀和 DP
ok = all(U_column_fast(m, 40)[k] == U_naive(k, m) for m in range(0, 11) for k in range(0, 41))
rep('anchor_dp', ok, 'own naive O(k m^3) DP (literal row rule) == own suffix-sum DP, k<=40, m<=10')

KMAX, MMAX = 80, 25
cols = [U_column_fast(m, KMAX + 2) for m in range(MMAX + 1)]


def U(k, m):
    return cols[m][k]


S = stirling2(KMAX + MMAX + 10)
SM = KMAX // 3 + 3
Hh = {}
for m in range(MMAX + 1):
    for j in range(0, m + 2):
        Hh[(j, m)] = [hfun(s, j, m) for s in range(SM + 1)]

CT = c_rec_table(MMAX, KMAX + 3 * MMAX + 10)
ok = all(CT[i][n] == c_expl(i, n) for i in range(MMAX + 1) for n in range(len(CT[0])))
rep('c_atoms', ok, 'c_i(n) explicit sum (C(a,b)=0 unless 0<=b<=a) == recurrence c(n)=c(n-1)+i c(n-3), i<=%d, n<=%d' % (MMAX, len(CT[0]) - 1))


def cv(i, n):
    return CT[i][n] if n >= 0 else 0


def Theta(t, n, m):
    s = sum((-1) ** r * comb(t, r) * cv(m - r, n) for r in range(t + 1))
    q, rr = divmod(s, factorial(t))
    if rr:
        raise ArithmeticError('Theta not integral %d %d %d' % (t, n, m))
    return q


def Gam(n, j, m):
    """r-Stirling 内层：sum_s h_s(j..m) C(n+m-j-2s, m-j+s)。"""
    if n < 0:
        return 0
    hh = Hh[(j, m)]
    return sum(hh[s] * C(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))


def F1(k, m):
    return Theta(m, k + 1 + 3 * m, m) - sum(Theta(t, k + 3 * t, m) for t in range(m))


def F2(k, m):
    tot = sum(S[m + s][m] * C(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
    for j in range(1, m + 1):
        hh = Hh[(j, m)]
        tot += j * sum(hh[s] * C(k - 2 + m - j - 2 * s, m - j + s) for s in range(max(k - 2, 0) // 3 + 1))
    return tot


def F3(k, m):
    tot = sum(S[m + s][m] * C(k + 1 + m - 2 * s, m + s) for s in range((k + 1) // 3 + 1))
    for j in range(1, m + 1):
        hh = Hh[(j, m)]
        tot -= sum(hh[s] * C(k + m - j - 2 * s, m - j + s) for s in range(k // 3 + 1))
    return tot


def F4(k, m):
    tot = 0
    for i in range(m + 1):
        inner = cv(i, k + 3 * m)
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            inner += j * ff * cv(i, k + 3 * m - 3 * j - 2)
        tot += (-1) ** (m - i) * comb(m, i) * inner
    q, rr = divmod(tot, factorial(m))
    if rr:
        raise ArithmeticError('F4 not integral')
    return q


def F5(k, m):
    return Theta(m, k + 3 * m, m) + sum(j * Theta(m - j, k - 2 + 3 * (m - j), m) for j in range(1, m + 1))


def F7(k, m):
    def hpos(s, j):
        M = m - j
        return sum(C(M + s, M + t) * S[M + t][M] * j ** (s - t) for t in range(s + 1))
    tot = sum(hpos(s, 0) * C(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
    for j in range(1, m + 1):
        tot += j * sum(hpos(s, j) * C(k - 2 + m - j - 2 * s, m - j + s) for s in range(max(k - 2, 0) // 3 + 1))
    return tot


# F6：Gamma 三角递推（自写）
GT = {}
# 按 m 递增：Gamma_m(.;j) = Gamma_{m-1}(.;j) / b_m（系数递推），起点 Gamma_{j-1}(.;j) = delta
for j in range(0, MMAX + 1):
    prev = [1] + [0] * (KMAX + 2)            # Gamma_{j-1}(n;j)
    for m in range(j, MMAX + 1):
        new = [0] * (KMAX + 3)
        for n in range(KMAX + 3):
            new[n] = prev[n] + (new[n - 1] if n >= 1 else 0) + (m * new[n - 3] if n >= 3 else 0)
        GT[(j, m)] = new
        prev = new


def F6(k, m):
    tot = GT[(0, m)][k]
    if k >= 2:
        tot += sum(j * GT[(j, m)][k - 2] for j in range(1, m + 1))
    return tot


forms = [('F1_Theta', F1), ('F2_H', F2), ('F3', F3), ('F4', F4), ('F5_ThetaH', F5), ('F6_GammaTri', F6)]
for name, f in forms:
    t0 = time.time()
    bad = [(k, m) for m in range(MMAX + 1) for k in range(KMAX + 1) if f(k, m) != U(k, m)]
    rep('form_' + name, not bad, '== own DP for all 0<=k<=%d, 0<=m<=%d (%.1fs) first_bad=%s' % (KMAX, MMAX, time.time() - t0, bad[:3]))

bad = [(k, m) for m in range(13) for k in range(41) if F7(k, m) != U(k, m)]
rep('form_F7_allpos', not bad, 'all-positive triple sum == own DP, k<=40, m<=12; first_bad=%s' % bad[:3])

# Gamma 内层 (a) == 级数除法 == 三角递推
def series_inv_int(p, N):
    r = [0] * N
    r[0] = 1  # p[0] = 1
    for n in range(1, N):
        r[n] = -sum(p[i] * r[n - i] for i in range(1, min(n, len(p) - 1) + 1))
    return r


def polymul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


ok = True
for m in range(0, MMAX + 1):
    for j in range(0, m + 1):
        pr = [1]
        for v in range(j, m + 1):
            pr = polymul(pr, [1, -1, 0, -v])
        ser = series_inv_int(pr, KMAX + 1)
        ok = ok and all(ser[n] == Gam(n, j, m) == GT[(j, m)][n] for n in range(KMAX + 1))
rep('gamma_inner', ok, 'Gamma_m(n;j): series division of prod_{v=j}^m b_v == r-Stirling single sum == triangle recurrence, n<=%d, 0<=j<=m<=%d' % (KMAX, MMAX))

# G_m = W_m / P_m
ok = True
for m in range(0, MMAX + 1):
    P = [1]
    for v in range(0, m + 1):
        P = polymul(P, [1, -1, 0, -v])
    W = [1]
    Pj = [1]                       # P_{j-1}, j=1 -> P_0
    for j in range(1, m + 1):
        Pj = polymul(Pj, [1, -1, 0, -(j - 1)])
        term = [0, 0] + [j * a for a in Pj]
        W = [(W[i] if i < len(W) else 0) + (term[i] if i < len(term) else 0) for i in range(max(len(W), len(term)))]
    ser = series_inv_int(P, KMAX + 1)
    G = [sum(W[i] * ser[n - i] for i in range(min(n, len(W) - 1) + 1)) for n in range(KMAX + 1)]
    ok = ok and G == [U(k, m) for k in range(KMAX + 1)]
rep('gf_WP', ok, 'G_m = W_m/P_m coefficientwise == own DP, k<=%d, m<=%d' % (KMAX, MMAX))


# N(k,q) 反演 vs 自写 DFS（值域恰为 {0..q-1}）
def N_dfs(k):
    res = {}
    seq = []

    def rec():
        if len(seq) == k:
            st = set(seq)
            q = len(st)
            if max(seq) == q - 1:
                res[q] = res.get(q, 0) + 1
            return
        for v in range(k):
            if len(seq) >= 2 and not (seq[-1] == v or (seq[-2] >= seq[-1] and seq[-2] >= v)):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return res


def N_inv(k, q):
    return sum((-1) ** (q - i) * comb(q, i) * F2(k, i - 1) for i in range(1, q + 1))


t0 = time.time()
ok = True
for k in range(1, 10):
    br = N_dfs(k)
    ok = ok and all(N_inv(k, q) == br.get(q, 0) for q in range(0, k + 1))
rep('N_inversion_dfs', ok, 'N(k,q) = sum_i (-1)^(q-i) C(q,i) U_H(k,i-1) == own DFS of surjective legal words, k<=9 (%.1fs)' % (time.time() - t0))

# 额外：较大 (k,m) 的抽查（自写后缀和 DP 直接算列）
t0 = time.time()
ok = True
pts = [(150, 30), (200, 35), (120, 40), (199, 37), (90, 45)]
for (k, m) in pts:
    col = U_column_fast(m, k)
    SMk = k // 3 + 3
    for j in range(0, m + 2):
        Hh[(j, m)] = [hfun(s, j, m) for s in range(SMk + 1)]
    CT = c_rec_table(m, k + 3 * m + 10)
    S = stirling2(k + m + 10)
    vals = (F1(k, m), F2(k, m), F3(k, m), F4(k, m), F5(k, m))
    ok = ok and all(v == col[k] for v in vals)
rep('spot_large', ok, 'F1..F5 == own DP at (k,m) in %s (%.1fs)' % (pts, time.time() - t0))

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r1 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
