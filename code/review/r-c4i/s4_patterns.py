# -*- coding: utf-8 -*-
"""s4：独立复核模式展开（定理 3，C4-12/13/14）与块分解（定理 1.4，C4-2）。
  (A) 定理 1.4：对 m<=4、L<=8 的全部合法词验证分解存在且结构正确；反向生成全部块词验证合法、互不相同、个数相等。
  (B) Pat(d) 的按定义暴力枚举（DFS 合法满射词 + 自写分块 + 平凡值判定），d<=4，σ 枚举到 2d+3（检验 σ<=2d+2 的界）。
  (C) Pat(d) 的显式生成（自上而下逐层放块，a 值在放块时立即选定；每个输出词都按三元组定义复验），d<=5（可选 6）。
  (D) Φ/Ψ 双射的逐词检验：d<=3、q<=7 的全部合法满射词，检验 Φ(w) 是模式、S 满足 s_i=i (i<=β)、
      平凡值 > E 层、Ψ(Φ(w))=w、像两两不同、个数 = Σ M C+。
  (E) 用独立 N 表核对 D(k,d)=Σ M C+(k-d-β,σ-β)（d<=DPAT，k<=K），以及 C4-13 的计数与 C4-14 的族。
用法：py -3.14 s4_patterns.py [K] [DGEN]
"""
import sys, os, time, pickle
from fractions import Fraction
from math import comb, factorial
from collections import defaultdict
from itertools import product
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import legal, word_ok, dfact

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
K = int(sys.argv[1]) if len(sys.argv) > 1 else 150
DGEN = int(sys.argv[2]) if len(sys.argv) > 2 else 5
t0 = time.time()
with open(os.path.join(HERE, 'N_K%d.pkl' % K), 'rb') as fh:
    N = pickle.load(fh)['N']


def D(k, d):
    q = k - d
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


def Cp(n, r):
    return comb(n, r) if (n >= 0 and 0 <= r <= n) else 0


RES = []


def rep(tag, ok, msg):
    RES.append(ok)
    print(('OK  ' if ok else 'BAD ') + tag + ' ' + msg, flush=True)


# ---------------------------------------------------------------- 分块（自写，按「后缀最大值首次出现位置」）
def blocks_of(w):
    out, i, n = [], 0, len(w)
    while i < n:
        M = max(w[i:])
        j = w.index(M, i)
        if j == i:
            out.append(('S', M, None, i))
            i += 1
        elif j == i + 1:
            if i + 2 == n:
                out.append(('E', M, w[i], i))
                i += 2
            else:
                if w[i + 2] != M:
                    raise ValueError('Lemma A violated')
                out.append(('T', M, w[i], i))
                i += 3
        else:
            raise ValueError('first max at position >= 3')
    return out


def blocks_valid(bl):
    layers = [b[1] for b in bl]
    if any(layers[i] < layers[i + 1] for i in range(len(layers) - 1)):
        return False
    for idx, b in enumerate(bl):
        if b[0] == 'E' and idx != len(bl) - 1:
            return False
        if b[0] in 'TE' and not (b[2] < b[1]):
            return False
    return True


def flatten(bl):
    w = []
    for b in bl:
        if b[0] == 'S':
            w.append(b[1])
        elif b[0] == 'T':
            w += [b[2], b[1], b[1]]
        else:
            w += [b[2], b[1]]
    return tuple(w)


def trivial_set(w, bl):
    mu = defaultdict(int)
    for x in w:
        mu[x] += 1
    return {b[1] for b in bl if b[0] == 'S' and mu[b[1]] == 1}


# ---------------------------------------------------------------- (A) 定理 1.4
okA = True
for m in range(1, 5):
    for L in range(0, 9):
        legal_words = [w for w in product(range(1, m + 1), repeat=L) if word_ok(w)]
        for w in legal_words:
            bl = blocks_of(w)
            if not blocks_valid(bl) or flatten(bl) != w:
                okA = False
        # 反向：生成全部块词（值 ⊆ {1..m}，长度 L）
        gen = set()

        def rec(rem, maxlayer, cur):
            if rem == 0:
                gen.add(tuple(cur))
                return
            for v in range(1, maxlayer + 1):
                if rem >= 1:
                    rec(rem - 1, v, cur + [v])
                if rem >= 3:
                    for a in range(1, v):
                        rec(rem - 3, v, cur + [a, v, v])
                if rem == 2:
                    for a in range(1, v):
                        gen.add(tuple(cur + [a, v]))
        rec(L, m, [])
        if not all(word_ok(w) for w in gen) or len(gen) != len(legal_words):
            okA = False
rep('C4-2', okA, '定理 1.4：m<=4、L<=8 的全部合法词可按规则分块且结构合法；全部块词合法且个数 == 合法词个数（双向）')


# ---------------------------------------------------------------- (B) 模式暴力（按定义）
def brute_patterns(d, sig_max):
    res = defaultdict(int)
    words = defaultdict(list)
    for sigma in range(0, sig_max + 1):
        L = sigma + d
        if sigma == 0:
            if L == 0:
                res[(0, 0)] += 1
            continue
        used = [0] * (sigma + 1)
        seq = []

        def dfs(distinct):
            n = len(seq)
            if n - distinct > d:
                return
            if sigma - distinct > L - n:
                return
            if n == L:
                bl = blocks_of(seq)
                if trivial_set(seq, bl):
                    return
                beta = bl[-1][1] if bl[-1][0] == 'E' else 0
                res[(sigma, beta)] += 1
                if d <= 3:
                    words[(sigma, beta)].append(tuple(seq))
                return
            for v in range(1, sigma + 1):
                if n >= 2 and not legal(seq[-2], seq[-1], v):
                    continue
                seq.append(v)
                used[v] += 1
                dfs(distinct + (1 if used[v] == 1 else 0))
                used[v] -= 1
                seq.pop()
        dfs(0)
    return dict(res), words


TAB4 = {
    0: {(0, 0): 1, (2, 2): 1},
    1: {(1, 0): 1, (2, 0): 1, (2, 2): 1, (3, 2): 1, (4, 2): 1, (4, 3): 2},
    2: dict([((s, 0), v) for s, v in zip(range(1, 5), [1, 4, 3, 3])] + [((s, 2), v) for s, v in zip(range(2, 7), [1, 4, 5, 3, 3])]
            + [((s, 3), v) for s, v in zip(range(3, 7), [2, 6, 4, 6])] + [((6, 4), 6)]),
    3: dict([((s, 0), v) for s, v in zip(range(1, 7), [1, 8, 17, 24, 15, 15])]
            + [((s, 2), v) for s, v in zip(range(2, 9), [2, 9, 17, 26, 27, 15, 15])]
            + [((s, 3), v) for s, v in zip(range(3, 9), [4, 14, 34, 42, 24, 30])]
            + [((s, 4), v) for s, v in zip(range(5, 9), [12, 30, 18, 36])] + [((8, 5), 24)]),
    4: dict([((s, 0), v) for s, v in zip(range(1, 9), [1, 14, 53, 110, 155, 180, 105, 105])]
            + [((s, 2), v) for s, v in zip(range(2, 11), [3, 17, 54, 115, 161, 200, 195, 105, 105])]
            + [((s, 3), v) for s, v in zip(range(3, 11), [6, 44, 132, 210, 310, 330, 180, 210])]
            + [((s, 4), v) for s, v in zip(range(4, 11), [6, 48, 114, 252, 324, 180, 270])]
            + [((s, 5), v) for s, v in zip(range(7, 11), [72, 168, 96, 240])] + [((10, 6), 120)]),
    5: dict([((s, 0), v) for s, v in zip(range(1, 11), [1, 23, 129, 394, 841, 1290, 1575, 1680, 945, 945])]
            + [((s, 2), v) for s, v in zip(range(2, 13), [4, 34, 146, 391, 802, 1341, 1665, 1890, 1785, 945, 945])]
            + [((s, 3), v) for s, v in zip(range(3, 13), [14, 114, 394, 988, 1900, 2510, 3150, 3150, 1680, 1890])]
            + [((s, 4), v) for s, v in zip(range(4, 13), [18, 126, 546, 1422, 2124, 3180, 3510, 1890, 2520])]
            + [((s, 5), v) for s, v in zip(range(6, 13), [72, 432, 888, 1968, 2640, 1440, 2520])]
            + [((s, 6), v) for s, v in zip(range(9, 13), [480, 1080, 600, 1800])] + [((12, 7), 720)]),
}
TOTALS = [2, 7, 51, 459, 4990, 63537, 928393]

BR = {}
WORDS = {}
for d in range(0, 5):
    tt = time.time()
    BR[d], WORDS[d] = brute_patterns(d, 2 * d + 3)
    over = [key for key in BR[d] if key[0] > 2 * d + 2]
    print('   brute d=%d: %d patterns, %.1fs, sigma>2d+2 found: %s' % (d, sum(BR[d].values()), time.time() - tt, over))
okB = all(BR[d] == TAB4[d] for d in range(0, 5))
rep('C4-12-brute', okB, '按定义暴力枚举的 M(d;σ,β)（σ 枚举到 2d+3）== c4.md 表 4，d<=4；σ=2d+3 处无模式')


# ---------------------------------------------------------------- (C) 显式生成
def gen_patterns(d, sigma):
    """自上而下逐层放块，a 值在放块时立即选定。返回 dict beta->count 与（小 d 时）词集合。"""
    out = defaultdict(int)
    seen = set()
    need_words = d <= 5

    def layer_options(x, budget_mu):
        """层 x 的块序列：S 与 T_a（1<=a<x）组成的序列，可再接 E_a。返回 (blocks, s, t, eps)。
        budget_mu：本层 s+2t+eps 的上界。"""
        res = []

        def rec(cur, s, t, used):
            # 不接 E
            res.append((list(cur), s, t, 0))
            if x >= 2 and used + 1 <= budget_mu:
                for a in range(1, x):
                    res.append((cur + [('E', x, a)], s, t, 1))
            if used + 1 <= budget_mu:
                rec(cur + [('S', x, None)], s + 1, t, used + 1)
            if x >= 2 and used + 2 <= budget_mu:
                for a in range(1, x):
                    rec(cur + [('T', x, a)], s, t + 1, used + 2)
        rec([], 0, 0, 0)
        return res

    def rec(x, closed, beta, blocks, acount, excess):
        # acount: dict 值->已被分配为 a 值的次数（仅 < 当前层的值）
        if x == 0:
            if excess == d:
                out[beta] += 1
                if need_words:
                    w = flatten([(b[0], b[1], b[2], 0) for b in blocks])
                    seen.add(w)
            return
        ax = acount.get(x, 0)
        pend = sum(max(0, c - 1) for y, c in acount.items() if y < x)
        if closed:
            mu = ax
            if mu < 1 or excess + mu - 1 + pend > d:
                return
            rec(x - 1, closed, beta, blocks, acount, excess + mu - 1)
            return
        budget = d - excess - pend + 1 - ax  # s+2t+eps <= budget
        for (bl, s, t, eps) in layer_options(x, max(budget, 0) + 0):
            mu = ax + s + 2 * t + eps
            if mu < 1:
                continue
            if ax == 0 and s == 1 and t == 0 and eps == 0:
                continue
            ex2 = excess + mu - 1
            # 新增 a 值
            na = dict(acount)
            for b in bl:
                if b[0] in 'TE':
                    na[b[2]] = na.get(b[2], 0) + 1
            pend2 = sum(max(0, c - 1) for y, c in na.items() if y < x)
            if ex2 + pend2 > d:
                continue
            rec(x - 1, closed or eps == 1, x if eps else beta, blocks + bl, na, ex2)

    rec(sigma, False, 0, [], {}, 0)
    return out, seen


GEN = {}
okC = True
for d in range(0, DGEN + 1):
    tt = time.time()
    M = defaultdict(int)
    nbad = 0
    tot = 0
    for sigma in range(0, 2 * d + 4):
        if sigma == 0:
            if d == 0:
                M[(0, 0)] += 1      # 空模式（σ=0），计入总数
                tot += 1
            continue
        out, seen = gen_patterns(d, sigma)
        for beta, c in out.items():
            M[(sigma, beta)] += c
        tot += sum(out.values())
        # 逐词复验（小 d）：合法、长度 σ+d、值域 {1..σ}、无平凡值、β 一致、互不相同（set 大小 == 计数）
        if d <= 5:
            if len(seen) != sum(out.values()):
                nbad += 1
            for w in seen:
                if not word_ok(w) or len(w) != sigma + d or set(w) != set(range(1, sigma + 1)):
                    nbad += 1
                    continue
                bl = blocks_of(w)
                if trivial_set(w, bl):
                    nbad += 1
    GEN[d] = dict(M)
    ok = (nbad == 0) and (d not in TAB4 or GEN[d] == TAB4[d]) and (d not in BR or GEN[d] == BR[d]) and tot == TOTALS[d]
    okC = okC and ok
    print('   gen d=%d: total %d (claimed %d), per-word recheck bad=%d, %.1fs, match table4=%s' % (
        d, tot, TOTALS[d], nbad, time.time() - tt, (GEN[d] == TAB4.get(d, GEN[d]))))
rep('C4-12-gen', okC, '显式生成的 Pat(d)（逐词按定义复验）与表 4 / 暴力 / 总数一致，d<=%d' % DGEN)


# ---------------------------------------------------------------- (E) 自写的 M 计数 DP（用于更大的 d）
def M_dp(d):
    """M(d;σ,β)：自上而下按值的计数 DP（与 (C) 同一组合描述，但只计数）。状态 (p, e, closed, beta)。"""
    res = defaultdict(int)
    if d == 0:
        res[(0, 0)] = 1
    for sigma in range(1, 2 * d + 4):
        st = {(0, 0, 0, 0): 1}
        for x in range(sigma, 0, -1):
            nst = defaultdict(int)
            for (p, e, closed, beta), w in st.items():
                for j in range(0, p + 1):
                    wj = w * comb(p, j)
                    if closed:
                        lay = [(0, 0, 0)]
                    else:
                        lay = []
                        for t in range(0, d + 2):
                            for s in range(0, d + 3):
                                for eps in (0, 1):
                                    if s + 2 * t + eps + j - 1 + e <= d:
                                        lay.append((s, t, eps))
                    for (s, t, eps) in lay:
                        mu = s + 2 * t + eps + j
                        if mu == 0 or (mu == 1 and s == 1):
                            continue
                        e2 = e + mu - 1
                        if e2 > d:
                            continue
                        nst[(p - j + t + eps, e2, 1 if (closed or eps) else 0, x if eps else beta)] += wj * comb(s + t, s)
            st = nst
        for (p, e, closed, beta), w in st.items():
            if p == 0 and e == d:
                res[(sigma, beta)] += w
    return dict(res)


DPAT = 8
MD = {d: M_dp(d) for d in range(0, DPAT + 1)}
okE0 = all(MD[d] == GEN[d] for d in range(0, DGEN + 1)) and all(sum(MD[d].values()) == TOTALS[d] for d in range(0, 7))
rep('C4-12-dp', okE0, '自写计数 DP == 显式生成（d<=%d），且总数 == 2,7,51,459,4990,63537,928393（d<=6）；d=7,8 总数 %s' % (
    DGEN, [sum(MD[d].values()) for d in (7, 8)]))

okE = True
for d in range(0, DPAT + 1):
    for k in range(d, K + 1):
        q = k - d
        if sum(w * Cp(q - b, s - b) for (s, b), w in MD[d].items()) != D(k, d):
            okE = False
            print('   expansion fails d=%d k=%d' % (d, k))
            break
rep('C4-12-exp', okE, 'D(k,d)=Σ M C+(k-d-β,σ-β) 对 d<=%d、d<=k<=%d 全成立（独立 N 表）' % (DPAT, K))

ok = True
for d in range(0, DPAT + 1):
    M = MD[d]
    df = dfact(2 * d - 1)
    for (s, b), w in M.items():
        if w <= 0 or s > 2 * d + 2 or b == 1 or b > d + 2 or (b > 0 and b > s) or s + d > 3 * d + 2:
            ok = False
    if sum(w for (s, b), w in M.items() if s - b == 2 * d) != 2 * df:
        ok = False
    if M.get((2 * d, 0), 0) != df or M.get((2 * d + 2, 2), 0) != df:
        ok = False
    if {(s, b): w for (s, b), w in M.items() if b == d + 2} != {(2 * d + 2, d + 2): factorial(d + 1)}:
        ok = False
    if any(s - b > 2 * d for (s, b) in M):
        ok = False
rep('C4-13', ok, 'σ<=2d+2、β∈{0}∪[2,d+2]、σ-β<=2d；σ-β=2d 共 2(2d-1)!!（两族各 (2d-1)!!）；β=d+2 只在 σ=2d+2、共 (d+1)!；d<=%d' % DPAT)

ok = True
for d in range(1, DPAT + 1):
    M = MD[d]
    if M.get((2 * d - 1, 0)) != dfact(2 * d - 1) or M.get((2 * d + 1, 2)) != dfact(2 * d - 1):
        ok = False
    if M.get((2 * d + 2, d + 1)) != d * factorial(d + 1) // 2:
        ok = False
    if d >= 2 and M.get((2 * d - 2, 0)) != 4 * (d - 1) * dfact(2 * d - 3):
        ok = False
rep('C4-14', ok, '四个族 M(d;2d-1,0)=M(d;2d+1,2)=(2d-1)!!, M(d;2d+2,d+1)=d(d+1)!/2, M(d;2d-2,0)=4(d-1)(2d-3)!!：1<=d<=%d 成立' % DPAT)


# ---------------------------------------------------------------- (D) Φ/Ψ 逐词检验
def Phi(w):
    bl = blocks_of(w)
    triv = trivial_set(w, bl)
    vals = sorted(set(w))
    S = [v for v in vals if v not in triv]
    rel = {v: i + 1 for i, v in enumerate(S)}
    bl2 = [b for b in bl if not (b[0] == 'S' and b[1] in triv)]
    wp = flatten([(b[0], rel[b[1]], (rel[b[2]] if b[2] is not None else None), 0) for b in bl2])
    return wp, tuple(S), triv, bl


def Psi(wp, S, q):
    bl = blocks_of(wp)
    mp = {i + 1: s for i, s in enumerate(S)}
    bl = [(b[0], mp[b[1]], (mp[b[2]] if b[2] is not None else None)) for b in bl]
    ins = [x for x in range(1, q + 1) if x not in set(S)]
    # 插入：S 块 [x] 放在所有层 > x 的块之后、层 < x 的块之前
    out = []
    i = 0
    for x in sorted(ins, reverse=True):
        while i < len(bl) and bl[i][1] > x:
            out.append(bl[i])
            i += 1
        if i < len(bl) and bl[i][1] == x:
            raise ValueError('layer collision')
        out.append(('S', x, None))
    out += bl[i:]
    return flatten([(b[0], b[1], b[2], 0) for b in out])


okD = True
detail = []
for d in range(0, 4):
    patset = set()
    if d == 0:
        patset.add(())
    for key, ws in WORDS[d].items():
        for w in ws:
            patset.add(w)
    for q in range(0, 8):
        k = q + d
        images = set()
        cnt = 0
        # 枚举全部合法满射词（值域 {1..q}，长度 k）
        if q == 0:
            allw = [()] if k == 0 else []
        else:
            allw = []
            used = [0] * (q + 1)
            seq = []

            def dfs(distinct):
                n = len(seq)
                if q - distinct > k - n:
                    return
                if n == k:
                    allw.append(tuple(seq))
                    return
                for v in range(1, q + 1):
                    if n >= 2 and not legal(seq[-2], seq[-1], v):
                        continue
                    seq.append(v)
                    used[v] += 1
                    dfs(distinct + (1 if used[v] == 1 else 0))
                    used[v] -= 1
                    seq.pop()
            dfs(0)
        for w in allw:
            cnt += 1
            wp, S, triv, bl = Phi(w)
            beta = bl[-1][1] if (bl and bl[-1][0] == 'E') else 0
            vE = beta
            if triv and vE and not all(x > vE for x in triv):
                okD = False
                detail.append(('trivial<=vE', w))
            if wp not in patset:
                okD = False
                detail.append(('not pattern', w, wp))
            bwp = blocks_of(wp) if wp else []
            betap = bwp[-1][1] if (bwp and bwp[-1][0] == 'E') else 0
            if any(S[i] != i + 1 for i in range(betap)):
                okD = False
                detail.append(('S not pinned', w))
            if Psi(wp, S, q) != w:
                okD = False
                detail.append(('Psi(Phi) != id', w))
            images.add((wp, S))
        if len(images) != cnt:
            okD = False
            detail.append(('Phi not injective', d, q))
        pred = sum(c * Cp(q - b, s - b) for (s, b), c in BR[d].items())
        if pred != cnt or cnt != D(k, d):
            okD = False
            detail.append(('count', d, q, cnt, pred))
    # 满射性：每个 (w', S) 都在像里 —— 由计数相等 + 单射 推出
rep('C4-12-bij', okD, 'Φ/Ψ 逐词检验 d<=3、q<=7：平凡值 > E 层、Φ(w)∈Pat(d)、s_i=i(i<=β)、Ψ∘Φ=id、Φ 单射、计数 = Σ M C+ = D %s' % detail[:3])

print('SUMMARY s4 ok=%d bad=%d runtime=%.1fs' % (sum(RES), len(RES) - sum(RES), time.time() - t0))
