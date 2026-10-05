# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 2：合法满射词 N(k,q) 的 N^c / N^E 公式（定理 7、命题 7.2）、R(p,s)、R'、二阶 Euler 表示。

对照对象：直接按定义数「长 k、值集恰为 {0..q-1}」的合法词——DP 状态 (末两项, 已用值集合)，
不经过任何容斥，也不用 c2b 的 tabNc/tabNE。
"""
import sys, os, time, itertools
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, CODE)
import core  # noqa

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

T0 = time.time()
RESULTS = []


def rep(name, ok, msg=''):
    RESULTS.append((name, ok))
    print(('OK   ' if ok else 'BAD  ') + name + ('  ' + msg if msg else ''), flush=True)


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def stirling_table(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


ST = stirling_table(80)


def hsym(s, lo, hi):
    if s < 0:
        return 0
    row = [1] + [0] * s
    for v in range(lo, hi + 1):
        for t in range(1, s + 1):
            row[t] += v * row[t - 1]
    return row[s]


# ---------- 直接 DP：满射词按结尾拆分 ----------
def surj_dp(K, q):
    full = (1 << q) - 1
    Nc = [0] * (K + 1)
    NE = [0] * (K + 1)
    if q == 0:
        Nc[0] = 1
        return Nc, NE
    if K >= 1 and q == 1:
        Nc[1] = 1
    st = {}
    for a in range(q):
        for b in range(q):
            key = (a, b, (1 << a) | (1 << b))
            st[key] = st.get(key, 0) + 1
    def tally(k):
        for (a, b, ms), v in st.items():
            if ms == full:
                if a < b:
                    NE[k] += v
                else:
                    Nc[k] += v
    if K >= 2:
        tally(2)
    for k in range(3, K + 1):
        nst = {}
        for (a, b, ms), v in st.items():
            for c in range(q):
                if good(a, b, c):
                    key = (b, c, ms | (1 << c))
                    nst[key] = nst.get(key, 0) + v
        st = nst
        tally(k)
    return Nc, NE


KMAX, QMAX = 30, 9
DPN = {q: surj_dp(KMAX, q) for q in range(0, QMAX + 1)}
print('[dp] built %.1fs' % (time.time() - T0), flush=True)

# 先拿 core.N_brute（DFS 定义）对照 DP 本身
ok = True
for k in range(1, 9):
    nb = core.N_brute(k)
    for q in range(1, min(k, QMAX) + 1):
        if nb.get(q, 0) != DPN[q][0][k] + DPN[q][1][k]:
            ok = False
rep('surjDP_vs_core_N_brute', ok, '满射 DP 总数 == core.N_brute（DFS 按定义）(1<=k<=8)')


# ---------- R(p,s) ----------
def skeletons(p, s):
    """s 条弧 (v,a)，0<=a<v<=p-1，头非增（同头有序）。"""
    res = []
    def rec(cur, top, rem):
        if rem == 0:
            res.append(tuple(cur))
            return
        for v in range(1, top + 1):
            for a in range(v):
                cur.append((v, a)); rec(cur, v, rem - 1); cur.pop()
    rec([], p - 1, s)
    return res


def R_ie(p, s):
    tot = 0
    for i in range(p + 1):
        if i == 0:
            hs = 1 if s == 0 else 0
        else:
            hs = ST[i - 1 + s][i - 1]
        tot += (-1) ** (p - i) * comb(p, i) * hs
    return tot


okR = True
cnt_by = {}
for p in range(0, 9):
    for s in range(0, 5 if p <= 8 else 4):
        if p >= 8 and s >= 5:
            continue
        sk = skeletons(p, s)
        exact = sum(1 for x in sk if set(e for arc in x for e in arc) == set(range(p)))
        if exact != R_ie(p, s):
            okR = False
        # 最小头分布（R'）
        for x in sk:
            if set(e for arc in x for e in arc) == set(range(p)) and s >= 1:
                h0 = min(v for v, a in x)
                cnt_by[(p, s, h0)] = cnt_by.get((p, s, h0), 0) + 1
dfact = 1
okDF = True
for s in range(0, 12):
    if s >= 1:
        dfact *= (2 * s - 1)
    if R_ie(2 * s, s) != dfact:
        okDF = False
    if any(R_ie(p, s) != 0 for p in range(2 * s + 1, 2 * s + 8)):
        okDF = False
    if s >= 1 and (R_ie(0, s) != 0 or R_ie(1, s) != 0):
        okDF = False
rep('R_bruteforce', okR, 'R(p,s) 骨架暴力 == 二项式反演式 (p<=8, s<=4)')
rep('R_props', okDF, 'R(2s,s)=(2s-1)!!、p>2s 时 0、s>=1 时 R(0,s)=R(1,s)=0 (s<=11)')


def eul2(n, k, memo={}):
    if n == 0:
        return 1 if k == 0 else 0
    if k < 0 or k >= n:
        return 0
    if (n, k) not in memo:
        memo[(n, k)] = (k + 1) * eul2(n - 1, k) + (2 * n - 1 - k) * eul2(n - 1, k - 1)
    return memo[(n, k)]


ok = all(R_ie(p, s) == sum(eul2(s, kk) * C(2 * s - 2 - kk, 2 * s - p) for kk in range(s))
         for s in range(1, 16) for p in range(0, 2 * s + 4))
rep('R_euler', ok, 'R(p,s)=sum_k <<s,k>> C(2s-2-k,2s-p) (1<=s<=15) —— 比作者的 s<=11 更远')


# ---------- 定理 7 ----------
RC = {}
def R(p, s):
    if (p, s) not in RC:
        RC[(p, s)] = R_ie(p, s)
    return RC[(p, s)]


def Nc_thm7(k, q):
    tot = 0
    for s in range(0, k // 3 + 1):
        for p in range(0, 2 * s + 1):
            r = R(p, s)
            if r:
                tot += C(q, p) * r * C(k - 2 * s + p - 1, s + q - 1)
    return tot


ok = all(Nc_thm7(k, q) == DPN[q][0][k] for q in range(1, QMAX + 1) for k in range(0, KMAX + 1))
rep('T7_Nc_vs_directDP', ok, 'N^c 公式 == 直接满射 DP（不经容斥）(k<=30, 1<=q<=9)')
edge = (Nc_thm7(0, 0), DPN[0][0][0])
rep('T7_edge_q0', edge[0] != edge[1], '边界：(k,q)=(0,0) 时公式给 %d，真值 N^c(0,0)=%d（空词）——定理需注明 q>=1 或 k>=1' % edge)


# ---------- 命题 7.2 ----------
def Rp_ie(p, s, h0):
    tot = 0
    for z1 in range(0, h0 + 1):
        for z2 in range(0, p - h0):
            w = p - z1 - z2
            r0 = h0 - z1
            tot += (-1) ** (z1 + z2) * comb(h0, z1) * comb(p - 1 - h0, z2) * (hsym(s, r0, w - 1) - hsym(s, r0 + 1, w - 1))
    return tot


ok = all(cnt_by.get((p, s, h0), 0) == Rp_ie(p, s, h0) for p in range(2, 9) for s in range(1, 5) for h0 in range(0, p))
rep("Rprime_bruteforce", ok, "R'(p,s,h0) 容斥式 == 骨架暴力（按最小头分类）(p<=8, s<=4)")

RP = {}
for s in range(1, KMAX // 3 + 2):
    for p in range(2, 2 * s + 1):
        for h0 in range(1, p):
            v = Rp_ie(p, s, h0)
            if v:
                RP[(p, s, h0)] = v


def NE_p72(k, q):
    return sum(r * C(q - 1 - h0, p - 1 - h0) * C(k - 1 - 2 * s + p - h0, s + q - 2 - h0) for (p, s, h0), r in RP.items())


ok = all(NE_p72(k, q) == DPN[q][1][k] for q in range(1, QMAX + 1) for k in range(0, KMAX + 1))
rep('P7.2_NE_vs_directDP', ok, 'N^E 三重和 == 直接满射 DP (k<=30, 1<=q<=9)')

# ---------- 容斥等价（命题 7.3 的结论）也拿直接 DP 对一下 ----------
# 标准容斥：N^c(k,q)=sum_i (-1)^{q-i} C(q,i) A_{i-1}(k)，A_{-1}(k)=[k=0]
def A_complete(k, m):
    if m < 0:
        return 1 if k == 0 else 0
    return sum(ST[m + s][m] * C(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1))


ok = all(sum((-1) ** (q - i) * comb(q, i) * A_complete(k, i - 1) for i in range(q + 1)) == DPN[q][0][k]
         for q in range(1, QMAX + 1) for k in range(0, KMAX + 1))
# 「a 值覆盖」容斥：sum_z (-1)^z C(q-1,z) [A_{q-1-z}(k) - A_{q-2-z}(k)]
ok2 = all(sum((-1) ** z * comb(q - 1, z) * (A_complete(k, q - 1 - z) - A_complete(k, q - 2 - z)) for z in range(q)) == DPN[q][0][k]
          for q in range(1, QMAX + 1) for k in range(0, KMAX + 1))
rep('P7.3_two_IE_forms', ok and ok2, '标准容斥与「a 值覆盖」容斥（中间式 sum_z (-1)^z C(q-1,z)[A_{q-1-z}-A_{q-2-z}]）都 == 直接 DP (k<=30, q<=9)')

print('[time] %.1fs' % (time.time() - T0))
nb = sum(1 for _, o in RESULTS if not o)
print('SUMMARY r2 ok=%d bad=%d' % (len(RESULTS) - nb, nb))
