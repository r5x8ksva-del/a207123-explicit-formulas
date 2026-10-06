# -*- coding: utf-8 -*-
"""t3：T4.3(6) 的结构核对。
(A) 构造法（按 s6-t436 证明的算法）：P_j ∈ Q[U,Λ] -> 分解 P_j = Σ_i p_{j,i}(D)Λ^i -> π_{j,i} = i!·p_{j,i}；
    对 j<=JC、q<=QR 精确核对 a_{q,j} = Σ_{i=1}^{⌊j/2⌋+1} π_{j,i}(q) c(q,i)（a_{q,j} 由截断递推 (R) 给出），
    对 q<=QN 再用 Num_q 直接给出的 a_{q,j} 核对一次；核对子断言 (a)(b)(c)。
(B) 拟合法（与证明无关，只用命题的形状）：对 j<=JF，未知数 π_{j,i} 的系数（1<=i<=⌊j/2⌋+1，统一次数上界 dmax），
    取 q=1..Qfit 列方程，dmax 从 0 往上加，直到方程组相容；求解用模 4 个大素数的 Gauss-Jordan + CRT + 有理重构，
    再用精确整数在全部 q<=QR 上复验（模素数只用于“找”解，结论只依赖精确复验）。
    列满秩（模 p 满秩 => 在 Q 上满秩）说明在该次数上界内解唯一；再把上界加 3 重解一次，看多出的系数是否全为 0。
    最后与 (A) 的结果逐系数比较。
"""
import sys
sys.dont_write_bytecode = True
import time
from fractions import Fraction
from math import factorial, lcm
import s6lib as L

t0 = time.time()
ok_all = True


def report(name, ok, extra=''):
    global ok_all
    ok_all = ok_all and ok
    print('[%s] %s %s' % ('OK ' if ok else 'BAD', name, extra))
    sys.stdout.flush()


JC = 40          # 构造法的 j 上界
JF = int(sys.argv[1]) if len(sys.argv) > 1 else 20   # 拟合法的 j 上界
QR, QN = 300, 80
R = L.R_trunc(QR, JC + 1)
N = L.num_polys(QN)
c = L.stirling1_rec(QR, JC // 2 + 2)


def a(q, j):
    return R[q][j]


def to_int_polys(polys):
    den = 1
    for p in polys:
        for x in p:
            den = lcm(den, Fraction(x).denominator)
    return den, [[int(Fraction(x) * den) for x in p] for p in polys]


def ipeval(p, x):
    v = 0
    for cc in reversed(p):
        v = v * x + cc
    return v


def check_repr(pis, j, qmax, src):
    """pis[i] (i=0..K) 是 Fraction 系数多项式；核对 a_{q,j} = Σ_{i>=1} π_i(q) c(q,i)，q=1..qmax。"""
    den, ip = to_int_polys(pis)
    for q in range(1, qmax + 1):
        s = 0
        for i in range(1, len(ip)):
            if ip[i]:
                s += ipeval(ip[i], q) * c[q][i]
        if s != den * src(q, j):
            return q
    return None

# ---------------------------------------------------------------- (A) 构造法
P = L.P_family(JC)
pi_con = {}
okA = True
const_nonzero = []
for j in range(JC + 1):
    K = j // 2 + 1
    p, steps, const = L.decompose(P[j], K)
    if const != 0:
        const_nonzero.append(j)
    pis = [L.tp_scale(p[i], factorial(i)) for i in range(K + 1)]
    pis[0] = []                      # i=0 项：c(q,0)=0（q>=1），分解给出的常数也为 0（见下）
    pi_con[j] = pis
    bad = check_repr(pis, j, QR, a)
    bad2 = check_repr(pis, j, QN, lambda q, jj: L.a_from_num(N, q, jj))
    if bad is not None or bad2 is not None:
        okA = False
        print('   (A) j=%d 失败于 q=%s / %s' % (j, bad, bad2))
report('(A) 构造法：a_{q,j} = Σ_{i=1}^{⌊j/2⌋+1} π_{j,i}(q)c(q,i)', okA,
       '(j<=%d；q<=%d 用截断递推，q<=%d 用 Num_q 直接核对)' % (JC, QR, QN))
report('(A) 分解得到的 i=0 常数项全为 0', not const_nonzero, str(const_nonzero))

oka = all(L.tp_trim(pi_con[2 * m][m + 1]) == [1] for m in range(0, JC // 2 + 1))
okb = all(L.tp_trim(pi_con[2 * m + 1][m + 1]) == [Fraction(-m), Fraction(1)] for m in range(1, (JC - 1) // 2 + 1))
okc = all(not L.tp_trim(p) for p in pi_con[1])
report('(A) 子断言 (a) π_{2m,m+1} ≡ 1', oka, '(0<=m<=%d)' % (JC // 2))
report('(A) 子断言 (b) π_{2m+1,m+1} = q-m', okb, '(1<=m<=%d)' % ((JC - 1) // 2))
report('(A) 子断言 (c) j=1 的全部 π_{1,i} 为 0', okc)
print('   注：m=0 时 π_{1,1} = %s（不是 q），所以 (b) 必须要求 m>=1。' % L.tp_str(pi_con[1][1]))

udeg = [max((aa for (aa, i) in P[j]), default=-1) for j in range(JC + 1)]
okud = all(udeg[j] == (j + 1) // 3 for j in range(JC + 1) if j != 1) and udeg[1] == -1
report('(A) P_j 关于 U 的次数 = ⌊(j+1)/3⌋（j≠1；P_1=0）', okud, '(j<=%d)' % JC)
okdeg = all(len(L.tp_trim(pi_con[j][i])) - 1 <= (j + 1) // 3 for j in range(JC + 1) for i in range(1, j // 2 + 2))
okdeg1 = all(len(L.tp_trim(pi_con[j][1])) - 1 == (j + 1) // 3 for j in range(JC + 1) if j != 1)
report('(A) deg π_{j,i} <= ⌊(j+1)/3⌋（附注 R2 的推论）', okdeg, '(j<=%d)' % JC)
report('   观察：i=1 时等号成立 deg π_{j,1} = ⌊(j+1)/3⌋（j≠1）', okdeg1, '(j<=%d)' % JC)

print('\n   π_{j,i}（构造法），j<=24：')
for j in range(0, 25):
    K = j // 2 + 1
    print('   j=%2d:' % j, ' | '.join('i=%d: %s' % (i, L.tp_str(pi_con[j][i])) for i in range(1, K + 1)))
print('\n   次数表 deg π_{j,i}（i=1..⌊j/2⌋+1；-inf 记为 .），j<=%d：' % JC)
for j in range(0, JC + 1):
    K = j // 2 + 1
    degs = []
    for i in range(1, K + 1):
        pp = L.tp_trim(pi_con[j][i])
        degs.append('.' if not pp else str(len(pp) - 1))
    print('   j=%2d: %s' % (j, ' '.join(degs)))

# ---------------------------------------------------------------- (B) 拟合法
primes = L.primes_below(1 << 62, 4)
print('\n   素数：', primes)


def fit(j, dmax, Qfit):
    K = j // 2 + 1
    cols = [(i, d) for i in range(1, K + 1) for d in range(dmax + 1)]
    rows = list(range(1, Qfit + 1))
    sols = []
    for p in primes:
        M = [[(pow(q, d, p) * (c[q][i] % p)) % p for (i, d) in cols] for q in rows]
        b = [a(q, j) % p for q in rows]
        st, sol = L.solve_mod(M, b, p)
        if st != 'ok':
            return st, cols, None
        sols.append(sol)
    pis = [[] for _ in range(K + 1)]
    for idx, (i, d) in enumerate(cols):
        x, Mod = sols[0][idx], primes[0]
        for k in range(1, len(primes)):
            x, Mod = L.crt_pair(x, Mod, sols[k][idx], primes[k])
        fr = L.ratrec(x, Mod)
        if fr is None:
            return 'ratrec_fail', cols, None
        while len(pis[i]) <= d:
            pis[i].append(Fraction(0))
        pis[i][d] = fr
    pis = [L.tp_trim(pp) for pp in pis]
    return 'ok', cols, pis


okB = True
okCmp = True
okU = True
summary = []
prev_d = 0


def attempt(j, dmax):
    """返回 ('inconsistent'|'ok'|其他, (dmax, ncols, Qfit, pis))；'ok' 时已做精确复验。"""
    K = j // 2 + 1
    ncols = K * (dmax + 1)
    Qfit = min(QR, ncols + 40)
    st, cols, pis = fit(j, dmax, Qfit)
    if st != 'ok':
        return st, None
    bad = check_repr(pis, j, QR, a)
    bad2 = check_repr(pis, j, QN, lambda q, jj: L.a_from_num(N, q, jj))
    if bad is not None or bad2 is not None:
        print('   (B) j=%d dmax=%d 重构解精确复验失败 q=%s/%s' % (j, dmax, bad, bad2))
        return 'verify_fail', None
    return 'ok', (dmax, ncols, Qfit, pis)


for j in range(0, JF + 1):
    # 次数上界的搜索只是加速手段：从上一个 j 的结果减 1 开始；找到相容的 dmax 后，
    # 再显式确认 dmax-1 不相容（dmax>0 时），所以报告的是真正的最小统一次数上界。
    d = max(0, prev_d - 1)
    found = None
    st, res = attempt(j, d)
    if st == 'ok':
        found = res
        while d > 0:
            st2, res2 = attempt(j, d - 1)
            if st2 == 'ok':
                d -= 1
                found = res2
            else:
                break
    else:
        while st == 'inconsistent' and d < 20:
            d += 1
            st, res = attempt(j, d)
        if st == 'ok':
            found = res
    if found is None:
        okB = False
        print('   (B) j=%d 没有找到解（最后状态 %s）' % (j, st))
        continue
    dmax, ncols, Qfit, pis = found
    if dmax > 0:
        stm, _ = attempt(j, dmax - 1)
        if stm != 'inconsistent':
            okB = False
            print('   (B) j=%d：dmax-1 时状态为 %s，最小性没有确认' % (j, stm))
    prev_d = dmax
    same = all(L.tp_trim(pis[i]) == L.tp_trim(pi_con[j][i]) for i in range(1, j // 2 + 2))
    okCmp = okCmp and same
    # 唯一性探针：次数上界 +3 重解
    st, cols, pis3 = fit(j, dmax + 3, min(QR, (j // 2 + 1) * (dmax + 4) + 40))
    uniq = (st == 'ok') and all(L.tp_trim(pis3[i]) == L.tp_trim(pis[i]) for i in range(1, j // 2 + 2))
    okU = okU and uniq
    summary.append((j, dmax, ncols, Qfit, same, uniq))
    print('   (B) j=%2d：最小统一次数上界 dmax=%d，未知数 %d，拟合用 q<=%d；精确复验 q<=%d 通过；与 (A) 一致=%s；上界+3 仍唯一且相同=%s  [%.1fs]'
          % (j, dmax, ncols, Qfit, QR, same, uniq, time.time() - t0))
    sys.stdout.flush()

report('(B) 拟合法：每个 j 都找到满足命题形状的解，并在 q<=%d（含 Num_q 直接给出的 q<=%d）上精确成立' % (QR, QN), okB, '(j<=%d)' % JF)
report('(B) 拟合解与构造法 (A) 逐系数相同', okCmp, '(j<=%d)' % JF)
report('(B) 唯一性探针：次数上界加 3 后列仍满秩，解不变', okU, '(j<=%d)' % JF)
print('ALL_OK' if ok_all else 'SOME_BAD', '  time %.1fs' % (time.time() - t0))
