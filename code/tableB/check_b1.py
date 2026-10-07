# -*- coding: utf-8 -*-
"""表 B 的 B1（h_k 全实根、根互异）的核对脚本（2026-10-07）。证明见 notes/05-主Agent-表B-B1-h_k实根性.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b1 pass=<n> fail=<n>」。
  b1-tri    三角递推（T1.4(2) 及初值）算出的 N 与 core 的两种真值一致：按定义 DFS（k<=9）、U 的 DP 容斥（k<=60）
  b1-rec    引理 0：n_k = (1+z) n_{k-1} + Phi n_{k-3}（4<=k<=60）
  b1-ops    引理 5(iv)：T((1+z)f) = (1+z)(Tf + z f)；以及 T n_{k+1} 的四项展开（3<=k<=40）
  b1-base   基例 alpha_2, beta_2, alpha_3, beta_3, delta_3, epsilon_3（精确）
  b1-rel    四条交错关系 alpha_k, beta_k, delta_k, epsilon_k（3<=k<=40）与 alpha_2, beta_2 精确成立
  b1-gcd    gcd(n_k, n_{k-1}) = (1+z)^(ceil((k-1)/3)-1)（2<=k<=60）
  b1-roots  n_k 去掉 (1+z)^(ceil(k/3)-1) 后有 floor(2k/3) 个互异实根（1<=k<=60）
  b1-nu     n_k 在 (-inf,-1) 的根数 = floor(k/3) = h_k 系数的符号变化数（1<=k<=60）
  b1-b8     j>s_k 时 U_k(-j) 的变号次数 <= floor(k/3)（j<=10k，1<=k<=60），以及 U_k(-j)=0（1<=j<=s_k）
  b1-rev    反向检查：Phi 去掉 2zn 项后 b1-rec 的等式不成立；beta_k、delta_k 反过来写判为不成立；两个玩具例子判对

精确判定方法：要判断 g << f（交错，最大根属于 f），先精确约去公共因子 z^a(1+z)^b，再用一个大素数 p 上的 gcd 证明余下两部分互素；
然后用 numpy 求近似根，只用来挑有理分点；每个分点处的符号用整数精确计算，分点之间的符号变化个数等于次数即证明全部根为实单根，
且所有 f、g 的根被分点两两隔开，顺序因而确定。numpy 的近似不够时用精确二分细化。不依赖任何浮点比较。
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import N_brute, U_fast_table, N_from_U  # noqa: E402

try:
    import numpy as np
except ImportError:  # 没有 numpy 时只能跑不需要求根的部分
    np = None

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ---------------------------------------------------------------- 多项式（整数系数，低次在前）
def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(*ps):
    n = max(len(p) for p in ps)
    out = [0] * n
    for p in ps:
        for i, c in enumerate(p):
            out[i] += c
    return trim(out)


def pscale(p, c):
    return trim([c * x for x in p])


def pmul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return trim(out)


def pderiv(p):
    return trim([i * p[i] for i in range(1, len(p))] or [0])


ONEZ = [1, 1]   # 1+z
Z = [0, 1]      # z


def T(n):
    """T n = z(1+z) n' + 2 z n"""
    return padd(pmul([0, 1, 1], pderiv(n)), pmul([0, 2], n))


def Phi(n):
    return pmul(ONEZ, T(n))


def mult_root(p, r):
    """p 在整数 r（0 或 -1）处的重数，以及除掉 (z-r)^mult 后的商。"""
    p = trim(p)
    m = 0
    while len(p) > 1:
        hi = list(reversed(p))
        out = [hi[0]]
        for a in hi[1:]:
            out.append(a + r * out[-1])
        if out[-1] != 0:
            break
        out.pop()
        p = list(reversed(out))
        m += 1
    return m, p


def gcd_is_one_mod(p, q, P=(1 << 61) - 1):
    """在 F_P 上算 gcd；首项系数不被 P 整除时，F_P 上互素 => Q 上互素。"""
    if p[-1] % P == 0 or q[-1] % P == 0:
        raise ValueError('bad prime')
    a = [x % P for x in p]
    b = [x % P for x in q]

    def tr(v):
        while len(v) > 1 and v[-1] == 0:
            v.pop()
        return v

    a, b = tr(a), tr(b)
    while not (len(b) == 1 and b[0] == 0):
        # a mod b
        inv = pow(b[-1], P - 2, P)
        a = list(a)
        while len(a) >= len(b) and not (len(a) == 1 and a[0] == 0):
            c = a[-1] * inv % P
            s = len(a) - len(b)
            for i, x in enumerate(b):
                a[s + i] = (a[s + i] - c * x) % P
            a = tr(a)
            if len(a) < len(b):
                break
        a, b = b, a
    return len(a) == 1 and a[0] != 0


def sign_at(p, x):
    """p(x) 的符号，x 为 Fraction，整数运算精确求值。"""
    a, b = x.numerator, x.denominator
    n = len(p) - 1
    s = 0
    apow = 1
    bpow = b ** n
    for i, c in enumerate(p):
        if c:
            s += c * apow * bpow
        apow *= a
        if i < n:
            bpow //= b
    return (s > 0) - (s < 0)


def approx_roots(p):
    r = np.roots([float(c) for c in reversed(p)])
    return sorted(float(z.real) for z in r)


def isolate(p, extra_pts=()):
    """p：整数系数、首项为正。返回升序的有理区间 [l, r] 列表，每个恰含 p 的一个根，
    区间个数 = deg p（于是 p 全部是实单根）；做不到时返回 None。"""
    deg = len(p) - 1
    if deg == 0:
        return []
    bound = Fr(1) + max(Fr(abs(c), abs(p[-1])) for c in p[:-1])
    rs = approx_roots(p)
    pts = [-bound] + [Fr(rs[i] + rs[i + 1]) / 2 for i in range(deg - 1)] + [bound]
    pts = sorted(set(pts))
    sg = [sign_at(p, x) for x in pts]
    if any(s == 0 for s in sg):
        return None
    ivs = [(pts[i], pts[i + 1]) for i in range(len(pts) - 1) if sg[i] != sg[i + 1]]
    if len(ivs) != deg:
        return None
    return ivs


def refine(p, iv):
    l, r = iv
    sl = sign_at(p, l)
    m = (l + r) / 2
    sm = sign_at(p, m)
    if sm == 0:
        # 恰好打中根：取一个不含它以外根的小区间
        eps = (r - l) / 1024
        return (m - eps, m + eps)
    return (l, m) if sm != sl else (m, r)


def interlaces(g, f):
    """精确判定 g << f（g 交错 f，最大根属于 f；弱交错）。f, g 系数非负、首项为正。"""
    f, g = trim(f), trim(g)
    df, dg = len(f) - 1, len(g) - 1
    if dg not in (df, df - 1):
        return False
    a0f, f1 = mult_root(f, 0)
    a0g, g1 = mult_root(g, 0)
    c0 = min(a0f, a0g)
    # 公共的 z 因子约去后余下的 z 因子仍属各自
    f1 = [0] * (a0f - c0) + f1
    g1 = [0] * (a0g - c0) + g1
    a1f, f2 = mult_root(f1, -1)
    a1g, g2 = mult_root(g1, -1)
    c1 = min(a1f, a1g)
    f2 = pmul(f2, [1] if a1f == c1 else _pow1z(a1f - c1))
    g2 = pmul(g2, [1] if a1g == c1 else _pow1z(a1g - c1))
    if len(g2) == 1 and len(f2) == 1:
        return True
    if len(g2) > 1 and len(f2) > 1 and not gcd_is_one_mod(f2, g2):
        return False  # 还有别的公共根：本脚本不处理（实际未出现）
    If = isolate(f2) if len(f2) > 1 else []
    Ig = isolate(g2) if len(g2) > 1 else []
    if If is None or Ig is None:
        return False
    # 细化直到 f、g 的区间两两不交
    for _ in range(200):
        clash = False
        for i, a in enumerate(If):
            for j, b in enumerate(Ig):
                if a[0] < b[1] and b[0] < a[1]:
                    If[i] = refine(f2, If[i])
                    Ig[j] = refine(g2, Ig[j])
                    clash = True
        if not clash:
            break
    else:
        return False
    tags = sorted([(iv[0], 'F') for iv in If] + [(iv[0], 'G') for iv in Ig])
    word = ''.join(t for _, t in tags)
    n = len(If)
    if len(Ig) == n:
        return word == 'GF' * n
    if len(Ig) == n - 1:
        return word == 'F' + 'GF' * (n - 1)
    return False


def _pow1z(e):
    out = [1]
    for _ in range(e):
        out = pmul(out, ONEZ)
    return out


# ---------------------------------------------------------------- N 表与 n_k
def N_triangle(K):
    N = [[0] * (K + 3) for _ in range(K + 1)]
    N[0][0] = 1
    N[1][1] = 1
    N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            v = N[k - 1][r] + N[k - 1][r + 1]
            if r >= 1:
                v += r * (N[k - 3][r - 1] + 2 * N[k - 3][r] + N[k - 3][r + 1])
            N[k][q] = v
    return N


def main():
    t0 = time.time()
    K = 60
    N = N_triangle(K)
    # b1-tri
    ok = True
    for k in range(0, 10):
        nb = N_brute(k)
        for q in range(0, k + 1):
            ok = ok and nb.get(q, 0) == N[k][q]
    Tab = U_fast_table(K, K - 1)
    for k in range(1, K + 1):
        for q in range(1, k + 1):
            ok = ok and N_from_U(Tab, k, q) == N[k][q]
    report('b1-tri', ok, '三角递推的 N(k,q) = 按定义 DFS（k<=9）= U 的 DP 容斥（1<=k<=%d）' % K)
    n = {k: [N[k][q] for q in range(1, k + 1)] for k in range(1, K + 1)}
    # b1-rec
    ok = all(n[k] == padd(pmul(ONEZ, n[k - 1]), Phi(n[k - 3])) for k in range(4, K + 1))
    ok = ok and n[3] != padd(pmul(ONEZ, n[2]), Phi([1]))  # k=3 处 N(0,0)=1 使递推不成立（只是确认说明）
    report('b1-rec', ok, '引理 0：n_k = (1+z)n_{k-1} + Phi n_{k-3} 对 4<=k<=%d 精确成立（k=3 不成立，符合说明）' % K)
    # b1-ops
    ok = True
    for k in range(3, 41):
        f = n[k]
        ok = ok and T(pmul(ONEZ, f)) == pmul(ONEZ, padd(T(f), pmul(Z, f)))
        lhs = T(n[k + 1])
        rhs = padd(Phi(n[k]), pmul([0, 1, 1], n[k]), pmul(ONEZ, T(T(n[k - 2]))), pmul([0, 1, 1], T(n[k - 2])))
        ok = ok and lhs == rhs
    report('b1-ops', ok, '引理 5(iv) 与 T n_{k+1} = Phi n_k + z(1+z)n_k + (1+z)T^2 n_{k-2} + z(1+z)T n_{k-2}（3<=k<=40）')
    if np is None:
        report('b1-base', False, '缺 numpy，无法求近似根')
        return
    # b1-base
    ok = (interlaces(n[1], n[2]) and interlaces(n[2], T(n[1])) and interlaces(n[2], n[3])
          and interlaces(n[3], T(n[2])) and interlaces(n[3], Phi(n[1])) and interlaces(Phi(n[1]), T(n[3])))
    report('b1-base', ok, '基例 alpha_2, beta_2, alpha_3, beta_3, delta_3, epsilon_3 精确成立')
    # b1-rel
    KR = 40
    bad = []
    if not (interlaces(n[1], n[2]) and interlaces(n[2], T(n[1]))):
        bad.append(2)
    for k in range(3, KR + 1):
        rel = [interlaces(n[k - 1], n[k]), interlaces(n[k], T(n[k - 1])),
               interlaces(n[k], Phi(n[k - 2])), interlaces(Phi(n[k - 2]), T(n[k]))]
        if not all(rel):
            bad.append((k, rel))
    report('b1-rel', not bad, '四条关系 alpha_k, beta_k, delta_k, epsilon_k 对 3<=k<=%d 精确成立（另 alpha_2, beta_2）%s'
           % (KR, '' if not bad else '；失败：%s' % bad[:5]))
    # b1-gcd
    bad = []
    for k in range(2, K + 1):
        a1, r1 = mult_root(n[k], -1)
        a0, r0 = mult_root(n[k - 1], -1)
        expect = -(-(k - 1) // 3) - 1
        if min(a1, a0) != expect or a0 != expect:
            bad.append(k)
            continue
        if len(r1) > 1 and len(r0) > 1 and not gcd_is_one_mod(r1, r0):
            bad.append(k)
    report('b1-gcd', not bad, 'gcd(n_k, n_{k-1}) = (1+z)^(ceil((k-1)/3)-1)，2<=k<=%d（模 2^61-1 证明余部互素）%s'
           % (K, '' if not bad else '；失败：%s' % bad))
    # b1-roots
    bad = []
    for k in range(1, K + 1):
        a, r = mult_root(n[k], -1)
        if a != max(0, -(-k // 3) - 1):
            bad.append(k)
            continue
        if len(r) - 1 != (2 * k) // 3:
            bad.append(k)
            continue
        if len(r) > 1 and isolate(r) is None:
            bad.append(k)
    report('b1-roots', not bad, 'n_k/(1+z)^(ceil(k/3)-1) 有 floor(2k/3) 个互异实根（1<=k<=%d，有理分点精确隔离）%s'
           % (K, '' if not bad else '；失败：%s' % bad))
    # b1-nu：n_k 在 (-inf,-1) 的根数 = floor(k/3) = h_k 系数的符号变化数
    bad = []
    for k in range(1, K + 1):
        a, r = mult_root(n[k], -1)
        nu = 0
        if len(r) > 1:
            ivs = isolate(r)
            s_m1 = sign_at(r, Fr(-1))           # r(-1) != 0
            for (l, rr) in ivs:
                if rr <= -1:
                    nu += 1
                elif l < -1 < rr and sign_at(r, Fr(l)) != s_m1:
                    nu += 1                     # 根在 (l, -1)
        h = [0] * k
        for q in range(1, k + 1):
            for i in range(k - q + 1):
                h[q - 1 + i] += N[k][q] * comb(k - q, i) * (-1) ** i
        sg = [c for c in h if c != 0]
        changes = sum(1 for i in range(len(sg) - 1) if (sg[i] > 0) != (sg[i + 1] > 0))
        if nu != k // 3 or changes != k // 3:
            bad.append((k, nu, changes))
    report('b1-nu', not bad, 'n_k 在 (-inf,-1) 的根数 = floor(k/3) = h_k 系数的符号变化数（1<=k<=%d）%s'
           % (K, '' if not bad else '；失败：%s' % bad[:5]))
    # b1-b8：j>s_k 时 U_k(-j) 的变号次数 <= floor(k/3)（j 到 10k 为止；U_k(-j) 由 n_k 按互反式算出）
    bad = []
    for k in range(1, K + 1):
        sk = (k + 2) // 3
        vals = []
        for j in range(sk + 1, 10 * k + 2):
            # U_k(-j) = sum_q (-1)^q N(k,q) C(j+q-2, q)
            vals.append(sum((-1) ** q * N[k][q] * comb(j + q - 2, q) for q in range(1, k + 1)))
        if any(v == 0 for v in vals):
            bad.append((k, 'zero'))
            continue
        ch = sum(1 for i in range(len(vals) - 1) if (vals[i] > 0) != (vals[i + 1] > 0))
        if ch > k // 3:
            bad.append((k, ch))
        # 互反式自检：U_k(-j)=0 对 1<=j<=s_k
        if any(sum((-1) ** q * N[k][q] * comb(j + q - 2, q) for q in range(1, k + 1)) != 0 for j in range(1, sk + 1)):
            bad.append((k, 'recip'))
    report('b1-b8', not bad, 'j>s_k 时 U_k(-j) 变号至多 floor(k/3) 次（s_k<j<=10k，1<=k<=%d；窗口内无零值）；U_k(-j)=0 对 1<=j<=s_k%s'
           % (K, '' if not bad else '；失败：%s' % bad[:5]))
    # b1-rev：反向检查（确认核对程序能报出失败）
    def Phi_bad(nn):
        return pmul(ONEZ, pmul([0, 1, 1], pderiv(nn)))
    rec_bad = any(n[k] == padd(pmul(ONEZ, n[k - 1]), Phi_bad(n[k - 3])) for k in range(4, 20))
    reversed_ok = all(not interlaces(T(n[k - 1]), n[k]) and not interlaces(Phi(n[k - 2]), n[k])
                      for k in range(3, 21))
    toy_bad = interlaces([4, 5, 1], [6, 5, 1])        # 根 -4,-1 对 -3,-2：不交替
    toy_good = interlaces([3, 4, 1], [2, 5, 2])       # 根 -3,-1 对 -2,-1/2：交替
    report('b1-rev', (not rec_bad) and reversed_ok and (not toy_bad) and toy_good,
           '反向检查：去掉 Phi 的 2zn 项后递推在 4<=k<=19 全不成立；beta_k、delta_k 反过来写全部判为不成立（3<=k<=20）；'
           '(z+1)(z+4) 对 (z+2)(z+3) 判为不交错，(z+1)(z+3) 对 (z+2)(2z+1) 判为交错')
    print('time %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b1 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
