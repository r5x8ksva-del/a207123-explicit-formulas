# -*- coding: utf-8 -*-
"""s9-b2 复核 r3：定理 7 的筛法 + l 进步骤，独立实现（不导入项目代码），并换模数、换素数重做。

实现与 check_b2.py 不同的地方：
  * 筛法用「逐个素数做 CRT 提升」：维护当前模 L 下的幸存类 (n,b)，加入周期 P 的素数时提升到 lcm(L,P) 再过滤；
    最后要求幸存类全部满足 b ≡ 0 (mod L)（L = 所用周期的 lcm）。check_b2 是对每个 b0 向量化 n0 的二重循环。
  * mu 用代数整数 y = i*eta（y^3 + i y - i^2 = 0）的大整数精确幂 y^P 算出：eta^P = y^P / i^P，
    再取 (eta^P - 1)/l 模 l；另用模 l^2 的乘方复核。
  * 阶：逐次乘 eta，记录第一次回到 1 的指数，要求等于 P（即 P 是精确的阶）。

配置：
  A  notes/08 的证书（T=5040，表中 13 个素数，原样）——复现其结论与「用到的素数」计数；
  B  新证书：模数 T_new（命令行给出），只用 notes/08 表中没有出现的素数（每个纤维分别排除），l < LIM；
  C  （可选）T_new 下全部素数。
负对照（用配置 B 的素数）：
  N1 U 只用纤维 1：|n|,|b|<=20 内纤维 1 的全部真解所在的类都必须幸存；
  N2 把纤维 2 的元素换成 eta^{-1}(1+2 eta^4)，使 (1,4) 成为纤维 1、2 的公共真解：它的类必须幸存，且整套判定不能报「排除」；
  N3 E 只用纤维 1：平凡族 n ≡ -5 的类在 l 进步骤里必须未解决；
  N4 把纤维 1 的元素换成 eta^{-7}(3+eta^L)（L 为最终模数），使 (7,L) 成为 b ≡ 0 的真解：l 进步骤在 n ≡ 7 必须未解决。
"""
import sys
import time
from math import gcd
import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


NOTE_CERT = {
    1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
    2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
    3: [(13, 84), (71, 70)],
}


def is_prime(n):
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def Wt(i, kind):
    w = [0] * (3 * i + 3)
    w[0] = 1 if kind == 'U' else 0
    for j in range(1, i + 1):
        ff = 1
        for t in range(j):
            ff *= i - t
        w[3 * j + 2] += j * ff
    return w


# ---------------- F_l[x]/(b_i)（或模 l^2） ----------------
def mulx(v, ii, mod):
    return ((v[2] * ii) % mod, (v[0] - v[2] * ii) % mod, v[1] % mod)


def mulm(a, b, ii, mod):
    acc = [0, 0, 0]
    v = b
    for t in range(3):
        if a[t]:
            acc = [acc[r] + a[t] * v[r] for r in range(3)]
        v = mulx(v, ii, mod)
    return (acc[0] % mod, acc[1] % mod, acc[2] % mod)


def powm(e, ii, mod, i):
    base = (0, 1, 0)
    if e < 0:
        base = (1, 0, i % mod)      # eta^{-1} = 1 + i eta^2
        e = -e
    r = (1, 0, 0)
    while e:
        if e & 1:
            r = mulm(r, base, ii, mod)
        base = mulm(base, base, ii, mod)
        e >>= 1
    return r


def evm(poly, ii, mod):
    acc = (0, 0, 0)
    for cf in reversed(poly):
        acc = mulx(acc, ii, mod)
        acc = ((acc[0] + cf) % mod, acc[1], acc[2])
    return acc


def mu_exact(i, l, P):
    """(eta^P - 1)/l 的后两个坐标模 l，用 y = i*eta 的整数幂精确计算。"""
    # Z[t]/(t^3 + i t - i^2)：t^3 = -i t + i^2，t^4 = -i t^2 + i^2 t
    def mul(a, b):
        c0 = a[0] * b[0]
        c1 = a[0] * b[1] + a[1] * b[0]
        c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0]
        c3 = a[1] * b[2] + a[2] * b[1]
        c4 = a[2] * b[2]
        return (c0 + i * i * c3, c1 - i * c3 + i * i * c4, c2 - i * c4)
    r = (1, 0, 0)
    base = (0, 1, 0)
    e = P
    while e:
        if e & 1:
            r = mul(r, base)
        base = mul(base, base)
        e >>= 1
    iP = i ** P
    nums = (r[0] - iP, r[1] * i, r[2] * i * i)    # (eta^P - 1) * i^P 在基 (1,eta,eta^2) 下
    if any(x % l for x in nums):
        return None
    inv = pow(iP % l, -1, l)
    return tuple(((x // l) % l) * inv % l for x in nums)


def mu_l2(i, l, P):
    mod = l * l
    ii = pow(i, -1, mod)
    y = powm(P, ii, mod, i)
    if (y[0] - 1) % l or y[1] % l or y[2] % l:
        return None
    return (((y[0] - 1) // l) % l, (y[1] // l) % l, (y[2] // l) % l)


def make_cert(i, kind, l, P, elem_mod=None):
    """elem_mod：可选的函数 l -> 元素模 l（三元组），用于负对照。"""
    assert is_prime(l) and l % 2 == 1 and i % l != 0
    ii = pow(i, -1, l)
    W = evm(Wt(i, kind), ii, l) if elem_mod is None else elem_mod(l)
    beta = np.zeros((P, 2), dtype=np.int64)
    gam = np.zeros((P, 2), dtype=np.int64)
    cur, curW = (1, 0, 0), W
    first = None
    for e in range(P):
        beta[e] = (cur[1], cur[2])
        gam[e] = (curW[1], curW[2])
        cur = mulx(cur, ii, l)
        curW = mulx(curW, ii, l)
        if first is None and cur == (1, 0, 0):
            first = e + 1
    assert cur == (1, 0, 0), (i, l, P)
    mu = mu_exact(i, l, P)
    mu2 = mu_l2(i, l, P)
    assert mu is not None and mu == mu2, (i, l, P, mu, mu2)
    Emu = (mu[1] * gam[:, 1] - mu[2] * gam[:, 0]) % l
    return {'i': i, 'l': l, 'P': P, 'order': first, 'beta': beta, 'gam': gam, 'Emu': Emu, 'mu': mu}


def find_primes(i, T, lim, exclude):
    """l < lim、奇素数、l∤i、eta^T ≡ 1 (mod l)；返回 (l, 精确阶)。"""
    out = []
    l = 3
    while l < lim:
        if is_prime(l) and i % l and l not in exclude:
            ii = pow(i, -1, l)
            if powm(T, ii, l, i) == (1, 0, 0):
                o = T
                for p in prime_factors(T):
                    while o % p == 0 and powm(o // p, ii, l, i) == (1, 0, 0):
                        o //= p
                out.append((l, o))
        l += 2
    return out


def prime_factors(n):
    f = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            f.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        f.append(n)
    return f


# ---------------- 筛法：逐素数 CRT 提升 ----------------
def sieve(certs, cap=2_000_000):
    order = sorted(certs, key=lambda c: (c['P'], -c['l']))
    L = 1
    N = np.zeros(1, dtype=np.int64)
    B = np.zeros(1, dtype=np.int64)
    peak = 1
    for c in order:
        P, l, beta, gam = c['P'], c['l'], c['beta'], c['gam']
        L2 = L * P // gcd(L, P)
        k = L2 // L
        t = np.arange(k, dtype=np.int64) * L
        outN, outB = [], []
        step = max(1, cap // (k * k))
        for s0 in range(0, len(N), step):
            n = N[s0:s0 + step]
            b = B[s0:s0 + step]
            NN = np.repeat(n[:, None] + t[None, :], k, axis=1).ravel()
            BB = np.tile(b[:, None] + t[None, :], (1, k)).ravel()
            peak = max(peak, len(NN))
            g = gam[NN % P]
            be = beta[BB % P]
            D = (be[:, 0] * g[:, 1] - be[:, 1] * g[:, 0]) % l
            keep = D == 0
            outN.append(NN[keep])
            outB.append(BB[keep])
        N = np.concatenate(outN)
        B = np.concatenate(outB)
        L = L2
    return L, N, B, peak


def padic(certs, L):
    """对每个 n mod L，按 certs 的顺序找第一个 E(n) ≢ 0 的证书；返回 (未解决的 n 数组, 每个证书首中次数)。"""
    n = np.arange(L, dtype=np.int64)
    unresolved = np.ones(L, dtype=bool)
    first = np.full(L, -1, dtype=np.int64)
    for idx, c in enumerate(certs):
        assert L % c['P'] == 0
        nz = c['Emu'][n % c['P']] != 0
        first[nz & (first < 0)] = idx
        unresolved &= ~nz
    used = {}
    for idx, c in enumerate(certs):
        cnt = int((first == idx).sum())
        if cnt:
            used[(c['i'], c['l'])] = cnt
    return np.nonzero(unresolved)[0], used


def run_config(tag, kind, fibers, certs_by_fiber):
    certs = [c for i in fibers for c in certs_by_fiber[i]]
    t0 = time.time()
    L, N, B, peak = sieve(certs)
    bad = int(((B % L) != 0).sum())
    zero_line = int(((B % L) == 0).sum())
    unres, used = padic(certs, L)
    ok = bad == 0 and zero_line == L and len(unres) == 0
    desc = ('%s %s：纤维 %s，%d 个证书素数，最终模数 L=%d；筛后 b≢0 (mod L) 的幸存类 %d 个（b≡0 的类 %d 个 = L：%s）；'
            'l 进步骤未解决的 n0 %d 个；首中计数 %s；最大候选批 %d；用时 %.1fs'
            % (tag, kind, fibers, len(certs), L, bad, zero_line, zero_line == L, len(unres), used, peak, time.time() - t0))
    return ok, desc, (L, N, B, unres)


def main():
    t_all = time.time()
    T_new = int(sys.argv[1]) if len(sys.argv) > 1 else 83160
    LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    also_all = len(sys.argv) > 3 and sys.argv[3] == 'all'

    # ---------- 配置 A：notes/08 的证书 ----------
    info = []
    okA0 = True
    for i, lst in NOTE_CERT.items():
        for (l, P) in lst:
            c = make_cert(i, 'U', l, P)
            okA0 = okA0 and c['order'] == P and 5040 % P == 0
            disc = -i * (4 + 27 * i)
            info.append('%d:%d 阶=%d%s' % (i, l, c['order'], '' if disc % l else '（l|disc）'))
    report('r3-A-cert', okA0, 'notes/08 的 13 个证书素数：素数、奇、l∤i、首次回到 1 的指数=表中 P、P|5040：%s' % '，'.join(info))
    for kind, fibers in (('U', (1, 2)), ('E', (1, 2, 3))):
        cb = {i: [make_cert(i, kind, l, P) for (l, P) in NOTE_CERT[i]] for i in fibers}
        ok, desc, _ = run_config('A(T=5040)', kind, fibers, cb)
        # check_b2 的首中计数（按纤维 1,2,3、表中顺序尝试）
        expect = {'U': {(1, 3): 3780, (1, 11): 1176, (1, 13): 72, (1, 29): 6, (1, 2521): 6},
                  'E': {(1, 3): 3150, (1, 11): 1722, (1, 13): 156, (1, 29): 6, (1, 2521): 4, (2, 7): 1, (2, 17): 1}}[kind]
        certs = [c for i in fibers for c in cb[i]]
        _, used5040 = padic(certs, 5040)
        report('r3-A-%s' % kind, ok and used5040 == expect, desc + '；按 check_b2 的尝试顺序、在 n0 mod 5040 上的首中计数 %s，与日志一致：%s'
               % (used5040, used5040 == expect))

    # ---------- 配置 B：新模数、新素数 ----------
    newc = {}
    for i in (1, 2, 3):
        exclude = {l for (l, P) in NOTE_CERT[i]}
        newc[i] = find_primes(i, T_new, LIM, exclude)
    report('r3-B-primes', all(newc[i] for i in (1, 2, 3)),
           'T_new=%d，l<%d，排除 notes/08 表中素数后：%s' % (T_new, LIM, '；'.join('纤维 %d：%s' % (i, newc[i]) for i in (1, 2, 3))))
    results_B = {}
    for kind, fibers in (('U', (1, 2)), ('E', (1, 2, 3))):
        cb = {i: [make_cert(i, kind, l, P) for (l, P) in newc[i]] for i in fibers}
        okord = all(c['order'] == c['P'] for i in fibers for c in cb[i])
        ok, desc, data = run_config('B(T=%d,新素数)' % T_new, kind, fibers, cb)
        results_B[kind] = (cb, data)
        report('r3-B-%s' % kind, ok and okord, desc)
        if not ok:
            L, N, B, unres = data
            badidx = np.nonzero((B % L) != 0)[0][:20]
            print('   幸存类样例：', [(int(N[t]), int(B[t])) for t in badidx], ' 未解决 n0 样例：', [int(v) for v in unres[:20]])

    if also_all:
        allc = {i: [(l, P) for (l, P) in NOTE_CERT[i] if T_new % P == 0] + newc[i] for i in (1, 2, 3)}
        for kind, fibers in (('U', (1, 2)), ('E', (1, 2, 3))):
            cb = {i: [make_cert(i, kind, l, P) for (l, P) in allc[i]] for i in fibers}
            ok, desc, _ = run_config('C(T=%d,全部素数)' % T_new, kind, fibers, cb)
            report('r3-C-%s' % kind, ok, desc)

    # ---------- 负对照（配置 B 的素数） ----------
    cbU, (LU, _, _, _) = results_B['U']
    # 小范围纤维 1 真解（精确，用 Fraction）
    from fractions import Fraction as Fr

    def exact_solutions(i, kind, R):
        q = Fr(1, i)

        def mx(v):
            return [v[2] * q, v[0] - v[2] * q, v[1]]

        def ml(a, b):
            acc = [Fr(0)] * 3
            v = list(b)
            for t in range(3):
                if a[t]:
                    acc = [acc[r] + a[t] * v[r] for r in range(3)]
                v = mx(v)
            return acc
        pw = {0: [Fr(1), Fr(0), Fr(0)]}
        for e in range(1, R + 1):
            pw[e] = mx(pw[e - 1])
        inv = [Fr(1), Fr(0), Fr(i)]
        for e in range(1, R + 1):
            pw[-e] = ml(pw[-e + 1], inv)
        Wv = [Fr(0)] * 3
        for cf in reversed(Wt(i, kind)):
            Wv = mx(Wv)
            Wv[0] += cf
        sols = []
        for n in range(-R, R + 1):
            w = ml(Wv, pw[n])
            for b in range(-R, R + 1):
                if b and pw[b][1] * w[2] - pw[b][2] * w[1] == 0:
                    sols.append((n, b))
        return sols

    s1 = exact_solutions(1, 'U', 20)
    L1, N1, B1, _ = sieve(cbU[1])
    surv1 = set(zip((N1 % L1).tolist(), (B1 % L1).tolist()))
    need = {(n % L1, b % L1) for (n, b) in s1}
    okN1 = need <= surv1 and len(s1) == 28
    report('r3-N1', okN1, 'U 只用纤维 1（配置 B 素数，L=%d）：|n|,|b|<=20 的 %d 个真解所在的类全部幸存：%s（幸存类共 %d 个，其中 b≢0 的 %d 个）'
           % (L1, len(s1), need <= surv1, len(surv1), sum(1 for (n, b) in surv1 if b % L1)))

    # N2：纤维 2 元素换成 eta^{-1}(1 + 2 eta^4)
    def planted(l):
        ii = pow(2, -1, l)
        e4 = powm(4, ii, l, 2)
        x = ((1 + 2 * e4[0]) % l, (2 * e4[1]) % l, (2 * e4[2]) % l)
        return mulm(x, powm(-1, ii, l, 2), ii, l)
    cbN2 = {1: cbU[1], 2: [make_cert(2, 'U', c['l'], c['P'], elem_mod=planted) for c in cbU[2]]}
    okN2, descN2, (L2_, N2_, B2_, unres2) = run_config('N2(人为公共解)', 'U', (1, 2), cbN2)
    surv2 = set(zip((N2_ % L2_).tolist(), (B2_ % L2_).tolist()))
    hit = (1 % L2_, 4 % L2_) in surv2
    report('r3-N2', hit and not okN2, '把纤维 2 的元素换成 eta^{-1}(1+2eta^4) 后：(1,4) 的类幸存：%s；整套判定没有报「排除」：%s（%s）'
           % (hit, not okN2, descN2))

    # N3：E 只用纤维 1 的 l 进步骤
    cbE, (LE, _, _, _) = results_B['E']
    unresE1, _ = padic(cbE[1], LE)
    m5 = (-5) % LE
    report('r3-N3', m5 in set(unresE1.tolist()), 'E 只用纤维 1 的 l 进步骤：n0 ≡ -5 (mod %d) 未解决：%s（未解决共 %d 个）'
           % (LE, m5 in set(unresE1.tolist()), len(unresE1)))

    # N4：纤维 1 元素换成 eta^{-7}(3 + eta^L)
    Lfin = LU

    def planted4(l):
        e = powm(Lfin, 1, l, 1)
        x = ((3 + e[0]) % l, e[1] % l, e[2] % l)
        return mulm(x, powm(-7, 1, l, 1), 1, l)
    cbN4 = [make_cert(1, 'U', c['l'], c['P'], elem_mod=planted4) for c in cbU[1]]
    unres4, _ = padic(cbN4, Lfin)
    report('r3-N4', 7 in set(unres4.tolist()), '纤维 1 元素换成 eta^{-7}(3+eta^L)（L=%d，(7,L) 是 b≡0 的真解）：l 进步骤在 n0=7 未解决：%s'
           % (Lfin, 7 in set(unres4.tolist())))

    print('time %.1fs' % (time.time() - t_all))
    npass = sum(RES)
    print('SUMMARY s9-r3 pass=%d fail=%d' % (npass, len(RES) - npass))
    return 0 if npass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
