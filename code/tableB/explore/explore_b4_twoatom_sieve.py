# -*- coding: utf-8 -*-
"""探索（2026-10-08，B4 注 2.7「每个 i 两个原子」）：纤维 3 上 D_3^U(n,b)=0（b≠0）是否无解。

两原子条件 W̃_i ∈ span_Q(x^a, x^a') ⇔ 1, x^b, W̃_i x^n 在 Q 上线性相关（n=-a, b=a'-a）⇔ D_i^U(n,b)=0，
与 notes/08 的 (F_i^U) 完全相同；那里 U 只用纤维 1、2 的联合条件，这里要的是纤维 3 单独无解。
方法照搬 notes/08 §2：先找 η 模 l 的阶整除 T=5040 的素数，筛 b≢0 (mod T)，再对 b≡0 用 l 进导数。
复用 check_b2.py 的模运算与筛法实现（把纤维 3 的证书表换成这里找到的素数）。
用法（任务 C 根目录）： py -3.14 code/tableB/explore/explore_b4_twoatom_sieve.py [L=200000] [纤维=3] [T=5040]
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TB = os.path.dirname(HERE)
sys.path.insert(0, TB)
import check_b2 as B2  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

L = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
FIB = int(sys.argv[2]) if len(sys.argv) > 2 else 3
T = int(sys.argv[3]) if len(sys.argv) > 3 else 5040
B2.T = T  # check_b2 的 sieve/padic 读模块全局 T


def divisors(n):
    return sorted(d for d in range(1, n + 1) if n % d == 0)


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = bytearray(len(s[p * p::p]))
    return [p for p in range(n + 1) if s[p]]


def find_cert(i, L):
    out = []
    DV = divisors(T)
    for l in primes_upto(L):
        if l == 2 or i % l == 0:
            continue
        if B2.powm(T, i, l) != [1, 0, 0]:
            continue
        P = next(d for d in DV if B2.powm(d, i, l) == [1, 0, 0])
        out.append((l, P))
    return out


def main():
    t0 = time.time()
    i = FIB
    cert = find_cert(i, L)
    print('纤维 %d，l<=%d 中阶整除 %d 的素数（%d 个）：%s' % (i, L, T, len(cert), cert), flush=True)
    print('  disc(b_%d)=%d；用时 %.1fs' % (i, B2.disc(i), time.time() - t0), flush=True)
    B2.CERT[i] = cert
    surv, tabs = B2.sieve('U', (i,))
    print('筛法：b≢0 的 %d 个剩余类，幸存 %d 个；用时 %.1fs' % (T * (T - 1), len(surv), time.time() - t0), flush=True)
    if surv:
        bs = sorted({b for (_, b) in surv})
        print('  幸存类的 b0（前 40 个）：%s' % bs[:40])
        print('  幸存类（前 40 个）：%s' % surv[:40])
    unr, used = B2.padic('U', (i,), tabs)
    print('l 进：未解决的 n0 %d 个（前 40 个 %s）；首中次数 %s；用时 %.1fs'
          % (len(unr), unr[:40], dict(sorted(used.items())), time.time() - t0), flush=True)
    # 小范围精确解
    sm = B2.small_solutions(i, 'U', R=40)
    print('|n|,|b|<=40 的精确解：%d 个 %s' % (len(sm), sorted(sm)[:20]))
    print('time %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
