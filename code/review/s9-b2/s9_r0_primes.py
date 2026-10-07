# -*- coding: utf-8 -*-
"""s9-b2 复核 r0（探索）：找 eta 模 l 的阶是光滑数的素数 l，用来另选模数 T 做筛法。
不导入项目里的任何代码。eta 为 b_i = 1 - x - i x^3 的根（i=1,2,3），在 F_l[x]/(b_i) 中运算：
  x^3 = i^{-1} (1 - x)。
输出：每个纤维 i、每个 l < LIM，若 eta^LAM = 1（LAM 为一个大光滑数）就给出精确阶。
"""
import sys
import time
import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
LAM_FACT = {2: 7, 3: 4, 5: 2, 7: 2, 11: 1, 13: 1, 17: 1, 19: 1, 23: 1}
LAM = 1
for p, e in LAM_FACT.items():
    LAM *= p ** e


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return [int(v) for v in np.nonzero(s)[0]]


def mul(a, b, ii, l):
    # a, b: 系数 (a0,a1,a2)，代表 a0 + a1 x + a2 x^2；x^3 = ii*(1-x)，x^4 = ii*(x - x^2)
    a0, a1, a2 = a
    b0, b1, b2 = b
    c0 = a0 * b0
    c1 = a0 * b1 + a1 * b0
    c2 = a0 * b2 + a1 * b1 + a2 * b0
    c3 = a1 * b2 + a2 * b1
    c4 = a2 * b2
    c3 %= l
    c4 %= l
    # x^3 -> ii - ii x ; x^4 -> ii x - ii x^2
    c0 += ii * c3
    c1 += -ii * c3 + ii * c4
    c2 += -ii * c4
    return (c0 % l, c1 % l, c2 % l)


def pw(e, ii, l):
    r = (1, 0, 0)
    base = (0, 1, 0)
    while e:
        if e & 1:
            r = mul(r, base, ii, l)
        base = mul(base, base, ii, l)
        e >>= 1
    return r


def main():
    t0 = time.time()
    ps = primes_upto(LIM)
    found = {1: [], 2: [], 3: []}
    for l in ps:
        if l == 2:
            continue
        for i in (1, 2, 3):
            if i % l == 0:
                continue
            ii = pow(i, -1, l)
            if pw(LAM, ii, l) != (1, 0, 0):
                continue
            o = LAM
            for p in LAM_FACT:
                while o % p == 0 and pw(o // p, ii, l) == (1, 0, 0):
                    o //= p
            found[i].append((l, o))
    for i in (1, 2, 3):
        lst = sorted(found[i], key=lambda t: t[1])
        print('fiber %d: %d primes with smooth order' % (i, len(lst)))
        print('  ' + ' '.join('(%d,%d)' % t for t in lst if t[1] <= 200000))
    # 对若干候选 T 列出阶整除 T 的素数
    note = {1: {3, 11, 13, 29, 2521}, 2: {7, 17, 19, 41, 71, 127}, 3: {13, 71}}
    for T in (5040, 10080, 15120, 7560, 27720, 55440, 30240, 50400, 65520, 83160, 110880):
        line = []
        for i in (1, 2, 3):
            sel = [(l, o) for (l, o) in found[i] if T % o == 0]
            new = [(l, o) for (l, o) in sel if l not in note[i]]
            line.append('i=%d:%d(new %d)' % (i, len(sel), len(new)))
        print('T=%d  %s' % (T, '  '.join(line)))
    print('time %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
