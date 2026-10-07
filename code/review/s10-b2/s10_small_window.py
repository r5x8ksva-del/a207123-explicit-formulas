# -*- coding: utf-8 -*-
"""s10-b2 check (d): exact linear dependence of 1, eta^b, W(eta) eta^n over Q in a window.

Two independent exact models of K_i:
  * eta basis (1, eta, eta^2), eta^3 = (1-eta)/i, via the 2x2 shortcut D_i(n,b) of note 08, and
  * y basis (1, y, y^2), y = 1/eta, y^3 = y^2 + i, via the full 3x3 determinant of the coordinates.
The two determinants must differ by one fixed nonzero factor (the change-of-basis determinant).
Then: all zeros per fibre, common zeros, and the specific values quoted in note 08 section 3,
plus the m = 1 (F3 type), E_1, E_2 and G_1 representations checked as power series.
"""
import sys
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10lib import Ki, Ky, Wtilde_poly, cols_det, P_poly, W_poly, series_div

FAIL = 0
PASS = 0


def report(name, ok, info=''):
    global FAIL, PASS
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + (' | ' + info if info else ''), flush=True)


WIN = 60
WIN_NOTE = 40


def Wpoly(part, i):
    w = list(Wtilde_poly(i))
    if part == 'E':
        w[0] -= 1
    return w


zeros = {}
values = {}
for part in ('U', 'E'):
    for i in (1, 2, 3):
        K = Ki(i)
        Y = Ky(i)
        w = Wpoly(part, i)
        Wk = K.ev(w)
        ratio = None
        okr = True
        Z = set()
        for n in range(-WIN, WIN + 1):
            q = K.mul(Wk, K.eta_pow(n))
            qy = Y.ev_eta(w, shift=n)
            for b in range(-WIN, WIN + 1):
                p = K.eta_pow(b)
                D = p[1] * q[2] - p[2] * q[1]
                Dy = cols_det((Fr(1), Fr(0), Fr(0)), Y.eta_pow(b), qy)
                if (D == 0) != (Dy == 0):
                    okr = False
                if D != 0:
                    r = Dy / D
                    if ratio is None:
                        ratio = r
                    elif r != ratio:
                        okr = False
                    values[(part, i, n, b)] = D
                else:
                    values[(part, i, n, b)] = D
                    Z.add((n, b))
        zeros[(part, i)] = Z
        report('two models agree, %s fibre %d (|n|,|b|<=%d): det_y/det_eta constant = %s' % (part, i, WIN, ratio), okr)

# ------------------------------------------------------------------ zero sets
def inwin(S, w):
    return sorted((n, b) for (n, b) in S if abs(n) <= w and abs(b) <= w)


for part in ('U', 'E'):
    for i in (1, 2, 3):
        Z = zeros[(part, i)]
        nz = [z for z in Z if z[1] != 0]
        print('   %s fibre %d: zeros with b!=0 in |n|,|b|<=%d: %d ; in |n|,|b|<=%d: %d' %
              (part, i, WIN, len(nz), WIN_NOTE, len(inwin(nz, WIN_NOTE))))
        if len(inwin(nz, WIN_NOTE)) <= 40:
            print('      ', inwin(nz, WIN_NOTE))

Z1, Z2 = zeros[('U', 1)], zeros[('U', 2)]
U12 = sorted(z for z in Z1 & Z2 if z[1] != 0)
report('U: no common zero of fibres 1,2 with b!=0 in |n|,|b|<=%d' % WIN, len(U12) == 0, str(U12))
nz1 = [z for z in Z1 if z[1] != 0]
report('U fibre 1: 28 zeros with b!=0 in |n|,|b|<=40 (note 08 sect. 3)', len(inwin(nz1, 40)) == 28, str(len(inwin(nz1, 40))))
nz2 = inwin([z for z in Z2 if z[1] != 0], 40)
report('U fibre 2: exactly (-15,-10),(-8,-5),(-5,10),(-3,5) in |n|,|b|<=40',
       nz2 == [(-15, -10), (-8, -5), (-5, 10), (-3, 5)], str(nz2))
E1, E2, E3 = zeros[('E', 1)], zeros[('E', 2)], zeros[('E', 3)]
E12 = sorted(z for z in E1 & E2 if z[1] != 0)
print('   E: common zeros of fibres 1,2 (b!=0, |n|,|b|<=%d): %s' % (WIN, E12))
report('E: common zeros of fibres 1,2 in |n|,|b|<=40 are exactly the six of note 08',
       inwin(E12, 40) == sorted([(-5, 3), (-8, -3), (-5, 1), (-6, -1), (-6, 2), (-8, -2)]), str(inwin(E12, 40)))
E123 = sorted(z for z in E1 & E2 & E3 if z[1] != 0)
report('E: no common zero of fibres 1,2,3 with b!=0 in |n|,|b|<=%d' % WIN, len(E123) == 0, str(E123))
# trivial families of E fibre 1: n = -5 and n + 5 = b
triv = all((-5, b) in E1 for b in range(-WIN, WIN + 1)) and all((b - 5, b) in E1 for b in range(-WIN + 5, WIN + 1))
report('E fibre 1 contains the trivial families n=-5 and n+5=b', triv)

# ------------------------------------------------------------------ quoted values (eta basis)
report('D_2^U(1,4) = 3/8', values[('U', 2, 1, 4)] == Fr(3, 8), str(values[('U', 2, 1, 4)]))
report('D_2^U(-3,-4) = -6', values[('U', 2, -3, -4)] == -6, str(values[('U', 2, -3, -4)]))
report('D_3^E(-5,3) = -2/3', values[('E', 3, -5, 3)] == Fr(-2, 3), str(values[('E', 3, -5, 3)]))
report('(1,4), (-3,-4), (0,5), (-5,-5) satisfy U fibre 1',
       all(z in Z1 for z in [(1, 4), (-3, -4), (0, 5), (-5, -5)]))

# ------------------------------------------------------------------ the representations of section 3
N = 60


def conv_binom_family(A, c, d, m, N):
    """coefficients k = 0..N of sum_s A(s) C(k + c - 2s, m + s + d)  with C(a,b)=0 unless 0<=b<=a"""
    out = []
    for k in range(N + 1):
        tot = 0
        for s in range(-m - d, k + abs(c) + 5):
            a_, b_ = k + c - 2 * s, m + s + d
            if 0 <= b_ <= a_:
                tot += A(s) * comb(a_, b_)
        out.append(tot)
    return out


def gf(num_list, m, N):
    return series_div(num_list, P_poly(m), N)


def ind(f):
    """A(s) = f(s) for s >= 0 and 0 for s < 0 (the sums of note 08 sect. 3 start at s = 0)"""
    return lambda s: f(s) if s >= 0 else 0


W1 = W_poly(1)
G1 = gf(W1, 1, N)
F3 = [x - y for x, y in zip(conv_binom_family(ind(lambda s: 1), 2, 0, 1, N),
                            conv_binom_family(ind(lambda s: 1), 0, -1, 1, N))]
report('F3 type: U_k(1) = sum_{s>=0} C(k+2-2s,1+s) - sum_{s>=0} C(k-2s,s), k<=60', F3 == G1)
# the same with the s = -1 term of the first family included (paper's "all s" reading) is off by one:
F3all = [x - y for x, y in zip(conv_binom_family(lambda s: 1, 2, 0, 1, N),
                               conv_binom_family(lambda s: 1, 0, -1, 1, N))]
print('   F3 with A(s)=1 for all s (incl. s=-1): difference to U_k(1) for k<=5:',
      [F3all[k] - G1[k] for k in range(6)])
W2 = W_poly(2)
W2m1 = list(W2)
W2m1[0] -= 1
E2 = gf(W2m1, 2, N)
rep = [x + y for x, y in zip(conv_binom_family(ind(lambda s: 2 ** (s + 1) - 1), -1, -1, 2, N),
                             conv_binom_family(ind(lambda s: 2 ** (s + 1)), -2, -2, 2, N))]
report('E(k,2) = sum (2^{s+1}-1) C(k-1-2s,s+1) + sum 2^{s+1} C(k-2-2s,s), k<=60', rep == E2)
W1m1 = list(W1)
W1m1[0] -= 1
E1s = gf(W1m1, 1, N)
rep1 = conv_binom_family(ind(lambda s: 1), -2, -1, 1, N)
report('E_1 single family: E(k,1) = sum C(k-2-2s, s), k<=60', rep1 == E1s)
# G_1 = x^{-6} u^2/(1-u) + x^{-1} u/(1-u):  x^{-6}u^{t+2} -> C(k+1-2t, t+1) ; x^{-1}u^{t+1} -> C(k-2-2t, t)
repG1 = [x + y for x, y in zip(conv_binom_family(ind(lambda s: 1), 1, 0, 1, N),
                               conv_binom_family(ind(lambda s: 1), -2, -1, 1, N))]
report('G_1 = x^-6 u^2/(1-u) + x^-1 u/(1-u) (as binomial sums), k<=60', repG1 == G1)

print('SUMMARY s10_small_window: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
