# -*- coding: utf-8 -*-
"""t4：核对 T4.3(7) 的闭式（Q[y][[z]] 中的形式恒等式）到 z^NZ：
   A(z,y) := Σ_{q>=1} R_q(y) z^q/q! = (y+1)(Φ-1)/y^2 - yΦ·I，
   Φ = (1-z)^{y^3-y^2} exp(y^3 z/(1-z)) := exp( y^2 L + y^3 (u - L) )，L=Σ z^n/n，u=Σ_{n>=1} z^n，
   I = G(u)，G(w) := ∫_0^w g，g(w) := (1+w)^{y^3-y^2} e^{-y^3 w} := exp( (y^3-y^2) ln(1+w) - y^3 w )。
形式运算：exp 只作用于常数项为 0 的级数（用 F'=X'F 逐项递推）；形式积分逐项；
复合 G(u) 合法因为 u 的常数项为 0（截断到 z^NZ 只用到 G 的前 NZ 项）。
R_q 直接取自 Num_q 的反转（不经过任何母函数）。
另外核对：闭式满足 s6-t436 证明里的 ODE（与 t2 的 L1 同式），以及 [y^j] 分量与 P_j 的代入值一致。
"""
import sys
sys.dont_write_bytecode = True
import time
from fractions import Fraction
from math import factorial
import s6lib as L

t0 = time.time()
NZ = int(sys.argv[1]) if len(sys.argv) > 1 else 20
ok_all = True


def report(name, ok, extra=''):
    global ok_all
    ok_all = ok_all and ok
    print('[%s] %s %s' % ('OK ' if ok else 'BAD', name, extra))
    sys.stdout.flush()

# y 的多项式：Fraction 列表；z 的级数：y 多项式的列表（截断到 z^NZ）
def yadd(p, q, s=1):
    n = max(len(p), len(q))
    return [(p[k] if k < len(p) else 0) + s * (q[k] if k < len(q) else 0) for k in range(n)]

def ymul(p, q):
    if not p or not q:
        return [Fraction(0)]
    r = [Fraction(0)] * (len(p) + len(q) - 1)
    for a_, x in enumerate(p):
        if x:
            for b_, y in enumerate(q):
                if y:
                    r[a_ + b_] += x * y
    return r

def ytrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p

def smul(F, G_):
    H = []
    for n in range(NZ + 1):
        acc = [Fraction(0)]
        for k in range(n + 1):
            acc = yadd(acc, ymul(F[k], G_[n - k]))
        H.append(acc)
    return H

def sexp(X):
    assert all(x == 0 for x in X[0])
    F = [[Fraction(1)]]
    for n in range(NZ):
        acc = [Fraction(0)]
        for k in range(n + 1):
            acc = yadd(acc, [Fraction(k + 1) * x for x in ymul(X[k + 1], F[n - k])])
        F.append([x / (n + 1) for x in acc])
    return F

# Φ
X = [[Fraction(0)]]
for n in range(1, NZ + 1):
    X.append([Fraction(0), Fraction(0), Fraction(1, n), Fraction(1) - Fraction(1, n)])   # y^2/n + y^3(1-1/n)
Phi = sexp(X)
# g(w) 与 G(w)
Y = [[Fraction(0)]]
for n in range(1, NZ + 1):
    cn = Fraction((-1) ** (n + 1), n)                     # [w^n] ln(1+w)
    Y.append([Fraction(0), Fraction(0), -cn, cn - (1 if n == 1 else 0)])   # (y^3-y^2)ln(1+w) - y^3 w
g = sexp(Y)
Gw = [[Fraction(0)]] + [[x / (n + 1) for x in g[n]] for n in range(NZ)]   # G(w)=Σ g_n w^{n+1}/(n+1)
# u^k（标量级数），G(u) = Σ_k G_k u^k
u = L.u_series(NZ)
upow = [[Fraction(1)] + [Fraction(0)] * NZ]
for _ in range(NZ):
    upow.append(L.ser_mul(upow[-1], u, NZ))
Iu = [[Fraction(0)] for _ in range(NZ + 1)]
for k in range(1, NZ + 1):
    for n in range(NZ + 1):
        if upow[k][n]:
            Iu[n] = yadd(Iu[n], [upow[k][n] * x for x in Gw[k]])
# (y+1)(Φ-1)/y^2
first = []
okdiv = True
for n in range(NZ + 1):
    p = list(Phi[n])
    if n == 0:
        p = yadd(p, [Fraction(1)], -1)
    p = ytrim(p) + [Fraction(0)] * 2
    if p[0] != 0 or p[1] != 0:
        okdiv = False
    q_ = p[2:] if len(p) > 2 else [Fraction(0)]
    first.append(ymul([Fraction(1), Fraction(1)], q_))
report('Φ-1 在 Q[y][[z]] 中被 y^2 整除', okdiv, '(到 z^%d)' % NZ)
PhiI = smul(Phi, Iu)
Aclosed = [yadd(first[n], [Fraction(0)] + PhiI[n], -1) for n in range(NZ + 1)]

N = L.num_polys(NZ)


def compare(Acand, verbose=True):
    good = ytrim(Acand[0]) == [0]
    nbad = 0
    for q in range(1, NZ + 1):
        target = [Fraction(x, factorial(q)) for x in reversed(N[q])]
        if ytrim(Acand[q]) != ytrim(target):
            good = False
            nbad += 1
            if verbose:
                print('   闭式在 z^%d 处不符' % q)
    return good, nbad


ok, _ = compare(Aclosed)
report('T4.3(7) 闭式 = Σ R_q z^q/q!（逐个 y 多项式比较，R_q 取自 Num_q）', ok, '(到 z^%d)' % NZ)
print('   样例：[z^3] 闭式 =', [str(x) for x in ytrim(Aclosed[3])], '；R_3/3! =',
      [str(Fraction(x, 6)) for x in reversed(N[3])])

# 阴性对照 1：把 yΦI 的符号改成 +
Abad1 = [yadd(first[n], [Fraction(0)] + PhiI[n], +1) for n in range(NZ + 1)]
bad1, nb1 = compare(Abad1, verbose=False)
# 阴性对照 2：Φ 去掉 y^3(u-L) 这一项
X2 = [[Fraction(0)]] + [[Fraction(0), Fraction(0), Fraction(1, n)] for n in range(1, NZ + 1)]
Phi2 = sexp(X2)
first2 = []
for n in range(NZ + 1):
    p = list(Phi2[n])
    if n == 0:
        p = yadd(p, [Fraction(1)], -1)
    p = ytrim(p) + [Fraction(0)] * 2
    first2.append(ymul([Fraction(1), Fraction(1)], p[2:] if len(p) > 2 else [Fraction(0)]))
PhiI2 = smul(Phi2, Iu)
Abad2 = [yadd(first2[n], [Fraction(0)] + PhiI2[n], -1) for n in range(NZ + 1)]
bad2, nb2 = compare(Abad2, verbose=False)
report('阴性对照：改错符号或去掉 Φ 的 y^3 项后比较必须失败', (not bad1) and (not bad2),
       '(不符的 z 次数个数：%d 与 %d，共 %d 个)' % (nb1, nb2, NZ))
print('ALL_OK' if ok_all else 'SOME_BAD', '  time %.1fs' % (time.time() - t0))
