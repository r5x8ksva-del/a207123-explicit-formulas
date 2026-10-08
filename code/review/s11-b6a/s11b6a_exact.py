# -*- coding: utf-8 -*-
"""s11-b6a 复核 X1–X6：精确算术（Fraction 与 Gauss 有理数）核对 notes/11 的代数部分。

不导入项目里的任何模块，只用标准库。

  X1  命题 1 的 t^m 系数恒等式作为 Q(x) 中的有理函数恒等式成立（m<=14），这是证明而不是抽样：
      两边乘 D_m(x)=x^{3m-2}P_m(x) 后都是次数 <= 6m-2 的多项式（W_m 次数 3m；(1/P_m-1)/x 项给 x^{3m-3}(1-P_m)；
      z 项每一项是 x^{>=1} 乘 P_m/b_{m-j}），在 6m-1 个以上的点相等即恒等。取 x=2,3,...,85（84 个点，D_m 不为零）。
      左边的 G_m 用原始递推 b_m G_m = G_{m-1} + m x^2（G_{-1}=1）。反向：把 e_{m-1-j} 换成 e_{m-j}，在 x=2 就失败。
  X2  命题 8 在 x=-1（lam=-2）：F(-1,t)=[e^t-1+t^2/(1-t)+e^{t-1}(Ei(1-t)-Ei(1))]/t^2 的 Taylor 系数全是有理数：
      B(t):=e^{t-1}(Ei(1-t)-Ei(1)) 满足 B'=B-1/(1-t)、B(0)=0。与 G_m(-1) 逐项相等（m<=60）。
      反向：把 t^2/(1-t) 换成 t^2/(1-t)^2，或把 B 的符号取反，都失败。
  X3  命题 8 在复数 x=(1+i)/2（lam=-2，z=-2-2i）：闭式
      f = (M-1/(1-t))/x + z t^{-2}[-C_0-C_1-B_z]，C_k=e^{-zt}∫_0^t s^k e^{zs}ds，B_z=e^{z(1-t)}(Ei(-z(1-t))-Ei(-z))，
      都满足有理系数的一阶方程（C_k'=-zC_k+t^k，B_z'=-zB_z-1/(1-t)），在 Q(i) 中精确展开，与 G_m(x) 逐项相等（m<=40）；
      括号的 t^0、t^1 系数恰为 0（t^{-2} 可以整除）。反向：把 z 换成 -z 失败。
  X4  Phi_1(1-lam,1;2-lam;t,zt) 的 t^N 系数 = (1-lam)e_N(z)/(N+1-lam)：把 lam、z 当作互相独立的有理数也成立（N<=25，
      4 组 (lam,z)），所以这个改写与 z=x^-3、lam=(1-x)/x^3 的关系无关。
  X5  M 在 lam=-n 时是初等函数：1F1(1;n+1;w) = n! w^{-n}(e^w - sum_{k<n} w^k/k!)（n<=6，w^k 系数 k<=30）；
      以及 z-lam=x^-2、1-lam=-b_1/x^3、n+1-lam=-b_{n+1}/x^3（10 个 x）。
  X6  L 的两条算子恒等式（精确，t^30 以内，5 个有理 x）：L[(M-1/(1-t))/x] = gamma + t/(1-t)，L[z*Xi] = -t/(1-t)。
"""
import sys
import time
from fractions import Fraction as Fr
from math import factorial

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


class Q:
    """Q(i) 的元素 a+bi（a、b 为 Fraction）。"""
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        o = qq(o)
        return Q(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __sub__(self, o):
        o = qq(o)
        return Q(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        return qq(o) - self

    def __mul__(self, o):
        o = qq(o)
        return Q(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = qq(o)
        d = o.a * o.a + o.b * o.b
        return Q((self.a * o.a + self.b * o.b) / d, (self.b * o.a - self.a * o.b) / d)

    def __rtruediv__(self, o):
        return qq(o) / self

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __pow__(self, k):
        r = Q(1)
        for _ in range(k):
            r = r * self
        return r

    def __eq__(self, o):
        o = qq(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def is_zero(self):
        return self.a == 0 and self.b == 0


def qq(o):
    return o if isinstance(o, Q) else Q(o)


def G_rec(x, M):
    G, prev = [], 1
    for m in range(M + 1):
        g = (prev + m * x * x) / (1 - x - m * x ** 3)
        G.append(g)
        prev = g
    return G


def rhs_coeffs(x, M, shift_e=0):
    z = 1 / x ** 3
    lam = (1 - x) / x ** 3
    P, out = 1, []
    e = []
    acc, term = 0, 1
    for n in range(M + 2):
        acc += term
        e.append(acc)
        term = term * z / (n + 1)
    for m in range(M + 1):
        P = P * (1 - x - m * x ** 3)
        s = (1 / P - 1) / x
        for j in range(m):
            s += z * (-z) ** j / factorial(j) * e[m - 1 - j + shift_e] / (m - j - lam)
        out.append(s)
    return out


def series_mul(a, b, N):
    return [sum(a[i] * b[n - i] for i in range(n + 1)) for n in range(N + 1)]


def main():
    t_start = time.time()
    # X1
    M = 14
    pts = [Fr(k) for k in range(2, 86)]
    ok1 = True
    for x in pts:
        if G_rec(x, M) != rhs_coeffs(x, M):
            ok1 = False
            break
    rev1 = G_rec(Fr(2), 4) != rhs_coeffs(Fr(2), 4, shift_e=1)
    report('X1', ok1 and rev1 and len(pts) >= 6 * M - 1,
           '命题 1 的 [t^m] 恒等式在 x=2..85（%d 点 >= 6M-1=%d）上精确成立，m<=%d，故为 Q(x) 中的恒等式；'
           '反向（e 指标加 1）失败：%s' % (len(pts), 6 * M - 1, M, rev1))
    # X2
    N = 62
    A = [Fr(0)] * (N + 1)          # B(t) 的系数：B' = B - 1/(1-t)
    for n in range(N):
        A[n + 1] = (A[n] - 1) / (n + 1)
    expo = [Fr(1, factorial(n)) for n in range(N + 1)]

    def F_m1(sign_B=1, geo_pow=1):
        br = [Fr(0)] * (N + 1)
        for n in range(N + 1):
            br[n] += expo[n] - (1 if n == 0 else 0)
            if n >= 2:
                br[n] += (1 if geo_pow == 1 else (n - 1))     # t^2/(1-t) 或 t^2/(1-t)^2
            br[n] += sign_B * A[n]
        assert br[0] == 0 and br[1] == 0 or sign_B != 1 or geo_pow != 1
        return [br[n + 2] for n in range(N - 1)]
    G = G_rec(Fr(-1), N - 2)
    ok2 = F_m1()[:61] == G[:61]
    rev2 = F_m1(sign_B=-1)[:61] != G[:61] and F_m1(geo_pow=2)[:61] != G[:61]
    report('X2', ok2 and rev2, 'x=-1：闭式的 t^m 系数与 G_m(-1) 逐项相等（m<=60）：%s；反向（B 变号 / 换成 (1-t)^{-2}）失败：%s'
           % (ok2, rev2))
    # X3
    x = Q(Fr(1, 2), Fr(1, 2))
    N3 = 44

    def closed_lam_m2(x, z, N3):
        P, Mc = Q(1), []
        for m in range(N3 + 1):
            P = P * (1 - x - x * x * x * m)
            Mc.append(1 / P)
        R = [(Mc[m] - 1) / x for m in range(N3 + 1)]
        C = []
        for k in (0, 1):
            ck = [Q(0)] * (N3 + 3)
            for n in range(N3 + 2):
                ck[n + 1] = (-z * ck[n] + (1 if n == k else 0)) / (n + 1)
            C.append(ck)
        Bz = [Q(0)] * (N3 + 3)
        for n in range(N3 + 2):
            Bz[n + 1] = (-z * Bz[n] - 1) / (n + 1)
        br = [-(C[0][n] + C[1][n] + Bz[n]) for n in range(N3 + 3)]
        head_zero = br[0].is_zero() and br[1].is_zero()
        f = [R[m] + z * br[m + 2] for m in range(N3 + 1)]
        return f, head_zero
    z = 1 / (x * x * x)
    lam = (1 - x) / (x * x * x)
    f3, hz = closed_lam_m2(x, z, N3)
    G3 = G_rec(x, N3)
    ok3 = lam == Q(-2) and z == Q(-2, -2) and hz and all(f3[m] == G3[m] for m in range(41))
    f3bad, _ = closed_lam_m2(x, -z, N3)
    rev3 = not all(f3bad[m] == G3[m] for m in range(41))
    report('X3', ok3 and rev3, 'x=(1+i)/2：lam=%s，z=%s；括号 t^0,t^1 系数为 0：%s；闭式与 G_m 逐项相等（m<=40）：%s；'
           '反向（z->-z）失败：%s' % ('-2' if lam == Q(-2) else '?', '-2-2i' if z == Q(-2, -2) else '?', hz,
                                   all(f3[m] == G3[m] for m in range(41)), rev3))
    # X4
    ok4 = True
    for lam_, z_ in [(Fr(7, 3), Fr(5, 2)), (Fr(-11, 4), Fr(-3, 7)), (Fr(1, 2), Fr(9)), (Fr(13, 5), Fr(-2, 9))]:
        e_acc, term = Fr(0), Fr(1)
        for NN in range(26):
            e_acc += term
            term = term * z_ / (NN + 1)
            pa, pc = Fr(1), Fr(1)
            for i in range(NN):
                pa *= (1 - lam_ + i)
                pc *= (2 - lam_ + i)
            s = sum(pa * Fr(factorial(NN - n)) / (pc * factorial(NN - n) * factorial(n)) * z_ ** n for n in range(NN + 1))
            if s != (1 - lam_) * e_acc / (NN + 1 - lam_):
                ok4 = False
    report('X4', ok4, 'Phi_1 改写对独立的有理 (lam,z) 逐系数成立（N<=25，4 组）：%s' % ok4)
    # X5
    ok5 = True
    for n in range(1, 7):
        for k in range(31):
            lhs = Fr(1)
            for i in range(k):
                lhs /= (n + 1 + i)          # 1/(n+1)_k
            rhs = Fr(factorial(n), factorial(n + k))
            ok5 &= lhs == rhs
    for x_ in [Fr(3, 5), Fr(2), Fr(-1), Fr(-3, 2), Fr(5, 4), Fr(2, 7), Fr(9, 10), Fr(-2, 3), Fr(7, 3), Fr(1, 3)]:
        lam_ = (1 - x_) / x_ ** 3
        z_ = 1 / x_ ** 3
        ok5 &= (z_ - lam_ == 1 / x_ ** 2)
        b1 = 1 - x_ - x_ ** 3
        ok5 &= (1 - lam_ == -b1 / x_ ** 3)
        for nn in range(6):
            ok5 &= (nn + 1 - lam_ == -(1 - x_ - (nn + 1) * x_ ** 3) / x_ ** 3)
    report('X5', ok5, '1F1(1;n+1;w) 的初等形式（n<=6）与 z-lam=x^-2 等关系（10 个 x）：%s' % ok5)
    # X6
    ok6 = True
    N6 = 30
    for x_ in [Fr(3, 5), Fr(2), Fr(-1), Fr(5, 4), Fr(-2, 3)]:
        lam_ = (1 - x_) / x_ ** 3
        z_ = 1 / x_ ** 3
        P, Mc = Fr(1), []
        for m in range(N6 + 1):
            P *= (1 - x_ - m * x_ ** 3)
            Mc.append(1 / P)
        Acoef = [(Mc[m] - 1) / x_ for m in range(N6 + 1)]
        e_list, acc, term = [], Fr(0), Fr(1)
        for n in range(N6 + 1):
            acc += term
            e_list.append(acc)
            term = term * z_ / (n + 1)
        K = [e_list[n] / (n + 1 - lam_) for n in range(N6 + 1)]
        em = [(-z_) ** j / factorial(j) for j in range(N6 + 1)]
        Xi = series_mul(em, [Fr(0)] + K[:N6], N6)

        def Lop(Y):
            return [(1 - x_ - m * x_ ** 3) * Y[m] - (Y[m - 1] if m >= 1 else 0) for m in range(N6 + 1)]
        gam_plus = [Fr(1)] + [m * x_ ** 2 + 1 for m in range(1, N6 + 1)]
        ok6 &= Lop(Acoef) == gam_plus
        ok6 &= [z_ * v for v in Lop(Xi)] == [Fr(0)] + [Fr(-1)] * N6
    report('X6', ok6, 'L[(M-1/(1-t))/x]=gamma+t/(1-t) 与 L[z Xi]=-t/(1-t)（t^30 以内，5 个 x）：%s' % ok6)
    n_pass = sum(RES)
    print('SUMMARY s11b6a_exact pass=%d fail=%d time=%.1fs' % (n_pass, len(RES) - n_pass, time.time() - t_start))
    return 0 if n_pass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
