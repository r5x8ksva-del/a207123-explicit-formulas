# T2.6(ii) 的主 Agent 独立重推（2026-10-07）所依赖的计算核对。不导入 core，也不复用复核者 x1 的脚本。
# 核对内容：
#   (a) E 部分的母函数：以上升结尾的合法序列数 E(k,m) 的母函数等于 (W_m−1)/P_m（自写 DP，m≤6、k≤30）；
#   (b) 在 b_i 的根 η 处的化简：b_v(η)=(i−v)η³，η·b_i′(η)=2η−3，W̃_i(η)−1=i!·η²·Σ_j j·η^{3j}/(i−j)!；
#   (c) 留数闭式：Res_η E_m · u′(η) = (−1)^{m−i+1}·(W̃_i(η)−1)·η^{−3m−3} / ((m−i)!·i!·i²)，在 Q[x]/(b_i) 中精确成立（1≤i≤8，i≤m≤40）；
#   (d) 纤维 u=1/2 的范数：N(η)=1/2，N(4−2η)=68，N(W̃_2(η)−1)=17/8；N((4−2η)η^n) 的 17-进赋值恒为 1，不可能是有理数的立方；
#   (e) b_1、b_2 在 Q 上不可约（有理根检验）；顺带确认 b_4 可约（有根 1/2），说明证明只能用不可约的纤维。
# 用法：py -3.14 code/review/main-t26ii/check_t26ii.py   （逐条打印 PASS/FAIL，任何 FAIL 时退出码为 1）
import sys
from fractions import Fraction as Fr
from math import factorial

FAILS = []


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""), flush=True)
    if not ok:
        FAILS.append(name)


# ---------- 整系数幂级数（截断） ----------
def pmul(a, b, n):
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j, y in enumerate(b[: n - i]):
                r[i + j] += x * y
    return r


def pdiv(a, b, n):  # a/b，b[0]=1
    q = [0] * n
    rem = (a + [0] * n)[:n]
    for i in range(n):
        q[i] = rem[i]
        if q[i]:
            for j in range(1, min(len(b), n - i)):
                rem[i + j] -= q[i] * b[j]
    return q


def E_series(m, n):
    b = lambda v: [1, -1, 0, -v]
    P = [1]
    Ps = [[1]]  # Ps[j] = P_{j-1}，P_{-1}=1
    for v in range(0, m + 1):
        P = pmul(P, b(v), n)
        Ps.append(P)
    W1 = [0] * n  # W_m − 1 = x²·Σ_{j=1}^{m} j·P_{j−1}
    for j in range(1, m + 1):
        for t, c in enumerate(Ps[j][: n - 2]):
            W1[t + 2] += j * c
    return pdiv(W1, Ps[m + 1], n)


def good(a, b, c):
    return b == c or a >= max(b, c)


def E_dp(k, m):
    # 状态 (倒数第二个值, 最后一个值)；只数以上升结尾（h_{k−1}<h_k）的序列
    if k < 2:
        return 0
    cur = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for _ in range(k - 2):
        nxt = {}
        for (a, b), c in cur.items():
            for d in range(m + 1):
                if good(a, b, d):
                    nxt[(b, d)] = nxt.get((b, d), 0) + c
        cur = nxt
    return sum(c for (a, b), c in cur.items() if a < b)


# ---------- Q[x]/(f)，f 为首一三次 ----------
class Cubic:
    def __init__(self, i):
        self.i = i
        self.f = [Fr(-1, i), Fr(1, i), Fr(0)]  # b_i = 1 − x − i x³ = −i·(x³ + x/i − 1/i)

    def red(self, p):
        p = [Fr(c) for c in p]
        while len(p) > 3:
            top = p.pop()
            d = len(p) - 3
            for t in range(3):
                p[d + t] -= top * self.f[t]
        return p + [Fr(0)] * (3 - len(p))

    def mul(self, a, b):
        r = [Fr(0)] * (len(a) + len(b) - 1)
        for s, x in enumerate(a):
            for t, y in enumerate(b):
                r[s + t] += x * y
        return self.red(r)

    def mat(self, a):
        cols = [self.mul(a, [0] * t + [1]) for t in range(3)]
        return [[cols[c][r] for c in range(3)] for r in range(3)]

    def norm(self, a):
        M = self.mat(a)
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    def inv(self, a):
        M = [row[:] + [Fr(int(r == 0))] for r, row in enumerate(self.mat(a))]  # 解 M·y = e_0
        for c in range(3):
            piv = next(r for r in range(c, 3) if M[r][c] != 0)
            M[c], M[piv] = M[piv], M[c]
            for r in range(3):
                if r != c and M[r][c] != 0:
                    fac = M[r][c] / M[c][c]
                    M[r] = [x - fac * y for x, y in zip(M[r], M[c])]
        return [M[r][3] / M[r][r] for r in range(3)]

    def pw(self, a, n):
        if n < 0:
            return self.pw(self.inv(a), -n)
        r, base = [Fr(1), Fr(0), Fr(0)], self.red(a)
        while n:
            if n & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            n >>= 1
        return r


def main():
    # (a) E 部分母函数
    n = 31
    ok = True
    for m in range(1, 7):
        ser = E_series(m, n)
        for k in range(n):
            if ser[k] != E_dp(k, m):
                ok = False
                print("   不一致", m, k, ser[k], E_dp(k, m))
                break
    check("a.E 部分母函数 (W_m−1)/P_m 与自写 DP 一致（1≤m≤6，0≤k≤30）", ok)

    # (b)(c) 化简与留数闭式
    ok_b = ok_c = True
    for i in range(1, 9):
        K = Cubic(i)
        eta = [Fr(0), Fr(1), Fr(0)]
        e3 = K.pw(eta, 3)
        bv = lambda v: K.red([1, -1, 0, -v])
        bi_prime = K.red([-1, 0, -3 * i])
        for v in range(0, 45):
            if bv(v) != [Fr(i - v) * c for c in e3]:
                ok_b = False
        if K.mul(eta, bi_prime) != K.red([-3, 2]):
            ok_b = False
        Wt1 = K.red([0] * 2 + [0])  # W̃_i − 1 = Σ_{j=1}^{i} j·i!/(i−j)!·x^{3j+2}
        poly = [Fr(0)] * (3 * i + 3)
        for j in range(1, i + 1):
            poly[3 * j + 2] += Fr(j * factorial(i), factorial(i - j))
        Wt1 = K.red(poly)
        alt = [Fr(0)] * (3 * i + 3)
        for j in range(1, i + 1):
            alt[3 * j + 2] += Fr(factorial(i) * j, factorial(i - j))
        if Wt1 != K.red(alt):
            ok_b = False
        # u′(η) = η²(3−2η)/(1−η)²
        one_m = K.red([1, -1])
        uprime = K.mul(K.mul(K.pw(eta, 2), K.red([3, -2])), K.pw(one_m, -2))
        inv_bip = K.inv(bi_prime)
        for m in range(i, 41):
            acc = [Fr(0)] * 3
            for j in range(1, i + 1):  # 只有 j≤i 的项含 1/b_i
                den = [Fr(1), Fr(0), Fr(0)]
                for v in range(j, m + 1):
                    if v != i:
                        den = K.mul(den, bv(v))
                term = K.mul(K.red([0, 0, j]), K.inv(den))
                acc = [x + y for x, y in zip(acc, term)]
            res = K.mul(acc, inv_bip)
            lhs = K.mul(res, uprime)
            C = Fr((-1) ** (m - i + 1), factorial(m - i) * factorial(i) * i * i)
            rhs = [C * c for c in K.mul(Wt1, K.pw(eta, -3 * m - 3))]
            if lhs != rhs:
                ok_c = False
                print("   闭式不符", i, m)
    check("b.在 b_i 的根处 b_v(η)=(i−v)η³、η·b_i′(η)=2η−3（1≤i≤8，0≤v≤44）", ok_b)
    check("c.留数闭式在 Q[x]/(b_i) 中精确成立（1≤i≤8，i≤m≤40，共 292 组）", ok_c)

    # (d) 纤维 u=1/2 的范数
    K2 = Cubic(2)
    eta = [Fr(0), Fr(1), Fr(0)]
    Ne = K2.norm(eta)
    N42 = K2.norm(K2.red([4, -2]))
    Wt2m1 = K2.red([0, 0, 0, 0, 0, 2, 0, 0, 4])  # W̃_2 − 1 = 2x⁵ + 4x⁸
    check("d.N(η)=1/2，N(4−2η)=68", Ne == Fr(1, 2) and N42 == 68, f"{Ne}, {N42}")
    check("d.W̃_2(η)−1 = η⁵(4−2η)", Wt2m1 == K2.mul(K2.pw(eta, 5), K2.red([4, -2])))
    check("d.N(W̃_2(η)−1) = 17/8", K2.norm(Wt2m1) == Fr(17, 8), str(K2.norm(Wt2m1)))

    def v17(q):
        q = Fr(q)
        num, den, v = q.numerator, q.denominator, 0
        while num % 17 == 0:
            num //= 17
            v += 1
        while den % 17 == 0:
            den //= 17
            v -= 1
        return v
    check("d.对 −60≤n≤60，N((4−2η)η^n) 的 17-进赋值都是 1（不是 3 的倍数，故不是有理数的立方）",
          all(v17(K2.norm(K2.mul(K2.red([4, -2]), K2.pw(eta, t)))) == 1 for t in range(-60, 61)))

    # (e) 不可约性：i x³ + x − 1 的有理根只可能是 ±1/d（d | i）
    def has_rational_root(i):
        cands = {Fr(s, d) for d in range(1, i + 1) if i % d == 0 for s in (1, -1)}
        return [r for r in cands if i * r ** 3 + r - 1 == 0]
    check("e.b_1、b_2 没有有理根（三次式，故在 Q 上不可约）", not has_rational_root(1) and not has_rational_root(2))
    check("e.b_4 有有理根 1/2（可约；证明只用 i=1、2，不受影响）", has_rational_root(4) == [Fr(1, 2)])

    print("结果：", "全部通过" if not FAILS else f"{len(FAILS)} 项 FAIL：" + "；".join(FAILS))
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
