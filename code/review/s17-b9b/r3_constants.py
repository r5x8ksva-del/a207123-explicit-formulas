# -*- coding: utf-8 -*-
"""s17-b9b r3：定理 1 各引理与常数的独立核对（不 import 项目代码）。
  r3-lem11  引理 1.1 两侧界（1<=j<=300，100 位十进制）；c_j/c_i 与 P_j/P_i 之比的实际上确界（说明常数 3 的来源）
  r3-lem12  引理 1.2：λ_0..λ_3（120 位）；j>=4 的不等式链逐步核对（a=ρ_j，j<=3000 的每个 j 都核对每一步）；φ(2)=3.359375；
            φ'(a)>2 的解析式在 a∈[2,200] 抽样
  r3-lem13  引理 1.3（0<=j<i<=300，60 位）
  r3-lem14  引理 1.4：M(ρ_1)（60 位）、M 递减、M(ρ_j) 的前几项；|γ_j(σ_j)|/c_j 的实际值（说明 4.2 有多松）
  r3-K      K_i 的严格上界（i<=320）与「名义值」；K_i/D_i 的最小值（检查 4.08）；A_1（检查 19.8）；
            X(K_i)<=0.26、E(K_i)<=0.01 对 i<=10^5 逐个核对；0.9702 与 X 的最大可取值
  r3-asym   K_i/(3i)-ln i-ln ln i 趋于 ln(3/0.26)=2.4457（i 到 10^15）
  r3-s14    注 1.1：按 s14-b9 §4 的三条不等式（c_j<=(u_j+jρ_j)e^{u_j}/(3j)、c_i>=u_iP_i/D_i）得到的门槛 K^{s14}_i 与 K_i 之比随 i 增大，
            K^{s14}_i/i^{4/3} 趋于常数（信息性）
用法：py -3.14 code/review/s17-b9b/r3_constants.py
"""
import math
import os
import sys
import time
from decimal import Decimal as D, getcontext, localcontext

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import rho_bracket, rho_dec, c_dec, K_bound  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def rho_f(j):
    if j == 0:
        return 1.0
    y = max(1.5, j ** (1 / 3) + 1 / 3)
    for _ in range(200):
        y2 = y - (y ** 3 - y ** 2 - j) / (3 * y * y - 2 * y)
        if abs(y2 - y) <= 1e-16 * y:
            return y2
        y = y2
    return y


t00 = time.time()
getcontext().prec = 110

# ---------------------------------------------------------------- 引理 1.1
JM = 300
rho = [D(1)] + [rho_dec(j, 110) for j in range(1, JM + 1)]
c = [D(1)] + [c_dec(j, 100) for j in range(1, JM + 1)]
u = [r ** 3 for r in rho]
Dj = [rho[j] ** 2 + 3 * j for j in range(JM + 1)]
lnP = [D(0)] + [D(j) * u[j].ln() - D(math.lgamma(j + 1)) for j in range(1, JM + 1)]   # lgamma 只给 1e-15，下面用精确阶乘重算
lnP = [D(0)] + [j * u[j].ln() - D(math.factorial(j)).ln() for j in range(1, JM + 1)]
P = [lnP[j].exp() for j in range(JM + 1)]
ok = True
minmargin = D(10)
for j in range(0, JM + 1):
    lo = u[j] * P[j] / Dj[j]
    hi = (u[j] + j) * P[j] / Dj[j]
    ok = ok and lo <= c[j] * (1 + D('1e-90')) and c[j] <= hi * (1 + D('1e-90'))
    if j >= 1:
        minmargin = min(minmargin, (c[j] - lo) / c[j], (hi - c[j]) / c[j])
# c_j/c_i 与 P_j/P_i 之比的上确界（0<=j<=i<=300）
worst, arg = D(0), None
for i in range(1, JM + 1):
    for j in range(0, i + 1):
        r = (c[j] / c[i]) / (P[j] / P[i])
        if r > worst:
            worst, arg = r, (j, i)
cp = [c[j] / P[j] for j in (1, 2, 10, 100, 300)]
report('r3-lem11', ok and worst <= 3,
       '引理 1.1：u_jP_j/D_j<=c_j<=(u_j+j)P_j/D_j 对 0<=j<=300 成立（j>=1 时最小相对余量 %.3e）；'
       '(c_j/c_i)/(P_j/P_i) 在 0<=j<=i<=300 上的最大值 %.4f（在 (j,i)=%s，<=3；j=0 时就是 1/(c_i/P_i)，'
       'c_i/P_i 在 i=1,2,10,100,300 为 %s，趋于 2/3，所以常数 3 不能换成 1，最好也只能到约 1.5）'
       % (minmargin, worst, arg, ', '.join('%.4f' % x for x in cp)))

# ---------------------------------------------------------------- 引理 1.2
lam = []
for j in range(0, 4):
    a, b = rho[j], rho[j + 1]
    lam.append((u[j + 1] / (j + 1)).ln() + j * (u[j + 1] / u[j]).ln())   # 直接按定义 ln(P_{j+1}/P_j)
lam_formula = [(rho[j + 1] / (rho[j + 1] - 1)).ln() + 3 * j * (rho[j + 1] / rho[j]).ln() for j in range(0, 4)]
ok_small = all(x > 1 for x in lam) and all(abs(x - y) < D('1e-90') for x, y in zip(lam, lam_formula))
# j>=4 的不等式链：逐步核对
ok_chain = True
rf = [rho_f(j) for j in range(0, 3002)]
worst_ratio = 1e9
for j in range(4, 3001):
    a, b = rf[j], rf[j + 1]
    delta = b - a
    Q = a * a + a * b + b * b - a - b
    s1 = abs(delta * Q - 1) < 1e-9                                  # (b-a)Q=1
    s2 = abs(Q - (3 * a * a - 2 * a + delta * (3 * a - 1) + delta ** 2)) < 1e-9 * Q
    s3 = delta <= 1 / (a * (3 * a - 2)) + 1e-15
    lowphi = 2 * a - (3 * a - 1) / (a * (3 * a - 2)) - 1 / (a * (3 * a - 2)) ** 2
    s4 = 3 * a * a - Q >= lowphi - 1e-9
    s5 = (a - 1) * (3 * a * a - Q) >= 1
    lam_lb = (1 + 3 * j * delta) / b                                # λ_j 的下界
    lam_true = math.log(b / (b - 1)) + 3 * j * math.log(b / a)
    s6 = lam_true >= lam_lb - 1e-12 and lam_lb >= 1 - 1e-12
    worst_ratio = min(worst_ratio, (a - 1) * (3 * a * a - Q))
    ok_chain = ok_chain and s1 and s2 and s3 and s4 and s5 and s6
phi2 = D(4) - D(5) / D(8) - D(1) / D(64)
# φ'(a) = 2 + (9a^2-6a+2)/(3a^2-2a)^2 + 2(6a-2)/(3a^2-2a)^3 > 2
dphi_ok = all(2 + (9 * a * a - 6 * a + 2) / (3 * a * a - 2 * a) ** 2 + 2 * (6 * a - 2) / (3 * a * a - 2 * a) ** 3 > 2
              for a in [2 + 0.01 * s for s in range(19801)])
# 「λ_j≥1 ⇔ …」实际只是「⇐」：λ_j 本身与下界 (1+3jδ)/b 的差
gap = [math.log(rf[j + 1] / (rf[j + 1] - 1)) + 3 * j * math.log(rf[j + 1] / rf[j]) - (1 + 3 * j * (rf[j + 1] - rf[j])) / rf[j + 1]
       for j in (4, 100, 1000)]
lam_asym = [((math.log(rf[j + 1] / (rf[j + 1] - 1)) + 3 * j * math.log(rf[j + 1] / rf[j])) - 1) / (2 / (3 * rf[j])) for j in (100, 1000, 3000)]
report('r3-lem12', ok_small and ok_chain and phi2 == D('3.359375') and dphi_ok,
       '引理 1.2：λ_0..λ_3=%s（按定义 ln(P_{j+1}/P_j) 与按 ln(b/(b-1))+3j ln(b/a) 两种算法一致到 1e-90，均 >1）；'
       '4<=j<=3000 的每个 j 上不等式链 (b-a)Q=1、Q 的展开、δ<=1/(a(3a-2))、3a^2-Q>=φ(a)、(a-1)(3a^2-Q)>=1（实际最小 %.4f）、'
       'λ_j>=(1+3jδ)/b>=1 逐步成立；φ(2)=4-5/8-1/64=3.359375；φ\'(a)>2（a∈[2,200] 抽样，解析上三项都正）；'
       'λ_j 与下界之差在 j=4,100,1000 为 %s（所以原文「λ_j≥1 ⇔ …」应为「⇐」）；(λ_j-1)/(2/(3ρ_j)) 在 j=100,1000,3000 为 %s'
       % ([float(round(x, 4)) for x in lam], worst_ratio, ['%.2e' % g for g in gap], ['%.3f' % x for x in lam_asym]))

# ---------------------------------------------------------------- 引理 1.3
ok = True
for i in range(1, JM + 1):
    for j in range(0, i):
        ok = ok and (rho[j] / rho[i]).ln() <= -D(i - j) / Dj[i] + D('1e-80')
report('r3-lem13', ok, '引理 1.3：ln(ρ_j/ρ_i)<=-(i-j)/D_i 对 0<=j<i<=300 成立（110 位）')

# ---------------------------------------------------------------- 引理 1.4
def M_dec(r):
    return (r / (r - 1)) * ((3 * r - 2) / (3 * r + 1)).sqrt()


M1 = M_dec(rho[1])
Ms = [M_dec(rho[j]) for j in range(1, 8)]
dec_ok = all(Ms[s] > Ms[s + 1] for s in range(len(Ms) - 1))
ana_ok = all(4.5 * x * x + 1.5 * x - 2 > 0 for x in [1 + 0.001 * s for s in range(100001)])
# |γ_j(σ_j)|/c_j 的实际值：γ_j(σ)=ĝ_j(σ)/(σ^2+3j)，复数用 Python complex（j<=30 时数值安全）
def ghat(j, y):
    s = y ** (3 * j + 3) / math.factorial(j)
    for l in range(j):
        s += (j - l) * y ** (3 * l + 1) / math.factorial(l)
    return s


gam = []
for j in range(1, 31):
    a = float(rho[j])
    # 复根：y^3-y^2-j=(y-a)(y^2+(a-1)y+a(a-1))
    disc = complex((a - 1) ** 2 - 4 * a * (a - 1))
    sig = (-(a - 1) + disc ** 0.5) / 2
    g = abs(ghat(j, sig) / (sig * sig + 3 * j)) / float(c[j])
    gam.append(g)
report('r3-lem14', abs(M1 - D('2.0978')) < D('0.0001') and M1 < D('2.1') and dec_ok and ana_ok,
       '引理 1.4：M(ρ_1)=%s<2.1；M(ρ_1..ρ_7)=%s 递减（4.5ρ^2+1.5ρ-2>0 在 ρ∈[1,101] 抽样）；M(ρ_j)<1.5 要到 j>=5（M(ρ_4)=M(2)=%.4f），'
       '所以把 4.2 换成 3 时引理 1.4 的一致界对 j=1..4 不成立。实际的 |γ_j(σ_j)|/c_j 在 j=1,2,3,5,10,30 为 %s（远小于 M(ρ_j)，'
       '所以 4.2 是这条估计的损失，不是真实量的要求）'
       % (str(M1)[:10], ', '.join('%.4f' % float(x) for x in Ms), float(Ms[3]),
          ', '.join('%.4f' % gam[j - 1] for j in (1, 2, 3, 5, 10, 30))))

# ---------------------------------------------------------------- K_i
Kup = {}
Kd = {}
for i in range(1, 321):
    Kup[i], Kd[i] = K_bound(i)
nominal = {}
for i in (1, 10, 40, 100, 300):
    with localcontext() as ctx:
        ctx.prec = 40
        Dn = rho[i] ** 2 + 3 * i
        A = Dn / D('0.26')
        nominal[i] = Dn * (A.ln() + A.ln().ln())
over = [i for i in range(1, 321) if math.ceil(Kup[i]) > 10000]
first_over = over[0] if over else None
ok_le = all(math.ceil(Kup[i]) <= 10000 for i in range(1, 301))
with localcontext() as ctx:
    ctx.prec = 40
    D1 = rho[1] ** 2 + 3
    A1 = D1 / D('0.26')
    ratio_min = min((Kup[i] - D('1e-30')) / Kd[i] for i in range(1, 321))   # K_i/D_i=ln A+ln ln A，i=1 最小
    r09702 = 3 * (D('0.26').exp() - 1) * (1 + D('4.2') * D('0.01')) + D('4.2') * D('0.01')
    Xmax = (1 + (1 - D('0.042')) / (3 * D('1.042'))).ln()
# X(K_i)、E(K_i) 对大量 i 直接算（浮点；K_i 用名义值，余量很大）
okXE = True
worstX, worstE = 0.0, 0.0
for i in list(range(1, 2001)) + [int(10 ** (3 + 0.01 * s)) for s in range(0, 201)]:
    r = rho_f(i)
    Dn = r * r + 3 * i
    A = Dn / 0.26
    K = Dn * (math.log(A) + math.log(math.log(A)))
    X = (K + 1 + r ** 3) * math.exp(-1 - K / Dn)
    E = math.exp(-K / (2 * r))
    worstX, worstE = max(worstX, X), max(worstE, E)
    okXE = okXE and X <= 0.26 * (1 + 1e-12) and E <= 0.01 and K >= 2 * i - 1
report('r3-K', ok_le and first_over is not None and okXE,
       'K_i 严格上界：⌈K_i⌉<=10000 对 1<=i<=300 成立，第一个超过 10000 的是 i=%d（K<=%s）；名义值 K_1=%.4f、K_10=%.3f、K_40=%.3f、'
       'K_100=%.3f、K_300=%.3f（原文注 1.2 写 K_1=23、K_10=240、K_40=1087，是脚本加 1 后取整的值）；'
       'min K_i/D_i=%.5f（在 i=1；原文「K_i≥4.08D_i」在 i=1 差一点不成立，但 E<=0.01 只需 K_i>=2ln100·ρ_i，余量很大）；'
       'A_1=%.5f（原文写 19.8）；对 i<=2000 与 10^3..10^5 的 201 个 i 直接算 X(K_i)<=0.26（最大 %.6f）、E(K_i)<=0.01（最大 %.2e）、K_i>=2i-1（X 在 k>=2i-1 上递减）；'
       '3(e^0.26-1)(1.042)+0.042=%s；在 E<=0.01 下 X 的最大可取值 %s'
       % (first_over, str(Kup[first_over])[:9] if first_over else '-', nominal[1], nominal[10], nominal[40], nominal[100], nominal[300],
          ratio_min, A1, worstX, worstE, str(r09702)[:8], str(Xmax)[:7]))

# ---------------------------------------------------------------- 渐近
asym = []
for e in (3, 6, 9, 12, 15):
    i = 10 ** e
    r = rho_f(i)
    Dn = r * r + 3 * i
    A = Dn / 0.26
    K = Dn * (math.log(A) + math.log(math.log(A)))
    asym.append((e, K / (3 * i) - math.log(i) - math.log(math.log(i))))
target = math.log(3 / 0.26)
report('r3-asym', abs(asym[-1][1] - target) < 0.2 and all(asym[s][1] > asym[s + 1][1] for s in range(len(asym) - 1)),
       'K_i/(3i)-ln i-ln ln i 在 i=10^3,10^6,10^9,10^12,10^15 为 %s，单调降向 ln(3/0.26)=%.4f（o(1) 项约 2.45/ln i，收敛很慢）'
       % (', '.join('%.4f' % v for _, v in asym), target))

# ---------------------------------------------------------------- 注 1.1：s14-b9 的不等式能给出的门槛
def thr_generic(i, lnratio_fn):
    """最小 k 使 Σ_n [ratio_j·(ρ_j/ρ_i)^k·(k+1+u_i)^n/n!]·(1+4.2E)+4.2E < 1（与定理 1 同样的复根处理），二分。"""
    r_i = rho_f(i)
    Dn = r_i * r_i + 3 * i
    u_i = r_i ** 3
    rj = [rho_f(j) for j in range(i)]
    lr = [lnratio_fn(j) for j in range(i)]

    def total(k):
        E = math.exp(-k / (2 * r_i))
        s = 0.0
        for j in range(i):
            n = i - j
            lt = lr[j] + k * math.log(rj[j] / r_i) + n * math.log(k + 1 + u_i) - math.lgamma(n + 1)
            if lt > 700:
                return float('inf')
            s += math.exp(lt)
        return s * (1 + 4.2 * E) + 4.2 * E

    lo, hi = 1, 200
    while total(hi) >= 1:
        hi *= 2
    while hi - lo > 1:
        m = (lo + hi) // 2
        if total(m) < 1:
            hi = m
        else:
            lo = m
    return hi


def make_s14(i):
    r_i = rho_f(i)
    u_i = r_i ** 3
    lnci_low = (i + 1) * math.log(u_i) - math.lgamma(i + 1) - math.log(r_i * r_i + 3 * i)

    def fn(j):
        if j == 0:
            return 0.0 - lnci_low
        r = rho_f(j)
        uj = r ** 3
        return math.log(uj + j * r) + uj - math.log(3 * j) - lnci_low
    return fn


def make_lem(i):
    r_i = rho_f(i)
    lnPi = i * math.log(r_i ** 3) - math.lgamma(i + 1)

    def fn(j):
        r = rho_f(j)
        lnPj = j * math.log(r ** 3) - math.lgamma(j + 1) if j else 0.0
        return math.log(3) + lnPj - lnPi        # 引理 1.1：c_j/c_i<=3P_j/P_i（不再用 P_j/P_i<=e^{-(i-j)}）
    return fn


rows = []
for i in (10, 100, 300, 1000, 3000):
    k_s14 = thr_generic(i, make_s14(i))
    k_lem = thr_generic(i, make_lem(i))
    r_i = rho_f(i)
    Dn = r_i * r_i + 3 * i
    A = Dn / 0.26
    K = Dn * (math.log(A) + math.log(math.log(A)))
    rows.append((i, k_s14, k_lem, K, k_s14 / k_lem, k_s14 / i ** (4 / 3)))
report('r3-s14', rows[-1][4] > rows[0][4],
       '（信息性）按 s14-b9 §4 第 2、3 条估计 c_j/c_i（c_j<=(u_j+jρ_j)e^{u_j}/(3j)，c_i>=u_i^{i+1}/(i!D_i)），'
       '其余与定理 1 的逐项界相同，二分得到最小可认证的 k，记 K^{s14}_i；同法用引理 1.1 的 3P_j/P_i 得 K^{lem}_i：%s。'
       'K^{s14}/K^{lem} 随 i 增大，与注 1.1 的「只得到 O(i^{4/3})」一致（i^{1/3}/2 要到很大的 i 才压过 ln i）'
       % '; '.join('i=%d: K^s14=%d, K^lem=%d, K_i=%.0f, K^s14/K^lem=%.2f, K^s14/i^(4/3)=%.2f' % r for r in rows))

print('# elapsed %.1fs' % (time.time() - t00))
print('SUMMARY s17-r3 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
