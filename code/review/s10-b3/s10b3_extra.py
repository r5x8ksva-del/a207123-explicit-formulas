# -*- coding: utf-8 -*-
"""s10-b3 检查 4：针对笔记个别说法的定点核对。

X1 笔记 §5 说「对照组恰在 max(k0,0)+c-d>=0 时可解」。按笔记 §1 的定义（s0 存在即可），
   (0,1) 的条件应是 max(k0,0)+c>=0（与 d 无关）。例：m=1,c=0,d=3,k0=0：
   s 自由（s>=-d）=> 可解；人为限定 s>=0 => 不可解。
X2 (1,0)：m=1,c=0,d=2,k0=0：s0=-2 可解（A=x^{c-d}(1-x)^{d+1}G_m）；s0=0 不可解。
X3 推广建议的佐证：U^up（以上升结尾的部分，母函数 (W_m-1)/P_m）在 ξ 处也有极点
   （W_m(xi)-1=xi^5≠0，精确），所以纤维论证对它逐字成立。截断方程组：m=1,2,3，2<=α+β<=5 的全部形状，
   c,d∈[-2,2]，k0∈{0,5}：除 m=1 的 (2,1) 外全部无解；m=1 的 (2,1) 在 c=0,d=-1 可解（G^up_1=x^{-1}u/(1-u)）。
X4 笔记 §5 说 α+β=1、α<0（如 (-1,2)）时任何数列都有表示：U 的 (-1,2) 表示在 c=d=0,k0=0 时截断可解。
"""
import sys
from s10b3_common import U_dp, U_up_dp, W_poly, keval_intpoly, kpow, ksub, KONE, XI, kiszero
from s10b3_linsys import build_system, decide

res = []


def report(tag, ok, info=""):
    res.append((tag, ok))
    print(("PASS " if ok else "FAIL ") + tag + ("  " + info if info else ""))


Kmax = 90
U = {m: U_dp(m, Kmax) for m in (1, 2, 3)}
Uup = {m: U_up_dp(m, Kmax) for m in (1, 2, 3)}

# X1
rows, rhs, sl = build_system(0, 1, 0, 3, 0, None, lambda k: U[1][k])
v_free, _ = decide(rows, rhs)
# 人为 s>=0：去掉 s<0 的列
keep = [i for i, s in enumerate(sl) if s >= 0]
rows0 = [[r[i] for i in keep] for r in rows]
v_s0, _ = decide(rows0, rhs)
report("X1 (0,1), m=1,c=0,d=3,k0=0: s free -> %s; s>=0 forced -> %s" % (v_free, v_s0),
       v_free == "sol" and v_s0.startswith("nosol"))

# X2
rows, rhs, sl = build_system(1, 0, 0, 2, 0, -2, lambda k: U[1][k])
v_m2, _ = decide(rows, rhs)
rows, rhs, sl = build_system(1, 0, 0, 2, 0, 0, lambda k: U[1][k])
v_0, _ = decide(rows, rhs)
report("X2 (1,0), m=1,c=0,d=2,k0=0: s0=-2 -> %s; s0=0 -> %s" % (v_m2, v_0),
       v_m2 == "sol" and v_0.startswith("nosol"))

# X3
ok = True
for m in range(1, 21):
    val = ksub(keval_intpoly(W_poly(m), XI), KONE)
    if val != kpow(XI, 5) or kiszero(val):
        ok = False
nsys = 0
solv = []
for n in range(2, 6):
    for al in range(0, n + 1):
        be = n - al
        for m in (1, 2, 3):
            for c in range(-2, 3):
                for d in range(-2, 3):
                    for k0 in (0, 5):
                        for s0 in ((-3, 0) if be == 0 else (None,)):
                            sysd = build_system(al, be, c, d, k0, s0, lambda k, m=m: Uup[m][k])
                            nsys += 1
                            if sysd is None:
                                continue
                            rows, rhs, sl = sysd
                            v, _ = decide(rows, rhs)
                            if v == "sol":
                                solv.append((al, be, m, c, d, k0))
bad = [t for t in solv if not (t[0] == 2 and t[1] == 1 and t[2] == 1)]
has_m1 = any(t[:2] == (2, 1) and t[2] == 1 and t[3] == 0 and t[4] == -1 for t in solv)
print("  U^up solvable systems: %s" % solv)
report("X3 U^up: W_m(xi)-1=xi^5 (m<=20); %d systems, solvable only for (2,1) at m=1 (incl. c=0,d=-1)" % nsys,
       ok and not bad and has_m1)

# X4
rows, rhs, sl = build_system(-1, 2, 0, 0, 0, None, lambda k: U[2][k])
v, _ = decide(rows, rhs)
report("X4 (-1,2), m=2, c=d=k0=0 truncated system solvable: %s" % v, v == "sol")

nf = sum(1 for _, o in res if not o)
print("SUMMARY extra: %d PASS, %d FAIL" % (len(res) - nf, nf))
sys.exit(1 if nf else 0)
