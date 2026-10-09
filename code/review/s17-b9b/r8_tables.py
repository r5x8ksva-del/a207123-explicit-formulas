# -*- coding: utf-8 -*-
"""s17-b9b r8：notes/18 §4 的表与日志、数据文件逐项对照（不 import 项目代码；作者的 JSON 只作为数据读入）。
  r8-ell    表 1：ℓ_k 与 ℓ_k−ξ*k（作者 scan20000 的 JSON；k<=10000 部分与我的 r2 数据对照）；「1000<=k<=20000 时 ∈[3.47,5.58]」
  r8-tau    表 2 与 §4 的文字：τ_i、τ_i/i、τ_i−α*i、窗口平均差、差值计数 413/579、τ_i/(i ln i)；
            作者 k<=20000 的经验 τ 与我 k<=10000 的自写 T1.7 在 i<=1000 上对照；20000 的扫描其实已能认证到哪个 i
  r8-rate   表 4：用自写 T1.7 重算 ln h_{k,ξk}（k=1250、2500、5000），与作者日志的 emp 对照；β(s_1) 与比值 diff·k^{1/3}·3^{2/3}/β(s_1)；
            k 加倍时 diff 之比的实际范围
用法：py -3.14 code/review/s17-b9b/r8_tables.py
"""
import json
import math
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import K_bound, t17_rows, lnbig  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


XI = 0.10407497693333   # r5-xi
ALPHA = 1 / XI
t00 = time.time()
A = json.load(open(os.path.join(ROOT, 'logs', 'tableB_explore_b9_growth_scan20000.json'), encoding='utf-8'))
mine = json.load(open(os.path.join(ROOT, 'logs', 'review_s17-b9b_r2_tau_data.json'), encoding='utf-8'))
ellA = {int(k): v for k, v in A['ell'].items()}
ellM = {int(k): v for k, v in mine['ell'].items()}
tauA = A['tau_emp']          # 下标 i（tau_emp[0] 对应 i=0）
tauM = [None] + mine['tau_T']

# ---------------------------------------------------------------- 表 1
T1k = [100, 300, 600, 1000, 2000, 3000, 5000, 7000, 10000, 15000, 20000]
T1v = [13, 35, 66, 108, 213, 317, 525, 734, 1046, 1566, 2085]
T1d = [2.59, 3.78, 3.56, 3.93, 4.85, 4.78, 4.63, 5.48, 5.25, 4.88, 3.50]
ok1 = all(ellA[k] == v for k, v in zip(T1k, T1v)) and all(abs(ellA[k] - XI * k - dv) < 0.006 for k, dv in zip(T1k, T1d))
okm = all(ellM[k] == ellA[k] for k in range(0, 10001))
devA = [ellA[k] - XI * k for k in range(1000, 20001)]
devM = [ellM[k] - XI * k for k in range(1000, 10001)]
report('r8-ell', ok1 and okm and abs(min(devA) - 3.47) < 0.006 and abs(max(devA) - 5.58) < 0.006,
       '表 1 的 ℓ_k 与 ℓ_k−ξ*k 全部与作者 JSON 一致；k<=10000 的 ℓ_k 与我自写 T1.7 的结果逐个相同；'
       '1000<=k<=20000 时 ℓ_k−ξ*k∈[%.2f,%.2f]（原文 [3.47,5.58]），1000<=k<=10000 时 ∈[%.2f,%.2f]；'
       'k=15000..20000 段的最小值 %.2f（在 k=%d），比前面明显下降'
       % (min(devA), max(devA), min(devM), max(devM), min(devA[14000:]),
          1000 + 14000 + devA[14000:].index(min(devA[14000:]))))

# ---------------------------------------------------------------- 表 2
T2i = [10, 40, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
T2v = [77, 357, 927, 1883, 2841, 3801, 4761, 5722, 6682, 7644, 8605, 9566]
T2r = [7.70, 8.93, 9.27, 9.42, 9.47, 9.50, 9.52, 9.54, 9.55, 9.56, 9.56, 9.57]
T2d = [-19.1, -27.3, -33.8, -38.7, -41.5, -42.4, -43.2, -43.1, -43.9, -42.8, -42.6, -42.5]
ok2 = all(tauA[i] == v for i, v in zip(T2i, T2v)) and all(abs(tauA[i] - ALPHA * i - dv) < 0.051 for i, dv in zip(T2i, T2d))
ratio_bad = [(i, tauA[i] / i, r) for i, r in zip(T2i, T2r) if abs(tauA[i] / i - r) > 0.0051]
okAM = all(tauA[i] == tauM[i] for i in range(1, 1001))
diffs = [tauA[i + 1] - tauA[i] for i in range(8, 1000)]
c9, c10 = diffs.count(9), diffs.count(10)
win = [(tauA[a + 100] - tauA[a]) / 100 for a in range(100, 1000, 100)]
dd = [tauA[i] - ALPHA * i for i in range(400, 1001)]
Kc = 0
for i in range(300, 700):
    if math.ceil(K_bound(i)[0]) <= 20000:
        Kc = i
report('r8-tau', ok2 and okAM and (c9, c10) == (413, 579) and len(ratio_bad) <= 1,
       '表 2 的 τ_i 与 τ_i−α*i 与作者 JSON 一致（τ_i/i 的舍入差异：%s）；作者 k<=20000 的经验 τ_i 与我 k<=10000 的自写 T1.7 在 1<=i<=1000 上逐个相同'
       '（所以 i<=1000 时 10000<k<=20000 之间没有新的非正系数）；8<=i<1000 的差值 9 出现 %d 次、10 出现 %d 次（原文 413、579）；'
       '窗口平均（100–200 到 900–1000）%s；400<=i<=1000 时 τ_i−α*i∈[%.2f,%.2f]；τ_100/(100 ln100)=%.3f，τ_1000/(1000 ln1000)=%.3f；'
       '⌈K_i⌉<=20000 对 i<=%d 成立，所以 k<=20000 的扫描配合定理 1 其实已能认证 τ_1..τ_%d（原文只说「301<=i<=1000 只查了 k<=20000」）'
       % (ratio_bad, c9, c10, ['%.2f' % w for w in win], min(dd), max(dd), tauA[100] / (100 * math.log(100)),
          tauA[1000] / (1000 * math.log(1000)), Kc, Kc))

# ---------------------------------------------------------------- 表 4
log = open(os.path.join(ROOT, 'logs', 'tableB_explore_b9_growth_scan20000.log'), encoding='utf-8').read()
log10 = open(os.path.join(ROOT, 'logs', 'tableB_explore_b9_growth_scan.log'), encoding='utf-8').read()
pat = re.compile(r'k=\s*(\d+) i=\s*(\d+) xi=([0-9.]+)\s+emp=([-0-9.]+)\s+model=([-0-9.]+)\s+diff=([-+0-9.]+)')
rowsA = {}
for txt in (log10, log):
    for m in pat.finditer(txt):
        k, i = int(m.group(1)), int(m.group(2))
        rowsA[(k, i)] = (float(m.group(3)), float(m.group(4)), float(m.group(5)), float(m.group(6)))


def psi(t):
    return t - 1 - math.log(t)


def g(t):
    return (1 - t) / (3 * psi(t)) - t / (1 - t)


TS = 0.07548688811224


def s1(xi):
    lo, hi = math.log(1e-300), math.log(TS)
    for _ in range(400):
        m = (lo + hi) / 2
        if g(math.exp(m)) < xi:
            lo = m
        else:
            hi = m
    return math.exp((lo + hi) / 2)


def beta(t):
    return math.log(1 / t) / psi(t) ** (2 / 3)


# 自写 T1.7 重算 ln h_{k,i}
need = {}
for (k, i) in rowsA:
    if k <= 5000:
        need.setdefault(k, []).append(i)
lnh = {}
for k, row in t17_rows(5000, 510):
    if k in need:
        for i in need[k]:
            lnh[(k, i)] = lnbig(row[i])
emp_ok = True
for (k, i), v in lnh.items():
    emp_me = (v - (k / 3) * math.log(k / (3 * math.e))) / k
    emp_ok = emp_ok and abs(emp_me - rowsA[(k, i)][1]) < 6e-6
TAB4 = {2500: [1.031, 1.017, 1.009, 1.003, 1.001, 0.999], 20000: [1.018, 1.012, 1.009, 1.006, 1.005, 1.003]}
xis = [0.02, 0.04, 0.06, 0.08, 0.09, 0.10]
ratios = {}
for k in (1250, 2500, 5000, 10000, 20000):
    rr = []
    for xi in xis:
        i = int(xi * k)
        if (k, i) not in rowsA:
            rr.append(None)
            continue
        x, emp, model, diff = rowsA[(k, i)]
        s = s1(i / k)
        rr.append(diff * k ** (1 / 3) * 3 ** (2 / 3) / beta(s))
    ratios[k] = rr
ok4 = all(abs(a - b) < 0.0015 for k in (2500, 20000) for a, b in zip(ratios[k], TAB4[k]))
dbl = []
for k0, k1 in ((1250, 2500), (2500, 5000), (5000, 10000), (10000, 20000)):
    for xi in xis:
        a = rowsA.get((k0, int(xi * k0)))
        b = rowsA.get((k1, int(xi * k1)))
        if a and b:
            dbl.append(b[3] / a[3])
report('r8-rate', emp_ok and ok4,
       '表 4：我用自写 T1.7 重算 k=1250、2500、5000 的 ln h_{k,ξk}，与作者日志的 emp 一致（<6e-6）；'
       '比值 diff·k^{1/3}·3^{2/3}/β(s_1) 在 k=2500 为 %s、k=20000 为 %s（与表 4 一致）；k=1250、5000、10000 为 %s、%s、%s。'
       'k 加倍时 diff 之比的实际范围是 [%.4f,%.4f]（%d 对；原文写 0.795–0.798，2^{-1/3}=0.7937）'
       % (['%.3f' % r for r in ratios[2500]], ['%.3f' % r for r in ratios[20000]],
          ['%.3f' % r for r in ratios[1250]], ['%.3f' % r for r in ratios[5000]], ['%.3f' % r for r in ratios[10000]],
          min(dbl), max(dbl), len(dbl)))
print('# elapsed %.1fs' % (time.time() - t00))
print('SUMMARY s17-r8 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
