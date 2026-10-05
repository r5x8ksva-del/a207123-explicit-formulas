# -*- coding: utf-8 -*-
"""r-c3a 探针：(x,t)=(21/100,-1/20) 处 I-S 的第 17 位分歧。逐个打印中间量，与作者 explore6 日志对照：
  作者（170 位）：I-S = 3.814017765530373708055498445061E-62，Γ(-λ) = 3.532084579462180165762298574105E-129，
                  K = 5.422072398993107642807937863904E-129。
"""
import os
import sys
from fractions import Fraction as Fr
from decimal import Decimal as D, getcontext

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import importlib.util
spec = importlib.util.spec_from_file_location('r2', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'r2_numeric.py'))

# 只复用 r2 里的函数定义（不执行其检查部分）：手工 exec 函数段
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'r2_numeric.py'), encoding='utf-8').read()
cut = src.index('# ============================================================ 1.')
ns = {}
exec(compile(src[:cut], 'r2_funcs', 'exec'), ns)

x, t = Fr(21, 100), Fr(-1, 20)
for prec in (110, 150):
    getcontext().prec = prec
    PI = ns['agm_pi']()
    xd, td = ns['dec'](x), ns['dec'](t)
    lamd = (1 - xd) / xd ** 3
    a = -td / xd ** 3
    I1, e1 = ns['I_quad'](x, t, True)
    S1 = ns['S_dec'](x, t, True)
    g = ns['gamma_neg_reflect'](lamd, PI)
    r = ns['ratio_formula'](x)
    pref = a.exp() * (lamd * a.ln()).exp() / xd ** 3
    # 注意：不要用 '%E' % Decimal —— 那会先转成 float，只剩 ~17 位有效（作者 explore6 日志正是这样打印的）
    print('prec', prec)
    print('  I       =', str(+I1)[:75])
    print('  S       =', str(+S1)[:75])
    print('  I-S     =', str(I1 - S1)[:50])
    print('  Gamma   =', str(g)[:50])
    print('  K       =', str(g * r)[:50], '  K/Gamma =', str(r)[:45])
    print('  pref    =', str(pref)[:50])
    print('  pred    =', str(pref * g * r)[:50])
    print('  float(I-S) printed with %.30E (the author-log style):', '%.30E' % (I1 - S1))
    print('  quad err est', e1)
print('author explore6 log: I-S = 3.814017765530373708055498445061E-62 (float artifact beyond ~17 digits)')
