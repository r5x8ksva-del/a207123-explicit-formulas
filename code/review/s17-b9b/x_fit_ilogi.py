# -*- coding: utf-8 -*-
"""探索（信息性）：在 300<=i<=1000 上用 τ_i = a i + c i ln i + b + e i^{2/3} 等形式拟合（作者 k<=20000 的经验 τ，i<=579 已可认证），
看 i ln i 项的系数能被数据压到多小。只说明数据的分辨力，不是证明。"""
import json, math, os, sys
import numpy as np
sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
A = json.load(open(os.path.join(ROOT, 'logs', 'tableB_explore_b9_growth_scan20000.json'), encoding='utf-8'))
tau = A['tau_emp']
I = np.arange(300, 1001)
y = np.array([tau[i] for i in I], dtype=float)
def fit(cols, names):
    X = np.column_stack(cols)
    coef, res, rk, sv = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ coef
    print(' + '.join('%s*%.5g' % (n, c) for n, c in zip(names, coef)), '  rms resid %.3f' % math.sqrt(np.mean(r * r)))
    return coef
fit([I, np.ones_like(I, dtype=float)], ['i', '1'])
c1 = fit([I, I * np.log(I), np.ones_like(I, dtype=float)], ['i', 'i ln i', '1'])
c2 = fit([I, I * np.log(I), I ** (2 / 3), np.ones_like(I, dtype=float)], ['i', 'i ln i', 'i^(2/3)', '1'])
xi = 0.10407497693333
fit([I - I / xi + I / xi, np.ones_like(I, dtype=float)], ['i', '1'])
print('alpha* = %.5f' % (1 / xi))
