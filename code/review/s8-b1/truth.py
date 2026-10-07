# -*- coding: utf-8 -*-
"""s8-b1：从 code/core.py 取 N(k,q) 的真值（不导入 code/tableB 下任何脚本）。"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402


def N_table_from_U(K):
    """N[k][q]（0<=k,q<=K）：U 由 core.U_fast_table（按定义的高度 DP）给出，再用 core.N_from_U 容斥。"""
    T = core.U_fast_table(K, K)
    return [[core.N_from_U(T, k, q) for q in range(K + 1)] for k in range(K + 1)]


def N_brute_rows(kmax):
    """按定义 DFS（core.N_brute）：rows[k][q]。"""
    rows = {}
    for k in range(0, kmax + 1):
        d = core.N_brute(k)
        rows[k] = [d.get(q, 0) for q in range(kmax + 2)]
    return rows


def nrow(N, k):
    """n_k(z) = Σ_{q>=1} N(k,q) z^{q-1} 的系数表（低次在前，去掉末尾的 0）。"""
    r = [N[k][q] for q in range(1, len(N[k]))]
    while r and r[-1] == 0:
        r.pop()
    return r
