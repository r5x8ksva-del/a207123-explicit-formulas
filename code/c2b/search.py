# -*- coding: utf-8 -*-
"""单和形状搜索引擎（精确有理数增量消元）。

形状：V(k) = sum_{s>=0} A_s * C(k + c - g*s, d + e*s)，k = 0..K；C 采用组合约定（上指标<0 或下指标<0 或下>上 时为 0，
与 core.binom 相同）。对固定 (c,g,d,e) 判定：存在有理数 A_s 使全部 K+1 个方程成立？
返回 (consistent, n_checks, n_free, first_fail_k)：
  n_checks = 被已确定未知数完全决定、且被满足的「多余方程」个数（真正的检验次数）；
  n_free   = 出现过但最终未被确定的未知数个数（>0 表示欠定）。
"""
from fractions import Fraction
from math import comb


def binom(n, r):
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


def columns(K, c, g, d, e, smax_cap=None):
    """所有在 k<=K 时可能非零的 s。"""
    cap = smax_cap if smax_cap is not None else 3 * K + 10
    out = []
    for s in range(0, cap + 1):
        r = d + e * s
        if r < 0:
            if e >= 0:
                continue   # r 随 s 不减，仍可能后来变非负
            else:
                break      # e<0 时 r 只会更小
        # 最小非零 k：k + c - g*s >= r  =>  k >= r + g*s - c
        kmin = max(0, r + g * s - c)
        if kmin <= K:
            out.append(s)
        else:
            if g + e > 0:
                break      # kmin 随 s 单增，后面都超出
    return out


def test_shape(V, c, g, d, e, smax_cap=None):
    K = len(V) - 1
    cols = columns(K, c, g, d, e, smax_cap)
    # 增量约化行阶梯：pivots: col -> (rowdict, rhs)，rowdict 在主元列为 1，在其他主元列为 0
    pivots = {}
    seen = set()
    n_checks = 0
    for k in range(K + 1):
        row = {}
        for s in cols:
            v = binom(k + c - g * s, d + e * s)
            if v:
                row[s] = Fraction(v)
        rhs = Fraction(V[k])
        # 约化
        for pc in [p for p in row if p in pivots]:
            coef = row.get(pc)
            if not coef:
                continue
            prow, prhs = pivots[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - coef * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= coef * prhs
        seen.update(row.keys())
        nz = [cc for cc, vv in row.items() if vv]
        if not nz:
            if rhs != 0:
                return (False, n_checks, None, k)
            n_checks += 1
            continue
        # 新主元
        pc = min(nz)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items() if vv}
        prhs = rhs * inv
        # 从已有主元行消去 pc
        for qc in list(pivots.keys()):
            qrow, qrhs = pivots[qc]
            coef = qrow.get(pc)
            if coef:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - coef * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                qrhs -= coef * prhs
                pivots[qc] = (qrow, qrhs)
        pivots[pc] = (prow, prhs)
    n_free = len(set(cols) & seen) - len(pivots)
    return (True, n_checks, n_free, None)


def solution(V, c, g, d, e, smax_cap=None):
    """若唯一可解，返回 {s: A_s}（只含主元列）；否则返回 None。"""
    K = len(V) - 1
    cols = columns(K, c, g, d, e, smax_cap)
    pivots = {}
    for k in range(K + 1):
        row = {}
        for s in cols:
            v = binom(k + c - g * s, d + e * s)
            if v:
                row[s] = Fraction(v)
        rhs = Fraction(V[k])
        for pc in [p for p in row if p in pivots]:
            coef = row.get(pc)
            if not coef:
                continue
            prow, prhs = pivots[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - coef * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= coef * prhs
        nz = [cc for cc, vv in row.items() if vv]
        if not nz:
            if rhs != 0:
                return None
            continue
        pc = min(nz)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items() if vv}
        prhs = rhs * inv
        for qc in list(pivots.keys()):
            qrow, qrhs = pivots[qc]
            coef = qrow.get(pc)
            if coef:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - coef * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                qrhs -= coef * prhs
                pivots[qc] = (qrow, qrhs)
        pivots[pc] = (prow, prhs)
    sol = {}
    for pc, (prow, prhs) in pivots.items():
        if len(prow) != 1:
            return None   # 欠定
        sol[pc] = prhs
    return sol
