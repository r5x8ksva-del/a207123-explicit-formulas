# -*- coding: utf-8 -*-
"""T4.2(1) 引用的 S(k,k-d)=Σ_j S_2(d+j,j)C(k,d+j)：S_2 必须是「每块至少 2 个元素」的相伴 Stirling 数（final-audit math-c4c5）。"""
from math import comb
from alib import say, check, write_log

NM = 70
S = [[0] * (NM + 1) for _ in range(NM + 1)]
S[0][0] = 1
for n in range(1, NM + 1):
    for k in range(1, n + 1):
        S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
# 相伴 Stirling：S2a(n,k)=k S2a(n-1,k)+(n-1) S2a(n-2,k-1)
A = [[0] * (NM + 1) for _ in range(NM + 1)]
A[0][0] = 1
for n in range(1, NM + 1):
    for k in range(1, n + 1):
        A[n][k] = k * A[n - 1][k] + ((n - 1) * A[n - 2][k - 1] if n >= 2 else 0)
ok_assoc = all(S[k][k - d] == sum(A[d + j][j] * comb(k, d + j) for j in range(0, k - d + 1)) for d in range(0, 9) for k in range(d, 60))
ok_plain = all(S[k][k - d] == sum(S[d + j][j] * comb(k, d + j) for j in range(0, k - d + 1)) for d in range(1, 9) for k in range(d, 60))
ex = (S[4][3], sum(S[1 + j][j] * comb(4, 1 + j) for j in range(0, 4)))
check('T4.2.1-S2-meaning', ok_assoc and not ok_plain,
      'S(k,k-d)=Σ_j S_2(d+j,j)C(k,d+j) 对相伴 Stirling 数（块大小>=2）成立（d<=8,k<60）；若把 S_2 读成第二类 Stirling 数 S 则不成立，例如 k=4,d=1：S(4,3)=%d，而 Σ_j S(1+j,j)C(4,1+j)=%d' % ex)
write_log('final_audit_math-c4c5_s9.log')
