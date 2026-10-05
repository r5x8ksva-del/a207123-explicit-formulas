# -*- coding: utf-8 -*-
"""s5：复核 C4-16（Stirling 类比）与 c4.md §3.5 中的两条附带恒等式。
  S(k,k-d) = Σ_j <<d,j>> C(k+d-1-j, 2d)          （GKP 6.43；对 0<=k 全成立）
  S(k,k-d) = Σ_j S2(d+j, j) C(k, d+j)             （S2 = 每块 >=2 元的划分数）
  Σ_k S(k,k-d) x^k = x^{d+1} Σ_j <<d,j>> x^j / (1-x)^{2d+1}
第二类 Stirling 数用独立的集合划分递推；S2 用独立递推 S2(n,j) = j S2(n-1,j) + (n-1) S2(n-2,j-1)。
"""
import sys, time
from math import comb
try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
KM, DM = 150, 14
S = [[0] * (KM + 2) for _ in range(KM + 1)]
S[0][0] = 1
for n in range(1, KM + 1):
    for j in range(1, n + 1):
        S[n][j] = j * S[n - 1][j] + S[n - 1][j - 1]
E = [[0] * (DM + 2) for _ in range(DM + 1)]
E[0][0] = 1
for n in range(1, DM + 1):
    for j in range(0, n):
        E[n][j] = (j + 1) * E[n - 1][j] + ((2 * n - 1 - j) * E[n - 1][j - 1] if j >= 1 else 0)
S2 = [[0] * (2 * DM + 2) for _ in range(2 * DM + 2)]
S2[0][0] = 1
for n in range(1, 2 * DM + 2):
    for j in range(1, n + 1):
        S2[n][j] = j * S2[n - 1][j] + ((n - 1) * S2[n - 2][j - 1] if n >= 2 else 0)


def Sv(k, i):
    return S[k][i] if 0 <= i <= k else 0


ok1 = all(Sv(k, k - d) == (sum(E[d][j] * comb(k + d - 1 - j, 2 * d) for j in range(d)) if d > 0 else 1)
          for d in range(0, DM + 1) for k in range(0, KM + 1) if not (d == 0 and k < 0))
ok2 = all(Sv(k, k - d) == sum(S2[d + j][j] * comb(k, d + j) for j in range(0, d + 1))
          for d in range(0, DM + 1) for k in range(0, KM + 1))
ok3 = True
for d in range(1, DM + 1):
    ser = [Sv(k, k - d) for k in range(KM + 1)]
    for _ in range(2 * d + 1):
        ser = [ser[i] - (ser[i - 1] if i > 0 else 0) for i in range(KM + 1)]
    want = [0] * (KM + 1)
    for j in range(d):
        want[d + 1 + j] = E[d][j]
    if ser != want:
        ok3 = False
print(('OK  ' if ok1 else 'BAD ') + 'C4-16: S(k,k-d)=Σ<<d,j>>C(k+d-1-j,2d)，0<=d<=%d, 0<=k<=%d（含 k<d 的平凡 0）' % (DM, KM))
print(('OK  ' if ok2 else 'BAD ') + '§3.5: S(k,k-d)=Σ_j S2(d+j,j)C(k,d+j)，0<=d<=%d, 0<=k<=%d' % (DM, KM))
print(('OK  ' if ok3 else 'BAD ') + '§3.5: (1-x)^{2d+1}Σ_k S(k,k-d)x^k = x^{d+1}Σ_j<<d,j>>x^j（系数非负），1<=d<=%d' % DM)
print('SUMMARY s5 ok=%d bad=%d runtime=%.1fs' % (ok1 + ok2 + ok3, 3 - ok1 - ok2 - ok3, time.time() - t0))
