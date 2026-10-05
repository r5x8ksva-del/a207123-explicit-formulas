import sys, time
CODE = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code'
sys.path.insert(0, CODE + r'\c2b')
sys.path.insert(0, CODE)
import blocks
from core import U_fast_table


def check(K, m, bug=False):
    sys.setrecursionlimit(10000)
    ones = [1] * (m + 1); rng = range(m + 1)
    stats = {'nodes': 0, 'parse1': 0, 'legal': 0, 'mismatch': 0}

    def rec(s, legal, V0, V1, V2):
        n = len(s)
        if n >= 1:
            stats['nodes'] += 1
            if V0[m] == 1: stats['parse1'] += 1
            if legal: stats['legal'] += 1
            if V0[m] != (1 if legal else 0): stats['mismatch'] += 1
        if n == K: return
        for x in rng:
            lg = legal and (n < 2 or blocks.good3(x, s[0], s[1]))
            if bug and n >= 2 and x == 0 and s[0] == 1 and s[1] == 0: lg = legal  # inject: treat 010 as legal
            newV = [0] * (m + 1)
            tcase = n >= 2 and x < s[0] == s[1]
            ecase = n == 1 and x < s[0]
            for top in rng:
                t = V0[x] if x <= top else 0
                if tcase and s[0] <= top: t += V2[s[0]]
                if ecase and s[0] <= top: t += 1
                newV[top] = t
            rec((x,) + s, lg, newV, V0, V1)
    rec((), True, ones, None, None)
    return stats


T = U_fast_table(10, 4)
for m in range(1, 5):
    t0 = time.time(); st = check(10, m); dt = time.time() - t0
    print(m, st, 'sumU=', sum(T[k][m] for k in range(1, 11)), '%.2fs' % dt, flush=True)
print('with injected bug m=2:', check(8, 2, bug=True), flush=True)
