# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 4b：两项 u 型的后续检查。

mode = k60  ：把 k<=30 上「相容」（检验数 0）的形状对放到 k<=60 的数据上重测；
mode = full ：对 E m=5,6、U m=4,5,6 的全部形状对（k<=30）独立重跑，统计相容对及其检验数
             （作者 explore7 只报告了「相容且检验数>=5」的对数 = 0）。
mode = k0   ：E m=3、U m=2 的全部形状对，只要求 k>=k0（k0=1,2）成立。
"""
import sys, os, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import r4_twoterm as R4  # noqa

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

TAB60 = {}


def init60():
    for m in range(0, 7):
        cp, ad = R4.split_dp(60, m)
        TAB60[('E', m)] = ad
        TAB60[('U', m)] = [cp[k] + ad[k] for k in range(61)]
    R4.init()


def work_k60(args):
    name, m, c1, d1, c2, d2 = args
    ok30, ch30 = R4.solve_two(R4.TAB[(name, m)], c1, d1, c2, d2, 0)
    if not ok30:
        return (name, m, c1, d1, c2, d2, False, ch30, None, None)
    ok60, ch60 = R4.solve_two(TAB60[(name, m)], c1, d1, c2, d2, 0)
    return (name, m, c1, d1, c2, d2, True, ch30, ok60, ch60)


def work_full(args):
    name, m, c1, d1, c2, d2, k0 = args
    ok, ch = R4.solve_two(R4.TAB[(name, m)], c1, d1, c2, d2, k0)
    return (name, m, c1, d1, c2, d2, k0, ok, ch)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'k60'
    T0 = time.time()
    if mode == 'k60':
        jobs = []
        for name in ('E', 'U'):
            for m in (5, 6):
                jobs += [(name, m) + p for p in R4.pairs_for(m, 27)]
        print('jobs %d' % len(jobs), flush=True)
        with Pool(4, initializer=init60) as pool:
            res = pool.map(work_k60, jobs, chunksize=100)
        summ = {}
        for r in res:
            name, m, c1, d1, c2, d2, ok30, ch30, ok60, ch60 = r
            d = summ.setdefault((name, m), {'cons30': 0, 'cons60': 0, 'ex60': [], 'ch30': set()})
            if ok30:
                d['cons30'] += 1
                d['ch30'].add(ch30)
                if ok60:
                    d['cons60'] += 1
                    if len(d['ex60']) < 10:
                        d['ex60'].append((c1, d1, c2, d2, ch60))
        for key in sorted(summ):
            d = summ[key]
            print('%s m=%d: k<=30 相容 %d 对（检验数集合 %s）；其中在 k<=60 上仍相容 %d 对 %s' %
                  (key[0], key[1], d['cons30'], sorted(d['ch30']), d['cons60'], d['ex60']), flush=True)
    else:
        jobs = []
        if mode == 'full':
            for name, ms in (('E', (5, 6)), ('U', (4, 5, 6))):
                for m in ms:
                    jobs += [(name, m) + p + (0,) for p in R4.pairs_for(m)]
        elif mode == 'small':
            for name, ms in (('E', (3, 4)), ('U', (2, 3))):
                for m in ms:
                    jobs += [(name, m) + p + (0,) for p in R4.pairs_for(m)]
        else:
            for name, m in (('E', 3), ('U', 2)):
                for k0 in (1, 2):
                    jobs += [(name, m) + p + (k0,) for p in R4.pairs_for(m)]
        print('jobs %d' % len(jobs), flush=True)
        with Pool(4, initializer=R4.init) as pool:
            res = pool.map(work_full, jobs, chunksize=300)
        summ = {}
        for (name, m, c1, d1, c2, d2, k0, ok, ch) in res:
            d = summ.setdefault((name, m, k0), {'tested': 0, 'cons': 0, 'ge5': 0, 'hist': {}, 'ex': []})
            d['tested'] += 1
            if ok:
                d['cons'] += 1
                d['hist'][ch] = d['hist'].get(ch, 0) + 1
                if ch >= 5:
                    d['ge5'] += 1
                    if len(d['ex']) < 10:
                        d['ex'].append((c1, d1, c2, d2, ch))
        for key in sorted(summ):
            d = summ[key]
            print('%s m=%d k0=%d: tested %d, consistent %d, checks histogram %s, consistent with >=5 checks %d %s' %
                  (key[0], key[1], key[2], d['tested'], d['cons'], dict(sorted(d['hist'].items())), d['ge5'], d['ex']), flush=True)
    print('[time] %.1fs' % (time.time() - T0))
