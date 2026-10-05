# -*- coding: utf-8 -*-
"""探索 1：块分解的唯一性与覆盖，k<=10, m<=4 全枚举（只用三元组条件，不用 core 计数函数）。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocks import *

t0 = time.time()
K, MM = 10, 4
allok = True
for m in range(0, MM + 1):
    for k in range(0, K + 1):
        L = dfs_legal(k, m)
        Ls = set(L)
        W = gen_block_words(k, m)
        ok_bw = all(is_block_word(w, m) for w in W)
        imgs = [concat(w) for w in W]
        ok_len = all(len(x) == k for x in imgs)
        ok_legal = all(is_legal(x) for x in imgs)
        ok_inj = len(set(imgs)) == len(imgs)
        ok_sur = set(imgs) == Ls
        # 每个合法序列：确定性解析 + 解析计数恰为 1 + 统计量
        ok_parse = True
        ok_stats = True
        for h in L:
            bl = parse_det(h)
            if bl is None or not is_block_word(bl, m) or concat(bl) != h:
                ok_parse = False
                break
            if count_parses(h, m) != 1:
                ok_parse = False
                break
            nT = sum(1 for b in bl if b[0] == 'T')
            nE = sum(1 for b in bl if b[0] == 'E')
            asc_end = k >= 2 and h[-2] < h[-1]
            if ascents(h) != nT + nE or asc_end != (nE == 1):
                ok_stats = False
            if k >= 1 and max(h) != bl[0][1]:
                ok_stats = False
        ok = ok_bw and ok_len and ok_legal and ok_inj and ok_sur and ok_parse and ok_stats
        allok &= ok
        if not ok or k == K:
            print('m=%d k=%2d  #legal=%6d #blockwords=%6d  bw=%s len=%s legal=%s inj=%s sur=%s parse=%s stats=%s'
                  % (m, k, len(L), len(W), ok_bw, ok_len, ok_legal, ok_inj, ok_sur, ok_parse, ok_stats))
print('bijection block-words <-> legal sequences, k<=%d m<=%d:' % (K, MM), 'PASS' if allok else 'FAIL',
      '(%.1fs)' % (time.time() - t0))

# 全部 (m+1)^k 序列：解析计数 == [合法]
t1 = time.time()
tot = 0
okall = True
for m in range(0, MM + 1):
    c, fails = all_sequences_parse_check(K, m)
    tot += c
    if fails:
        okall = False
        print('  FAIL m=%d first fails:' % m, fails[:5])
    print('  m=%d: checked %d sequences (1<=k<=%d), fails=%d' % (m, c, K, len(fails)))
print('all sequences: #parses == [legal], k<=%d m<=%d (%d seqs):' % (K, MM, tot), 'PASS' if okall else 'FAIL',
      '(%.1fs)' % (time.time() - t1))
