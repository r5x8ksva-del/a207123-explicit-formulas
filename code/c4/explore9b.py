import time
from explore9_pattern_brute import brute_patterns
from explore4_patterns import pattern_counts
t0 = time.time()
B = brute_patterns(4)
print('d=4 brute==DP:', B == pattern_counts(4), sum(B.values()), '%.1fs' % (time.time() - t0))
