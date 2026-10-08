# -*- coding: utf-8 -*-
"""s13-b5skel 复核 r2：对 code/tableB/check_b5_skel.py 做「故意改坏」的反向演示。
不改原文件：读入源码，在内存里的副本上做一处替换，再以原路径为 __file__ 执行（这样它的 import 路径不变），
记录每个变体的 PASS/FAIL 与退出码。期望：每个变体都有 FAIL、退出码为 1，且 FAIL 的条目与改动对应。
  v1  W~_2 的 x^8 系数 4 -> 3（N 的留数元改错）：期望 b5s-res、b5s-subst、b5s-norm FAIL
  v2  纤维 w 的闭式常数 1/(w! w^2) -> 1/(w! w)：期望 b5s-resw FAIL（w=3 受影响，w=1 不受影响）
  v3  b5s-bivar 的低 p 修正系数置 0：期望 b5s-bivar FAIL
"""
import io
import os
import sys
import contextlib

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
ORIG = os.path.join(ROOT, 'code', 'tableB', 'check_b5_skel.py')
with open(ORIG, encoding='utf-8') as fh:
    SRC = fh.read()
# 先在真实 stdout 下导入它依赖的模块（它们在模块级调用 sys.stdout.reconfigure）
sys.path.insert(0, os.path.join(ROOT, 'code'))
sys.path.insert(0, os.path.join(ROOT, 'code', 'tableB'))
import core  # noqa: E402,F401
import check_b4  # noqa: E402,F401


class Buf(io.StringIO):
    def reconfigure(self, **kw):
        pass

    def isatty(self):
        return False

VARIANTS = [
    ('v1', 'WT2 = red([1, 0, 0, 0, 0, 2, 0, 0, 4], I)', 'WT2 = red([1, 0, 0, 0, 0, 2, 0, 0, 3], I)',
     {'b5s-res', 'b5s-subst', 'b5s-norm'}),
    ('v2', 'sc(Fr(-1, factorial(wf) * wf * wf), lam[kind])', 'sc(Fr(-1, factorial(wf) * wf), lam[kind])',
     {'b5s-resw'}),
    ('v3', "coef = sum(comb(q, pp) * (-1) ** (p - q) * comb(p, q) for q in range(pp, q0))", "coef = 0",
     {'b5s-bivar'}),
]

allok = True
for name, old, new, expect in VARIANTS:
    cnt = SRC.count(old)
    src = SRC.replace(old, new)
    buf = Buf()
    code = None
    g = {'__name__': '__main__', '__file__': ORIG}
    with contextlib.redirect_stdout(buf):
        try:
            exec(compile(src, ORIG + ' [' + name + ']', 'exec'), g)
        except SystemExit as ex:
            code = ex.code
    out = buf.getvalue().splitlines()
    fails = {ln.split()[1] for ln in out if ln.startswith('FAIL ')}
    summ = [ln for ln in out if ln.startswith('SUMMARY')]
    ok = cnt == 1 and code == 1 and expect <= fails
    allok &= ok
    print('%s %s：替换处 %d 个；退出码 %s；FAIL 条目 %s；期望至少 %s；%s' %
          ('PASS' if ok else 'FAIL', name, cnt, code, sorted(fails), sorted(expect), summ[0] if summ else '无 SUMMARY'))
    for ln in out:
        if ln.startswith('FAIL '):
            print('    ' + ln[:200])
print('SUMMARY s13-b5skel-r2 %s' % ('pass' if allok else 'fail'))
sys.exit(0 if allok else 1)
