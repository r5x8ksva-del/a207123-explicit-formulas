# -*- coding: utf-8 -*-
"""按依赖顺序打印 A207123 的模块名（每行一个，形如 A207123.Basic），供 run_lean_checks.sh 逐个构建。

从根文件 A207123.lean 的 import 出发，读取 A207123/*.lean 中的 `import A207123.X` 做拓扑排序。
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAT = re.compile(r"^import A207123\.(\w+)", re.M)


def imports(name):
    with open(os.path.join(HERE, "A207123", name + ".lean"), encoding="utf-8") as f:
        return PAT.findall(f.read())


def main():
    with open(os.path.join(HERE, "A207123.lean"), encoding="utf-8") as f:
        roots = PAT.findall(f.read())
    order, done = [], set()

    def visit(m, stack):
        if m in done:
            return
        if m in stack:
            sys.exit("import cycle at " + m)
        for d in imports(m):
            visit(d, stack + [m])
        done.add(m)
        order.append(m)

    for m in roots:
        visit(m, [])
    print("\n".join("A207123." + m for m in order))


if __name__ == "__main__":
    main()
