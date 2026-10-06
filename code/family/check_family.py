# 核对：OEIS 里列规则同为「竖向禁止 0 0 1 与 0 1 1」的 6 张 Hardin 表，都满足
#     T(n,k) = Z_k(ceil(n/2)) * Z_k(floor(n/2)),
# 其中 Z_k(m) = 长 k 的允许行（避开该表的两个横向模式）在逐分量序下的弱降 m 元组个数，Z_k(0) = 1。
# 理由：列规则 <=> 每列 b_i >= b_{i+2}，奇数行、偶数行各成一条弱降链、互不干扰；行规则只看单独一行。
# 对 A207123 就是 a_k(n) = U_k(ceil(n/2)) U_k(floor(n/2))（T1.0）；这里只核对它对另外 5 张表同样成立。
# 只读本目录的 OEIS 快照，不联网。用法：py -3.14 code/family/check_family.py
import re, itertools, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SNAP = os.path.join(HERE, "oeis_search_vertical_001_011_tabl.txt")

def parse(path):
    entries = {}
    for line in open(path, encoding="utf-8").read().splitlines():
        m = re.match(r"%([A-Za-z]) (A\d{6}) ?(.*)", line)
        if not m:
            continue
        tag, anum, rest = m.groups()
        e = entries.setdefault(anum, {"data": "", "name": ""})
        if tag in "STU":
            e["data"] += rest.strip()
        elif tag == "N":
            e["name"] = rest
    return entries

def rows_allowed(k, pats):
    out = []
    for r in itertools.product((0, 1), repeat=k):
        s = "".join(map(str, r))
        if all(p not in s for p in pats):
            out.append(r)
    return out

def Z_list(k, pats, M):
    """[Z_k(0), ..., Z_k(M)]：允许行偏序集里弱降 m 元组的个数。"""
    rows = rows_allowed(k, pats)
    n = len(rows)
    below = [[j for j in range(n) if all(rows[j][t] <= rows[i][t] for t in range(k))] for i in range(n)]
    res = [1]
    f = [1] * n                      # f[i] = 以第 i 行结尾的弱降元组个数
    res.append(sum(f))
    for _ in range(2, M + 1):
        f = [sum(f[j] for j in below[i]) for i in range(n)]
        res.append(sum(f))
    return res

def brute(n, k, pats):
    """按原始定义直接数 n×k 的 0/1 矩阵（用来核对约定）。"""
    cnt = 0
    for bits in itertools.product((0, 1), repeat=n * k):
        A = [bits[i * k:(i + 1) * k] for i in range(n)]
        ok = all(all(p not in "".join(map(str, row)) for p in pats) for row in A)
        if ok:
            for c in range(k):
                col = "".join(str(A[i][c]) for i in range(n))
                if "001" in col or "011" in col:
                    ok = False
                    break
        cnt += ok
    return cnt

def main():
    entries = parse(SNAP)
    nfail = 0
    for anum, e in sorted(entries.items()):
        m = re.search(r"avoiding (\d \d \d) and (\d \d \d) horizontally and 0 0 1 and 0 1 1 vertically", e["name"])
        if not m:
            print("FAIL", anum, "名称无法解析:", e["name"]); nfail += 1; continue
        pats = [m.group(1).replace(" ", ""), m.group(2).replace(" ", "")]
        data = [int(x) for x in e["data"].split(",") if x]
        cache = {}
        def T(n, k):
            if k not in cache:
                cache[k] = Z_list(k, pats, 12)
            return cache[k][(n + 1) // 2] * cache[k][n // 2]
        bad = [(n, k) for n in range(1, 5) for k in range(1, 4) if brute(n, k, pats) != T(n, k)]
        # OEIS 数据按反对角线读：T(1,d-1), T(2,d-2), ..., T(d-1,1)
        idx, checked, mism = 0, 0, []
        d = 2
        while idx < len(data):
            for n in range(1, d):
                if idx >= len(data):
                    break
                k = d - n
                if n <= 22 and k <= 10:
                    checked += 1
                    if T(n, k) != data[idx]:
                        mism.append((n, k))
                idx += 1
            d += 1
        ok = not bad and not mism
        nfail += not ok
        print("%s %s 横向避开 %s：暴力核对 n<=4,k<=3 %s；OEIS 数据 %d 项中核对 %d 项（n<=22,k<=10）%s" % (
            "PASS" if ok else "FAIL", anum, "、".join(pats), "一致" if not bad else "不一致 %s" % bad,
            len(data), checked, "全部一致" if not mism else "，不一致 %s" % mism[:5]))
    print("SUMMARY tables=%d fail=%d" % (len(entries), nfail))
    sys.exit(1 if nfail else 0)

if __name__ == "__main__":
    main()
