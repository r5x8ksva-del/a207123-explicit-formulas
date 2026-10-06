# 前向引用检索（只读）：对种子论文，用 OpenAlex 的开放引文数据取出「谁引用了它」，再按关键词筛出可能做过类似工作的后续论文。
# 这是 Google Scholar「被引用次数」功能的开放替代（覆盖面不同，不等价：OpenAlex 的引文来自 Crossref / 预印本解析，会漏一部分）。
# 原始返回存 data/lit/raw_cites/<种子>.json；候选表写 data/lit/cited_by_candidates.md。不带邮箱、不登录。
# 用法：py -3.14 code/novelty/cited_by.py run    （取数；已存在的种子不重取，--force 重取）
#       py -3.14 code/novelty/cited_by.py report （只用本地 raw 重新生成候选表）
import argparse, json, os, re, sys, time, urllib.parse, urllib.request, urllib.error

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "lit")
RAW = os.path.join(OUT, "raw_cites")
UA = "novelty-check/1.0 (read-only literature lookup)"
SEL = "id,doi,display_name,publication_year,authorships,primary_location,cited_by_count,abstract_inverted_index"

# (短名, 解析方式, 值)：doi 直接查；title 用标题检索取第一条（取回后打印题名，由人核对）
SEEDS = [
    ("kauers2007_stirling_summation", "doi", "10.1016/j.jsc.2007.08.002"),
    ("cks2009_nonholonomic_systems", "title", "A Non-Holonomic Systems Approach to Special Function Identities"),
    ("fgs2005_nonholonomic_character", "title", "On the non-holonomic character of logarithms, powers, and the n-th prime function"),
    ("fgs2010_lindelof", "doi", "10.37236/275"),
    ("klazar2003_bell_ade", "doi", "10.1016/s0097-3165(03)00014-1"),
    ("lipshitz1989_dfinite", "doi", "10.1016/0021-8693(89)90222-6"),
    ("bmp2000_multivariate_cc", "doi", "10.1016/s0012-365x(00)00147-3"),
    ("broder1984_rstirling", "doi", "10.1016/0012-365x(84)90161-4"),
    ("db_kauers2024_hardinian", "doi", "10.37236/12358"),
    ("db_spahn2024_rect_hardinian", "doi", "10.1145/3717582.3717589"),
    ("dbktz2024_balanced_matrices", "doi", "10.48550/arxiv.2410.07435"),
    ("kk2023_dfinite_oeis", "title", "Some D-finite and Some Possibly D-finite Sequences in the OEIS"),
    ("ekhad_yang_zeilberger2017_mathar", "doi", "10.48550/arxiv.1707.04654"),
    ("gessel_lin_zeng2012_jacobi_stirling", "doi", "10.48550/arxiv.1201.0622"),
    ("maier2022_triangular_recurrences", "doi", "10.1016/j.aam.2023.102485"),
    ("stanley1980_dfinite", "title", "Differentiably finite power series"),
]

KW = ["stirling", "annihilat", "ideal", "ore algebra", "holonomic", "d-finite", "non-holonomic", "oeis", "hardin", "binary array", "binary matri",
      "forbidden", "avoiding", "consecutive pattern", "transfer matrix", "recurrence", "lean", "formaliz", "conjecture", "zeta polynomial", "multichain"]
_last = [0.0]


def get(url):
    wait = 0.35 - (time.time() - _last[0])
    if wait > 0:
        time.sleep(wait)
    _last[0] = time.time()
    for i in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": UA}), timeout=60) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            if e.code in (429, 503) and i < 2:
                time.sleep(5 * (i + 1))
                continue
            return {"error": e.code}
        except Exception as e:
            if i < 2:
                time.sleep(3)
                continue
            return {"error": str(e)[:80]}


def resolve(kind, val):
    if kind == "doi":
        w = get("https://api.openalex.org/works/doi:" + urllib.parse.quote(val, safe="/:") + "?select=id,display_name,publication_year,cited_by_count")
        return w if "id" in w else None
    r = get("https://api.openalex.org/works?" + urllib.parse.urlencode({"search": val, "per-page": 3, "select": "id,display_name,publication_year,cited_by_count"}))
    res = r.get("results") or []
    return res[0] if res else None


def inv_abstract(ix):
    if not ix:
        return ""
    pos = {}
    for w, ps in ix.items():
        for p in ps:
            pos[p] = w
    return " ".join(pos[p] for p in sorted(pos))


def run(args):
    os.makedirs(RAW, exist_ok=True)
    for name, kind, val in SEEDS:
        path = os.path.join(RAW, name + ".json")
        if os.path.exists(path) and not args.force:
            continue
        seed = resolve(kind, val)
        if not seed:
            print(f"[{name}] 解析失败", flush=True)
            continue
        wid = seed["id"].rsplit("/", 1)[-1]
        works, cursor = [], "*"
        while cursor and len(works) < 1500:
            r = get("https://api.openalex.org/works?" + urllib.parse.urlencode({"filter": "cites:" + wid, "per-page": 200, "select": SEL, "cursor": cursor}))
            if "error" in r:
                print(f"[{name}] 取引用时出错 {r['error']}", flush=True)
                break
            works += r.get("results", [])
            cursor = (r.get("meta") or {}).get("next_cursor")
            if not r.get("results"):
                break
        json.dump(dict(seed=seed, kind=kind, val=val, n=len(works), works=works), open(path, "w", encoding="utf-8"), ensure_ascii=False)
        print(f"[{name}] 种子 = {seed.get('display_name')!r} ({seed.get('publication_year')}), OpenAlex 记录被引 {seed.get('cited_by_count')}, 取回 {len(works)} 篇", flush=True)


def report(args):
    pool = {}
    summary = []
    for name, kind, val in SEEDS:
        path = os.path.join(RAW, name + ".json")
        if not os.path.exists(path):
            continue
        d = json.load(open(path, encoding="utf-8"))
        summary.append((name, d["seed"].get("display_name"), d["seed"].get("publication_year"), d["seed"].get("cited_by_count"), d["n"]))
        for w in d["works"]:
            title = w.get("display_name") or ""
            ab = inv_abstract(w.get("abstract_inverted_index"))
            text = (title + " " + ab).lower()
            p = pool.setdefault(w["id"], dict(title=title, year=w.get("publication_year"), doi=w.get("doi") or "", id=w["id"], text=text, seeds=[],
                                             authors=[(a.get("author") or {}).get("display_name", "") for a in w.get("authorships", [])][:3], cites=w.get("cited_by_count"),
                                             venue=(((w.get("primary_location") or {}).get("source")) or {}).get("display_name") or "", abstract=ab))
            p["seeds"].append(name)
    rows = []
    for p in pool.values():
        kw = [k for k in KW if k in p["text"]]
        score = len(kw) + 2 * (len(p["seeds"]) - 1)
        if ("stirling" in p["text"] and any(k in p["text"] for k in ("annihilat", "ideal", "ore algebra", "holonomic", "d-finite"))) \
                or "oeis" in p["text"] or "hardin" in p["text"] or ("avoiding" in p["text"] and ("binary" in p["text"]) and ("array" in p["text"] or "matri" in p["text"])):
            score += 5
        rows.append((score, p, kw))
    rows.sort(key=lambda t: (-t[0], -(t[1]["year"] or 0)))
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "cited_by_candidates.md"), "w", encoding="utf-8", newline="\n") as f:
        f.write(f"# 前向引用候选（cited_by.py，{time.strftime('%Y-%m-%d %H:%M')}）\n\n## 种子与取回数量\n\n| 种子 | OpenAlex 里的题名 | 年 | OpenAlex 记录的被引 | 本次取回 |\n|---|---|---|---|---|\n")
        for s in summary:
            f.write(f"| {s[0]} | {str(s[1]).replace('|', '/')[:80]} | {s[2]} | {s[3]} | {s[4]} |\n")
        f.write(f"\n## 候选（共 {len(rows)} 篇去重引用，按关键词得分排序，列前 150）\n\n| 得分 | 年 | 题名 | 作者 | 出处 | 链接 | 引用了哪些种子 | 命中关键词 |\n|---|---|---|---|---|---|---|---|\n")
        for score, p, kw in rows[:150]:
            au = ", ".join(p["authors"]) + (" 等" if len(p["authors"]) >= 3 else "")
            link = p["doi"] or p["id"]
            f.write(f"| {score} | {p['year']} | {p['title'].replace('|', '/')[:110]} | {au.replace('|', '/')} | {p['venue'].replace('|', '/')[:36]} | {link} | {','.join(sorted(set(p['seeds'])))} | {','.join(kw)} |\n")
    print(f"种子 {len(summary)} 个，去重引用 {len(rows)} 篇；已写 data/lit/cited_by_candidates.md")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("run")
    p.add_argument("--force", action="store_true")
    p.set_defaults(fn=run)
    sub.add_parser("report").set_defaults(fn=report)
    a = ap.parse_args()
    a.fn(a)
