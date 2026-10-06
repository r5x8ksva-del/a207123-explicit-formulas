# 新颖性文献检索（只读）：按「声称」分组的查询，经 arXiv / OpenAlex / Crossref / Semantic Scholar / StackExchange 的官方开放接口检索。
# 原始返回存 data/lit/raw/（每个「来源__查询号」一个文件），规范化记录与候选表由 report 子命令从 raw 重新生成，离线可复现。
# 不查的站（原因都查过）：Google Scholar（robots.txt 对所有爬虫 Disallow /scholar）、zbMATH 网页（robots.txt 禁止 Anthropic 的爬虫）、
# MathSciNet / Web of Science / Scopus（需机构登录，不能替用户输入密码）；这些见 notes/ 里给用户的手动检索式。
# 请求间隔：arXiv >= 3.2 s，Crossref >= 1 s，Semantic Scholar >= 4 s（限流时退避、连续失败就放弃），OpenAlex、StackExchange 约 0.4–1.2 s。
# 不带邮箱、不登录、不发帖、不联系任何人。
# 用法：py -3.14 code/novelty/lit_search.py run [--only fam01,df01] [--sources arxiv,openalex,crossref,s2,se] [--retry-errors]
#       py -3.14 code/novelty/lit_search.py report
#       py -3.14 code/novelty/lit_search.py list
import argparse, glob, gzip, json, os, re, sys, time, urllib.error, urllib.parse, urllib.request
import xml.etree.ElementTree as ET

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "lit")
RAW = os.path.join(OUT, "raw")
UA = "novelty-check/1.0 (read-only literature lookup)"
NS = {"a": "http://www.w3.org/2005/Atom", "x": "http://arxiv.org/schemas/atom"}
SOURCES = ["arxiv", "openalex", "crossref", "s2", "se"]
MIN_GAP = {"arxiv": 3.2, "openalex": 0.4, "crossref": 1.0, "s2": 4.0, "se": 1.2}
EXT = {"arxiv": "xml", "openalex": "json", "crossref": "json", "s2": "json", "se": "json"}


def Q(qid, claim, text, ax=None, se=False):
    return dict(id=qid, claim=claim, text=text, ax=ax, se=se)


# text 用于 OpenAlex / Crossref / Semantic Scholar / StackExchange；ax 是 arXiv 的检索式（None 则不查 arXiv）。
QUERIES = [
    # ---- 家族与既有证明（T1.0、T1.3、T1.9、A15）----
    Q("fam01", "家族/Hardin", '"Hardinian arrays"', 'all:"Hardinian arrays"'),
    Q("fam02", "家族/Hardin", "Hardin OEIS arrays avoiding patterns horizontally vertically", "all:Hardin AND all:OEIS", se=True),
    Q("fam03", "家族/Hardin", '"arrays avoiding" OEIS Hardin 0..1', 'abs:"arrays avoiding" AND abs:OEIS'),
    Q("fam04", "家族/Hardin", "proof of conjectures by R. H. Hardin OEIS", "abs:Hardin AND abs:conjectures AND abs:OEIS"),
    Q("fam05", "家族/Hardin", "Ekhad Zeilberger automatic counting binary arrays avoiding patterns", "au:Zeilberger AND abs:arrays AND abs:avoiding"),
    Q("fam06", "家族/Hardin", "Kauers Koutschan D-finite sequences OEIS guessing", "au:Kauers AND au:Koutschan"),
    Q("fam07", "家族/模式", "binary matrices avoiding consecutive patterns rows columns transfer matrix enumeration", 'abs:"binary matrices" AND abs:avoiding AND abs:patterns', se=True),
    Q("fam08", "家族/模式", "two-dimensional consecutive pattern avoidance binary arrays generating function", 'abs:"consecutive patterns" AND abs:arrays'),
    Q("fam09", "家族/模式", "counting binary arrays forbidden horizontal and vertical words", 'abs:"binary arrays" AND abs:forbidden'),
    Q("fam10", "家族/OEIS号", '"A207123" OR "A207118" OR "A207119" OR "A207120" OR "A207121" OR "A207122"'),
    Q("fam11", "家族/OEIS号", '"A326247" OR "A207069" OR "A084990" OR "A038718"'),
    Q("fam12", "家族/Hardin", "Rectangular Hardinian arrays", "all:Hardinian"),
    Q("fam13", "家族/Hardin", "OEIS empirical conjectures Hardin tables proved linear recurrence order", "abs:OEIS AND abs:conjectures AND abs:recurrence"),
    Q("fam14", "家族/Hardin", "two-dimensional array rows and columns satisfy linear recurrences constant coefficients orders grow linearly", 'abs:"two-dimensional" AND abs:recurrences AND abs:OEIS'),
    # ---- 对象 U_k(m)：高度序列、模式、r-Stirling ----
    Q("obj01", "对象 U_k(m)", "height sequences adjacent triples forbidden consecutive patterns Stirling numbers", 'abs:Stirling AND abs:"consecutive patterns"', se=True),
    Q("obj02", "对象 U_k(m)", "words avoiding consecutive patterns of length three generating function alphabet", 'abs:words AND abs:"consecutive patterns" AND abs:"length 3"'),
    Q("obj03", "对象 U_k(m)", "r-Stirling numbers", 'abs:"r-Stirling"', se=True),
    Q("obj04", "对象 U_k(m)", "Cayley permutations consecutive pattern avoidance", 'abs:"Cayley permutations" AND abs:pattern'),
    Q("obj05", "对象 U_k(m)", "multichains zeta polynomial poset of words avoiding patterns", 'abs:multichains AND abs:"zeta polynomial"'),
    Q("obj06", "对象 U_k(m)", "Narayana cows sequence generalization root of x^3 = x^2 + m", "abs:Narayana AND abs:sequence"),
    # ---- 显式公式与「没有更短公式」（T2.4、T2.6、T2.7′）----
    Q("exp01", "T2.4/T2.6", "summation algorithms for Stirling number identities", "au:Kauers AND abs:Stirling"),
    Q("exp02", "T2.6/T2.7", "closed form Stirling numbers hypergeometric sums decision procedure nonexistence", 'abs:Stirling AND abs:"closed form" AND abs:hypergeometric', se=True),
    Q("exp03", "T2.7", "Gosper summability multiple sum proper hypergeometric term not expressible single sum", 'abs:Gosper AND abs:"proper hypergeometric"'),
    Q("exp04", "T2.4", "explicit formula Stirling numbers binomial coefficients all positive terms two-layer sum counting sequences"),
    Q("exp05", "T3.7", "Stirling numbers of the second kind bivariate generating function not D-finite", 'abs:Stirling AND abs:"D-finite"', se=True),
    # ---- D-finite、左理想、母函数（T3.x）----
    Q("df01", "T3.7/T3.8", "non-holonomic sequences annihilating ideal Ore algebra Stirling Bell numbers", "abs:holonomic AND abs:Stirling", se=True),
    Q("df02", "T3.8", "annihilating ideal of recurrences generated by a single recurrence non-holonomic double sequence", 'abs:"Ore algebra" AND abs:ideal AND abs:recurrence', se=True),
    Q("df03", "T3.7", "Lipshitz D-finite power series closure properties Hadamard product diagonal criterion not D-finite", 'abs:"D-finite" AND abs:diagonal AND abs:"power series"'),
    Q("df04", "T3.7", "Bell numbers algebraic differential equations", 'ti:"Bell numbers" AND abs:differential'),
    Q("df05", "T3.7", "non-holonomic character of logarithms powers nth prime function", "abs:holonomic AND abs:prime AND abs:logarithms"),
    Q("df06", "T3.8", "non-holonomic systems approach to special function identities", "au:Chyzak AND au:Salvy"),
    Q("df07", "T3.8", "quadrant recurrences polynomial coefficients two-variable sequence classification of all recurrences left ideal", 'abs:recurrences AND abs:ideal AND abs:"two variables"'),
    Q("df08", "T3.1-3.4", "Humbert confluent hypergeometric function Phi_1 generating function combinatorial sequence divergent series Borel", "abs:Humbert AND abs:hypergeometric"),
    Q("df09", "Lean", "Lean formalization D-finite holonomic sequences Ore algebra Mathlib", "abs:Lean AND abs:holonomic"),
    Q("df10", "Lean", "formal verification Lean 4 OEIS sequence generating function recurrence proof", "abs:Lean AND abs:OEIS"),
    Q("df11", "T3.8", "Stirling numbers recurrence operators Groebner basis nonholonomic creative telescoping", 'abs:Stirling AND abs:"creative telescoping"'),
    # ---- 最小递推阶、近对角线、h 多项式 ----
    Q("rec01", "T1.3/T1.9", "minimal order linear recurrence rational generating function numerator denominator coprime transfer matrix OEIS arrays", 'abs:"minimal recurrence" AND abs:OEIS'),
    Q("nd01", "T4.1", "Stirling numbers near diagonal polynomial in n degree 2k", "abs:Stirling AND abs:polynomial AND abs:diagonal", se=True),
    Q("nd02", "T4.1", "Stirling polynomials Gessel Stanley", "au:Gessel AND abs:Stirling"),
    Q("nd03", "T4.1", "triangular array recurrence diagonals polynomial structure Eulerian type recurrences", "abs:triangular AND abs:recurrence AND abs:polynomial"),
    Q("hp01", "B1(h_k)", "Neggers Stanley conjecture real roots W-polynomial poset", 'abs:"Neggers-Stanley"', se=True),
    Q("hp02", "B1(h_k)", "zeta polynomial h-vector real-rooted poset multichains", 'abs:"zeta polynomial" AND abs:real'),
    # ---- AI / 形式化 ----
    Q("ai01", "AI/Lean", "AI proves OEIS conjectures Lean formal proof", 'abs:OEIS AND abs:"language model"'),
    Q("ai02", "AI/Lean", "large language model proof of OEIS conjecture recurrence combinatorics", "abs:OEIS AND abs:proof AND abs:AI"),
    Q("ai03", "AI/Lean", "AI-assisted proof Hardin conjecture formalized combinatorics arrays"),
    # ---- 第二轮（读完第一轮结果后补的更精确查询）----
    Q("fam15", "T1.0/家族", "Hardin binary arrays avoiding patterns proof formula product of binomial coefficients even odd rows", "abs:Hardin AND abs:arrays AND abs:binary"),
    Q("fam16", "T1.0/家族", "binary arrays horizontal and vertical forbidden patterns fixed number of rows symbolic number of columns linear recurrence rigorous proof", 'abs:"binary arrays" AND abs:horizontal AND abs:vertical'),
    Q("fam17", "T1.9", "OEIS Hardin tables proved recurrences binary arrays avoiding patterns rows columns Barker conjectures", "abs:OEIS AND abs:Barker"),
    Q("obj07", "对象 U_k(m)", "words avoiding consecutive patterns 112 121 123 132 213 231 generating function", 'abs:words AND abs:consecutive AND abs:"patterns"'),
    Q("obj08", "对象 U_k(m)", "weakly decreasing chains of binary words poset zeta polynomial counting arrays rows columns pattern", 'abs:"zeta polynomial" AND abs:binary'),
    Q("obj09", "对象 U_k(m)", "Stirling numbers counting sequences with local condition on consecutive triples explicit formula generating function not D-finite"),
    Q("df12", "T3.8", "annihilator Stirling-like sequences precisely generated by triangular recurrence pure recurrence", "abs:Stirling-like"),
    Q("df13", "T3.7", "bivariate sequence not holonomic absence of pure recurrence in each variable Stirling numbers proof", "abs:holonomic AND abs:bivariate AND abs:Stirling"),
    Q("df14", "T3.7/T3.8", "Ore algebra left ideal annihilating recurrences combinatorial triangle classification polynomial coefficients saturation", 'abs:"Ore algebra" AND abs:combinatorial'),
    Q("nd04", "T4.1", "diagonal polynomials Stirling-type numbers degree 2k P-partitions Gessel Stanley Legendre-Stirling", "abs:Legendre-Stirling"),
]

_last = {}


def throttle(src):
    wait = MIN_GAP[src] - (time.time() - _last.get(src, 0))
    if wait > 0:
        time.sleep(wait)
    _last[src] = time.time()


def fetch(src, url, tries=3):
    status = None
    for i in range(tries):
        throttle(src)
        req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json, application/atom+xml, */*"})
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                data = r.read()
                if r.headers.get("Content-Encoding") == "gzip":
                    data = gzip.decompress(data)
                return data, r.status
        except urllib.error.HTTPError as e:
            status = e.code
            if e.code in (429, 503) and i < tries - 1:
                time.sleep(6 * (i + 1) * (2 if src == "s2" else 1))
                continue
            return None, status
        except Exception as e:
            status = str(e)[:80]
            if i < tries - 1:
                time.sleep(3)
                continue
            return None, status
    return None, status


def enc(params):
    return urllib.parse.urlencode(params)


def build_url(src, q, site=None):
    if src == "arxiv":
        if not q["ax"]:
            return None
        return "https://export.arxiv.org/api/query?" + enc({"search_query": q["ax"], "start": 0, "max_results": 20, "sortBy": "relevance"})
    if src == "openalex":
        sel = "id,doi,display_name,publication_year,authorships,primary_location,cited_by_count,abstract_inverted_index"
        return "https://api.openalex.org/works?" + enc({"search": q["text"], "per-page": 20, "select": sel})
    if src == "crossref":
        sel = "DOI,title,author,issued,container-title,type,abstract,is-referenced-by-count,URL"
        return "https://api.crossref.org/works?" + enc({"query": q["text"], "rows": 15, "select": sel})
    if src == "s2":
        fields = "title,year,authors,venue,externalIds,abstract,citationCount,url"
        return "https://api.semanticscholar.org/graph/v1/paper/search?" + enc({"query": q["text"].replace('"', ""), "limit": 15, "fields": fields})
    if src == "se":
        if not q["se"]:
            return None
        return "https://api.stackexchange.com/2.3/search/advanced?" + enc({"q": q["text"].replace('"', ""), "site": site, "pagesize": 10, "order": "desc", "sort": "relevance"})
    raise ValueError(src)


def inv_abstract(ix):
    if not ix:
        return ""
    pos = {}
    for w, ps in ix.items():
        for p in ps:
            pos[p] = w
    return " ".join(pos[p] for p in sorted(pos))


def clean(s):
    return " ".join(re.sub(r"<[^>]+>", " ", s or "").split())


def arxiv_from_doi(doi):
    doi = (doi or "").lower().replace("https://doi.org/", "")
    return doi.split("arxiv.", 1)[1] if doi.startswith("10.48550/arxiv.") else ""


def parse_arxiv(raw):
    out = []
    for i, e in enumerate(ET.fromstring(raw).findall("a:entry", NS)):
        aid = e.findtext("a:id", "", NS)
        arx = re.sub(r"v[0-9]+$", "", re.sub(r"^https?://arxiv.org/abs/", "", aid))
        out.append(dict(rank=i + 1, title=clean(e.findtext("a:title", "", NS)), authors=[a.findtext("a:name", "", NS) for a in e.findall("a:author", NS)],
                        year=int((e.findtext("a:published", "0", NS) or "0")[:4] or 0), venue=e.findtext("x:journal_ref", "", NS) or "arXiv",
                        doi=(e.findtext("x:doi", "", NS) or "").lower(), arxiv=arx, url=aid, abstract=clean(e.findtext("a:summary", "", NS)), cited_by=None))
    return out


def parse_openalex(raw):
    out = []
    for i, r in enumerate(json.loads(raw).get("results", [])):
        src = ((r.get("primary_location") or {}).get("source") or {}).get("display_name") or ""
        doi = (r.get("doi") or "").replace("https://doi.org/", "").lower()
        out.append(dict(rank=i + 1, title=clean(r.get("display_name")), authors=[(a.get("author") or {}).get("display_name", "") for a in r.get("authorships", [])],
                        year=r.get("publication_year") or 0, venue=src, doi=doi, arxiv=arxiv_from_doi(doi), url=r.get("id", ""),
                        abstract=clean(inv_abstract(r.get("abstract_inverted_index"))), cited_by=r.get("cited_by_count")))
    return out


def parse_crossref(raw):
    out = []
    for i, r in enumerate(json.loads(raw).get("message", {}).get("items", [])):
        dp = ((r.get("issued") or {}).get("date-parts") or [[0]])[0]
        doi = (r.get("DOI") or "").lower()
        auth = [" ".join(x for x in (a.get("given"), a.get("family")) if x) for a in r.get("author", [])]
        out.append(dict(rank=i + 1, title=clean((r.get("title") or [""])[0]), authors=auth, year=(dp[0] if dp else 0) or 0,
                        venue=(r.get("container-title") or [""])[0], doi=doi, arxiv=arxiv_from_doi(doi), url=r.get("URL", ""),
                        abstract=clean(r.get("abstract")), cited_by=r.get("is-referenced-by-count")))
    return out


def parse_s2(raw):
    out = []
    for i, r in enumerate(json.loads(raw).get("data", []) or []):
        ex = r.get("externalIds") or {}
        out.append(dict(rank=i + 1, title=clean(r.get("title")), authors=[a.get("name", "") for a in r.get("authors", [])], year=r.get("year") or 0,
                        venue=r.get("venue") or "", doi=(ex.get("DOI") or "").lower(), arxiv=(ex.get("ArXiv") or "").lower(), url=r.get("url", ""),
                        abstract=clean(r.get("abstract")), cited_by=r.get("citationCount")))
    return out


def parse_se(raw):
    out = []
    for site, resp in json.loads(raw).items():
        for i, r in enumerate((resp or {}).get("items", [])):
            out.append(dict(rank=i + 1, title=clean(r.get("title")), authors=[(r.get("owner") or {}).get("display_name", "")],
                            year=time.gmtime(r.get("creation_date", 0)).tm_year, venue=site, doi="", arxiv="", url=r.get("link", ""),
                            abstract="tags: " + ",".join(r.get("tags", [])) + f" | score {r.get('score')} | answers {r.get('answer_count')}", cited_by=None))
    return out


PARSERS = dict(arxiv=parse_arxiv, openalex=parse_openalex, crossref=parse_crossref, s2=parse_s2, se=parse_se)


def raw_path(src, qid, ext=None):
    return os.path.join(RAW, f"{src}__{qid}.{ext or EXT[src]}")


def log_manifest(src, qid, status, nbytes):
    with open(os.path.join(RAW, "_manifest.jsonl"), "a", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(dict(t=time.strftime("%Y-%m-%d %H:%M:%S"), src=src, qid=qid, status=status, bytes=nbytes), ensure_ascii=False) + "\n")


def run(args):
    os.makedirs(RAW, exist_ok=True)
    only = set(args.only.split(",")) if args.only else None
    srcs = args.sources.split(",") if args.sources else SOURCES
    s2_fail = 0
    for q in QUERIES:
        if only and q["id"] not in only:
            continue
        for src in srcs:
            path, err = raw_path(src, q["id"]), raw_path(src, q["id"], "err")
            if os.path.exists(path) or (os.path.exists(err) and not args.retry_errors):
                continue
            if src == "s2" and s2_fail >= 4:
                continue
            if src == "se":
                if not q["se"]:
                    continue
                combo, bad = {}, None
                for site in ("mathoverflow.net", "math"):
                    data, status = fetch("se", build_url("se", q, site))
                    if data is None:
                        bad = status
                        break
                    combo[site] = json.loads(data)
                if bad:
                    open(err, "w").write(str(bad))
                    log_manifest(src, q["id"], bad, 0)
                    print(f"[{q['id']}] se FAIL {bad}", flush=True)
                    continue
                data = json.dumps(combo).encode("utf-8")
                status = 200
            else:
                url = build_url(src, q)
                if url is None:
                    continue
                data, status = fetch(src, url)
            if data is None:
                if src == "s2":
                    s2_fail += 1
                open(err, "w").write(str(status))
                log_manifest(src, q["id"], status, 0)
                print(f"[{q['id']}] {src} FAIL {status}", flush=True)
                continue
            if src == "s2":
                s2_fail = 0
            if os.path.exists(err):
                os.remove(err)
            open(path, "wb").write(data)
            n = len(PARSERS[src](data))
            log_manifest(src, q["id"], status, len(data))
            print(f"[{q['id']}] {src} ok {n} results", flush=True)


def load_records():
    recs = []
    for path in sorted(glob.glob(os.path.join(RAW, "*__*"))):
        base = os.path.basename(path)
        if base.endswith(".err"):
            continue
        src, rest = base.split("__", 1)
        qid = rest.rsplit(".", 1)[0]
        try:
            items = PARSERS[src](open(path, "rb").read())
        except Exception as e:
            print("parse fail", base, e)
            continue
        for it in items:
            it.update(source=src, qid=qid)
            recs.append(it)
    return recs


KEYWORDS = ["hardin", "oeis", "stirling", "d-finite", "holonomic", "annihilat", "ore algebra", "consecutive pattern", "forbidden", "avoiding",
            "transfer matrix", "zeta polynomial", "multichain", "gosper", "telescoping", "binary array", "binary matri", "recurrence",
            "generating function", "lean", "formaliz", "r-stirling"]


def norm_title(t):
    return re.sub(r"[^a-z0-9]+", " ", (t or "").lower()).strip()


def report(args):
    recs = load_records()
    groups = {}
    for r in recs:
        k = norm_title(r["title"])
        if len(k) < 12:
            k = (r.get("doi") or r.get("url") or k)
        groups.setdefault(k, []).append(r)
    rows = []
    for k, rs in groups.items():
        best = max(rs, key=lambda r: len(r.get("abstract") or ""))
        text = (best["title"] + " " + (best.get("abstract") or "")).lower()
        kw = sum(1 for w in KEYWORDS if w in text)
        qids = sorted({r["qid"] for r in rs})
        srcs = sorted({r["source"] for r in rs})
        cited = max([r["cited_by"] for r in rs if r.get("cited_by") is not None] or [0])
        link = ("https://doi.org/" + best["doi"]) if best.get("doi") else (best.get("url") or "")
        arx = next((r["arxiv"] for r in rs if r.get("arxiv")), "")
        rows.append(dict(title=best["title"], authors=best["authors"], year=best["year"], venue=best["venue"], link=link, arxiv=arx,
                         qids=qids, srcs=srcs, kw=kw, cited=cited, abstract=best.get("abstract") or ""))
    rows.sort(key=lambda r: (-len(r["qids"]), -r["kw"], -(r["year"] or 0)))
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "candidates.md"), "w", encoding="utf-8", newline="\n") as f:
        f.write(f"# 文献检索候选表（由 lit_search.py report 生成，{time.strftime('%Y-%m-%d %H:%M')}）\n\n")
        f.write(f"原始记录 {len(recs)} 条，按题名合并后 {len(rows)} 篇；按「命中的查询数、关键词数、年份」排序，只列前 300。\n\n")
        f.write("| # | 年 | 题名 | 作者 | 出处 | 链接 | 命中查询 | 来源 | 关键词 | 被引 |\n|---|---|---|---|---|---|---|---|---|---|\n")
        for i, r in enumerate(rows[:300], 1):
            au = ", ".join(r["authors"][:3]) + (" 等" if len(r["authors"]) > 3 else "")
            f.write(f"| {i} | {r['year']} | {r['title'].replace('|', '/')} | {au.replace('|', '/')} | {r['venue'].replace('|', '/')[:50]} | {r['link']} | {','.join(r['qids'])} | {','.join(r['srcs'])} | {r['kw']} | {r['cited']} |\n")
    with open(os.path.join(OUT, "results.jsonl"), "w", encoding="utf-8", newline="\n") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    # 审计表：每个「来源 × 查询」是否取到、取到多少
    man = {}
    p = os.path.join(RAW, "_manifest.jsonl")
    if os.path.exists(p):
        for line in open(p, encoding="utf-8"):
            m = json.loads(line)
            man[(m["src"], m["qid"])] = m
    with open(os.path.join(OUT, "query_audit.md"), "w", encoding="utf-8", newline="\n") as f:
        f.write("# 查询审计表\n\n每格：返回条数；FAIL 后面是状态码；空白 = 没查（该来源对这条查询不适用或被限流后放弃）。\n\n")
        f.write("| 查询 | 对应声明 | 检索词 | arXiv | OpenAlex | Crossref | S2 | SE |\n|---|---|---|---|---|---|---|---|\n")
        counts = {}
        for r in recs:
            counts[(r["source"], r["qid"])] = counts.get((r["source"], r["qid"]), 0) + 1
        for q in QUERIES:
            cells = []
            for s in SOURCES:
                if os.path.exists(raw_path(s, q["id"])):
                    cells.append(str(counts.get((s, q["id"]), 0)))
                elif os.path.exists(raw_path(s, q["id"], "err")):
                    cells.append("FAIL " + open(raw_path(s, q["id"], "err")).read().strip())
                else:
                    cells.append("")
            f.write(f"| {q['id']} | {q['claim']} | {q['text'].replace('|', '/')} | " + " | ".join(cells) + " |\n")
    print(f"records {len(recs)}, merged {len(rows)}; wrote candidates.md, results.jsonl, query_audit.md in {OUT}")


def list_queries(args):
    for q in QUERIES:
        print(q["id"], "|", q["claim"], "|", q["text"], "|", q["ax"], "| se" if q["se"] else "")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("run")
    p.add_argument("--only")
    p.add_argument("--sources")
    p.add_argument("--retry-errors", action="store_true")
    p.set_defaults(fn=run)
    sub.add_parser("report").set_defaults(fn=report)
    sub.add_parser("list").set_defaults(fn=list_queries)
    a = ap.parse_args()
    a.fn(a)
