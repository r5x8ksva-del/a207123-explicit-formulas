# 核对 notes/新颖性核查_2026-10-07.md 里写的数字与关键事实，都能由仓库里的数据重新证实（不联网）。
# 笔记里的数字是写死在这里的：以后若用 lit_search.py 补跑了更多查询（例如 Semantic Scholar 不再限流），这里会 FAIL，提醒你同步改笔记。
# 每项打印 PASS / FAIL，任何 FAIL 时退出码为 1。
# 用法：先 py -3.14 code/novelty/lit_search.py report 与 cited_by.py report，再 py -3.14 code/novelty/check_note_facts.py
import glob, html, importlib.util, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
FAILS = []


def p(*a):
    return os.path.join(ROOT, *a)


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""))
    if not ok:
        FAILS.append(name)


def text_lines(path):
    h = open(path, encoding="utf-8", errors="ignore").read()
    t = html.unescape(re.sub(r"<[^>]+>", "\n", re.sub(r"<script.*?</script>", " ", h, flags=re.S)))
    return [l.strip() for l in t.splitlines() if l.strip()]


def rev_line(lines):
    for l in lines:
        if l.startswith("%I"):
            return re.sub(r"^%I (A[0-9]{6} )?", "", l)
    return None


def main():
    # A. 各来源的覆盖数字（笔记 §1 的表）
    raw = os.listdir(p("data", "lit", "raw"))
    cnt = {}
    for f in raw:
        if "__" not in f:
            continue
        src = f.split("__", 1)[0]
        d = cnt.setdefault(src, {"ok": 0, "err": 0})
        d["err" if f.endswith(".err") else "ok"] += 1
    for src, ok_n, err_n in [("arxiv", 50, 0), ("openalex", 55, 0), ("crossref", 55, 0), ("s2", 3, 9), ("se", 10, 0)]:
        d = cnt.get(src, {"ok": 0, "err": 0})
        check(f"覆盖.{src}", d["ok"] == ok_n and d["err"] == err_n, f"成功 {d['ok']}（笔记 {ok_n}），失败 {d['err']}（笔记 {err_n}）")
    s2_err = [open(p("data", "lit", "raw", f)).read().strip() for f in raw if f.startswith("s2__") and f.endswith(".err")]
    check("覆盖.s2 的失败全是 429", s2_err and all(x == "429" for x in s2_err), str(sorted(set(s2_err))))

    # B. 记录数
    spec = importlib.util.spec_from_file_location("lit_search", os.path.join(HERE, "lit_search.py"))
    ls = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ls)
    check("查询总数 55", len(ls.QUERIES) == 55, str(len(ls.QUERIES)))
    nrec = len(ls.load_records())
    check("原始记录 1711", nrec == 1711, str(nrec))
    merged = sum(1 for _ in open(p("data", "lit", "results.jsonl"), encoding="utf-8"))
    check("按题名合并 1345", merged == 1345, str(merged))
    rows = [json.loads(l) for l in open(p("data", "lit", "results.jsonl"), encoding="utf-8")]
    niu = [r for r in rows if r["year"] == 2026 and any("Niu" in a for a in r["authors"])]
    check("Niu 2026 年的预印本 7 篇", len(niu) == 7, str(len(niu)))

    # C. 前向引用
    cites = [json.load(open(f, encoding="utf-8")) for f in glob.glob(p("data", "lit", "raw_cites", "*.json"))]
    ids = {w["id"] for c in cites for w in c["works"]}
    check("前向引用种子 16 个", len(cites) == 16, str(len(cites)))
    check("前向引用去重 956 篇", len(ids) == 956, str(len(ids)))

    # D. OEIS 关键事实（笔记 §0、§3.4、§4）
    oe = p("data", "lit", "oeis")
    a93 = " ".join(text_lines(os.path.join(oe, "A202093.txt")))
    # OEIS 用 _名字_ 标记署名，所以名字两侧允许下划线
    check("A202093 标注 Krause 于 2026-06-26 证明", bool(re.search(r"\bproved by\s*_?Christian Krause_?\s*,?\s*Jun 26 2026", a93, re.I)) and "Proof of formula" in a93)
    check("A202093 修订行为 #36 Jun 28 2026", (rev_line(text_lines(os.path.join(oe, "A202093.txt"))) or "").startswith("#36 Jun 28 2026"))
    a100 = " ".join(text_lines(os.path.join(oe, "A202100.txt")))
    check("A202100 的整表公式署名 Zhuorui He，2026-06-29", bool(re.search(r"_?Zhuorui He_?\s*,?\s*Jun 29 2026", a100)))
    check("A202100 修订行为 #18 Jul 06 2026", (rev_line(text_lines(os.path.join(oe, "A202100.txt"))) or "").startswith("#18 Jul 06 2026"))
    proof = open(os.path.join(oe, "A202093_proof_a202093.txt"), encoding="utf-8").read()
    check("Krause 附件含关键引理（s_i=0 ⇒ s_{i+2}=0）", "s_i = 0 implies s_{i+2} = 0" in proof)
    a228 = " ".join(text_lines(os.path.join(oe, "A228285.txt")))
    check("A228285 评论：第 k 列递推阶 F_{k+2}、k≤11 时最小", "F_{k+2}" in a228 and "minimal order" in a228)
    for a in ["A207118", "A207119", "A207120", "A207121", "A207122", "A207069", "A207070", "A326247", "A207123"]:
        new = rev_line(text_lines(os.path.join(oe, a + ".txt")))
        old = rev_line([l.strip() for l in open(p("data", "oeis", a + ".txt"), encoding="utf-8").read().splitlines()])
        check(f"{a} 的修订行与 data/oeis 旧快照相同", new is not None and new == old, f"新 {new} | 旧 {old}")
    a123 = text_lines(os.path.join(oe, "A207123.txt"))
    # 注意 \bproved\b：普通视图页里有 STATUS approved，不能让 approved 里的 proved 误伤
    check("A207123 当前页没有公式行（%F）与「proved」字样", not any(l.startswith("%F") for l in a123) and not any(re.search(r"\bproved\b", l, re.I) for l in a123))

    # E. 读过的论文记录
    rp = open(p("data", "lit", "read_papers.md"), encoding="utf-8").read()
    check("read_papers.md 记录了 9 个 PDF 的 SHA-256（第一次精读 6 篇 + 10-07 第二次 arXiv 复查全文检索 3 篇）", len(re.findall(r"\| [0-9a-f]{64} \|", rp)) == 9)

    # F. 两份公开形式化清单（笔记 §4、§2 Lean 行）
    fl = open(p("data", "lit", "formal_lists_check.md"), encoding="utf-8").read()
    check("formal_lists_check.md：两个仓库都没有命中本家族", len(re.findall(r"\| 无 \|", fl)) == 2 and "截断" not in fl)

    # G. Mathlib（只在本机有 lean/.lake 时检查）
    ml = p("lean", ".lake", "packages", "mathlib", "Mathlib")
    if os.path.isdir(ml):
        pat = re.compile(r"IsDFinite|DFinite|Holonomic|holonomic|P-recursive|PRecursive|D-finite")
        hits = 0
        for dp, dn, fn in os.walk(ml):
            for f in fn:
                if f.endswith(".lean"):
                    hits += len(pat.findall(open(os.path.join(dp, f), encoding="utf-8", errors="ignore").read()))
        check("Mathlib 里 D-finite / holonomic / P-recursive 的出现次数为 0", hits == 0, str(hits))
        check("Mathlib 有单变量的 SkewPolynomial", os.path.exists(os.path.join(ml, "Algebra", "SkewPolynomial", "Basic.lean")))
    else:
        print("SKIP Mathlib 检查：本机没有 lean/.lake/packages/mathlib")

    print("结果：", "全部通过" if not FAILS else f"{len(FAILS)} 项 FAIL：" + "；".join(FAILS))
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
