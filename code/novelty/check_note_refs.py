# 核对新颖性笔记里出现的每个 arXiv 号、DOI、OEIS 编号，都能在本仓库的检索数据里找到（防止凭印象写出不存在的文献）。
# 证据来源：data/lit/results.jsonl、raw/、raw_cites/、raw_arxiv_recheck/（10-07 第二次 arXiv 复查）、read_papers.md、oeis/，以及 data/oeis/ 的旧快照。
# 找不到的编号打印 FAIL，退出码为 1。只读，不联网。
# 用法：py -3.14 code/novelty/check_note_refs.py [笔记路径 ...]   （默认检查 notes/ 下两份新颖性笔记）
import glob, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DEFAULT_NOTES = ["notes/新颖性核查_2026-10-07.md", "notes/新颖性核查_手动检索清单.md"]


def corpus():
    parts = []
    for pat in ["data/lit/results.jsonl", "data/lit/read_papers.md", "data/lit/raw/*", "data/lit/raw_cites/*.json", "data/lit/raw_arxiv_recheck/*.xml", "data/lit/oeis/*", "data/oeis/*"]:
        for p in glob.glob(os.path.join(ROOT, pat)):
            if os.path.isfile(p):
                parts.append(open(p, encoding="utf-8", errors="ignore").read())
    return "\n".join(parts).lower()


def ids_in(text):
    arx = set(re.findall(r"arxiv[:\s]*([0-9]{4}\.[0-9]{4,5})", text, re.I)) | set(re.findall(r"arxiv[:\s]*([a-z\-]+/[0-9]{7})", text, re.I))
    doi = {d.rstrip(".,;:)）】|") for d in re.findall(r"10\.[0-9]{4,9}/[^\s|`，；）】\]]+", text)}
    oeis = set(re.findall(r"\bA[0-9]{6}\b", text))
    return arx, doi, oeis


def main():
    notes = sys.argv[1:] or DEFAULT_NOTES
    blob = corpus()
    bad = 0
    for n in notes:
        path = os.path.join(ROOT, n)
        if not os.path.exists(path):
            print(f"[skip] {n} 不存在")
            continue
        arx, doi, oeis = ids_in(open(path, encoding="utf-8").read())
        print(f"== {n}: arXiv {len(arx)} 个，DOI {len(doi)} 个，OEIS {len(oeis)} 个")
        for kind, items in (("arXiv", sorted(arx)), ("DOI", sorted(doi)), ("OEIS", sorted(oeis))):
            for i in items:
                ok = i.lower() in blob
                bad += 0 if ok else 1
                if not ok:
                    print(f"  FAIL {kind} {i}：检索数据里没有")
        print("  其余均在数据里找到" if bad == 0 else "  （见上面的 FAIL）")
    print("结果：", "全部通过" if bad == 0 else f"{bad} 个编号缺证据")
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
