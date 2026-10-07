"""Follow-up on the user's Google Scholar results (2026-10-07): bibliographic data and abstracts
of the few new hits, from the official Crossref and OpenAlex APIs (read-only, no e-mail, 1 s apart).

Usage: py -3.14 code/novelty/scholar_followup.py
Raw JSON goes to data/lit/raw_scholar_followup/; a summary is printed.
"""
import json, os, time, urllib.parse, urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RAW = os.path.join(ROOT, "data", "lit", "raw_scholar_followup")
UA = {"User-Agent": "a207123-novelty-check/1.0 (read-only literature check)"}

QUERIES = [
    ("crossref_dbs24", "https://api.crossref.org/works/10.1145/3717582.3717589"),
    ("crossref_kauers23_book", "https://api.crossref.org/works/10.1007/978-3-031-34652-1"),
    ("crossref_cmst14", "https://api.crossref.org/works?rows=3&query.bibliographic="
     + urllib.parse.quote("A computer-algebra-based formal proof of the irrationality of zeta(3) Chyzak Mahboubi Sibut-Pinote Tassi")),
    ("openalex_kmv05", "https://api.openalex.org/works?per-page=3&search="
     + urllib.parse.quote("Pattern avoidance in matrices Kitaev Mansour Vella")),
    ("openalex_db_thesis", "https://api.openalex.org/works?per-page=3&search="
     + urllib.parse.quote("Experimental Methods in Number Theory and Combinatorics Dougherty-Bliss")),
    ("crossref_kauers25_survey", "https://api.crossref.org/works?rows=3&query.bibliographic="
     + urllib.parse.quote("D-finiteness: a success story Kauers")),
]


def get(url):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=40) as r:
        return json.loads(r.read().decode("utf-8"))


def abstract_from_inverted(inv):
    if not inv:
        return ""
    pos = {}
    for w, idx in inv.items():
        for i in idx:
            pos[i] = w
    return " ".join(pos[i] for i in sorted(pos))


def show_crossref(item):
    a = ", ".join((p.get("given", "") + " " + p.get("family", "")).strip() for p in item.get("author", []))
    year = (item.get("issued", {}).get("date-parts") or [[None]])[0][0]
    print("  title :", " ".join(item.get("title", [""])))
    print("  author:", a)
    print("  where :", " ".join(item.get("container-title", [""])), "| vol", item.get("volume"), "| issue",
          item.get("issue"), "| pages", item.get("page"), "| year", year, "| type", item.get("type"))
    print("  doi   :", item.get("DOI"), "| publisher:", item.get("publisher"))
    if item.get("abstract"):
        print("  abstract:", item["abstract"][:700].replace("\n", " "))


def show_openalex(w):
    a = ", ".join(x["author"]["display_name"] for x in w.get("authorships", []))
    b = w.get("biblio", {})
    src = ((w.get("primary_location") or {}).get("source") or {}).get("display_name")
    print("  title :", w.get("display_name"))
    print("  author:", a)
    print("  where :", src, "| vol", b.get("volume"), "| issue", b.get("issue"), "| pages",
          b.get("first_page"), "-", b.get("last_page"), "| year", w.get("publication_year"), "| type", w.get("type"))
    print("  doi   :", w.get("doi"), "| id:", w.get("id"))
    ab = abstract_from_inverted(w.get("abstract_inverted_index"))
    if ab:
        print("  abstract:", ab[:900])


def main():
    os.makedirs(RAW, exist_ok=True)
    for name, url in QUERIES:
        print("==", name)
        try:
            data = get(url)
        except Exception as e:  # report and continue
            print("  ERROR:", e)
            time.sleep(1)
            continue
        json.dump(data, open(os.path.join(RAW, name + ".json"), "w", encoding="utf-8"), ensure_ascii=False, indent=1)
        if name.startswith("crossref"):
            msg = data.get("message", {})
            items = msg.get("items") if "items" in msg else [msg]
            for it in items[:3]:
                show_crossref(it)
                print("  --")
        else:
            for w in data.get("results", [])[:3]:
                show_openalex(w)
                print("  --")
        time.sleep(1)


if __name__ == "__main__":
    main()
