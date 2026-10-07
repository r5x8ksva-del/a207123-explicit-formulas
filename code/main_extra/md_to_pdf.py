"""Render a Markdown note from notes/ to PDF with headless Edge (nothing is downloaded).

Usage:
    py -3.14 code/main_extra/md_to_pdf.py <in.md> <out.pdf> [--label <source label>] [--html <keep.html>]

Supports the subset used in this project's notes: # headings, paragraphs, > quotes,
"- " and "1. " lists, pipe tables, ``` code blocks, **bold**, *italic*, `code`
(code spans that are http(s) URLs become links; scholar.google.com and zbmath.org are linked).
Fonts: Microsoft YaHei for Chinese, Consolas for code. Links stay clickable in the PDF.
"""
import argparse, datetime, html, os, re, shutil, subprocess, tempfile, time, urllib.parse

EDGE_CANDIDATES = [
    r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
    r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
]

CSS = """
@page { size: A4; margin: 16mm 15mm 16mm 15mm; }
body { font-family: "Microsoft YaHei", "SimSun", sans-serif; font-size: 10.5pt; line-height: 1.6; color: #1a1a1a; }
h1 { font-size: 16.5pt; margin: 0 0 10pt; line-height: 1.35; }
h2 { font-size: 13.5pt; margin: 16pt 0 6pt; padding-bottom: 3pt; border-bottom: 1px solid #ccc; break-after: avoid; }
h3 { font-size: 11.5pt; margin: 12pt 0 4pt; break-after: avoid; }
p { margin: 5pt 0; }
blockquote { margin: 8pt 0; padding: 6pt 10pt; background: #f4f6f8; border-left: 3px solid #8aa1b8; }
blockquote p { margin: 3pt 0; }
code { font-family: Consolas, "Microsoft YaHei", monospace; font-size: 9.5pt; background: #f0f0f0; padding: 0 2pt; border-radius: 2px; overflow-wrap: anywhere; }
pre { background: #f6f6f6; border: 1px solid #ddd; padding: 7pt 9pt; white-space: pre-wrap; overflow-wrap: anywhere; font-size: 9pt; line-height: 1.45; break-inside: avoid; }
pre code { background: none; padding: 0; font-size: 9pt; }
table { border-collapse: collapse; width: 100%; margin: 6pt 0; font-size: 9.5pt; }
th, td { border: 1px solid #bbb; padding: 4pt 6pt; vertical-align: top; text-align: left; }
th { background: #eef1f4; }
tr { break-inside: avoid; }
ol, ul { margin: 4pt 0; padding-left: 20pt; }
li { margin: 2pt 0; }
a { color: #0b5cad; text-decoration: none; }
.source { font-size: 8.5pt; color: #777; margin-bottom: 8pt; }
"""


def inline(text):
    codes = []

    def stash(m):
        codes.append(m.group(1))
        return "\x00%d\x00" % (len(codes) - 1)

    text = re.sub(r"`([^`]+)`", stash, text)
    text = html.escape(text, quote=False)
    text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<em>\1</em>", text)
    text = re.sub(r"\b(scholar\.google\.com|zbmath\.org)\b", r'<a href="https://\1/">\1</a>', text)

    def unstash(m):
        c = codes[int(m.group(1))]
        e = html.escape(c, quote=False)
        if re.match(r"https?://", c):
            return '<a href="%s"><code>%s</code></a>' % (html.escape(c), e)
        return "<code>%s</code>" % e

    return re.sub(r"\x00(\d+)\x00", unstash, text)


def cells(row):
    return [c.strip() for c in row.strip().strip("|").split("|")]


def convert(md):
    lines = md.splitlines()
    out, para = [], []
    i = 0

    def flush():
        if para:
            out.append("<p>" + "<br>".join(inline(x) for x in para) + "</p>")
            para.clear()

    while i < len(lines):
        s = lines[i].strip()
        if s.startswith("```"):
            flush()
            j, buf = i + 1, []
            while j < len(lines) and not lines[j].strip().startswith("```"):
                buf.append(lines[j])
                j += 1
            out.append("<pre><code>" + html.escape("\n".join(buf), quote=False) + "</code></pre>")
            i = j + 1
            continue
        m = re.match(r"(#{1,6})\s+(.*)", s)
        if m:
            flush()
            n = len(m.group(1))
            out.append("<h%d>%s</h%d>" % (n, inline(m.group(2)), n))
            i += 1
            continue
        if s.startswith(">"):
            flush()
            buf = []
            while i < len(lines) and lines[i].strip().startswith(">"):
                buf.append(lines[i].strip()[1:].strip())
                i += 1
            out.append("<blockquote>" + "".join("<p>%s</p>" % inline(b) for b in buf if b) + "</blockquote>")
            continue
        if s.startswith("|") and i + 1 < len(lines) and re.match(r"^\|?\s*:?-{3,}", lines[i + 1].strip()):
            flush()
            head = cells(s)
            i += 2
            rows = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                rows.append(cells(lines[i]))
                i += 1
            t = ["<table><thead><tr>" + "".join("<th>%s</th>" % inline(c) for c in head) + "</tr></thead><tbody>"]
            for r in rows:
                t.append("<tr>" + "".join("<td>%s</td>" % inline(c) for c in r) + "</tr>")
            t.append("</tbody></table>")
            out.append("".join(t))
            continue
        m_ol = re.match(r"(\d+)\.\s+(.*)", s)
        m_ul = re.match(r"-\s+(.*)", s)
        if m_ol or m_ul:
            flush()
            tag = "ol" if m_ol else "ul"
            pat = r"(\d+)\.\s+(.*)" if m_ol else r"-\s+(.*)"
            start = int(m_ol.group(1)) if m_ol else 1
            items = []
            while i < len(lines):
                mm = re.match(pat, lines[i].strip())
                if not mm:
                    break
                items.append(mm.group(mm.lastindex))
                i += 1
            attr = ' start="%d"' % start if start != 1 else ""
            out.append("<%s%s>" % (tag, attr) + "".join("<li>%s</li>" % inline(x) for x in items) + "</%s>" % tag)
            continue
        if not s:
            flush()
            i += 1
            continue
        para.append(s)
        i += 1
    flush()
    return "\n".join(out)


def build_html(md_path, label):
    md = open(md_path, encoding="utf-8").read()
    first = next((l for l in md.splitlines() if l.startswith("# ")), "# " + os.path.basename(md_path))
    title = html.escape(first[2:].strip())
    src = '<div class="source">%s</div>' % html.escape(label) if label else ""
    return ('<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><title>%s</title>'
            "<style>%s</style></head><body>%s%s</body></html>" % (title, CSS, src, convert(md)))


def print_pdf(html_text, pdf_path, keep_html=None):
    edge = next((p for p in EDGE_CANDIDATES if os.path.exists(p)), None)
    if edge is None:
        raise SystemExit("msedge.exe not found")
    work = tempfile.mkdtemp(prefix="md2pdf-")
    try:
        hp = os.path.join(work, "page.html")
        open(hp, "w", encoding="utf-8").write(html_text)
        if keep_html:
            shutil.copyfile(hp, keep_html)
        tmp_pdf = os.path.join(work, "out.pdf")
        url = "file:///" + urllib.parse.quote(hp.replace(os.sep, "/"), safe="/:")
        cmd = [edge, "--headless", "--disable-gpu", "--no-first-run", "--no-default-browser-check",
               "--user-data-dir=" + os.path.join(work, "profile"), "--no-pdf-header-footer",
               "--print-to-pdf-no-header", "--print-to-pdf=" + tmp_pdf, url]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
        # msedge.exe hands the job to a background process and returns at once (~0.1 s);
        # the PDF appears a few seconds later, so wait until the file is complete and stable.
        deadline, last = time.time() + 120, -1
        while time.time() < deadline:
            size = os.path.getsize(tmp_pdf) if os.path.exists(tmp_pdf) else -1
            if size > 0 and size == last:
                with open(tmp_pdf, "rb") as f:
                    f.seek(max(0, size - 1024))
                    if f.read().rstrip().endswith(b"%%EOF"):
                        break
            last = size
            time.sleep(1)
        else:
            raise SystemExit("Edge did not write the PDF (exit %s): %s" % (r.returncode, r.stderr[-800:]))
        shutil.copyfile(tmp_pdf, pdf_path)
    finally:
        time.sleep(2)  # let the background Edge process release its profile before cleanup
        shutil.rmtree(work, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("md")
    ap.add_argument("pdf")
    ap.add_argument("--label", default=None)
    ap.add_argument("--html", default=None)
    a = ap.parse_args()
    label = a.label
    if label is None:
        label = "来源：%s · 转成 PDF：%s" % (a.md.replace(os.sep, "/"), datetime.date.today().isoformat())
    print_pdf(build_html(a.md, label), a.pdf, a.html)
    print("wrote", a.pdf)


if __name__ == "__main__":
    main()
