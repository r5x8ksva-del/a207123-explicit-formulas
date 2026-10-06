# arXiv 复查（只读，2026-10-07 第二次）：在第一次系统检索（lit_search.py，55 条查询、按相关度取前 20）之后，
# 只用 arXiv 官方 API 再查一遍，补两类盲区：
#   (1) 按提交日期倒序的「最新」查询——看有没有人刚好发了这一族数组、Stirling-like / 零化理想、AI 证 OEIS 猜想的新文章（被抢先风险）；
#   (2) 针对 10-07 新增结论的精确查询——T3.9（不是 Stirling-like，牛顿多边形）、T2.6(ii)（单和不存在的留数–范数论证）、
#       T3.8（四项递推的零化理想）、块分解与 r-Stirling 显式式。
# 原始返回存 data/lit/raw_arxiv_recheck/（每条查询一个 xml），汇总表由同一脚本从 raw 重新生成：data/lit/arxiv_recheck.md。
# 与 lit_search.py 的结果分开存放，不改动第一次检索的 results.jsonl / candidates.md（笔记里引用了那些计数）。
# 请求间隔 >= 3.2 s（arXiv API 要求 >= 3 s），不带邮箱、不登录。arXiv API 只检索题名、摘要、作者等元数据，不含全文。
# 用法：py -3.14 code/novelty/arxiv_recheck.py run      # 取数（已有的 raw 跳过；加 --force 重取）
#       py -3.14 code/novelty/arxiv_recheck.py report   # 从 raw 生成 data/lit/arxiv_recheck.md
import os
import re
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
RAW = os.path.join(ROOT, 'data', 'lit', 'raw_arxiv_recheck')
OUT = os.path.join(ROOT, 'data', 'lit', 'arxiv_recheck.md')
UA = 'novelty-check/1.0 (read-only literature lookup)'
NS = {'a': 'http://www.w3.org/2005/Atom', 'x': 'http://arxiv.org/schemas/atom'}
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

# (id, 目的, arXiv 检索式, 排序 date/relevance, 条数)
QUERIES = [
    # ---- (1) 最新：被抢先风险 ----
    ('new01', '最新：Hardin 的表', 'all:Hardin', 'date', 50),
    ('new02', '最新：OEIS 猜想的证明', 'abs:OEIS AND (abs:conjecture OR abs:conjectures OR abs:conjectured)', 'date', 100),
    ('new03', '最新：0-1 数组/矩阵避开模式', '(abs:"binary arrays" OR abs:"0-1 arrays" OR abs:"binary matrices" OR abs:"01-matrices") AND (abs:avoiding OR abs:pattern OR abs:patterns OR abs:forbidden)', 'date', 50),
    ('new04', '最新：Stirling 型数与零化子/递推', 'abs:Stirling AND (abs:annihilator OR abs:annihilating OR abs:holonomic OR abs:"D-finite" OR abs:Ore)', 'date', 50),
    ('new05', '最新：Stirling-like', 'abs:"Stirling-like" OR abs:"Stirling like"', 'date', 50),
    ('new06', '最新：非 D-finite 的二元序列', '(abs:"not D-finite" OR abs:"non-D-finite" OR abs:"non-holonomic" OR abs:nonholonomic) AND abs:sequence', 'date', 50),
    ('new07', '最新：AI/Lean 证 OEIS', '(abs:OEIS) AND (abs:Lean OR abs:"language model" OR abs:"language models" OR abs:LLM OR abs:AI)', 'date', 50),
    ('new08', '最新：math.CO 里提到 OEIS 的', 'cat:math.CO AND abs:OEIS', 'date', 100),
    ('new09', '最新：Kauers', 'au:Kauers', 'date', 40),
    ('new10', '最新：Koutschan', 'au:Koutschan', 'date', 30),
    ('new11', '最新：Dougherty-Bliss（下划线写法，0 命中，保留作记录）', 'au:Dougherty_Bliss', 'date', 20),
    ('new11b', '最新：Dougherty-Bliss（拆开写法，0 命中，保留作记录）', 'au:Dougherty AND au:Bliss', 'date', 30),
    ('new11c', '最新：Dougherty-Bliss', 'au:"Dougherty-Bliss"', 'date', 30),
    ('x01', '最新：二维模式避免（数组/矩阵）', '(abs:"pattern avoidance" OR abs:"pattern-avoiding" OR abs:"avoiding patterns") AND (abs:"two-dimensional" OR abs:arrays OR abs:matrices)', 'date', 50),
    ('x02', '最新：zeta 多项式', 'abs:"zeta polynomial" OR abs:"zeta polynomials"', 'date', 40),
    ('x03', 'T3.8/T3.9：Stirling 数的零化子', 'abs:Stirling AND (abs:annihilator OR abs:annihilators OR abs:"annihilating operator")', 'relevance', 30),
    ('x05_fried', '找 Fried 的 OEIS 猜想证明系列（第一种写法）', 'au:Fried AND abs:OEIS', 'date', 20),
    ('x06_fried', '找 Fried 的 OEIS 猜想证明系列（补全）', 'au:Fried AND (ti:conjectures OR ti:OEIS OR abs:"Integer Sequences")', 'date', 30),
    ('x04', '最新：二进制数组的行列禁止模式', '(abs:"rows and columns" OR abs:"each row" OR abs:"every row") AND (abs:forbidden OR abs:avoid OR abs:avoiding OR abs:avoids) AND (abs:binary OR abs:"0-1")', 'date', 50),
    ('new12', '最新：Zeilberger', 'au:Zeilberger', 'date', 40),
    # ---- (2) 针对新结论 ----
    ('t39a', 'T3.9：牛顿多边形与递推算子', 'abs:"Newton polygon" AND (abs:recurrence OR abs:annihilator OR abs:"Ore algebra" OR abs:operator)', 'relevance', 30),
    ('t39b', 'T3.9/T3.8：二元序列的零化理想由一条递推生成', '(abs:annihilator OR abs:"annihilating ideal") AND (abs:bivariate OR abs:"two-dimensional" OR abs:"two variables") AND abs:recurrence', 'relevance', 30),
    ('t39c', 'T3.8：Ore 代数左理想、象限、饱和', 'abs:"Ore algebra" AND (abs:quadrant OR abs:saturation OR abs:contraction)', 'relevance', 30),
    ('t38a', 'T3.8：四项/三角递推的零化子分类', '(abs:"triangular recurrence" OR abs:"triangle recurrence") AND (abs:annihilator OR abs:ideal OR abs:holonomic)', 'relevance', 30),
    ('t26a', 'T2.6：Stirling×二项式单和不存在', 'abs:Stirling AND (abs:"single sum" OR abs:"no closed form" OR abs:"closed form") AND abs:binomial', 'relevance', 30),
    ('t26b', 'T2.6：留数与范数证明不存在某类公式', '(abs:residue OR abs:residues) AND abs:norm AND (abs:"generating function" OR abs:sum)', 'relevance', 30),
    ('t24a', 'T2.4：r-Stirling 与模式/词的计数', 'abs:"r-Stirling" AND (abs:words OR abs:patterns OR abs:sequences OR abs:arrays)', 'relevance', 30),
    ('t24b', 'T2.4：块分解计数高度序列', '(abs:"height sequences" OR abs:"height sequence") AND (abs:Stirling OR abs:patterns OR abs:enumeration)', 'relevance', 30),
    ('t10a', 'T1.0：允许行偏序集与 zeta 多项式', 'abs:"zeta polynomial" AND (abs:words OR abs:arrays OR abs:matrices)', 'relevance', 30),
    ('t13a', 'T1.3：y^3=y^2+m、P_m 型分母', '(abs:"1-x-mx^3" OR abs:"x^3=x^2+m" OR abs:"y^3=y^2+m") OR (abs:Narayana AND abs:generalized AND abs:recurrence)', 'relevance', 30),
    ('t41a', 'T4.1：三角的近对角线是多项式', '(abs:"near-diagonal" OR abs:"near diagonal" OR abs:subdiagonal OR abs:diagonals) AND abs:polynomial AND (abs:Stirling OR abs:triangle)', 'relevance', 30),
    ('t29a', 'T1.9：OEIS 列递推（Barker 猜想）被证明', 'abs:Barker AND abs:OEIS', 'relevance', 30),
]


def url(q):
    sort = 'submittedDate' if q[3] == 'date' else 'relevance'
    params = {'search_query': q[2], 'start': 0, 'max_results': q[4], 'sortBy': sort, 'sortOrder': 'descending'}
    return 'https://export.arxiv.org/api/query?' + urllib.parse.urlencode(params, quote_via=urllib.parse.quote)


def run(force):
    os.makedirs(RAW, exist_ok=True)
    last = 0.0
    for q in QUERIES:
        path = os.path.join(RAW, q[0] + '.xml')
        if os.path.exists(path) and not force:
            print('skip', q[0])
            continue
        for attempt in range(3):
            wait = 3.2 - (time.time() - last)
            if wait > 0:
                time.sleep(wait)
            last = time.time()
            try:
                req = urllib.request.Request(url(q), headers={'User-Agent': UA})
                with urllib.request.urlopen(req, timeout=60) as r:
                    data = r.read()
                ET.fromstring(data)          # 确认是完整的 XML 再存
                with open(path, 'wb') as f:
                    f.write(data)
                print('ok', q[0], len(data), 'bytes')
                break
            except Exception as e:
                print('retry', q[0], attempt, str(e)[:80])
                time.sleep(6 * (attempt + 1))
        else:
            print('FAILED', q[0])


def entries(path):
    root = ET.parse(path).getroot()
    total = root.find('{http://a9.com/-/spec/opensearch/1.1/}totalResults')
    out = []
    for e in root.findall('a:entry', NS):
        aid = e.find('a:id', NS).text.rsplit('/abs/', 1)[-1]
        title = ' '.join(e.find('a:title', NS).text.split())
        abstract = ' '.join(e.find('a:summary', NS).text.split())
        pub = e.find('a:published', NS).text[:10]
        upd = e.find('a:updated', NS).text[:10]
        authors = [a.find('a:name', NS).text for a in e.findall('a:author', NS)]
        cats = [c.get('term') for c in e.findall('a:category', NS)]
        out.append(dict(id=aid, title=title, abstract=abstract, published=pub, updated=upd, authors=authors, cats=cats))
    return (int(total.text) if total is not None else None), out


def report():
    rows, seen = [], {}
    lines = ['# arXiv 复查（2026-10-07 第二次，只读）', '',
             '由 `code/novelty/arxiv_recheck.py` 从 `data/lit/raw_arxiv_recheck/` 生成。arXiv API 只检索元数据（题名、摘要、作者），不含全文。', '',
             '| 查询 | 目的 | 排序 | 命中总数 | 取回 | 检索式 |', '|---|---|---|---|---|---|']
    for q in QUERIES:
        path = os.path.join(RAW, q[0] + '.xml')
        if not os.path.exists(path):
            lines.append('| %s | %s | %s | 缺 | 0 | `%s` |' % (q[0], q[1], q[3], q[2]))
            continue
        total, es = entries(path)
        lines.append('| %s | %s | %s | %s | %d | `%s` |' % (q[0], q[1], q[3], total, len(es), q[2].replace('|', '\\|')))
        for e in es:
            if e['id'] not in seen:
                seen[e['id']] = dict(e, queries=[q[0]])
                rows.append(seen[e['id']])
            else:
                seen[e['id']]['queries'].append(q[0])
    rows.sort(key=lambda e: e['published'], reverse=True)
    lines += ['', '## 全部取回的文章（%d 篇，按首次提交日期倒序）' % len(rows), '',
              '| arXiv | 提交 | 题名 | 作者 | 命中的查询 |', '|---|---|---|---|---|']
    for e in rows:
        au = ', '.join(e['authors'][:4]) + (' 等' if len(e['authors']) > 4 else '')
        lines.append('| %s | %s | %s | %s | %s |' % (e['id'], e['published'], e['title'].replace('|', '/'), au, ' '.join(e['queries'])))
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(lines) + '\n')
    print('wrote', OUT, len(rows), 'papers')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'report'
    if cmd == 'run':
        run('--force' in sys.argv)
    report()
