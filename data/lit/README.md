# data/lit：新颖性文献检索的数据（2026-10-07）

由 `code/novelty/lit_search.py` 与 `code/novelty/cited_by.py` 生成，结论与解读见 `notes/新颖性核查_2026-10-07.md`，手动检索清单见 `notes/新颖性核查_手动检索清单.md`。

| 路径 | 内容 |
|---|---|
| `raw/` | 每条「来源 × 查询」的原始返回（`<来源>__<查询号>.json/xml`）；`.err` 是失败记录（Semantic Scholar 的 429）；`_manifest.jsonl` 记每次请求的时间、状态、字节数 |
| `raw_cites/` | 16 篇种子论文在 OpenAlex 里的前向引用（每个种子一个 JSON） |
| `results.jsonl` | `lit_search.py report` 生成：按题名合并后的候选，每行一篇 |
| `candidates.md` | 同上，Markdown 表，按「命中的查询数、关键词数、年份」排序，前 300 |
| `query_audit.md` | 审计表：每条查询在每个来源取回多少条，或 FAIL 的状态码 |
| `cited_by_candidates.md` | `cited_by.py report` 生成：前向引用的候选，按关键词得分排序，前 150 |
| `read_papers.md` | 精读过的论文：来源、SHA-256、页数、读到什么程度、用到的事实（转述）。PDF 本身不入库 |
| `formal_lists_check.md` | DeepMind formal-conjectures 与 Epoch LeanOpenProblems 两份公开形式化清单的目录树检查（路径名里有没有本家族的编号），含检查时间与树的 SHA |
| `oeis/` | OEIS 条目页（`/A…/internal` 的 HTML）与一份证明附件，2026-10-07 取得；与 `data/oeis/` 的 68 个旧快照分开存放（`check_c5b.py` 要求 `data/oeis/` 里只有那 68 个快照） |

## 数据来源与许可

- OpenAlex（CC0）、Crossref（书目元数据）、arXiv（元数据）、Semantic Scholar（元数据）：只存题名、作者、摘要等元数据，没有存全文。
- StackExchange：只存题名、链接、标签和分数；内容适用 CC BY-SA，没有存正文。
- OEIS：适用 CC-BY-SA 4.0，署名见 `data/oeis/NOTICE.md`；`oeis/A202093_proof_a202093.txt` 是 Christian Krause 在 OEIS 条目 A202093 上挂的证明附件（2026-06-26），按 OEIS 的许可保留。
- 第三方论文的 PDF 没有放进仓库。

## 没覆盖的

Google Scholar、Web of Science、MathSciNet、zbMATH、Scopus、Project Euclid、出版社全文：原因见笔记 §5。Semantic Scholar 只成功 3/55 条查询。arXiv 与 Crossref 只查元数据；OpenAlex 的全文覆盖有限，所以「没找到」的分量比看上去的小。

## 重生成

```bash
py -3.14 code/novelty/lit_search.py report      # 只用本地 raw 重新生成 results.jsonl、candidates.md、query_audit.md
py -3.14 code/novelty/cited_by.py report        # 只用本地 raw_cites 重新生成 cited_by_candidates.md
py -3.14 code/novelty/arxiv_recheck.py run      # 2026-10-07 第二次 arXiv 复查：32 条查询，原始返回在 raw_arxiv_recheck/，汇总 arxiv_recheck.md（已有的 raw 跳过）
py -3.14 code/novelty/check_note_refs.py        # 核对笔记里的 arXiv 号、DOI、OEIS 编号都有数据支持
py -3.14 code/novelty/check_note_facts.py       # 核对笔记里的数字与 OEIS 关键事实能由本目录数据重新证实（不联网）
```

重新取数（联网）：`lit_search.py run` 与 `cited_by.py run`；已存在的原始文件不会重取，加 `--retry-errors`（前者）或 `--force`（后者）才重取。OEIS `robots.txt` 要求 Crawl-Delay 10 秒，取 OEIS 条目页请间隔 10 秒，不要用被 Disallow 的 `/search`。
