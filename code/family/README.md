# 同列规则的 Hardin 表：归约是否通用（2026-10-06）

**为什么做**：讨论发表路线时想确认，T1.0 的归约 a_k(n)=U_k(⌈n/2⌉)·U_k(⌊n/2⌋) 是不是 A207123 特有的。
它只用到列规则（竖向禁止 001、011 ⇔ 每列 b_i ≥ b_{i+2}），行规则是什么都不影响。所以凡是竖向规则相同的表，都应满足
T(n,k)=Z_k(⌈n/2⌉)·Z_k(⌊n/2⌋)，其中 Z_k(m) 是允许行偏序集（逐分量序）里弱降 m 元组的个数，即它的 zeta 多项式取值。

**结果**：OEIS 里竖向规则为「0 0 1 and 0 1 1」的二维表共 6 张，全部吻合（`check_family.log`）。

| 表 | 横向禁止 | 核对 |
|---|---|---|
| A207123 | 001、010 | 54/54 项 |
| A207368 | 000、011 | 55/56 项（有 1 项超出 k≤10 的核对窗口） |
| A208013 | 000、101 | 55/56 项（同上） |
| A208069 | 000、111 | 55/55 项 |
| A208118 | 000、010 | 54/54 项 |
| A208555 | 000、001 | 52/52 项 |

另外按原始定义对 n≤4、k≤3 暴力计数，6 张表都一致（核对约定与反对角线读法）。

**等级**：归约本身证明很短（同 T1.0），这里只是用 OEIS 数据核对了它对另外 5 张表的适用性。另外 5 张表的 Z_k(m) 有没有引理 1 那样的三项递推、显式公式或非 D-finite 性，都**没有研究**。

**OEIS 只读查询**（curl，UTC 2026-10-06 15:32 前后，每个 URL 一次，没有发帖、提交或联系任何人）

| 快照 | URL | 结果 |
|---|---|---|
| `oeis_search_vertical_001_011_tabl.txt` | https://oeis.org/search?q=%220+0+1+and+0+1+1+vertically%22+keyword%3Atabl&fmt=text | Showing 1-6 of 6 |
| `oeis_search_vertical_001_011_all_p1.txt` | https://oeis.org/search?q=%220+0+1+and+0+1+1+vertically%22&fmt=text | Showing 1-10 of 62（只取了第 1 页，用来看总数：6 张表加它们的行列序列共 62 个条目） |
| `oeis_search_vertical_100_110_tabl.txt` | https://oeis.org/search?q=%221+0+0+and+1+1+0+vertically%22+keyword%3Atabl&fmt=text | No results（镜像规则没有表） |
| `oeis_A207123_recheck.txt` | https://oeis.org/search?q=id:A207123&fmt=text | 去掉 # 开头的抬头行后与 `data/oeis/A207123.txt`（2026-10-04 快照）逐行相同：条目没有新增证明或评论 |

这些快照**故意不放进 `data/oeis/`**：`code/checks/check_c5b.py` 的 `c5b.snapshots` 要求那个目录里只有日志记录的 68 个快照（加 INDEX.md 与许可说明 NOTICE.md）。

**重跑**：在任务 C 根目录 `py -3.14 code/family/check_family.py`（只用标准库，不联网；全部 PASS 时退出码 0）。
