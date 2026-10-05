# OEIS 只读快照索引（c5b）

- 方式：Git Bash 下 `curl` 直接访问 oeis.org（条目 `search?q=id:A......&fmt=text`、搜索 `search?q=<逗号分隔项>&fmt=text`、b 文件 `/A....../b......txt`）；未使用 agent-reach 或任何第三方代理；没有发帖、提交或联系任何人。
- 每个 URL 只取一次（`code/c5b/fetch.sh` 先查 `logs/c5b_fetch.log`，出现过即跳过），请求间隔 2 秒。
- 总请求数：68（上限 80），全部 HTTP 200。
- 搜索项全部由 `code/c5b/build_list2.py`、`build_list5.py` 从 core 高度 DP 结果程序化生成（见 `code/c5b/search_terms.json`），没有手抄。
- OEIS 的逗号分隔搜索要求各项按给定顺序**相邻**出现（按绝对值匹配，故带符号版本也会命中）。
- 解读、证明与结论等级见 `notes/c5b.md`；离线核对见 `code/checks/check_c5b.py`（不联网，只读本目录快照）。

| # | 时间 (UTC) | 快照文件 | 查询 URL | HTTP | 字节 | 内容 | 结果 |
|---|---|---|---|---|---|---|---|
| 1 | 2026-10-04T10:15:37Z | `A207118.txt` | https://oeis.org/search?q=id:A207118&fmt=text | 200 | 1751 | 条目原文 A207118：n×3 数组（A207123 第 3 列） | Showing 1-1 of 1；命中：A207118 |
| 2 | 2026-10-04T10:15:39Z | `A207119.txt` | https://oeis.org/search?q=id:A207119&fmt=text | 200 | 1339 | 条目原文 A207119：n×4（第 4 列） | Showing 1-1 of 1；命中：A207119 |
| 3 | 2026-10-04T10:15:41Z | `A207120.txt` | https://oeis.org/search?q=id:A207120&fmt=text | 200 | 1383 | 条目原文 A207120：n×5（第 5 列） | Showing 1-1 of 1；命中：A207120 |
| 4 | 2026-10-04T10:15:44Z | `A207121.txt` | https://oeis.org/search?q=id:A207121&fmt=text | 200 | 1483 | 条目原文 A207121：n×6（第 6 列） | Showing 1-1 of 1；命中：A207121 |
| 5 | 2026-10-04T10:15:46Z | `A207122.txt` | https://oeis.org/search?q=id:A207122&fmt=text | 200 | 1519 | 条目原文 A207122：n×7（第 7 列） | Showing 1-1 of 1；命中：A207122 |
| 6 | 2026-10-04T10:15:48Z | `A207123.txt` | https://oeis.org/search?q=id:A207123&fmt=text | 200 | 2008 | 条目原文 A207123：二维表 T(n,k) | Showing 1-1 of 1；命中：A207123 |
| 7 | 2026-10-04T10:15:50Z | `A038718.txt` | https://oeis.org/search?q=id:A038718&fmt=text | 200 | 1995 | 条目原文 A038718：R_k 候选（第 1 行） | Showing 1-1 of 1；命中：A038718 |
| 8 | 2026-10-04T10:15:52Z | `A084990.txt` | https://oeis.org/search?q=id:A084990&fmt=text | 200 | 3629 | 条目原文 A084990：U_3 候选 | Showing 1-1 of 1；命中：A084990 |
| 9 | 2026-10-04T10:15:54Z | `A326247.txt` | https://oeis.org/search?q=id:A326247&fmt=text | 200 | 2037 | 条目原文 A326247：U_4 候选 | Showing 1-1 of 1；命中：A326247 |
| 10 | 2026-10-04T10:15:57Z | `b207118.txt` | https://oeis.org/A207118/b207118.txt | 200 | 2901 | b 文件 A207118 | n=1..210（210 项） |
| 11 | 2026-10-04T10:15:59Z | `b207119.txt` | https://oeis.org/A207119/b207119.txt | 200 | 3359 | b 文件 A207119 | n=1..210（210 项） |
| 12 | 2026-10-04T10:16:01Z | `b207120.txt` | https://oeis.org/A207120/b207120.txt | 200 | 3811 | b 文件 A207120 | n=1..210（210 项） |
| 13 | 2026-10-04T10:16:03Z | `b207121.txt` | https://oeis.org/A207121/b207121.txt | 200 | 4250 | b 文件 A207121 | n=1..210（210 项） |
| 14 | 2026-10-04T10:16:05Z | `b207122.txt` | https://oeis.org/A207122/b207122.txt | 200 | 4666 | b 文件 A207122 | n=1..210（210 项） |
| 15 | 2026-10-04T10:16:08Z | `b207123.txt` | https://oeis.org/A207123/b207123.txt | 200 | 8104 | b 文件 A207123 | n=1..545（545 项） |
| 16 | 2026-10-04T10:16:10Z | `b038718.txt` | https://oeis.org/A038718/b038718.txt | 200 | 3049690 | b 文件 A038718 | n=1..6023（6023 项） |
| 17 | 2026-10-04T10:16:12Z | `b084990.txt` | https://oeis.org/A084990/b084990.txt | 200 | 12663 | b 文件 A084990 | n=0..1000（1001 项） |
| 18 | 2026-10-04T10:16:14Z | `b326247.txt` | https://oeis.org/A326247/b326247.txt | 200 | 381 | b 文件 A326247 | n=0..40（41 项） |
| 19 | 2026-10-04T10:22:25Z | `search_U3_m0.txt` | https://oeis.org/search?q=1,6,17,36,65,106,161,232,321&fmt=text | 200 | 3651 | U_3(m), m=0..8 | Showing 1-1 of 1；命中：A084990 |
| 20 | 2026-10-04T10:22:27Z | `search_U3_m2.txt` | https://oeis.org/search?q=17,36,65,106,161,232,321,430,561&fmt=text | 200 | 3655 | U_3(m), m=2..10 | Showing 1-1 of 1；命中：A084990 |
| 21 | 2026-10-04T10:22:29Z | `search_U4_m0.txt` | https://oeis.org/search?q=1,9,32,80,165,301,504,792,1185&fmt=text | 200 | 2061 | U_4(m), m=0..8 | Showing 1-1 of 1；命中：A326247 |
| 22 | 2026-10-04T10:22:31Z | `search_U4_m2.txt` | https://oeis.org/search?q=32,80,165,301,504,792,1185,1705,2376&fmt=text | 200 | 2067 | U_4(m), m=2..10 | Showing 1-1 of 1；命中：A326247 |
| 23 | 2026-10-04T10:22:33Z | `search_U5_m0.txt` | https://oeis.org/search?q=1,14,64,192,457,938,1736,2976&fmt=text | 200 | 227 | U_5(m), m=0..7 | No results.；命中：无 |
| 24 | 2026-10-04T10:22:36Z | `search_U5_m1.txt` | https://oeis.org/search?q=14,64,192,457,938,1736,2976,4809&fmt=text | 200 | 230 | U_5(m), m=1..8 | No results.；命中：无 |
| 25 | 2026-10-04T10:22:38Z | `search_U5_m2.txt` | https://oeis.org/search?q=64,192,457,938,1736,2976,4809,7414&fmt=text | 200 | 232 | U_5(m), m=2..9 | No results.；命中：无 |
| 26 | 2026-10-04T10:22:40Z | `search_U6_m0.txt` | https://oeis.org/search?q=1,21,119,419,1136,2604,5306,9906&fmt=text | 200 | 230 | U_6(m), m=0..7 | No results.；命中：无 |
| 27 | 2026-10-04T10:22:42Z | `search_U6_m1.txt` | https://oeis.org/search?q=21,119,419,1136,2604,5306,9906,17283&fmt=text | 200 | 234 | U_6(m), m=1..8 | No results.；命中：无 |
| 28 | 2026-10-04T10:22:44Z | `search_U6_m2.txt` | https://oeis.org/search?q=119,419,1136,2604,5306,9906,17283,28567&fmt=text | 200 | 237 | U_6(m), m=2..9 | No results.；命中：无 |
| 29 | 2026-10-04T10:22:47Z | `search_U7_m0.txt` | https://oeis.org/search?q=1,31,214,873,2669,6778,15108,30558&fmt=text | 200 | 232 | U_7(m), m=0..7 | No results.；命中：无 |
| 30 | 2026-10-04T10:22:49Z | `search_U7_m1.txt` | https://oeis.org/search?q=31,214,873,2669,6778,15108,30558,57321&fmt=text | 200 | 236 | U_7(m), m=1..8 | No results.；命中：无 |
| 31 | 2026-10-04T10:22:51Z | `search_U7_m2.txt` | https://oeis.org/search?q=214,873,2669,6778,15108,30558,57321,101233&fmt=text | 200 | 240 | U_7(m), m=2..9 | No results.；命中：无 |
| 32 | 2026-10-04T10:22:53Z | `search_R.txt` | https://oeis.org/search?q=2,4,6,9,14,21,31,46,68,100,147,216&fmt=text | 200 | 2023 | R_k=U_k(1), k=1..12 | Showing 1-1 of 1；命中：A038718 |
| 33 | 2026-10-04T10:22:55Z | `search_Uk2.txt` | https://oeis.org/search?q=9,17,32,64,119,214,388,694,1222,2145&fmt=text | 200 | 234 | U_k(2), k=2..11 | No results.；命中：无 |
| 34 | 2026-10-04T10:22:57Z | `search_Uk3.txt` | https://oeis.org/search?q=16,36,80,192,419,873,1837,3788,7629,15285&fmt=text | 200 | 239 | U_k(3), k=2..11 | No results.；命中：无 |
| 35 | 2026-10-04T10:23:00Z | `search_Uk4.txt` | https://oeis.org/search?q=25,65,165,457,1136,2669,6334,14666,32971,73592&fmt=text | 200 | 244 | U_k(4), k=2..11 | No results.；命中：无 |
| 36 | 2026-10-04T10:23:02Z | `search_Udiag.txt` | https://oeis.org/search?q=1,2,9,36,165,938,5306,30558,190509,1229052&fmt=text | 200 | 240 | U_k(k), k=0..9 | No results.；命中：无 |
| 37 | 2026-10-04T10:23:04Z | `search_Nflat.txt` | https://oeis.org/search?q=1,1,2,1,4,2,1,7,8,2,1,12,25,16,2,1,19,59,65,26,2&fmt=text | 200 | 246 | N(k,q) rows q=1..k, k=1..6 | No results.；命中：无 |
| 38 | 2026-10-04T10:23:06Z | `search_Nflat_rev.txt` | https://oeis.org/search?q=1,2,1,2,4,1,2,8,7,1,2,16,25,12,1,2,26,65,59,19,1&fmt=text | 200 | 246 | N(k,q) rows q=k..1, k=1..6 | No results.；命中：无 |
| 39 | 2026-10-04T10:23:08Z | `search_Nflat_q0.txt` | https://oeis.org/search?q=1,0,1,0,1,2,0,1,4,2,0,1,7,8,2,0,1,12,25,16,2&fmt=text | 200 | 242 | N(k,q) rows q=0..k, k=0..5 | No results.；命中：无 |
| 40 | 2026-10-04T10:23:10Z | `search_Nrowsum.txt` | https://oeis.org/search?q=1,3,7,18,56,172,532,1760,5992,20640&fmt=text | 200 | 233 | sum_q N(k,q), k=1..10 | No results.；命中：无 |
| 41 | 2026-10-04T10:23:13Z | `search_Nkk1.txt` | https://oeis.org/search?q=8,16,26,38,52,68,86,106,128,152&fmt=text | 200 | 229 | N(k,k-1), k=4..13 | No results.；命中：无 |
| 42 | 2026-10-04T10:23:15Z | `search_Nkk2.txt` | https://oeis.org/search?q=7,25,65,139,277,509,871,1405,2159&fmt=text | 200 | 231 | N(k,k-2), k=4..12 | No results.；命中：无 |
| 43 | 2026-10-04T10:23:17Z | `search_Nkk3.txt` | https://oeis.org/search?q=12,59,199,574,1446,3257,6809,13390&fmt=text | 200 | 232 | N(k,k-3), k=5..12 | No results.；命中：无 |
| 44 | 2026-10-04T10:23:19Z | `search_Nk2.txt` | https://oeis.org/search?q=2,4,7,12,19,29,44,66,98,145,214&fmt=text | 200 | 229 | N(k,2), k=2..12 | No results.；命中：无 |
| 45 | 2026-10-04T10:23:21Z | `search_Nk3.txt` | https://oeis.org/search?q=2,8,25,59,124,253,493,925,1707,3104&fmt=text | 200 | 233 | N(k,3), k=3..12 | No results.；命中：无 |
| 46 | 2026-10-04T10:23:24Z | `search_hflat.txt` | https://oeis.org/search?q=1,2,-1,1,4,-3,1,8,-5,-2,1,14,-7,-8,2,1,23,-6,-27,11&fmt=text | 200 | 249 | h_k coefficients, k=3..7 | No results.；命中：无 |
| 47 | 2026-10-04T10:23:26Z | `search_C7num.txt` | https://oeis.org/search?q=2,2,7,0,2,2,8,13,15,29,0,6,2,16,29,99,81,104,146,0,24&fmt=text | 200 | 251 | (C7) numerator coeffs x^q..x^(3q-2), q=3..5 | No results.；命中：无 |
| 48 | 2026-10-04T10:23:28Z | `search_c2.txt` | https://oeis.org/search?q=1,1,1,3,5,7,13,23,37,63,109,183,309,527&fmt=text | 200 | 4383 | c_2(n), n=0..13 | Showing 1-2 of 2；命中：A077949 A077974 |
| 49 | 2026-10-04T10:23:30Z | `search_c3.txt` | https://oeis.org/search?q=1,1,1,4,7,10,22,43,73,139,268,487,904,1708&fmt=text | 200 | 3547 | c_3(n), n=0..13 | Showing 1-1 of 1；命中：A084386 |
| 50 | 2026-10-04T10:23:32Z | `search_ref_A207123.txt` | https://oeis.org/search?q=A207123&fmt=text | 200 | 14666 | entries referencing A207123 | Showing 1-10 of 11；命中：A207123 A207118 A207117 A207119 A207120 A207121 A207122 A207124 A207125 A207126 |
| 51 | 2026-10-04T10:23:34Z | `A207069.txt` | https://oeis.org/search?q=id:A207069&fmt=text | 200 | 1252 | entry A207069 (row 2 of A207123) | Showing 1-1 of 1；命中：A207069 |
| 52 | 2026-10-04T10:23:37Z | `A207070.txt` | https://oeis.org/search?q=id:A207070&fmt=text | 200 | 1331 | entry A207070 (row 3 of A207123) | Showing 1-1 of 1；命中：A207070 |
| 53 | 2026-10-04T10:23:39Z | `A002620.txt` | https://oeis.org/search?q=id:A002620&fmt=text | 200 | 45017 | entry A002620 (column 1 of A207123 is A002620(n+2)) | Showing 1-1 of 1；命中：A002620 |
| 54 | 2026-10-04T10:23:41Z | `A030179.txt` | https://oeis.org/search?q=id:A030179&fmt=text | 200 | 3276 | entry A030179 (column 2 of A207123 is A030179(n+2)) | Showing 1-1 of 1；命中：A030179 |
| 55 | 2026-10-04T10:26:09Z | `search_ref_A207123_p2.txt` | https://oeis.org/search?q=A207123&start=10&fmt=text | 200 | 3517 | entries referencing A207123, page 2 | Showing 11-11 of 11；命中：A207127 |
| 56 | 2026-10-04T10:26:11Z | `b207117.txt` | https://oeis.org/A207117/b207117.txt | 200 | 279 | b 文件 A207117 | n=1..19（19 项） |
| 57 | 2026-10-04T10:26:14Z | `b207124.txt` | https://oeis.org/A207124/b207124.txt | 200 | 11578 | b 文件 A207124 | n=1..210（210 项） |
| 58 | 2026-10-04T10:26:16Z | `b207125.txt` | https://oeis.org/A207125/b207125.txt | 200 | 12590 | b 文件 A207125 | n=1..210（210 项） |
| 59 | 2026-10-04T10:26:18Z | `b207126.txt` | https://oeis.org/A207126/b207126.txt | 200 | 13623 | b 文件 A207126 | n=1..210（210 项） |
| 60 | 2026-10-04T10:26:20Z | `b207069.txt` | https://oeis.org/A207069/b207069.txt | 200 | 8540 | b 文件 A207069 | n=1..210（210 项） |
| 61 | 2026-10-04T10:26:23Z | `b207070.txt` | https://oeis.org/A207070/b207070.txt | 200 | 10063 | b 文件 A207070 | n=1..210（210 项） |
| 62 | 2026-10-04T10:26:33Z | `b207127.txt` | https://oeis.org/A207127/b207127.txt | 200 | 14419 | b 文件 A207127 | n=1..210（210 项） |
| 63 | 2026-10-04T10:30:13Z | `search_Utab_k1m1_kinc.txt` | https://oeis.org/search?q=4,9,6,5,16,17,9,6,25,36,32,14,7,36,65,80,64,21&fmt=text | 200 | 244 | U table k>=1,m>=1 antidiagonals s=k+m=4..7, k increasing | No results.；命中：无 |
| 64 | 2026-10-04T10:30:16Z | `search_Utab_k1m1_kdec.txt` | https://oeis.org/search?q=6,9,4,9,17,16,5,14,32,36,25,6,21,64,80,65,36,7&fmt=text | 200 | 244 | U table k>=1,m>=1 antidiagonals s=4..7, k decreasing | No results.；命中：无 |
| 65 | 2026-10-04T10:30:18Z | `search_Utab_k1m0_kinc.txt` | https://oeis.org/search?q=4,9,6,1,5,16,17,9,1,6,25,36,32,14,1&fmt=text | 200 | 233 | U table k>=1,m>=0 antidiagonals s=4..6, k increasing | No results.；命中：无 |
| 66 | 2026-10-04T10:30:20Z | `search_Utab_k1m0_kdec.txt` | https://oeis.org/search?q=1,6,9,4,1,9,17,16,5,1,14,32,36,25,6&fmt=text | 200 | 233 | U table k>=1,m>=0 antidiagonals s=4..6, k decreasing | No results.；命中：无 |
| 67 | 2026-10-04T10:30:22Z | `search_Utab_k0m0_kinc.txt` | https://oeis.org/search?q=1,4,9,6,1,1,5,16,17,9,1,1,6,25,36,32,14,1&fmt=text | 200 | 239 | U table k>=0,m>=0 antidiagonals s=4..6, k increasing | No results.；命中：无 |
| 68 | 2026-10-04T10:30:24Z | `search_Utab_k0m0_kdec.txt` | https://oeis.org/search?q=1,6,9,4,1,1,9,17,16,5,1,1,14,32,36,25,6,1&fmt=text | 200 | 239 | U table k>=0,m>=0 antidiagonals s=4..6, k decreasing | No results.；命中：无 |

## 命中汇总

有命中的搜索：
- `search_U3_m0.txt`：Showing 1-1 of 1；命中：A084990
- `search_U3_m2.txt`：Showing 1-1 of 1；命中：A084990
- `search_U4_m0.txt`：Showing 1-1 of 1；命中：A326247
- `search_U4_m2.txt`：Showing 1-1 of 1；命中：A326247
- `search_R.txt`：Showing 1-1 of 1；命中：A038718
- `search_c2.txt`：Showing 1-2 of 2；命中：A077949 A077974
- `search_c3.txt`：Showing 1-1 of 1；命中：A084386
- `search_ref_A207123.txt`：Showing 1-10 of 11；命中：A207123 A207118 A207117 A207119 A207120 A207121 A207122 A207124 A207125 A207126
- `search_ref_A207123_p2.txt`：Showing 11-11 of 11；命中：A207127

无命中的搜索（30 个）：`search_U5_m0.txt`、`search_U5_m1.txt`、`search_U5_m2.txt`、`search_U6_m0.txt`、`search_U6_m1.txt`、`search_U6_m2.txt`、`search_U7_m0.txt`、`search_U7_m1.txt`、`search_U7_m2.txt`、`search_Uk2.txt`、`search_Uk3.txt`、`search_Uk4.txt`、`search_Udiag.txt`、`search_Nflat.txt`、`search_Nflat_rev.txt`、`search_Nflat_q0.txt`、`search_Nrowsum.txt`、`search_Nkk1.txt`、`search_Nkk2.txt`、`search_Nkk3.txt`、`search_Nk2.txt`、`search_Nk3.txt`、`search_hflat.txt`、`search_C7num.txt`、`search_Utab_k1m1_kinc.txt`、`search_Utab_k1m1_kdec.txt`、`search_Utab_k1m0_kinc.txt`、`search_Utab_k1m0_kdec.txt`、`search_Utab_k0m0_kinc.txt`、`search_Utab_k0m0_kdec.txt`

