# 精读过的论文：来源、哈希与用到的事实

记录于 2026-10-06 21:17 UTC。PDF 本身**没有**放进仓库（版权；放在会话临时目录），这里只留来源、SHA-256、页数和我用到的事实（均为转述）。`code/novelty/check_note_refs.py` 把本文件当作「已读过」的证据来源。

| 文件 | 来源 | 论文 | 读到什么程度 | 页数 | 字节 | SHA-256 |
|---|---|---|---|---|---|---|
| kauers2007_risc3240.pdf | https://www3.risc.jku.at/publications/download/risc_3240/main.pdf | Kauers 2007, Summation algorithms for Stirling number identities (J. Symbolic Comput. 42 (2007) 948-970, doi:10.1016/j.jsc.2007.08.002) | 全文 | 23 | 285859 | f143bdcdbf55a862c00c6eaae859fa0575da7d40df8bef9e4d9fd113017f4384 |
| cks2009_0904.2761.pdf | https://arxiv.org/pdf/0904.2761 | Chyzak-Kauers-Salvy 2009, A non-holonomic systems approach to special function identities (arXiv:0904.2761) | 第 1-3 节与 Stirling-like 段 | 16 | 255689 | a6fc013c23fa535be49af17efb8b0d1e97fff82a1cbc8b8e06a6aed689ef73ac |
| hardinian_2309.00487.pdf | https://arxiv.org/pdf/2309.00487 | Dougherty-Bliss-Kauers, Hardinian arrays (arXiv:2309.00487) | 全文 | 9 | 141383 | c83697de55fd183db013147a05f9af390861e71674fea40a9ef8f1b14dfed40d |
| dbktz_2410.07435.pdf | https://arxiv.org/pdf/2410.07435 | Dougherty-Bliss-Koutschan-Ter-Saakov-Zeilberger, counting 0-1 balanced matrices (arXiv:2410.07435 v2) | 摘要、引言、定理 2-3、程序说明 | 11 | 175182 | 8f9d2e04a3bd48852be87d98db16db358dad5424f4bfe46f391989eeddcf48d9 |
| kk2023_2303.02793.pdf | https://arxiv.org/pdf/2303.02793 | Kauers-Koutschan 2023, Some D-finite and some possibly D-finite sequences in the OEIS (arXiv:2303.02793) | 只做关键词检索（grep） | 42 | 399865 | 746d1059c85cb0f0c9b8467ca75496c3e4b324c42bf091942b2c5a1d7ef98011 |
| oeisopen.pdf | https://arxiv.org/pdf/2608.11941 | Adamczewski, OEIS Open (arXiv:2608.11941) | 关键词检索与附录条目 | 27 | 1245628 | 5d6ac6ae7c91ad7a93fdf7052e36fb382bb1059e3fd74087eae61008c022333e |
| fried_2410.07237.pdf | https://arxiv.org/pdf/2410.07237 | Fried, Proofs of some Conjectures from the OEIS (arXiv:2410.07237) | 全文抽取 A 号与关键词（2026-10-07 第二次 arXiv 复查） | 17 | 165950 | 5e8505f399d4e86667fb10041c12c5263dcc59f9dab4d93addb13855d262df05 |
| fried_2606.09913.pdf | https://arxiv.org/pdf/2606.09913 | Fried, Proofs of several OEIS conjectures on determinants and permanents (arXiv:2606.09913) | 同上 | 34 | 396640 | b96b1a65800eac002b228b297552d62219d448bcb0668f42a91f3a492b920ff6 |
| bl26_2412.06595.pdf | https://arxiv.org/pdf/2412.06595 | Brändén-Saud Maia Leite, Totally nonnegative matrices, chain enumeration and zeros of polynomials (arXiv:2412.06595v3; Adv. Math. 487 (2026) 110760, doi:10.1016/j.aim.2025.110760) | 摘要、引言、第 5 节（TN-偏序集与定理 5.5）、第 6 节（定义 6.1、定理 6.4-6.6）（2026-10-09 论文审读） | 33 | 670803 | bbcb98aac54a164f420059ed9601d1397670a792dd98f883dbd673b567fa2c43 |
| fried_2607.24832.pdf | https://arxiv.org/pdf/2607.24832 | Fried, Further proofs of conjectures from the OEIS (arXiv:2607.24832) | 同上 | 57 | 434520 | 9011a6cf3438a970ae6146d408beda510bfa9f2635143176d03014d59531e197 |

另有 OEIS 附件 `data/lit/oeis/A202093_proof_a202093.txt`（来源 https://oeis.org/A202093/a202093.txt，Christian Krause，2026-06-26，全文已读）。OEIS 内容适用 CC-BY-SA 4.0，见 `data/oeis/NOTICE.md`。

## 用到的事实（转述）

- Hardinian arrays（Dougherty-Bliss–Kauers）：研究 king-move 数组，OEIS 表 A253026、A253223、A253004（r=1,2,3）；证明 H_1(n,k) 的闭式、H_r(n,n) 是 D-finite、H_2(n,n) 的 Kauers–Koutschan 递推；不是 A207118–A207123 这一族。
- Rectangular Hardinian arrays（Dougherty-Bliss–Spahn，摘要级）：用转移矩阵证明固定 r、k 时 H_r(n,k) 是 n 的 r 次多项式，涉及 OEIS A253217。
- DBKTZ：定理 2——任意有限字母表与任意有限横向/纵向模式集，固定一边尺寸时序列满足常系数线性递推（有限自动机、转移矩阵或 Goulden–Jackson）；讨论的是平衡 0-1 矩阵（OEIS A172555、A172557 等）；配套 Maple 包 Hardin.txt。
- Kauers–Koutschan 2023：全文没有出现 A2071xx、A207xxx、A326247；有一节对 A188818 用奇偶位置分解。
- Kauers 2007：Stirling-like 序列的定义（零化子由一条三项三角算子加若干纯递推生成，位移向量构成 Z² 的基）；例 5：S₂ 在 K、N 方向都没有纯递推，零化子恰为由三角递推生成的理想（有理函数系数）。
- CKS 2009：例 3——S₂ 的三角递推生成的理想维数为 1，S₂ 不是 ∂-finite；引入维数与 polynomial growth 以推广创造性伸缩。
- Krause 附件（OEIS A202093）：行内禁 001 与 011 ⇔ s_i=0 ⇒ s_{i+2}=0；按列参数化为四条独立弱降序列，得到 a(n)=C(α+E,E)C(α+O,O)C(β+E,E)C(β+O,O)，对 w=3..9 与 OEIS 数据核对。
- OEIS Open：基于 492 个由 Tsoukalas 等在 Lean 中形式化的 OEIS 开放猜想；语言模型在 50 美元预算下解出 147 个；公开仓库 github.com/epoch-research/LeanOpenProblems（本家族不在其目录树里）。
- Fried 的三篇（2026-10-07 第二次 arXiv 复查时下载，用 PyMuPDF 抽全文后检索）：全文出现的 OEIS 编号分别为 18、13、41 个，都不含 A207118–A207127、A207069、A207070、A326247，也没有出现 0..1 arrays、binary arrays 等字样；arXiv:2606.09913 提到 Hardin 一次，指的是 A250742（Hardin 的另一张二进制矩阵表，与本家族无关）。
- Kauers 2007（上表第一行的 RISC 公开版，10-07 第二次复查时重读 §2.2–§3）：序列取为 f: Z²→C，算子 Σ p_{ij}(n,k)N^iK^j 的系数 p_{ij}∈C(n,k)，零化子是 Q·f≡0 的算子全体（左理想）；定义 3 的 Stirling-like 即「零化子由 s_iN_i−t_i 与一条 u+vN_1^{v_1}N_2^{v_2}−wN_1^{w_1}N_2^{w_2}（u,v,w 非零多项式，(v_1,v_2)、(w_1,w_2) 生成 Z²）生成」。Kauers 把 S₂ 等延拓到整个 Z²，使递推处处成立。
- Brändén-Saud Maia Leite（arXiv:2412.06595v3，2026-10-09 读）：下三角、对角线为 1 的全非负矩阵给出实根多项式族；拟秩一致且矩阵 R(P) 全非负的「TN-偏序集」的链多项式实根，零点在 [−1,0]（定理 5.5）；对 TN-偏序集 P，P-positive 偏序集（相对 P 的 h-向量非负）的链多项式零点在 [−1,0]（定理 6.6，推广 Brenti-Welker）。本项目的 n_k 在 k≥3 时有 ⌊k/3⌋ 个零点小于 −1，所以 Λ_k 不在这些定理的范围内（论文注记 8.16）。
