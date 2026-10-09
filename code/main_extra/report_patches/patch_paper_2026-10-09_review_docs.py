# -*- coding: utf-8 -*-
"""README.md 与 ROADMAP.md 跟着 patch_paper_2026-10-09_review.py 同步（2026-10-09 晚，用户：「都按建议」）：
论文源文件里已经没有 TODO 与内部注释，现 36 页，新增推论 8.15、注记 8.16；写明审读意见里还没做的几项。
每处替换断言原文出现一次；按字节读写（LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-09_review_docs.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

README = [
    ('2026-10-09 与项目现状同步（核对条数、注记 6.4、第 10 节开放问题），见下面「论文初稿」一条。',
     '2026-10-09 与项目现状同步（核对条数、注记 6.4、第 10 节开放问题），同日晚按审读意见修订（新摘要、推论 8.15、'
     '注记 8.16、5 条新文献，源文件里不再有 TODO 与内部注释），现 36 页；见下面「论文初稿」一条。'),
    (r'PDF 里已没有 `\todo`（2026-10-08 删去），源文件剩 1 处注释 TODO（引理 1 的出处），文献检索补完与 AI 声明仍待你做 |',
     r'PDF 里已没有 `\todo`（2026-10-08 删去）；2026-10-09 晚按审读意见修订后，源文件里也没有内部注释与 TODO 了'
     r'（36 页；新结论的核对见 `check_chains_negzeros.py`，文献 DOI 用 `check_bib_dois.py` 对照 Crossref），'
     r'文献检索补完（MathSciNet、zbMATH、WoS）与 AI 声明仍待你做 |'),
    ('源文件里还剩 1 处注释 TODO（引理 1 的出处）；',
     '2026-10-09 晚按审读意见修订（用户先答「可以」，看过改动清单与预览稿后答「都按建议」；补丁 '
     '`code/main_extra/report_patches/patch_paper_2026-10-09_review.py`，日志 `logs/*_2026-10-09_review.log`、'
     '`logs/check_chains_negzeros_2026-10-09.log`）：删去源文件里的内部注释、引理 2.5 前的 TODO（四项递推是你自己推的，'
     '不加引用）、草稿日期与不再使用的 `\\todo` 宏；摘要重写为 248 词、1711 字符（原稿约 2035 字符，超过 arXiv 的 1920 上限）；'
     '`\\thanks` 去掉 "and is the corresponding author"；MSC 分出 primary 与 secondary（去 11D61，加 06A07），关键词加 chain '
     'polynomials；新增推论 8.15（u_k 在 −1,…,−⌈k/3⌉ 为零，下一个点等于 (−1)^k·lc(h_k)≠0；原第 10 节开放问题 (3) 默认了这些零点，'
     '正文却只证了 u_k(−1)=0）与注记 8.16（N(k,q) 是 Λ_k 去掉最小最大元后 (q−1) 元链的个数，n_k 是链多项式，h_k 是序复形的 '
     'h-多项式；布尔格对应 q!S(k,q) 与 Euler 多项式；k≥3 时序复形不是 Cohen–Macaulay），引言与第 2 节各加指向它的句子，'
     '引言补连续模式的说法，相关工作补 transfer-matrix 的标准出处；新增 5 条文献（Athanasiadis–Douvropoulos–Kalampogia-Evangelinou、'
     'Athanasiadis–Kalampogia-Evangelinou、Brändén–Saud Maia Leite、Kitaev、Stanley 的 Combinatorics and Commutative Algebra）。'
     '核对：check_tex 无问题（31 条文献全被引用）、check_paper_numbers 32 PASS、check_appendix_lean 34 PASS、'
     'check_chains_negzeros 6 PASS（做过反向检查）、check_bib_dois 26 PASS，Tectonic 编译 36 页（只有第 9 页底部一条 '
     'Underfull \\vbox 排版提示）。审读意见里还没做的：注记 6.4 与第 10 节引用中文报告的结论，要么写进附录、要么另发英文短文、'
     '要么删去；推论 5.5 之后 Rel(N)=𝒪·L_N 只有证明梗概；定理 6.13 的 (N1)(N2) 偏人为；符号重载（h、τ、T、D、V、P、α、β、N）；'
     '篇幅（第 6 节占 8 页）；要读 Brändén–Saud Maia Leite（Adv. Math. 2026）确认它的一般理论是否已覆盖 Λ_k；pdflatex 还没实测。'),
]

ROADMAP = [
    ('剩下的 `TODO` 列在 README「当前状态与待办」。',
     '2026-10-09 晚按审读意见修订后（36 页）源文件里已没有 `TODO`，还要做的事列在 README「当前状态与待办」。'),
    ('→ 处理 TODO →', '→ 处理审读意见里余下的几项（见 README）→'),
]


def patch(path, reps):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d edits' % (os.path.basename(path), len(reps)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'ROADMAP.md'), ROADMAP)


if __name__ == '__main__':
    main()
