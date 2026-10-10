# -*- coding: utf-8 -*-
r"""Lean 续作第四十八项（2026-10-10）：notes/13 定理 5(b)（猜想总表 A26 (ii) 的存在唯一部分）——以 c_i(n) = [xⁿ]1/b_i
为原子、平移取 3(q−1)+σ（σ 与 q 无关）时，N(k,q) 的每个 i 三个相邻原子的单和存在且唯一，最高一项
(q−1)!·γ_r(q,q−1) = a_r^{(σ)}(q−1)。新模块 `lean/A207123/NThreeAtoms.lean`：
- `N_eq_sum_U`：k ≥ 1 时 N(k,q) = Σ_{M=0}^{q−1} (−1)^{q−1−M} C(q,M+1)·U_k(M)（T1.4(1) 换下标写在 ℚ 中）。
- 存在 `N_three_atoms_exists`：对每个 M 用第四十六项的 `three_atoms_exists`，平移取 σ + 3(q−1−M)，使原子都成为
  c_i(k+3(q−1)+σ−r)，再交换求和次序；系数 `NatomConst`、`NatomCoeff`。
- 唯一 `N_three_atoms_unique`：直接用原子的线性无关 `atoms_lin_indep`；合并为 `N_three_atoms`。
- `NatomCoeff_top`：(q−1)!·γ_r(q,q−1) 是 x^σ·W̃_{q−1} 在 K_{q−1} 中约化代表的系数（`atomRep`）。
- `NatomConst_eq`：γ^{(0)} = (−1)^{q−1} Σ_{M=0}^{q−1} C(q,M+1)/M!；`NatomConst_two`、`NatomConst_three`：−3、13/2。
根模块加 import，Axioms 加 8 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_nthreeatoms.log 读。
论文没有陈述 N 的原子表示：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A26 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_nthreeatoms.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_nthreeatoms.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '82'

PAPER_RE = [
    (r'consists of 73 files that start from', 'consists of 74 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`ThreeAtoms.lean` 与 `NumHigh.lean`）', '`ThreeAtoms.lean`、`NumHigh.lean` 与 `NThreeAtoms.lean`）'),
    ('共 73 个模块（', '共 74 个模块（'),
    ('，T4.3(6) 中 j = 2、3 的次高两项系数闭式（这些论文都没有陈述）后由 2675 增加',
     '，T4.3(6) 中 j = 2、3 的次高两项系数闭式，notes/13 定理 5(b)（猜想总表 A26 (ii)：N 的三原子单和存在且唯一）'
     '（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_numhigh.py`。',
     '补丁 `patch_paper_2026-10-10_lean_numhigh.py`。第四十八项：notes/13 定理 5(b)（猜想总表 A26 (ii) 的存在唯一部分），'
     '新模块 `NThreeAtoms.lean`（`N_three_atoms`：对每个 q 与每个整数 σ，k 充分大时 N(k,q) = γ^{(0)} + '
     'Σ_{i=1}^{q−1} Σ_{r=0}^{2} γ_r(q,i)·c_i(k+3(q−1)+σ−r)，而且这样的表示唯一；系数 `NatomConst`、`NatomCoeff`：'
     'γ_r(q,i) = Σ_{M=i}^{q−1} (−1)^{q−1−M} C(q,M+1)·γ_r(M,i)，γ_r(M,i) 是 U_k(M) 在平移 3M + (σ + 3(q−1−M)) 下的系数'
     '（第四十六项的 `atomCoeff`）。存在：由容斥式 N(k,q) = Σ_{M=0}^{q−1} (−1)^{q−1−M} C(q,M+1)·U_k(M)（k ≥ 1，'
     '`N_eq_sum_U`）对每个 M 用 `three_atoms_exists`，再交换求和次序；唯一：直接用 `atoms_lin_indep`；'
     '`NatomCoeff_top`：(q−1)!·γ_r(q,q−1) = a_r^{(σ)}(q−1)（i = q−1 只有 M = q−1 一项）；`NatomConst_eq`：'
     'γ^{(0)} = (−1)^{q−1} Σ_{M=0}^{q−1} C(q,M+1)/M!，q = 2、3 时为 −3、13/2（`NatomConst_two`、`NatomConst_three`，'
     '即 notes/13 注 5.2 两个例子里的常数））。定理 5(a)（每个 i 一个原子不存在）与「沿最高对角线的系数不是 '
     'P-递推的」（归结为 A25(c)）仍未形式化。编译改了一轮（`Nat.add_sub_cancel` 已把 p + 1 − 1 − p 改写成 p − p，'
     '改用 `Nat.sub_self`），最终无错误、无警告（34 s、峰值 8.0 GB；这时其他程序多占了约 1 GB 提交量，这一项的几次'
     '编译把看门狗上限从默认 11000 MB 调到 10000 MB，仍高于实测峰值）。论文没有陈述 N 的原子表示，只改第 9 节计数。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_nthreeatoms.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_numhigh.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_numhigh.log`）。同日第四十八项：新模块 `NThreeAtoms.lean`（notes/13 定理 '
     '5(b)，猜想总表 A26 (ii) 的存在唯一部分）。主定理 `N_three_atoms` 的陈述用到已核对的 `N` 与 `ciZ`，以及新定义 '
     '`NatomConst`、`NatomCoeff`：已与 notes/13 定理 5(b) 的证明对照——`NatomConst q` = Σ_{M=0}^{q−1} '
     '(−1)^{q−1−M} C(q,M+1)·(−1)^M/M!（各 U_k(M) 的常数项 (−1)^M/M! 按容斥式组合），`NatomCoeff q i σ r` = '
     'Σ_{M=i}^{q−1} (−1)^{q−1−M} C(q,M+1)·`atomCoeff M i (σ + 3(q−1−M)) r`：U_k(M) 取平移 3M + σ_M、'
     'σ_M = σ + 3(q−1−M)，原子都成为 c_i(k+3(q−1)+σ−r)，x^{σ_M}·W̃_i = x^{σ+3(q−1)}·x^{−3M}W̃_i，所以这就是 notes/13 '
     '中 F_q 在 b_i 处的部分分式系数 Σ_M (−1)^{q−1−M}C(q,M+1)·R_{i,M} 在这组原子下的坐标；平移 3(q−1)+σ 在陈述里写成'
     '整数 3·(q − 1) + σ（q = 0 时原子求和为空，不受影响）。`N_eq_sum_U` 是已有的 T1.4(1) 容斥式 `N_inv` 换下标写在 ℚ '
     '中（k ≥ 1）。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_nthreeatoms.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('同日由 A27 证明）。未形式化 |',
     '同日由 A27 证明）。(ii) 的「三个原子存在唯一」（含最高一项 (q−1)!·γ_r(q,q−1) = a_r^{(σ)}(q−1)、常数项 '
     'γ^{(0)} = (−1)^{q−1}Σ_{M=0}^{q−1}C(q,M+1)/M!）2026-10-10 已形式化（`NThreeAtoms.lean` 的 `N_three_atoms`、'
     '`NatomCoeff_top`、`NatomConst_eq`：由容斥式把 N(k,q) 写成 U_k(M) 的组合，对每个 M 用 A25(b) 的 '
     '`three_atoms_exists`，平移取 σ + 3(q−1−M)；唯一由原子的线性无关 `atoms_lin_indep`）；(ii) 的「每个 i 一个原子'
     '不存在」与「沿最高对角线的系数不是 P-递推的」（归结为 A25(c)），以及 (i)、(iii)、(iv) 未形式化 |'),
]


def patched(path, reps, regex=()):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    for pat, new in regex:
        found = re.findall(pat, s)
        assert len(found) == 1, (path, len(found), pat[:60])
        s = re.sub(pat, lambda _m: new, s)
    return s, len(reps) + len(regex)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS, ' Axioms lines:', _ax)
    jobs = [(os.path.join(ROOT, 'paper', 'main.tex'), [], PAPER_RE),
            (os.path.join(ROOT, 'README.md'), README, README_RE),
            (os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST, ()),
            (os.path.join(ROOT, '猜想总表.md'), TABLE, ())]
    out = [(path,) + patched(path, reps, regex) for path, reps, regex in jobs]
    for path, s, n in out:
        open(path, 'wb').write(s.encode('utf-8'))
        print('%s: %d edits' % (os.path.relpath(path, ROOT), n))


if __name__ == '__main__':
    main()
