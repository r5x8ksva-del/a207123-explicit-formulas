#!/usr/bin/env bash
# 全量检查的另一种跑法：不经 lake 的构建记录核对，按依赖顺序直接从源码逐个编译全部模块。
# 输出格式与 run_lean_checks.sh 相同（三步，各有一行 [exit code N]），写入 ../logs/lean_build.log，
# 所以 code/main_extra/report_patches/patch_lean4.py 可以直接读。
#
# 为什么需要它（2026-10-07 实测）：本机内存紧时，lake build 每一步都要先核对 Mathlib 约 8900 条构建记录，
# 冷缓存下一步就要 7–10 分钟（+A207123.Basic 什么都没编译也用了 612 s），26 个模块要好几个小时；而本机的
# Lake 5.0.0 没有限制并行数的选项，不能改用一次整体 lake build（会同时编译多个模块，单个就约 8 GB）。
#
# 做法：按 topo_order.py 的顺序，对每个模块运行 `lake env lean A207123/X.lean -o <olean> -i <ilean>`，最后编根模块
# A207123.lean。后面的模块 import 的就是刚编出来的版本，所以等价于从源码全量重编。lakefile.toml 没有设置额外的
# 编译选项，lake build 用的也是这一套默认设置。唯一的不同是不写 lake 的构建记录（.trace/.hash）：以后再运行
# lake build，lake 会把这些模块重编一遍，不影响这里的结论。
# 每一步都经 lean_one.sh（串行锁、内存闸门、看门狗）；任何一步失败就停止，不再做后面的步骤。
# 看门狗上限默认 LEAN_CAP_MB=9500（闸门因此要求系统提交余量 ≥ 9500+3000 MB），迄今成功编译的峰值不超过 8137 MB；
# 其他环境变量同 lean_one.sh。
cd "$(dirname "$0")" || exit 2
export LEAN_CAP_MB=${LEAN_CAP_MB:-9500}
LOG=../logs/lean_build.log
OUT=.lake/build/lib/lean
{
  echo "# Lean 构建与核对日志"
  echo "# 运行时间（本地）：$(powershell -NoProfile -Command "Get-Date -Format 'yyyy-MM-dd HH:mm:ss zzz'")"
  echo "# 环境：$(cat lean-toolchain)；Mathlib v4.34.1"
  echo "# 方式：run_lean_checks_direct.sh：按依赖顺序逐个模块 lake env lean -o 从源码编译（不经 lake 构建记录核对），"
  echo "#   最后编根模块；每一步经 lean_one.sh，同一时间只有一个 Lean 进程；看门狗上限 LEAN_CAP_MB=$LEAN_CAP_MB"
  echo
  echo "## 1. 编译（按依赖顺序逐个模块，最后根模块 A207123）"
  start=$(date +%s)
  fail=0
  mkdir -p "$OUT/A207123"
  for m in $(py -3.14 topo_order.py | tr -d '\r') A207123; do
    p="${m//.//}"                 # A207123.Basic -> A207123/Basic；根模块 A207123 不变
    s1=$(date +%s)
    out=$(./lean_one.sh "$p.lean" -o "$OUT/$p.olean" -i "$OUT/$p.ilean" 2>&1)
    c=$?
    if [ $c -ne 0 ] || echo "$out" | grep -qi "warning\|error"; then
      echo "$out"
    fi
    echo "- $m：退出码 $c（$(( $(date +%s) - s1 )) s）"
    if [ $c -ne 0 ]; then
      fail=1
      echo "（$m 失败，停止：不再编译后面的模块，也不做 Axioms、Checks 两步）"
      break
    fi
  done
  echo "[exit code $fail]  [$(( $(date +%s) - start )) s]"
  if [ $fail -eq 0 ]; then
    echo
    echo "## 2. lake env lean Axioms.lean"
    start=$(date +%s)
    ./lean_one.sh Axioms.lean 2>&1
    echo "[exit code $?]  [$(( $(date +%s) - start )) s]"
    echo
    echo "## 3. lake env lean Checks.lean"
    start=$(date +%s)
    ./lean_one.sh Checks.lean 2>&1
    echo "[exit code $?]  [$(( $(date +%s) - start )) s]"
  fi
} > "$LOG" 2>&1
echo done
