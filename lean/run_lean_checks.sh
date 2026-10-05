#!/usr/bin/env bash
# 依次运行三步，输出存到 ../logs/lean_build.log：
#   1. 按依赖顺序逐个模块 lake build（topo_order.py 给出顺序），再整体 lake build 一次（此时应无需编译）；
#   2. lake env lean Axioms.lean；
#   3. lake env lean Checks.lean。
# 本机单个 Lean 进程峰值超过 7.5 GB，两个同时跑会撑爆内存（进程被杀：退出码 127、无输出）。所以每一步都经
# lean_one.sh 串行执行（先拿锁，再等机器上没有其他 lean.exe），也不让 lake 一次编译多个模块（它会并行）。
cd "$(dirname "$0")"
LOG=../logs/lean_build.log
{
  echo "# Lean 构建与核对日志"
  echo "# 运行时间（本地）：$(powershell -NoProfile -Command "Get-Date -Format 'yyyy-MM-dd HH:mm:ss zzz'")"
  echo "# 环境：$(cat lean-toolchain)；Mathlib v4.34.1"
  echo "# 串行：每一步经 lean_one.sh，同一时间只有一个 Lean 进程"
  echo
  echo "## 1. lake build（按依赖顺序逐个模块，再整体一次）"
  start=$(date +%s)
  fail=0
  for m in $(py -3.14 topo_order.py); do
    s1=$(date +%s)
    out=$(./lean_one.sh build "$m" 2>&1)
    c=$?
    if [ $c -ne 0 ] || echo "$out" | grep -qi "warning\|error"; then
      echo "$out"
    fi
    [ $c -ne 0 ] && fail=1
    echo "- $m：退出码 $c（$(( $(date +%s) - s1 )) s）"
  done
  ./lean_one.sh build 2>&1
  c=$?
  [ $c -ne 0 ] && fail=1
  echo "[exit code $fail]  [$(( $(date +%s) - start )) s]"
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
} > "$LOG" 2>&1
echo done
