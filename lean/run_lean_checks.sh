#!/usr/bin/env bash
# 依次运行三步，输出存到 ../logs/lean_build.log：
#   1. 按依赖顺序逐个模块 lake build（topo_order.py 给出顺序），再整体 lake build 一次（此时应无需编译）；
#   2. lake env lean Axioms.lean；
#   3. lake env lean Checks.lean。
# 本机单个 Lean 进程峰值超过 7.5 GB，两个同时跑会撑爆内存（进程被杀：退出码 127、无输出）。所以每一步都经
# lean_one.sh 串行执行（先拿锁，再等机器上没有其他 lean.exe），也不让 lake 一次编译多个模块（它会并行；
# 本机的 Lake 5.0.0 没有限制并行数的选项）。
# topo_order.py 在 Windows 上输出 CRLF，模块名要先 `tr -d '\r'`（2026-10-07 实测：带着 \r 时 Lake 报
# unknown target，旧版本脚本因此每一步都在几秒内失败，之后的整体 lake build 会并行重编所有模块）。
# 单个模块的目标写成 `+A207123.X`（`+` 明确表示模块）。
# 任何一步失败就立即停止，不再做整体 lake build 与后两步：否则整体构建会同时重编失败的模块及其下游。
# 每一步要先核对 Mathlib 的约 8900 条构建记录：缓存热时约 30 s，冷启动可达 7 min。
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
  for m in $(py -3.14 topo_order.py | tr -d '\r'); do
    s1=$(date +%s)
    out=$(./lean_one.sh build "+$m" 2>&1)
    c=$?
    if [ $c -ne 0 ] || echo "$out" | grep -qi "warning\|error"; then
      echo "$out"
    fi
    echo "- $m：退出码 $c（$(( $(date +%s) - s1 )) s）"
    if [ $c -ne 0 ]; then
      fail=1
      echo "（$m 失败，停止：不再构建后面的模块，也不做整体 lake build 与 Axioms、Checks 两步）"
      break
    fi
  done
  if [ $fail -eq 0 ]; then
    ./lean_one.sh build 2>&1
    c=$?
    [ $c -ne 0 ] && fail=1
  fi
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
