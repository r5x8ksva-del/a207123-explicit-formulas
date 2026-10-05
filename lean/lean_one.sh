#!/usr/bin/env bash
# 串行、带内存保护地运行 Lean。所有编译都必须通过本脚本。
# 背景：本机 16 GB 内存。A207123 的模块都经 Basic.lean 导入整个 Mathlib，实测只加载 import 就要约 8.0 GB
# 私有内存（2026-10-05，import A207123.HNum）。2026-10-05 22:46 NumStruct.lean 在默认 12 线程下编译，
# 提交内存涨到 24 GB，系统虚拟内存耗尽后崩溃重启。所以本脚本做四层保护：
#   1. 互斥锁 + 等到机器上没有其他 lean.exe（同一时间只运行一个 Lean）；
#   2. 启动前的内存闸门：系统提交余量 ≥ CAP+MINHEAD 且可用物理内存 ≥ MINAVAIL 才启动，
#      否则每 30 秒重查，最多等 WAITMAX 秒，仍不够就放弃（退出码 75，不启动 Lean）；
#   3. 运行中的看门狗（lean_watchdog.ps1，每秒一次）：本次启动的 lean.exe 私有内存合计 > CAP，
#      或系统提交余量 < MINHEAD，就立即结束整棵进程树（退出码 137）；
#   4. 默认只用 THREADS 个线程（lean -j，并设 LEAN_NUM_THREADS 让 lake build 启动的 lean 也照此），
#      避免几十条证明同时展开把内存撑到 8 GB 之上很多。
# 每次运行的峰值内存、最小提交余量、退出码记到 ../logs/lean_mem.log。
# 用法（在 lean/ 下）：
#   ./lean_one.sh A207123/X.lean [其他 lean 参数]   # lake env lean -j THREADS ...
#   ./lean_one.sh build A207123.X                   # lake build A207123.X（只在依赖都已构建时用）
# 可调环境变量：LEAN_CAP_MB（默认 11000）、LEAN_MINHEAD_MB（默认 3000）、LEAN_MINAVAIL_MB（默认 3000）、
#   LEAN_THREADS（默认 1）、LEAN_WAITMAX_S（默认 1800）。
# 最后一行打印 [lean_one exit code N]：0 成功；75 内存不足没有启动；137 被看门狗结束；其他为 Lean/lake 的退出码。
cd "$(dirname "$0")" || exit 2
CAP=${LEAN_CAP_MB:-11000}
MINHEAD=${LEAN_MINHEAD_MB:-3000}
MINAVAIL=${LEAN_MINAVAIL_MB:-3000}
THREADS=${LEAN_THREADS:-1}
export LEAN_NUM_THREADS="$THREADS"
WAITMAX=${LEAN_WAITMAX_S:-1800}
LOCK=".lean_lock"
MEMLOG="../logs/lean_mem.log"
waited=0
while ! mkdir "$LOCK" 2>/dev/null; do
  holder=""
  [ -f "$LOCK/pid" ] && holder=$(cat "$LOCK/pid" 2>/dev/null)
  if [ -n "$holder" ] && ! kill -0 "$holder" 2>/dev/null; then
    rm -rf "$LOCK"; continue          # 持锁进程已退出：锁过期
  fi
  if [ -n "$(find "$LOCK" -maxdepth 0 -mmin +120 2>/dev/null)" ]; then
    rm -rf "$LOCK"; continue          # 锁存在超过 120 分钟：视为过期
  fi
  sleep 5; waited=$((waited + 5))
done
echo $$ > "$LOCK/pid"
trap 'rm -rf "$LOCK"' EXIT
# 等别的 lean.exe（例如其他会话的）结束
while tasklist //FI "IMAGENAME eq lean.exe" //NH 2>/dev/null | grep -qi "lean.exe"; do
  sleep 5; waited=$((waited + 5))
done
[ "$waited" -gt 0 ] && echo "[lean_one waited ${waited}s for other Lean processes]"

# 内存闸门
need_head=$((CAP + MINHEAD))
gate=0
while :; do
  st=$(powershell -NoProfile -ExecutionPolicy Bypass -File mem_status.ps1 2>/dev/null | tr -d '\r')
  avail=$(echo "$st" | sed -n 's/.*AVAIL=\([0-9-]*\).*/\1/p')
  head=$(echo "$st" | sed -n 's/.*HEADROOM=\([0-9-]*\).*/\1/p')
  if [ -n "$avail" ] && [ -n "$head" ] && [ "$head" -ge "$need_head" ] && [ "$avail" -ge "$MINAVAIL" ]; then
    break
  fi
  if [ "$gate" -ge "$WAITMAX" ]; then
    echo "[lean_one 内存不足，没有启动 Lean：$st；需要 HEADROOM≥${need_head} 且 AVAIL≥${MINAVAIL}（MB）]"
    echo "$(date '+%F %T') | $* | exit 75 (memory gate) | $st" >> "$MEMLOG"
    echo "[lean_one exit code 75]"
    exit 75
  fi
  [ "$gate" -eq 0 ] && echo "[lean_one 等待内存：$st；需要 HEADROOM≥${need_head} 且 AVAIL≥${MINAVAIL}]"
  sleep 30; gate=$((gate + 30))
done
echo "[lean_one 启动前：$st；看门狗上限 CAP=${CAP}MB，MINHEAD=${MINHEAD}MB]"

# 运行 + 看门狗
SF=$(mktemp)
start=$(date +%s)
if [ "$1" = "build" ]; then
  shift
  lake build "$@" &
else
  lake env lean -j "$THREADS" "$@" &
fi
LPID=$!
WPID=""
for _ in 1 2 3 4 5 6 7 8 9 10; do
  WPID=$(cat "/proc/$LPID/winpid" 2>/dev/null)
  [ -n "$WPID" ] && break
  sleep 0.2
done
if [ -z "$WPID" ]; then
  echo "[lean_one 拿不到进程号，无法启动看门狗，已中止]"
  kill "$LPID" 2>/dev/null
  wait "$LPID" 2>/dev/null
  echo "[lean_one exit code 70]"
  exit 70
fi
powershell -NoProfile -ExecutionPolicy Bypass -File lean_watchdog.ps1 -RootPid "$WPID" -CapMB "$CAP" \
  -MinHeadroomMB "$MINHEAD" -StatusFile "$(cygpath -w "$SF")" &
WDPID=$!
wait "$LPID"
code=$?
wait "$WDPID" 2>/dev/null
wd=$(tr -d '\r' < "$SF" 2>/dev/null)
rm -f "$SF"
if echo "$wd" | grep -q "KILLED=1"; then
  echo "[lean_one 被内存看门狗结束：$wd]"
  code=137
fi
dur=$(( $(date +%s) - start ))
echo "$(date '+%F %T') | $* | exit $code | ${dur}s | $wd" >> "$MEMLOG"
echo "[lean_one 内存：$wd；用时 ${dur}s]"
echo "[lean_one exit code $code]"
exit $code
