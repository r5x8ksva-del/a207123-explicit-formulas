#!/usr/bin/env bash
# 带内存保护地运行一个非 Lean 的任务（例如 verify_all.py），别把机器撑爆。Lean 编译仍然只走 lean/lean_one.sh。
# 背景：本机 16 GB 内存，常有别的会话同时在跑东西；Lean 编译曾两度耗尽虚拟内存导致重启（见 lean/lean_one.sh）。
# 三层保护：
#   1. 启动前：机器上有 lean.exe 在跑就不启动（单个 Lean 就 ≥ 8 GB，不和它并行）；
#      系统提交余量 ≥ CAP+MINHEAD 且可用物理内存 ≥ MINAVAIL 才启动。不满足就直接放弃（退出码 75），不等待；
#   2. 运行中：proc_watchdog.ps1 每秒统计整棵进程树（任意进程名）的私有内存，超过 CAP，或系统提交余量
#      低于 MINHEAD，就结束整棵树（退出码 137）。看门狗没能启动时中止任务（退出码 70），不裸跑；
#   3. 每次运行记一行到 logs/guarded_runs.log（时间为 UTC）：命令、退出码、用时、峰值、最小余量。
# 用法（路径都相对任务 C 根目录；脚本会先 cd 到根目录）：
#   code/main_extra/run_guarded.sh <输出文件> <命令> [参数...]
#   例：code/main_extra/run_guarded.sh logs/verify_all_x.log py -3.14 verify_all.py
# 命令的标准输出和标准错误都写进 <输出文件>。
# 可调环境变量：GUARD_CAP_MB（默认 4000）、GUARD_MINHEAD_MB（默认 3000）、GUARD_MINAVAIL_MB（默认 1500）。
# 最后一行打印 [run_guarded exit code N]：0 成功；75 条件不满足、没有启动；137 被看门狗结束；
#   70 拿不到进程号或看门狗没能启动；其他为命令本身的退出码。
cd "$(dirname "$0")/../.." || exit 2
CAP=${GUARD_CAP_MB:-4000}
MINHEAD=${GUARD_MINHEAD_MB:-3000}
MINAVAIL=${GUARD_MINAVAIL_MB:-1500}
LOG="logs/guarded_runs.log"
OUT="$1"
if [ -z "$OUT" ] || [ $# -lt 2 ]; then
  echo "用法：code/main_extra/run_guarded.sh <输出文件> <命令> [参数...]"
  exit 2
fi
shift

# 1. 启动前检查
if tasklist //FI "IMAGENAME eq lean.exe" //NH 2>/dev/null | grep -qi "lean.exe"; then
  echo "[run_guarded 有 lean.exe 在运行，没有启动：单个 Lean 就 ≥ 8 GB，不和它并行]"
  echo "$(date -u '+%F %T') UTC | $* > $OUT | exit 75 (lean.exe running)" >> "$LOG"
  echo "[run_guarded exit code 75]"
  exit 75
fi
st=$(powershell -NoProfile -ExecutionPolicy Bypass -File lean/mem_status.ps1 2>/dev/null | tr -d '\r')
avail=$(echo "$st" | sed -n 's/.*AVAIL=\([0-9-]*\).*/\1/p')
head=$(echo "$st" | sed -n 's/.*HEADROOM=\([0-9-]*\).*/\1/p')
need_head=$((CAP + MINHEAD))
if [ -z "$avail" ] || [ -z "$head" ] || [ "$head" -lt "$need_head" ] || [ "$avail" -lt "$MINAVAIL" ]; then
  echo "[run_guarded 内存不够，没有启动：$st；需要 HEADROOM≥${need_head} 且 AVAIL≥${MINAVAIL}（MB）]"
  echo "$(date -u '+%F %T') UTC | $* > $OUT | exit 75 (memory gate) | $st" >> "$LOG"
  echo "[run_guarded exit code 75]"
  exit 75
fi
echo "[run_guarded 启动前：$st；看门狗上限 CAP=${CAP}MB，MINHEAD=${MINHEAD}MB]"

# 2. 运行 + 看门狗
SF=$(mktemp)
start=$(date +%s)
"$@" > "$OUT" 2>&1 &
JPID=$!
WPID=""
for _ in 1 2 3 4 5 6 7 8 9 10; do
  WPID=$(cat "/proc/$JPID/winpid" 2>/dev/null)
  [ -n "$WPID" ] && break
  sleep 0.2
done
if [ -z "$WPID" ]; then
  echo "[run_guarded 拿不到进程号，无法启动看门狗，已中止]"
  kill "$JPID" 2>/dev/null
  wait "$JPID" 2>/dev/null
  echo "[run_guarded exit code 70]"
  exit 70
fi
powershell -NoProfile -ExecutionPolicy Bypass -File code/main_extra/proc_watchdog.ps1 -RootPid "$WPID" -CapMB "$CAP" \
  -MinHeadroomMB "$MINHEAD" -StatusFile "$(cygpath -w "$SF")" &
WDPID=$!
# 看门狗一启动就往状态文件写 STARTED；10 秒内看不到就当它没起来，中止任务，不裸跑。
# （不能用 kill -0 判断：已退出但还没被 wait 的子进程，kill -0 也会成功。）
wd_ok=0
for _ in $(seq 1 20); do
  [ -s "$SF" ] && { wd_ok=1; break; }
  sleep 0.5
done
if [ "$wd_ok" -eq 0 ]; then
  echo "[run_guarded 看门狗 10 秒内没有启动，已中止任务]"
  taskkill //PID "$WPID" //T //F >/dev/null 2>&1
  wait "$JPID" 2>/dev/null
  kill "$WDPID" 2>/dev/null
  wait "$WDPID" 2>/dev/null
  rm -f "$SF"
  echo "$(date -u '+%F %T') UTC | $* > $OUT | exit 70 (watchdog failed)" >> "$LOG"
  echo "[run_guarded exit code 70]"
  exit 70
fi
wait "$JPID"
code=$?
wait "$WDPID" 2>/dev/null
wd=$(tr -d '\r' < "$SF" 2>/dev/null)
rm -f "$SF"
if echo "$wd" | grep -q "KILLED=1"; then
  echo "[run_guarded 被内存看门狗结束：$wd]"
  code=137
fi
case "$wd" in PEAK=*) ;; *) echo "[run_guarded 警告：看门狗没有写回最终状态（读到「$wd」）]" ;; esac

# 3. 记录
dur=$(( $(date +%s) - start ))
echo "$(date -u '+%F %T') UTC | $* > $OUT | exit $code | ${dur}s | $wd" >> "$LOG"
echo "[run_guarded 内存：$wd；用时 ${dur}s]"
echo "[run_guarded exit code $code]"
exit $code
