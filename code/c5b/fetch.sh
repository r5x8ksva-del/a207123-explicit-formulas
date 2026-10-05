#!/usr/bin/env bash
# c5b 只读 OEIS 抓取：读取 "文件名|URL" 列表，每个 URL 只取一次（已在日志中出现过就跳过），
# 快照存 data/oeis/<文件名>，日志 logs/c5b_fetch.log（TSV：UTC 时间、文件名、HTTP 码、字节数、URL）。
# 用法：bash fetch.sh <列表文件>
set -u
ROOT="/c/Users/Michael Song/Desktop/私人办公/A207123-任务C-显式公式与母函数"
OUT="$ROOT/data/oeis"
LOG="$ROOT/logs/c5b_fetch.log"
LIST="$1"
mkdir -p "$OUT"
touch "$LOG"
n=0
while IFS='|' read -r name url; do
  [ -z "${name:-}" ] && continue
  case "$name" in \#*) continue;; esac
  if awk -F'\t' -v u="$url" '$5==u{f=1} END{exit !f}' "$LOG"; then
    echo "SKIP (already fetched) $name"
    continue
  fi
  if [ -e "$OUT/$name" ]; then
    echo "SKIP (file exists) $name"
    continue
  fi
  ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  res=$(curl -sS --max-time 90 -o "$OUT/$name" -w '%{http_code}	%{size_download}' "$url" 2>&1)
  printf '%s\t%s\t%s\t%s\n' "$ts" "$name" "$res" "$url" >> "$LOG"
  echo "$ts $name $res"
  n=$((n+1))
  sleep 2
done < "$LIST"
echo "fetched $n new URL(s); total log lines: $(wc -l < "$LOG")"
