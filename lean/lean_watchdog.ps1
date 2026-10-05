# Memory watchdog for one Lean run (used by lean_one.sh). Keep this file ASCII-only.
# Every second: sum the private (committed) memory of all lean.exe processes that descend from RootPid,
# and read the system commit headroom (CommitLimit - CommittedBytes).
# Kill the whole process tree of RootPid if
#   (a) the lean.exe private memory exceeds CapMB, or
#   (b) the system commit headroom drops below MinHeadroomMB while Lean is running.
# On exit (root gone or killed) write one line to StatusFile:
#   PEAK=<max lean private MB> MINHEAD=<min headroom MB seen> KILLED=<0|1> REASON=<text>
# Private memory (commit) is used on purpose: under paging the working set stays small while the
# commit charge keeps growing, and commit exhaustion is what crashed the machine on 2026-10-05 22:46.
param(
  [int]$RootPid,
  [int]$CapMB = 10000,
  [int]$MinHeadroomMB = 3000,
  [string]$StatusFile
)
$peak = 0
$minHead = [int64]::MaxValue
$killed = 0
$reason = ''
while ($true) {
  if (-not (Get-Process -Id $RootPid -ErrorAction SilentlyContinue)) { break }
  $all = @(Get-CimInstance Win32_Process -Property ProcessId, ParentProcessId, Name, PrivatePageCount)
  $children = @{}
  foreach ($p in $all) {
    $pp = [int]$p.ParentProcessId
    if (-not $children.ContainsKey($pp)) { $children[$pp] = New-Object System.Collections.ArrayList }
    [void]$children[$pp].Add($p)
  }
  $leanMB = 0
  $stack = New-Object System.Collections.Stack
  $stack.Push([int]$RootPid)
  $seen = @{}
  while ($stack.Count -gt 0) {
    $cur = $stack.Pop()
    if ($seen.ContainsKey($cur)) { continue }
    $seen[$cur] = $true
    if ($children.ContainsKey($cur)) {
      foreach ($c in $children[$cur]) {
        if ($c.Name -eq 'lean.exe') { $leanMB += [int64]($c.PrivatePageCount / 1048576) }
        $stack.Push([int]$c.ProcessId)
      }
    }
  }
  if ($leanMB -gt $peak) { $peak = $leanMB }
  $perf = Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory
  $head = [int64](($perf.CommitLimit - $perf.CommittedBytes) / 1048576)
  if ($head -lt $minHead) { $minHead = $head }
  if ($leanMB -gt $CapMB) {
    $killed = 1; $reason = "lean private $leanMB MB > cap $CapMB MB"
  } elseif ($leanMB -gt 0 -and $head -lt $MinHeadroomMB) {
    $killed = 1; $reason = "system commit headroom $head MB < $MinHeadroomMB MB"
  }
  if ($killed -eq 1) {
    & taskkill.exe /PID $RootPid /T /F | Out-Null
    break
  }
  Start-Sleep -Milliseconds 1000
}
if ($minHead -eq [int64]::MaxValue) { $minHead = -1 }
"PEAK=$peak MINHEAD=$minHead KILLED=$killed REASON=$reason" | Out-File -FilePath $StatusFile -Encoding ascii
