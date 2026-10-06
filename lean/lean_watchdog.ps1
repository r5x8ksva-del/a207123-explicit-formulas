# Memory watchdog for one Lean run (used by lean_one.sh). Keep this file ASCII-only.
# Every second: sum the private (committed) memory of all lean.exe processes that descend from RootPid,
# and read the system commit headroom (CommitLimit - CommittedBytes).
# Kill the whole process tree of RootPid if
#   (a) the lean.exe private memory exceeds CapMB, or
#   (b) the system commit headroom drops below MinHeadroomMB while Lean is running, or
#   (c) the memory could not be read MaxFail seconds in a row (the watchdog would be blind; a Lean
#       run can grow by gigabytes in that time, so being blind for longer is not acceptable).
# On exit (root gone or killed) write one line to StatusFile:
#   PEAK=<max lean private MB> MINHEAD=<min headroom MB seen> KILLED=<0|1> REASON=<text> QFAIL=<failed samples>
# Private memory (commit) is used on purpose: under paging the working set stays small while the
# commit charge keeps growing, and commit exhaustion is what crashed the machine on 2026-10-05 22:46.
# A single failed WMI query (seen 2026-10-07 in the non-Lean watchdog: Win32_PerfFormattedData_PerfOS_Memory
# returned nothing, HRESULT 0x80041032) used to be read as "headroom 0 MB" and killed the job. Now a failed
# sample falls back to Win32_OperatingSystem, and if that fails too the sample is skipped; only (c) kills on failures.
# Test hooks (never set them in normal use): PerfClass / OsClass replace the two WMI class names.
param(
  [int]$RootPid,
  [int]$CapMB = 10000,
  [int]$MinHeadroomMB = 3000,
  [string]$StatusFile,
  [int]$MaxFail = 5,
  [string]$PerfClass = 'Win32_PerfFormattedData_PerfOS_Memory',
  [string]$OsClass = 'Win32_OperatingSystem'
)

# Returns the commit headroom in MB, or $null when neither source gives a usable reading.
function Get-Headroom {
  try {
    $perf = Get-CimInstance $PerfClass -ErrorAction Stop
    if ($perf -and [int64]$perf.CommitLimit -gt 0) {
      return [int64](([int64]$perf.CommitLimit - [int64]$perf.CommittedBytes) / 1048576)
    }
  } catch {}
  try {
    # TotalVirtualMemorySize / FreeVirtualMemory (KB) are the commit limit / unused commit.
    $os = Get-CimInstance $OsClass -ErrorAction Stop
    if ($os -and [int64]$os.TotalVirtualMemorySize -gt 0) {
      return [int64]([int64]$os.FreeVirtualMemory / 1024)
    }
  } catch {}
  return $null
}

$peak = 0
$minHead = [int64]::MaxValue
$killed = 0
$reason = ''
$fail = 0
$qfail = 0
while ($true) {
  if (-not (Get-Process -Id $RootPid -ErrorAction SilentlyContinue)) { break }
  $all = @(Get-CimInstance Win32_Process -Property ProcessId, ParentProcessId, Name, PrivatePageCount -ErrorAction SilentlyContinue)
  $head = Get-Headroom
  if ($all.Count -eq 0 -or $null -eq $head) {
    $fail += 1
    $qfail += 1
    if ($fail -ge $MaxFail) {
      $killed = 1; $reason = "memory could not be read for $fail samples in a row"
      & taskkill.exe /PID $RootPid /T /F | Out-Null
      break
    }
    Start-Sleep -Milliseconds 1000
    continue
  }
  $fail = 0
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
"PEAK=$peak MINHEAD=$minHead KILLED=$killed REASON=$reason QFAIL=$qfail" | Out-File -FilePath $StatusFile -Encoding ascii
