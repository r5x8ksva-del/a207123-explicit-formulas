# Memory watchdog for one non-Lean job (used by code/main_extra/run_guarded.sh). Keep this file ASCII-only.
# Every second: sum the private (committed) memory of RootPid and all of its descendants (any process name),
# and read the system commit headroom (CommitLimit - CommittedBytes) and the available physical memory.
# Kill the whole process tree of RootPid if
#   (a) the tree's private memory exceeds CapMB, or
#   (b) the system commit headroom drops below MinHeadroomMB, or
#   (c) the memory could not be read MaxFail seconds in a row (the watchdog would be blind).
# Commit (private memory) is watched on purpose: commit exhaustion is what crashed the machine on 2026-10-05.
# A single failed WMI query (seen 2026-10-07: Win32_PerfFormattedData_PerfOS_Memory returned nothing,
# HRESULT 0x80041032) used to be read as "headroom 0 MB" and killed a 23 MB job. Now a failed sample falls
# back to Win32_OperatingSystem, and if that fails too the sample is skipped; only (c) kills on failures.
# At start write STARTED to StatusFile (run_guarded.sh waits for it, so a watchdog that failed to start is noticed).
# On exit (root gone or killed) overwrite StatusFile with one line:
#   PEAK=<max tree private MB> MINHEAD=<min headroom MB> MINAVAIL=<min available MB> KILLED=<0|1> REASON=<text> QFAIL=<failed samples>
# Test hooks (never set them in normal use): PerfClass / OsClass replace the two WMI class names.
param(
  [int]$RootPid,
  [int]$CapMB = 4000,
  [int]$MinHeadroomMB = 3000,
  [string]$StatusFile,
  [int]$MaxFail = 5,
  [string]$PerfClass = 'Win32_PerfFormattedData_PerfOS_Memory',
  [string]$OsClass = 'Win32_OperatingSystem'
)

# Returns @(headroomMB, availMB), or $null when neither source gives a usable reading.
function Get-MemReading {
  try {
    $perf = Get-CimInstance $PerfClass -ErrorAction Stop
    if ($perf -and [int64]$perf.CommitLimit -gt 0) {
      return @([int64](([int64]$perf.CommitLimit - [int64]$perf.CommittedBytes) / 1048576), [int64]$perf.AvailableMBytes)
    }
  } catch {}
  try {
    # TotalVirtualMemorySize / FreeVirtualMemory (KB) are the commit limit / unused commit.
    # FreePhysicalMemory excludes the standby list, so it is a lower bound for "available"; only reported.
    $os = Get-CimInstance $OsClass -ErrorAction Stop
    if ($os -and [int64]$os.TotalVirtualMemorySize -gt 0) {
      return @([int64]([int64]$os.FreeVirtualMemory / 1024), [int64]([int64]$os.FreePhysicalMemory / 1024))
    }
  } catch {}
  return $null
}

"STARTED" | Out-File -FilePath $StatusFile -Encoding ascii
$peak = 0
$minHead = [int64]::MaxValue
$minAvail = [int64]::MaxValue
$killed = 0
$reason = ''
$fail = 0
$qfail = 0
while ($true) {
  if (-not (Get-Process -Id $RootPid -ErrorAction SilentlyContinue)) { break }
  $all = @(Get-CimInstance Win32_Process -Property ProcessId, ParentProcessId, PrivatePageCount -ErrorAction SilentlyContinue)
  $mem = Get-MemReading
  if ($all.Count -eq 0 -or $null -eq $mem) {
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
  $priv = @{}
  foreach ($p in $all) {
    $id = [int]$p.ProcessId
    $pp = [int]$p.ParentProcessId
    $priv[$id] = [int64]$p.PrivatePageCount
    if ($pp -eq $id) { continue }
    if (-not $children.ContainsKey($pp)) { $children[$pp] = New-Object System.Collections.ArrayList }
    [void]$children[$pp].Add($id)
  }
  $treeMB = 0
  $stack = New-Object System.Collections.Stack
  $stack.Push([int]$RootPid)
  $seen = @{}
  while ($stack.Count -gt 0) {
    $cur = $stack.Pop()
    if ($seen.ContainsKey($cur)) { continue }
    $seen[$cur] = $true
    if ($priv.ContainsKey($cur)) { $treeMB += [int64]($priv[$cur] / 1048576) }
    if ($children.ContainsKey($cur)) { foreach ($c in $children[$cur]) { $stack.Push($c) } }
  }
  if ($treeMB -gt $peak) { $peak = $treeMB }
  $head = $mem[0]
  $avail = $mem[1]
  if ($head -lt $minHead) { $minHead = $head }
  if ($avail -lt $minAvail) { $minAvail = $avail }
  if ($treeMB -gt $CapMB) {
    $killed = 1; $reason = "job private $treeMB MB > cap $CapMB MB"
  } elseif ($head -lt $MinHeadroomMB) {
    $killed = 1; $reason = "system commit headroom $head MB < $MinHeadroomMB MB"
  }
  if ($killed -eq 1) {
    & taskkill.exe /PID $RootPid /T /F | Out-Null
    break
  }
  Start-Sleep -Milliseconds 1000
}
if ($minHead -eq [int64]::MaxValue) { $minHead = -1 }
if ($minAvail -eq [int64]::MaxValue) { $minAvail = -1 }
"PEAK=$peak MINHEAD=$minHead MINAVAIL=$minAvail KILLED=$killed REASON=$reason QFAIL=$qfail" | Out-File -FilePath $StatusFile -Encoding ascii
