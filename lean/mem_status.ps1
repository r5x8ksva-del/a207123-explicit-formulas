# Print memory status in MB (read-only), used by the memory gates in lean_one.sh and code/main_extra/run_guarded.sh.
# Output (one line): AVAIL=<available physical> COMMIT=<committed> LIMIT=<commit limit> HEADROOM=<limit-commit> TOTAL=<physical>
# If Win32_PerfFormattedData_PerfOS_Memory fails (seen 2026-10-07, HRESULT 0x80041032), fall back to
# Win32_OperatingSystem (AVAIL is then FreePhysicalMemory, a lower bound). If both fail, print -1 values,
# which the gates treat as "not enough memory" (they never start a job on a failed reading).
# NOTE: keep this file ASCII-only (Windows PowerShell 5.1 reads BOM-less files as ANSI/GBK).
$avail = -1; $commit = -1; $limit = -1; $total = -1
$os = $null
try { $os = Get-CimInstance Win32_OperatingSystem -ErrorAction Stop } catch {}
if ($os -and [int64]$os.TotalVisibleMemorySize -gt 0) { $total = [int64]($os.TotalVisibleMemorySize / 1024) }
$perf = $null
try { $perf = Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory -ErrorAction Stop } catch {}
if ($perf -and [int64]$perf.CommitLimit -gt 0) {
  $avail = [int64]$perf.AvailableMBytes
  $commit = [int64]($perf.CommittedBytes / 1048576)
  $limit = [int64]($perf.CommitLimit / 1048576)
} elseif ($os -and [int64]$os.TotalVirtualMemorySize -gt 0) {
  $avail = [int64]($os.FreePhysicalMemory / 1024)
  $limit = [int64]($os.TotalVirtualMemorySize / 1024)
  $commit = $limit - [int64]($os.FreeVirtualMemory / 1024)
}
if ($limit -ge 0 -and $commit -ge 0) { $head = $limit - $commit } else { $head = -1 }
"AVAIL=$avail COMMIT=$commit LIMIT=$limit HEADROOM=$head TOTAL=$total"
