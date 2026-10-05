# Print memory status in MB (read-only), used by the memory gate in lean_one.sh.
# Output (one line): AVAIL=<available physical> COMMIT=<committed> LIMIT=<commit limit> HEADROOM=<limit-commit> TOTAL=<physical>
# NOTE: keep this file ASCII-only (Windows PowerShell 5.1 reads BOM-less files as ANSI/GBK).
$os = Get-CimInstance Win32_OperatingSystem
$perf = Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory
$avail = [int64]$perf.AvailableMBytes
$commit = [int64]($perf.CommittedBytes / 1048576)
$limit = [int64]($perf.CommitLimit / 1048576)
$total = [int64]($os.TotalVisibleMemorySize / 1024)
"AVAIL=$avail COMMIT=$commit LIMIT=$limit HEADROOM=$($limit - $commit) TOTAL=$total"
