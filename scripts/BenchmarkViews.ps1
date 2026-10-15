param(
    [ValidateRange(1, 512)][int]$Stores = 64,
    [ValidateRange(1, 10)][int]$Repetitions = 3
)

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot
$artifactDirectory = Join-Path $repoRoot 'artifacts/ViewBenchmark'
New-Item -ItemType Directory -Force -Path $artifactDirectory | Out-Null
Push-Location $repoRoot
try {
    & lake build Tests.ViewReuse > (Join-Path $artifactDirectory 'build.log') 2>&1
    if ($LASTEXITCODE -ne 0) { throw 'Benchmark dependencies failed to build.' }
    $results = @()
    for ($iteration = 1; $iteration -le $Repetitions; $iteration++) {
        $variants = if ($iteration % 2 -eq 1) { @('optimized', 'legacy') } else { @('legacy', 'optimized') }
        foreach ($variant in $variants) {
            $writer = if ($variant -eq 'optimized') { 'write' } else { 'writeAlwaysPrepend' }
            $viewCount = if ($variant -eq 'optimized') { 1 } else { $Stores + 1 }
            $sourcePath = Join-Path $artifactDirectory "$variant.lean"
            @"
import Tests.ViewReuse
open CIL.Safety Tests.ViewReuse
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
example : (stores $writer $Stores benchmarkMemory).map (·.views.length) = .ok $viewCount := rfl
"@ | Set-Content -LiteralPath $sourcePath -Encoding utf8
            $timer = [Diagnostics.Stopwatch]::StartNew()
            & lake env lean $sourcePath > (Join-Path $artifactDirectory "$variant-$iteration.log") 2>&1
            $exitCode = $LASTEXITCODE
            $timer.Stop()
            if ($exitCode -ne 0) { throw "Kernel reduction failed: $variant iteration $iteration" }
            $results += [pscustomobject]@{
                variant = $variant; iteration = $iteration; stores = $Stores
                views = $viewCount; milliseconds = $timer.ElapsedMilliseconds
            }
            Write-Output "$variant iteration $iteration`: $($timer.ElapsedMilliseconds) ms, $viewCount views"
        }
    }
    $results | Export-Csv -LiteralPath (Join-Path $artifactDirectory 'results.csv') -NoTypeInformation
}
finally { Pop-Location }
