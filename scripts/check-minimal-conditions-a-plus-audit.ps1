Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$prohibitedPattern = "^\s*(axiom|unsafe)\b|\b(sorry|admit)\b"
$scanRoots = @(
    "MaleyLean\Papers\MinimalConditionsForAdmissibleConstruction",
    "Checks\Axiom"
)

$auditFiles = @(
    "Checks\Axiom\MinimalConditionsAPlusAudit.lean",
    "Checks\Axiom\MinimalConditionsAPlusSourceCrosswalkAudit.lean",
    "Checks\Axiom\MinimalConditionsAPlusProgressLedgerAudit.lean",
    "Checks\Axiom\MinimalConditionsAPlusResidualGateLedgerAudit.lean",
    "Checks\Axiom\MinimalConditionsAPlusResidualGateCallabilityAudit.lean",
    "Checks\Axiom\MinimalConditionsAPlusResidualGateSupplyQueueAudit.lean",
    "Checks\Axiom\MinimalConditionsAPlusCurrentFocusAudit.lean",
    "Checks\Axiom\NonDegenerateConstructionAndKernelOfAdmissibilityAxiomCheck.lean"
)

if ($auditFiles.Count -ne 8) {
    throw "Expected 8 kernel-paper A+ audit files, found $($auditFiles.Count)."
}

$uniqueAuditFiles = $auditFiles | Select-Object -Unique
if ($uniqueAuditFiles.Count -ne $auditFiles.Count) {
    throw "Kernel-paper A+ audit file list contains duplicates."
}

foreach ($auditFile in $auditFiles) {
    if (-not (Test-Path -LiteralPath $auditFile -PathType Leaf)) {
        throw "Missing kernel-paper A+ audit file: $auditFile"
    }
}

Write-Host "Lean toolchain:"
Get-Content -LiteralPath "lean-toolchain"

Write-Host "Mathlib manifest entry:"
$manifest = Get-Content -LiteralPath "lake-manifest.json" -Raw | ConvertFrom-Json
$mathlib = $manifest.packages | Where-Object { $_.name -eq "mathlib" } | Select-Object -First 1
if ($null -eq $mathlib) {
    throw "Could not locate mathlib in lake-manifest.json."
}
Write-Host ("mathlib rev: " + $mathlib.rev)

$rgArgs = @(
    "-n",
    "--glob",
    "*.lean",
    $prohibitedPattern
) + $scanRoots

$prohibitedMatches = & rg @rgArgs
if ($LASTEXITCODE -eq 0) {
    $prohibitedMatches | ForEach-Object { Write-Host $_ }
    throw "Prohibited Lean placeholder or escape found in Minimal Conditions audit surface."
}
if ($LASTEXITCODE -ne 1) {
    throw "Prohibited-token scan failed with exit code $LASTEXITCODE."
}
Write-Host "No live axiom/sorry/admit/unsafe declarations found in kernel-paper audit surface."

lake build MaleyLean.Papers.NonDegenerateConstructionAndKernelOfAdmissibility
foreach ($auditFile in $auditFiles) {
    lake env lean $auditFile
}
