$ErrorActionPreference = "Stop"

$repo = Split-Path -Parent $PSScriptRoot
$canonicalFiles = @(
    Get-ChildItem -LiteralPath (Join-Path $repo "AASC") -Recurse -Filter *.lean |
        Select-Object -ExpandProperty FullName
)

Push-Location $repo
try {
    $forbiddenPattern = '^\s*(?:(?:private|protected)\s+)*(?:axiom|opaque|constant|constants|unsafe)\s+|^\s*(?:sorry|admit)\b|:=\s*(?:sorry|admit)\b|\bsorryAx\b'
    $forbidden = rg -n -P --glob '*.lean' $forbiddenPattern `
        AASCKernelPaperClean.lean Checks
    if ($LASTEXITCODE -eq 0) {
        throw "Forbidden declarations found:`n$forbidden"
    }
    if ($LASTEXITCODE -gt 1) {
        throw "Source audit scan failed."
    }

    $canonicalForbidden = rg -n -P $forbiddenPattern $canonicalFiles
    if ($LASTEXITCODE -eq 0) {
        throw "Forbidden declarations found in the vendored AASC kernel source:`n$canonicalForbidden"
    }
    if ($LASTEXITCODE -gt 1) {
        throw "Vendored source audit scan failed."
    }

    $legacy = rg -n `
        'MaleyLean|SunflowerAASC|MechanizedKernelImport|APlusAudit|PaperStatements|V22PaperStatements' `
        AASCKernelPaperClean.lean Checks
    if ($LASTEXITCODE -eq 0) {
        throw "Legacy kernel or sunflower import found in the standalone target:`n$legacy"
    }
    if ($LASTEXITCODE -gt 1) {
        throw "Legacy-import scan failed."
    }

    $canonicalLegacy = rg -n `
        'MaleyLean|SunflowerAASC|MechanizedKernelImport|APlusAudit|PaperStatements|V22PaperStatements' `
        $canonicalFiles
    if ($LASTEXITCODE -eq 0) {
        throw "Legacy kernel or sunflower import found in the vendored AASC kernel source:`n$canonicalLegacy"
    }
    if ($LASTEXITCODE -gt 1) {
        throw "Vendored legacy-import scan failed."
    }

    $metadataLegacy = rg -n `
        'AASCMathlib|NonDegenerateConstructionAndKernelOfAdmissibility|MaleyLean|SunflowerAASC|MechanizedKernelImport' `
        lakefile.toml lake-manifest.json
    if ($LASTEXITCODE -eq 0) {
        throw "Legacy or mixed-package dependency found in standalone metadata:`n$metadataLegacy"
    }
    if ($LASTEXITCODE -gt 1) {
        throw "Standalone metadata scan failed."
    }

    $previousMathlibCacheSetting = $env:MATHLIB_NO_CACHE_ON_UPDATE
    $env:MATHLIB_NO_CACHE_ON_UPDATE = "1"
    lake build AASCKernelPaperClean
    if ($null -eq $previousMathlibCacheSetting) {
        Remove-Item Env:MATHLIB_NO_CACHE_ON_UPDATE -ErrorAction SilentlyContinue
    } else {
        $env:MATHLIB_NO_CACHE_ON_UPDATE = $previousMathlibCacheSetting
    }
    if ($LASTEXITCODE -ne 0) {
        throw "Standalone kernel-paper build failed."
    }

    $trustOutput = & lake env lean Checks/KernelPaperTrust.lean 2>&1
    $trustOutput | Write-Host
    if ($LASTEXITCODE -ne 0) {
        throw "Standalone kernel-paper axiom audit failed."
    }

    $approvedBaseAxioms = @("propext", "Classical.choice", "Quot.sound")
    $joinedTrustOutput = $trustOutput -join "`n"
    $dependencies = [regex]::Matches(
        $joinedTrustOutput,
        "depends on axioms:\s*\[([^]]*)\]",
        [System.Text.RegularExpressions.RegexOptions]::Singleline
    )
    $unexpected = @()
    foreach ($dependencyMatch in $dependencies) {
        foreach ($dependency in $dependencyMatch.Groups[1].Value.Split(',')) {
            $name = $dependency.Trim()
            if ($name -and $approvedBaseAxioms -notcontains $name) {
                $unexpected += $name
            }
        }
    }
    if ($unexpected) {
        throw "Unexpected axiom dependency:`n$($unexpected -join "`n")"
    }

    & lake env lean Checks/KernelPaperSemantic.lean
    if ($LASTEXITCODE -ne 0) {
        throw "Standalone kernel-paper semantic audit failed."
    }

    Write-Host "Standalone clean kernel-paper build, trust audit, and semantic audit passed."
}
finally {
    Pop-Location
}
