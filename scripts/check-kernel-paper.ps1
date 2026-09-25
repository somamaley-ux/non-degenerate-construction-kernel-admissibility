[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
$runDirectory = Join-Path $repo 'validation/run'
$utf8 = [System.Text.UTF8Encoding]::new($false)
$approvedBaseAxioms = @('propext', 'Classical.choice', 'Quot.sound')
$anchorNames = @(
    'AASC.Instances.KernelPaper.Manuscript.targetAdequacy_forces_kernel_roles'
    'AASC.Instances.KernelPaper.Manuscript.construction_forces_kernel'
    'AASC.Instances.KernelPaper.Manuscript.no_self_faithful_counterexample'
    'AASC.Instances.KernelPaper.Manuscript.ConcreteWitness.adequacyRegime_nondegenerate'
    'AASC.Instances.KernelPaper.Manuscript.ConcreteWitness.endpoint_and_role_occupancy_closure'
    'AASC.Instances.KernelPaper.ManuscriptClosure.raw_trace_governance_requires_explicit_witness'
    'AASC.Instances.KernelPaper.ManuscriptClosure.derivation_presupposes_kernel'
    'AASC.Instances.KernelPaper.ManuscriptClosure.no_faithful_lower_generator'
    'AASC.Instances.KernelPaper.ManuscriptClosure.cross_domain_transport_preserves_reference_and_standing'
    'AASC.Instances.KernelPaper.ManuscriptClosure.mutual_kernel_closure'
    'AASC.Instances.KernelPaper.ManuscriptClosure.no_intermediate_status'
    'AASC.Instances.KernelPaper.ManuscriptClosure.relabeling_invariant_is_constant'
    'AASC.Instances.KernelPaper.ManuscriptClosure.scope_preserving_preserves_standing'
    'AASC.Instances.KernelPaper.ManuscriptClosure.constructional_report_preservation'
    'AASC.Instances.KernelPaper.ManuscriptClosure.main_fixed_domain_exhaustion'
)

function Write-Utf8File([string] $Path, [string] $Content) {
    [System.IO.File]::WriteAllText($Path, $Content, $utf8)
}

function Remove-LeanTrivia([string] $Text) {
    # Keep line positions while ignoring nested block comments, line comments,
    # and literal strings. The environment scan additionally checks elaborated
    # types and values for placeholders, including inside interpolated terms.
    $result = [System.Text.StringBuilder]::new($Text.Length)
    $depth = 0
    $inString = $false
    $lineComment = $false
    $i = 0
    while ($i -lt $Text.Length) {
        $c = $Text[$i]
        $pair = if ($i + 1 -lt $Text.Length) { $Text.Substring($i, 2) } else { '' }
        if ($lineComment) {
            if ($c -eq "`n") { $lineComment = $false; [void] $result.Append($c) }
            else { [void] $result.Append(' ') }
            $i++; continue
        }
        if ($depth -gt 0) {
            if ($pair -eq '/-') { $depth++; [void] $result.Append('  '); $i += 2; continue }
            if ($pair -eq '-/') { $depth--; [void] $result.Append('  '); $i += 2; continue }
            [void] $result.Append($(if ($c -eq "`n") { "`n" } else { ' ' }))
            $i++; continue
        }
        if ($inString) {
            if ($c -eq '\' -and $i + 1 -lt $Text.Length) {
                [void] $result.Append('  '); $i += 2; continue
            }
            if ($c -eq '"') { $inString = $false }
            [void] $result.Append($(if ($c -eq "`n") { "`n" } else { ' ' }))
            $i++; continue
        }
        if ($pair -eq '--') { $lineComment = $true; [void] $result.Append('  '); $i += 2; continue }
        if ($pair -eq '/-') { $depth = 1; [void] $result.Append('  '); $i += 2; continue }
        if ($c -eq '"') { $inString = $true; [void] $result.Append(' '); $i++; continue }
        [void] $result.Append($c)
        $i++
    }
    if ($depth -ne 0 -or $inString) { throw 'Unterminated Lean comment or string during source audit.' }
    return $result.ToString()
}

function Invoke-LakeChecked([string[]] $Arguments, [string] $LogName) {
    $output = @(& lake @Arguments 2>&1 | ForEach-Object { $_.ToString() })
    $code = $LASTEXITCODE
    Write-Utf8File (Join-Path $runDirectory $LogName) (($output -join "`n") + "`n")
    if ($code -ne 0) {
        throw "lake $($Arguments -join ' ') failed (exit $code). See validation/run/$LogName.`n$($output -join "`n")"
    }
    return $output
}

function Assert-ExactNames([string[]] $Expected, [string[]] $Actual, [string] $Label) {
    $expectedSet = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
    $actualSet = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
    foreach ($name in $Expected) {
        if (-not $expectedSet.Add($name)) { throw "$Label has duplicate expected identity: $name" }
    }
    foreach ($name in $Actual) {
        if (-not $actualSet.Add($name)) { throw "$Label has duplicate reported identity: $name" }
    }
    $missing = @($Expected | Where-Object { -not $actualSet.Contains($_) })
    $extra = @($Actual | Where-Object { -not $expectedSet.Contains($_) })
    if ($missing.Count -or $extra.Count -or $Expected.Count -ne $Actual.Count) {
        throw "$Label identity/count mismatch. Expected $($Expected.Count), received $($Actual.Count). Missing: $($missing -join ', '). Extra: $($extra -join ', ')."
    }
}

function Read-AxiomReports([string[]] $Output, [string[]] $Expected, [string] $Label) {
    $joined = $Output -join "`n"
    $pattern = "(?m)^'(?<name>[^\r\n]+)'\s+(?:depends on axioms:\s*\[(?<axioms>[^\]]*)\]|does not depend on any axioms)"
    $reports = @()
    foreach ($match in [regex]::Matches($joined, $pattern)) {
        $dependencies = @($match.Groups['axioms'].Value.Split(',') |
            ForEach-Object { $_.Trim() } | Where-Object { $_ })
        foreach ($dependency in $dependencies) {
            if ($approvedBaseAxioms -cnotcontains $dependency) {
                throw "$Label unexpected axiom '$dependency' in '$($match.Groups['name'].Value)'."
            }
        }
        $reports += [ordered]@{ name = $match.Groups['name'].Value; axioms = $dependencies }
    }
    Assert-ExactNames $Expected @($reports | ForEach-Object { $_.name }) $Label
    return $reports
}

function Read-MarkedJson([string[]] $Output, [string] $Marker) {
    $items = @()
    foreach ($line in $Output) {
        if ($line.StartsWith($Marker, [System.StringComparison]::Ordinal)) {
            $items += ($line.Substring($Marker.Length) | ConvertFrom-Json)
        }
    }
    return $items
}

function Get-ProjectLeanSources {
    $files = @(Get-ChildItem -LiteralPath $repo -File -Filter '*.lean')
    foreach ($folder in @('AASC', 'Extensions', 'KernelReference', 'Checks')) {
        $folderPath = Join-Path $repo $folder
        if (Test-Path -LiteralPath $folderPath -PathType Container) {
            $files += @(Get-ChildItem -LiteralPath $folderPath -Recurse -File -Filter '*.lean')
        }
    }
    return @($files | Sort-Object FullName -Unique)
}

function Assert-ParserRejects([scriptblock] $Probe, [string] $Label) {
    $rejected = $false
    try { $null = & $Probe } catch { $rejected = $true }
    if (-not $rejected) { throw "Axiom parser self-check accepted $Label." }
}
function Get-SourceSnapshot([System.IO.FileInfo[]] $Files) {
    return @($Files | Sort-Object FullName | ForEach-Object {
        [ordered]@{
            path = [System.IO.Path]::GetRelativePath($repo, $_.FullName).Replace('\', '/')
            sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
        }
    })
}

[void] [System.IO.Directory]::CreateDirectory($runDirectory)
$audit = [ordered]@{
    schemaVersion = 1
    status = 'running'
    startedUtc = [DateTime]::UtcNow.ToString('o')
    approvedBaseAxioms = $approvedBaseAxioms
    inventoryMethod = 'Lean environment: defining project module and public theorem declaration kind'
    trustBoundary = 'Transitive theorem axiom audit; explicit theorem hypotheses and concrete domain interpretations require separate review.'
}
Write-Utf8File (Join-Path $runDirectory 'audit.json') ($audit | ConvertTo-Json -Depth 20)

$oldCacheSetting = $env:MATHLIB_NO_CACHE_ON_UPDATE
Push-Location $repo
try {
    # Exercise the historical failure modes: empty or partial output, duplicate
    # identities, unrelated reports, and an unapproved dependency must all fail.
    $probeNames = @('Audit.fixture')
    $probeValid = @("'Audit.fixture' depends on axioms: [propext,", ' Classical.choice, Quot.sound]')
    $null = Read-AxiomReports $probeValid $probeNames 'Parser valid fixture'
    Assert-ParserRejects { Read-AxiomReports @() $probeNames 'empty fixture' } 'empty output'
    Assert-ParserRejects { Read-AxiomReports $probeValid @('Audit.fixture', 'Audit.missing') 'missing fixture' } 'a missing theorem'
    Assert-ParserRejects { Read-AxiomReports ($probeValid + $probeValid) $probeNames 'duplicate fixture' } 'duplicate theorem reports'
    Assert-ParserRejects { Read-AxiomReports @("'Audit.other' does not depend on any axioms") $probeNames 'foreign fixture' } 'an unrelated theorem identity'
    Assert-ParserRejects { Read-AxiomReports @("'Audit.fixture' depends on axioms: [sorryAx]") $probeNames 'unapproved fixture' } 'an unapproved dependency'
    $audit.reportParserSelfChecks = @('valid multiline report accepted', 'empty output rejected',
        'missing identity rejected', 'duplicate identity rejected', 'foreign identity rejected', 'unapproved axiom rejected')
    $allLeanFiles = @(Get-ProjectLeanSources)
    $auditInputs = @($allLeanFiles)
    foreach ($relative in @('scripts/check-kernel-paper.ps1', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')) {
        $auditInputs += Get-Item -LiteralPath (Join-Path $repo $relative)
    }
    $initialSnapshot = Get-SourceSnapshot $auditInputs
    $forbidden = '\b(?:axiom|opaque|unsafe|sorry|admit|sorryAx)\b|(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|local)\s+)*(?:constant|constants)\b'
    $legacy = 'MaleyLean|SunflowerAASC|MechanizedKernelImport|APlusAudit|PaperStatements|V22PaperStatements'
    foreach ($file in $allLeanFiles) {
        $code = Remove-LeanTrivia ([System.IO.File]::ReadAllText($file.FullName))
        $bad = [regex]::Match($code, $forbidden)
        if ($bad.Success) {
            $line = 1 + [regex]::Matches($code.Substring(0, $bad.Index), "`n").Count
            throw "Forbidden Lean token/declaration at $($file.FullName):${line}: $($bad.Value)"
        }
        if ([regex]::IsMatch($code, $legacy)) { throw "Legacy/mixed import or reference in $($file.FullName)." }
    }
    foreach ($relative in @('lakefile.toml', 'lake-manifest.json')) {
        $metadata = [System.IO.File]::ReadAllText((Join-Path $repo $relative))
        if ($metadata -match 'AASCMathlib|NonDegenerateConstructionAndKernelOfAdmissibility|MaleyLean|SunflowerAASC|MechanizedKernelImport') {
            throw "Legacy or mixed-package dependency in $relative."
        }
    }
    $audit.sourceScanFileCount = $allLeanFiles.Count
    $audit.sourceScanPassed = $true

    $trustCode = Remove-LeanTrivia ([System.IO.File]::ReadAllText((Join-Path $repo 'Checks/KernelPaperTrust.lean')))
    $trustDeclarations = @([regex]::Matches($trustCode, '(?m)^\s*#print\s+axioms\s+(\S+)\s*$') |
        ForEach-Object { $_.Groups[1].Value })
    Assert-ExactNames $anchorNames $trustDeclarations 'Original 15 trust commands'

    $env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
    Write-Host 'Building all project libraries and the paper target...'
    $null = Invoke-LakeChecked @('build', 'AASC', 'Extensions', 'KernelReference', 'AASCKernelPaperClean') 'build.log'
    $audit.buildPassed = $true
    $audit.toolchain = ([System.IO.File]::ReadAllText((Join-Path $repo 'lean-toolchain'))).Trim()
    $audit.leanVersion = (Invoke-LakeChecked @('env', 'lean', '--version') 'lean-version.log') -join "`n"

    $anchorOutput = @(Invoke-LakeChecked @('env', 'lean', 'Checks/KernelPaperTrust.lean') 'anchor-axioms.log')
    $anchorReports = @(Read-AxiomReports $anchorOutput $anchorNames 'Original 15 anchor reports')
    $audit.anchorTheoremCount = $anchorReports.Count
    $audit.anchorReports = $anchorReports

    Write-Host 'Enumerating project theorems from the compiled Lean environment...'
    $inventoryOutput = @(Invoke-LakeChecked @('env', 'lean', 'Checks/ProjectDeclarations.lean') 'project-inventory.log')
    $declarations = @(Read-MarkedJson $inventoryOutput 'PROJECT_THEOREM_JSON|' | Sort-Object name)
    $modules = @(Read-MarkedJson $inventoryOutput 'PROJECT_MODULE_JSON|')
    $summary = @(Read-MarkedJson $inventoryOutput 'PROJECT_INVENTORY_JSON|')
    if ($summary.Count -ne 1 -or $declarations.Count -eq 0 -or $summary[0].publicTheorems -ne $declarations.Count) {
        throw 'Missing, empty, or inconsistent project theorem inventory.'
    }
    if ($summary[0].projectModules -ne $modules.Count) { throw 'Inconsistent project module inventory.' }
    $expectedModules = @($allLeanFiles | Where-Object {
        -not ([System.IO.Path]::GetRelativePath($repo, $_.FullName).Replace('\', '/').StartsWith('Checks/'))
    } | ForEach-Object {
        [System.IO.Path]::GetRelativePath($repo, $_.FullName).Replace('\', '/').Replace('/', '.').Substring(0,
            [System.IO.Path]::GetRelativePath($repo, $_.FullName).Length - 5)
    })
    Assert-ExactNames $expectedModules @($modules | ForEach-Object { $_.module }) 'Imported project modules'
    $allNames = @($declarations | ForEach-Object { $_.name })
    $uniqueCheck = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
    foreach ($name in $allNames) {
        if (-not $uniqueCheck.Add($name)) { throw "Duplicate environment theorem: $name" }
    }
    foreach ($anchor in $anchorNames) {
        if (-not $uniqueCheck.Contains($anchor)) { throw "Anchor missing from environment theorem inventory: $anchor" }
    }
    $generated = @('import AASC', 'import AASCKernelPaperClean', '') +
        @($allNames | ForEach-Object { '#print axioms _root_.' + $_ })
    Write-Utf8File (Join-Path $runDirectory 'AllProjectAxioms.lean') (($generated -join "`n") + "`n")
    $allOutput = @(Invoke-LakeChecked @('env', 'lean', 'validation/run/AllProjectAxioms.lean') 'all-project-axioms.log')
    $allReports = @(Read-AxiomReports $allOutput $allNames 'All project theorem reports')
    $audit.projectModuleCount = $modules.Count
    $audit.projectModules = @($modules | ForEach-Object { $_.module } | Sort-Object)
    $audit.allProjectConstantCount = $summary[0].allProjectConstants
    $audit.publicProjectTheoremCount = $declarations.Count
    $audit.auditedProjectTheoremCount = $allReports.Count
    $audit.publicProjectDeclarations = $declarations
    $audit.projectTheoremsByModule = @($declarations | Group-Object module | Sort-Object Name |
        ForEach-Object { [ordered]@{ module = $_.Name; theorems = $_.Count } })
    $audit.projectAxiomReports = $allReports
    $audit.exactReportCoveragePassed = $true

    $null = Invoke-LakeChecked @('env', 'lean', 'Checks/KernelPaperSemantic.lean') 'semantic.log'
    $audit.semanticChecksPassed = $true
    $finalLeanFiles = @(Get-ProjectLeanSources)
    Assert-ExactNames @($allLeanFiles | ForEach-Object { $_.FullName }) `
        @($finalLeanFiles | ForEach-Object { $_.FullName }) 'Lean source file-set stability'
    $finalSnapshot = Get-SourceSnapshot $auditInputs
    $initialByPath = @{}
    foreach ($item in $initialSnapshot) { $initialByPath[$item.path] = $item.sha256 }
    foreach ($item in $finalSnapshot) {
        if ($initialByPath[$item.path] -cne $item.sha256) { throw "Audit input changed during verification: $($item.path)" }
    }
    $audit.sourceSHA256 = $finalSnapshot
    $audit.generatedAxiomCommandsSHA256 = (Get-FileHash -LiteralPath (Join-Path $runDirectory 'AllProjectAxioms.lean') -Algorithm SHA256).Hash.ToLowerInvariant()
    $audit.manifestSHA256 = (Get-FileHash -LiteralPath 'lake-manifest.json' -Algorithm SHA256).Hash.ToLowerInvariant()
    $audit.status = 'passed'
    $audit.completedUtc = [DateTime]::UtcNow.ToString('o')
    Write-Utf8File (Join-Path $runDirectory 'audit.json') ($audit | ConvertTo-Json -Depth 20)
    Write-Host "PASS: $($anchorReports.Count) original anchors; $($allReports.Count) / $($declarations.Count) public project theorem axiom reports; $($modules.Count) project modules; semantic checks."
    Write-Host 'Machine-readable evidence: validation/run/audit.json'
}
catch {
    $audit.status = 'failed'
    $audit.completedUtc = [DateTime]::UtcNow.ToString('o')
    $audit.error = $_.Exception.Message
    Write-Utf8File (Join-Path $runDirectory 'audit.json') ($audit | ConvertTo-Json -Depth 20)
    throw
}
finally {
    if ($null -eq $oldCacheSetting) { Remove-Item Env:MATHLIB_NO_CACHE_ON_UPDATE -ErrorAction SilentlyContinue }
    else { $env:MATHLIB_NO_CACHE_ON_UPDATE = $oldCacheSetting }
    Pop-Location
}
