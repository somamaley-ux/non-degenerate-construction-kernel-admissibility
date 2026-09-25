# v0.3.0 verification

The canonical verification script passed on the frozen proof, configuration, and script inputs on 25 September 2026.

- 54 project Lean source files scanned.
- All 51 project library modules imported and built.
- All 2,814 project constants inspected for forbidden declaration kinds, unsafe definitions and placeholders, including private helpers.
- 911 of 911 public project theorem declarations received exact transitive axiom reports.
- All 15 original named anchors reported exactly once.
- Only `propext`, `Classical.choice`, and `Quot.sound` occurred.
- All five original semantic examples compiled; the reference modules also compile their concrete examples and counterexamples.
- All six report-parser fixtures passed.
- The source file set and all 58 recorded source/configuration/script hashes remained fixed during verification.

The machine-readable [audit record](v0.3.0-audit.json) identifies every audited theorem, defining module, axiom dependency, toolchain, and source hash. Counts include compiler-generated public equation lemmas; they are not counts of independent manuscript results. The earlier [v0.2.0 verification](v0.2.0-verification.md) and its audit remain historical evidence.

## Independent mathematical and publication review

Separate review roles checked the necessity construction, universal exact-realization criterion, identity and non-substitution implications, actual-incidence authorization bridge, typed contextual composition, comparison completeness, and reindexing. No hidden A1–A4, kernel-governance, agreement, or global soundness premise supplies these conclusions. Exact realization includes both preservation and reflection, with witnessed omission, surplus, and fibre collision.

The v51 manuscript package contains the detailed independent reports, publication disposition, stable-number check, clean-build comparison, and PDF inspection record. The necessity chain has checked mathematical content. Its interpretation as actual original physical or mathematical incidence is explicitly defended in the manuscript; particular domain identifications and physical laws retain their own evidential requirements.

The original AASC and Extensions source API is unchanged in this release. The five new reference modules are additive; the umbrella import and package version are updated. The supported audit remains `pwsh -NoProfile -File scripts/check-kernel-paper.ps1`.
