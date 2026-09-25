# v0.3.2 verification

The canonical build and audit passed on the frozen proof, configuration, and script inputs on 25 September 2026.

- 54 project Lean source files scanned.
- All 51 project library modules imported and built.
- All 2,814 project constants inspected for forbidden declaration kinds, unsafe definitions, and placeholders, including private helpers.
- 911 of 911 public project theorem declarations received exact transitive axiom reports.
- All 15 original named anchors reported exactly once.
- Only `propext`, `Classical.choice`, and `Quot.sound` occurred.
- Original semantic examples and six report-parser fixtures passed.
- The source file set and recorded source/configuration/script hashes remained fixed during verification.

The machine-readable [audit record](v0.3.2-audit.json) identifies every audited theorem, defining module, axiom dependency, toolchain, and source hash. Counts include generated public equation lemmas, not independent manuscript results. The [v0.3.1 verification](v0.3.1-verification.md) is retained as historical evidence.

## Manuscript and interpretation review

The v51.2 project contains independent hostile and publication reviews, their final disposition, theorem/formula/numbering checks, a clean rebuild comparison, and PDF layout verification. The necessity exposition distinguishes work in the actual incidence from any later account of it. Intrinsic joint satisfaction precedes A4 accountability; functional non-omissibility permits overlap and compression. The reconstruction does not independently establish its conceptual premises.

All Lean definitions, proofs, imports, and audit procedures are unchanged from v0.3.1. The package version is the only changed audited configuration input. The documentation makes no new machine-checked claim. All 60 manuscript statements, mathematical expressions, and 90 label numbers are preserved; explanatory and proof prose supplies the explicit interpretation.

The supported audit is `pwsh -NoProfile -File scripts/check-kernel-paper.ps1`.
