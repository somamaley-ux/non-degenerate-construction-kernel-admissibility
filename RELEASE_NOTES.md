# Release notes — v0.1.0

Initial standalone release of the clean Lean formalization of the latest
*Non-Degenerate Construction and the Kernel of Admissibility* manuscript.

## Trust and scope

- The repository is self-contained apart from the pinned mathlib dependency.
- The vendored 31-file AASC kernel source closure contains no project
  `axiom`, `opaque`, `unsafe`, `sorry`, or `admit` declaration.
- No legacy kernel repository, mixed AASC-Mathlib package, or conclusion-
  bearing project certificate is imported.
- Certificate-named structures are transparent witness packages with explicit
  fields.  They contain no hidden project axioms.
- Load-bearing `#print axioms` checks use only the approved Lean foundations:
  `propext`, `Classical.choice`, and `Quot.sound`.

## Verification

```text
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check-kernel-paper.ps1
```

The verification script performs the source scan, build, axiom audit, and
semantic audit.
