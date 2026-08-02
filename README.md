# AASC — Non-Degenerate Construction and the Kernel of Admissibility

This is the dedicated clean Lean project for the latest kernel manuscript.
It is separate from the mixed AASC full-stack project and from the historical
standalone kernel package.

The default target contains the clean AASC kernel source closure needed by the
paper and depends directly on pinned mathlib.  No AASC-Mathlib package, legacy
`MaleyLean` paper statement, sunflower translation, or conclusion-bearing
project certificate is part of this target.

## Certificate policy

There are no hidden project axioms inside certificates.  Certificate-named
structures in the source are transparent witness packages: every datum and
proof field is explicit, and their consequences are derived by ordinary Lean
theorems.  The trust script rejects `axiom`, `opaque`, `unsafe`, `sorry`, and
`admit` declarations and checks the load-bearing theorem axioms directly.

## Verification

From this directory:

```text
lake build AASCKernelPaperClean
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check-kernel-paper.ps1
```

The script checks every vendored source declaration, the focused Lean build,
the axiom reports, the semantic checks, and the absence of legacy imports in
this standalone source tree.

The formalization begins at the manuscript's own target class: fixed-domain,
determinate, target-adequate, identity-preserving, act-time-final
construction.  The regime data and any continuation, report, or cross-domain
preservation laws needed by a downstream application are explicit inputs.
They are not hidden inside the kernel result.

See `KERNEL_PAPER_FORMALIZATION_STATUS.md` and `PAPER_REFERENCE.md`.
