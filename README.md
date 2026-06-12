# Non-Degenerate Construction and the Kernel of Admissibility

Standalone Lean 4 formalization and A+ audit surface for:

`Non-Degenerate Construction and the Kernel of Admissibility`

The formalization treats the admissibility kernel as a formal mathematical
object: a fixed-domain closure structure whose consequence interface is checked
inside Lean 4. It records the strength of the paper result:

- formal kernel objecthood for admissibility, standing, reference, and
  irreversibility on a fixed constructional domain;
- fixed-domain uniqueness of the admissibility kernel;
- non-derivability from below, with no governance-free, same-domain construction
  beneath the kernel;
- no faithful lower generator and no deeper same-domain invariant;
- final A+ audit closure.

The Lean layer verifies the kernel structure and downstream consequence
interface. It does not supply a lower derivation of the kernel, because the
fixed-domain results rule out such a derivation.

Current A+ posture:

```text
("Final A+ closure", 31, 31, 0, 7, 14, 10, 0, 0)
```

That is: `31` theorem-spine rows tracked, `31` closed or audited, `0` residual gates, and `0` hypothesis gates.

## Canonical Module

```lean
MaleyLean.Papers.NonDegenerateConstructionAndKernelOfAdmissibility
```

The old `MinimalConditionsForAdmissibleConstruction` module name remains only as an internal compatibility namespace/path for theorem continuity.

## Audit

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-minimal-conditions-a-plus-audit.ps1
```

The audit script builds the canonical module, runs the focused A+ audit files, and checks that no live `axiom`, `sorry`, `admit`, or `unsafe` declarations appear in the kernel-paper audit surface.

## Key Theorem Anchors

- `KernelUniqueOnFixedDomain`
- `PaperKernelUniquenessOnFixedDomainStatement`
- `NoDerivationBelowKernel`
- `PaperNothingDerivableBelowKernelStatement`
- `PaperKernelNonDerivabilityStatement`
- `PaperNoFaithfulLowerGeneratorStatement`
- `PaperNoDeeperInvariantClosedStatement`
- `PaperGlobalSynthesisUnderCorpusClosuresClosedStatement`
- `Surface.APlusStrengthSummaryStatement`
