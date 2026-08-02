# Kernel-paper formalization status

## Clean standalone target

The standalone entry point is `AASCKernelPaperClean.lean`.  The reusable
mathematics is carried in the vendored clean source closure:

- `AASC/Instances/KernelPaper/Manuscript.lean`
- `AASC/Instances/KernelPaper/Closure.lean`
- the 29 clean AASC core and kernel-witness dependencies imported by them

The vendored source contains no project `axiom`, `opaque`, `unsafe`, `sorry`,
or `admit` declaration.  It has no dependency on the legacy kernel
repository, AASC-Mathlib, or a conclusion-bearing certificate.

Certificate policy: certificate-named declarations are transparent structures
with explicit data and proof fields.  They do not contain hidden project
axioms or pre-proved project conclusions.

## Formalized load-bearing spine

- target adequacy and the four derived kernel roles;
- failure-mode and route-coordinate exhaustion;
- act identity, governance equivalence, and faithful redescription;
- same-act repair exclusion and explicit role-necessity lemmas;
- bivalent admissibility status and the AMetric boundary;
- unique admissible interior and standing/reuse conservation interface;
- derivation presupposition and raw-generation/governance-generation
  separation;
- lower-generator exclusion and cross-domain preservation equations;
- mutual kernel closure and role-package minimality;
- status-effect quotient case split and relabeling-invariant parameter collapse;
- scope-preserving continuation, transport closure, admissible operator
  domains, and constructional report support;
- an assembled fixed-domain theorem with every continuation law explicit;
- an inhabited concrete endpoint/role-occupancy witness.

The exact declaration map is maintained in the canonical AASC-Mathlib ledger
`KERNEL_PAPER_FORMALIZATION_STATUS.md`.

## Trust boundary

`Checks/KernelPaperTrust.lean` audits the load-bearing declarations with
Lean's `#print axioms`.  Only the approved Lean foundations
`propext`, `Classical.choice`, and `Quot.sound` occur, and only the
classical status/case-split results use them.  `Checks/KernelPaperSemantic.lean`
provides independent type-level and witness-level checks.

The focused script passes.  The repository is ready for its first reviewed
commit and GitHub release; no manuscript edit is included in this repository.
