# v0.2.0 verification

The canonical verification script passed on the frozen release inputs on 25 September 2026.

- 49 project Lean source files scanned.
- All 46 project library modules imported and built.
- All 2,655 project constants inspected for forbidden declaration kinds, unsafe definitions and placeholders, including private helpers.
- 804 of 804 public project theorem declarations received exact transitive axiom reports.
- All 15 original named anchors reported exactly once.
- Only `propext`, `Classical.choice`, and `Quot.sound` occurred.
- All five original semantic examples compiled; new examples compile as part of the reference modules.
- Six audit-parser fixtures passed, including rejection of missing, duplicate, foreign and unapproved-axiom reports.
- The source file set and all 53 recorded source/configuration/script hashes remained fixed during verification.

The machine-readable [audit record](v0.2.0-audit.json) identifies every audited theorem and its defining module, axiom dependencies, toolchain and source hashes. Counts include compiler-generated public equation lemmas; they are not counts of independent manuscript results.

## Independent review

Separate agents reviewed the new proof modules and the public correspondence map. Review covered independently fixed occurrence identity, the finite globally minimal authorization ancestor, local-to-global support, complete predecessor retention, dependent result transport, observation-quotient uniqueness, original-context congruence, permutation extension, binary normal form, strict-order exclusion, partition realization, and finite-stage generated closure. No mathematical blocker remained after review.

The publication pass verified the v50 artifact identities and removed stale claims that the original represented API proves the whole current manuscript. Existing AASC mathematical source remains unchanged apart from comments and line-ending normalization; current results are additive. Every original AASC source file was compared with the preceding revision after removing comments and whitespace.

This record supports the stated formal results. The manuscript's constitutive objecthood argument and concrete domain identifications retain the scope described in the [proof map](../KERNEL_PAPER_FORMALIZATION_STATUS.md).
