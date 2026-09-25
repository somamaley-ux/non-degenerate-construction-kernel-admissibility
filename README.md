# Non-Degenerate Construction and the Kernel of Admissibility

The **v0.3.2 Lean companion** to the **v51.2 reference manuscript** formalizes the mathematical necessity construction and its conservation, representation, and construction consequences.

The manuscript establishes Admissibility, Standing, Reference, and Irreversibility as necessary work of non-degenerate determinate objecthood, including unobserved physical incidences. The formal development starts from independently specified original subjects, complete uses, their possible witnesses, and an original incidence relation. It constructs qualification and assessment, proves identity and retention results, and characterizes exactly which representations can retain the original work. The regime's semantic correctness and the criterion for exact reading are proved through this chain, without a supplied four-role or arbitrary-reader correctness certificate.

To instantiate a kernel role is to perform its work in actual realization. Reference concerns the actual bearer and relata; Standing concerns their qualification for the specified relation or use; Irreversibility retains the original occurrence and conditions; Admissibility concerns those conditions obtaining jointly. A faithful use or description answers to that realization. The work belongs to the incidence, including when no observer, checker, or report exists. Answer accountability (A4) states what any claim about that incidence must preserve; it does not assert that someone makes a claim.

The manuscript separately defends why actual identity-bearing incidence incurs these commitments. The checked semantic construction and role reconstruction then derive their mathematical consequences from the independently interpreted original data. Reconstruction cannot establish its own conceptual premises merely by naming the resulting functions. Domain-specific identifications and laws retain their original grounds.

Functional minimality means that the required work cannot be omitted while the same complete construction is retained. The roles may overlap, share an implementation, or be expressed by one sufficiently rich condition. Their necessity does not require a unique partition or four independent axioms. Exact quotient uniqueness concerns representations of the same independently fixed observation content.

## Principal checked results

- **Necessity from original incidence.** An actual witness supplies positive qualification. Classical logic constructs the unique complete Boolean qualification assessment; this does not require a single-valued result relation. Original identity characterizes uniform transfer of arbitrary original predicates, and retention preserves original incidence and its assessment. The assembled theorem constructs the assessment regime, proves its original semantic meaning, and derives its represented kernel roles.
- **Exact realization and witnessed failure.** For every proposed encoding and independently fixed predicate family, an exact reader exists if and only if each encoding fibre preserves the original profile. The relational reader is constructed without choice. Exactness excludes both omitted true answers and unsupported extra answers. Identity probes yield unique original-object reconstruction on the realized code image; redundant presentations may share a code. A genuine loss under erasure has a specific original distinction as its witness.
- **Conservation for arbitrary dependent queries.** Equal independently identified bearer and complete query, a determinate original result relation, and each answer's own incidence warrant imply equal answers. The query family may be arbitrary and its result types dependent. Agreement is the conclusion.
- **Authorization at an original warrant.** A finite acyclic support graph with an authoritative endpoint has a globally minimal authoritative ancestor. The incidence bridge extracts an actual original witness at that cut and constructs its semantic standing and kernel realization. The cut's first authoritative use need not be the final node's identical query.
- **Canonical quotients and typed composition.** An independently fixed original observation profile determines its canonical quotient and uniquely commuting exact classifiers. For finite heterogeneous operations, original one-hole context tests derive tuple congruence. The tuple quotient is identified with the product of the sort quotients, and operations descend uniquely with exactly their original domain image. Classification uniqueness does not identify distinct occupants.
- **Equality-only finite interfaces.** Finite tuples over any carrier lie in the same permutation orbit exactly when their equality patterns agree. Invariant observers factor uniquely through those patterns. Checked consequences include partition realization, binary normal forms, and exclusion of a fully invariant strict total order or fixed selector on a nontrivial carrier. Full permutation symmetry is an explicit hypothesis of this interface.
- **Licensed construction and grounded support.** Fixed partial operation graphs determine licensed outputs. The generated region is the least closed extension of its seed and equals its finite stages, including nullary construction. Original local checks and every required predecessor generate support; sound local rules yield global standing, and complete retention preserves it.
- **Comparison and reindexing.** Equality of complete profiles forms a thin semantic comparison groupoid. A primitive comparison language presents all semantic classes exactly when it supplies the required finite zigzags. Reindexing that preserves original edges, eligibility, and compatibility derives preservation of complete evidence and support. Semantic comparison paths are distinct from directed execution paths.

The five `Extensions/` modules also check canonical status and consumer invariance, exact primitive descent, preservation for a specified typed finite language, and an independently defined proof checker's soundness, completeness, and determinacy.

## Start here

- [Reference paper (PDF)](papers/Non_Degenerate_Construction_Kernel_Admissibility_v51_2.pdf)
- [Exact theorem map and scope](KERNEL_PAPER_FORMALIZATION_STATUS.md)
- [Trust policy and verification](TRUST.md)
- [Release verification record](validation/RELEASE_VERIFICATION.md)
- [Manuscript identity and checksums](PAPER_REFERENCE.md)
- [Downstream API guide](COMPATIBILITY.md)
- [Release v0.3.2 and project archives](https://github.com/somamaley-ux/non-degenerate-construction-kernel-admissibility/releases/tag/v0.3.2)

## Verify

Install the Lean toolchain selected by `lean-toolchain` and PowerShell 7 (`pwsh`). From the project root:

```text
lake exe cache get
pwsh -NoProfile -File scripts/check-kernel-paper.ps1
```

`lake build` imports the original API, all five extensions, and the current `KernelReference` modules. The complete audit additionally checks source hygiene, semantic examples, exact named anchor reports, and the transitive axiom dependencies of the public theorem inventory extracted from the compiled project modules. Missing reports fail the check. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The machine-readable result is written to `validation/run/audit.json`.

The theorem map identifies the constructive results, the uses of classical logic, and the original-domain premises of each application. A complete qualification assessment is semantic; it does not supply an executable decision procedure or a unique physical outcome. The numerical metric specialization of the checked binary classification retains its short written proof.
