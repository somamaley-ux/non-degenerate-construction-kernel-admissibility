# Trust and verification

This policy applies to the v0.3.2 Lean companion and the v51.2 reference manuscript.

## Proof policy

All published project proofs are Lean declarations with explicit hypotheses. The accepted foundational axiom names are `propext`, `Classical.choice`, and `Quot.sound`. They support extensionality, classical choice, and quotients; they supply no physical or domain-specific premise.

The complete audit rejects project axioms, placeholders, unsafe declarations, and unexamined opaque declarations. It combines source inspection, compilation, semantic examples, fixed-anchor checks, and transitive `#print axioms` reports for the public theorem inventory extracted from compiled project modules. Report identity and completeness are checked. An empty or truncated report cannot pass merely because it contains no disallowed axiom.

A structure's proof fields remain hypotheses of theorems using it. In particular, the retained redescription structures explicitly supply preservation equations. Their projection lemmas do not independently derive those equations.

## What the necessity proofs establish

The necessity interface takes original semantic subjects, complete uses, dependent witness types, an independently specified incidence relation, and an actual witness for positive nonvacuity. From those data it constructs qualification, its semantic assessment, the assessment regime, and the regime's proved relation to original qualification. The full correspondence to A1–A4 also uses the identity, original-retention, exact-realization, and defect theorems. A represented `DerivedKernelRoles` record alone is insufficient for that correspondence.

The exact-realization theorem constructs a relational reader and proves its existence equivalent to the original-profile fibre criterion. Exactness is tested, not supplied as an objecthood assumption. The finite authorization bridge interprets warrant through the original incidence relation and extracts an actual witness at the selected cut; it does not assume a kernel conclusion in an authority label. Semantic conservation takes the separate original answer warrants and proves agreement.

The manuscript separately defends the constitutive passage from actual determinate incidence to the target commitments. Lean checks the semantic constructions and implications from the independently interpreted original data. The role reconstruction cannot establish its own conceptual premises, and a checked exact-realization theorem does not by itself supply the original interpretation of a physical or mathematical domain.

Instantiation means that the actual realization performs the required work. Admissibility concerns its original conditions obtaining jointly; any faithful use must answer to them. A4 expresses the accountability of any claim offered about that incidence, not the existence of a claimant. No observer, checker, assessment convention, or optional governance flag is needed to activate the kernel.

Functional non-omissibility concerns preservation of the same complete original work. The roles may overlap or share a compressed implementation; four independent axioms or a unique partition of that work are not asserted. Exact readers and quotient classifications have their stated uniqueness for fixed original content. The observation family's completeness and any concrete interpretation remain explicit application obligations.

## Constructive and classical results

Positive qualification from a witness, exclusion of a contrary settled refusal, original-incidence retention, identity separation, and the relational exact-reader existence criterion have constructive proofs. In particular, the relational reader uses an existential statement over original presentations and requires no selected representative.

Classical logic supplies a complete Boolean qualification assessment and extracts witnesses from negated universal exactness claims. Reconstructing an original object as a function on the realized code image uses classical choice; so does the arbitrary-index product-quotient construction. These are semantic existence and classification results, not assertions of executable decision procedures. Unique qualification does not imply a single physical outcome.

## Reproduce

```text
lake exe cache get
pwsh -NoProfile -File scripts/check-kernel-paper.ps1
```

The versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Default builds include the original `AASC` umbrella and the complete paper umbrella. The supported script emits a machine-readable record under the ignored `validation/run/` directory. The release verification record identifies the checked source and manuscript artifacts.

Audit counts refer to public project theorem declarations, including compiler-generated equation lemmas. They are not counts of independent manuscript results. The complete inventory and dependency reports, rather than a hard-coded count in this document, identify the checked surface.

The audit concerns project theorem provenance, not independence of the mathematical foundation. Ordinary Lean equality, inductive types, and the accepted axioms remain part of the trust base. An empty axiom report still leaves the theorem's explicitly quantified hypotheses in force.

## Semantic checks

The semantic examples distinguish:

- positive actual incidence from existence of a failed locus;
- standing of a failed trial from success at its attempted use;
- a changed or assisted trial from the original unsupported trial;
- an actual object from the truth of a report about it;
- several incident results from one Boolean qualification answer;
- preservation of required answers from exactness that also excludes surplus;
- redundant presentations from distinct original semantic identities;
- deletion of constant storage from destruction of original work;
- first authority on a path from a globally minimal authoritative ancestor;
- semantic comparison from completeness of a chosen primitive generator;
- undirected comparison paths from directed execution;
- local role-data preservation from derived preservation of complete support.

The independently defined proof checker proves soundness and completeness from its own inference rules. Typed composition derives congruence from the original one-hole tests. Grounded support derives global standing from the local rules and complete dependencies. Each application must establish its stated original-domain premises.
