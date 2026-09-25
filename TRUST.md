# Trust and verification

## Proof policy

All published project proofs are Lean declarations with explicit hypotheses. The accepted foundational axiom names are `propext`, `Classical.choice`, and `Quot.sound`. These support extensionality, classical choice, and quotients; they supply no physical or domain-specific premise.

The audit rejects project axioms, placeholders, unsafe declarations, and unexamined opaque declarations. It combines source inspection, compilation, semantic examples, fixed-anchor checks, and transitive `#print axioms` reports for every enumerated public project theorem. Report identity and completeness are checked; an empty or truncated audit cannot pass merely because it prints no disallowed axiom.

A structure's proof fields are hypotheses of the theorems using that structure. A transparent field is not a proof that its proposition holds in a proposed application. In particular, the original redescription structure supplies preservation equations; its projection lemmas do not independently derive them. Current semantic conservation instead takes the two original incidence warrants separately and proves agreement. Authorization derives a finite cut; grounded support derives global soundness from local rules.

## Reproduce

```text
lake exe cache get
pwsh -NoProfile -File scripts/check-kernel-paper.ps1
```

The versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Default builds include the original `AASC` umbrella and the paper umbrella. The canonical script emits a machine-readable record under the ignored `validation/run/` directory. The release includes a checked snapshot of that record.

The audit concerns project theorem provenance, not independence of the entire mathematical foundation. Ordinary Lean equality, inductive types, and the named accepted axioms remain part of the trust base. An empty axiom report still leaves the theorem's explicitly quantified hypotheses in force.

## Semantic checks

The original semantic examples remain supported. New examples distinguish:

- actual positive incidence from a separate failure boundary;
- standing of a determinate failed trial from success at its attempted use;
- a changed or finger-supported trial from the original unsupported trial;
- loss of report warrant from alteration of the reported object;
- first authority on one path from a globally minimal authoritative ancestor;
- an empty seed with a licensed nullary construction from the entire standing carrier.

The independently defined proof checker proves soundness and completeness from its own inference rules. This is a concrete realization of the warrant premise; it does not license arbitrary external parsers or physical interpretations.

Audit counts refer to public project theorem declarations, including compiler-generated equation lemmas. They are not counts of independent manuscript results.
