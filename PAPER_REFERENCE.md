# Exact manuscript reference

**Title:** Non-Degenerate Construction and the Kernel of Admissibility
**Author:** Amos Jay Maley
**Edition:** v50, 25 September 2026
**Extent:** 61 pages
**Lean companion release:** v0.2.0

| Artifact | SHA-256 |
|---|---|
| [`Non_Degenerate_Construction_Kernel_Admissibility_v50.pdf`](papers/Non_Degenerate_Construction_Kernel_Admissibility_v50.pdf) | `a81ab696cbdaadb06aa87895c730ca47032fec2190c8489cc047a95d42dec147` |
| `Non_Degenerate_Construction_Kernel_Admissibility_v50_Project.zip` | `91543500b6a77a5def81a25c73fdab54fe2cbdee230e1264e020839827345db0` |

The PDF is committed in `papers/`; the exact original project ZIP is a [release asset](https://github.com/somamaley-ux/non-degenerate-construction-kernel-admissibility/releases/tag/v0.2.0). It includes the manuscript LaTeX and the proof snapshot supplied with v50. Neither artifact has been silently rewritten to describe subsequent mechanization.

The original v50 archive and its Appendix C document the support bundled with that edition. **The current Lean companion extends that coverage.** In particular it adds the finite semantic authorization-cut proof, dependent-query conservation, general profile quotient results, finite-arity equality-pattern classification, typed generated closure and dependency-DAG support. The current theorem correspondence is [KERNEL_PAPER_FORMALIZATION_STATUS.md](KERNEL_PAPER_FORMALIZATION_STATUS.md); use it for this release, rather than reading the archive's historical proof inventory as the current repository status.

The existing source API is retained from repository revision `8e0516d71f15d4fb86a4ebbaf3adee7ca28e6a70`. The five `Extensions/` files originate in the v50 manuscript support bundle. `KernelReference/` supplies the additional mechanization. Origin is evidence of provenance, not evidence that every theorem in the manuscript has a corresponding Lean declaration.

The toolchain is Lean 4.28.0; mathlib is pinned at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The complete dependency manifest is versioned with the project.
