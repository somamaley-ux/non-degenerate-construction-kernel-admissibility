import AASC.Instances.KernelPaper.Closure
import Extensions
import KernelReference

/-!
# Clean formalization of Non-Degenerate Construction and the Kernel of
# Admissibility

This is the supported reference-paper target. It imports the existing AASC
API, the five semantic/interface extensions, and the v50 KernelReference
mathematics. The example below is the original represented-role assembly;
it is not a declaration of the whole constitutive manuscript theorem.
See KERNEL_PAPER_FORMALIZATION_STATUS.md for exact proof correspondence.
-/

open AASC
open AASC.Instances.KernelPaper
open AASC.Instances.KernelPaper.Manuscript
open AASC.Instances.KernelPaper.ManuscriptClosure

example
    {Act Target Step : Type}
    (R : TargetAdequacy.Regime Act Target Step)
    (nondegenerate : R.Nondegenerate)
    (licensed : Step -> Step -> Prop)
    (preserves_standing : forall source destination,
      R.Standing source -> licensed source destination ->
        R.Standing destination) :
    TargetAdequacyProfile R /\
      DerivedKernelRoles R /\
      MutualKernelClosure R := by
  have main := main_fixed_domain_exhaustion
    R nondegenerate licensed preserves_standing
  exact ⟨main.1, main.2.1, mutual_kernel_closure R⟩

example :
    TargetAdequacyProfile ConcreteWitness.adequacyRegime :=
  ConcreteWitness.adequacyRegime_targetAdequate

example :
    DerivedKernelRoles ConcreteWitness.adequacyRegime :=
  ConcreteWitness.adequacyRegime_kernel_roles

example :
    Not (Nonempty (LowerGovernanceGenerator
      ConcreteWitness.adequacyRegime
      (fun _ => True))) := by
  intro generator
  exact no_faithful_lower_generator generator.some
