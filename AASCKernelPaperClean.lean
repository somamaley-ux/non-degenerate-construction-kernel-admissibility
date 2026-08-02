import AASC.Instances.KernelPaper.Closure

/-!
# Clean formalization of Non-Degenerate Construction and the Kernel of
# Admissibility

This is the standalone paper target.  It imports only the clean reusable
AASC kernel modules.  The legacy sunflower translation and the pinned
standalone kernel package are not imported here.
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
