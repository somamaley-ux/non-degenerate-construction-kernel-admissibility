import AASC.Instances.KernelPaper.Closure

open AASC
open AASC.Instances.KernelPaper
open AASC.Instances.KernelPaper.Manuscript
open AASC.Instances.KernelPaper.ManuscriptClosure

example
    {Act Target Step : Type}
    (R : TargetAdequacy.Regime Act Target Step) :
    MutualKernelClosure R :=
  mutual_kernel_closure R

example
    {Carrier : Type}
    (symmetry : RelabelingSymmetry Carrier)
    (predicate : Carrier -> Prop)
    (invariant : RelabelingInvariant predicate) :
    forall left right, predicate left <-> predicate right :=
  relabeling_invariant_is_constant symmetry predicate invariant

example
    {Step : Type}
    (report support : Step -> Prop) :
    (forall step, report step -> support step) \/
      exists step, report step /\ Not (support step) :=
  report_support_exhaustion report support

example :
    ConcreteWitness.adequacyRegime.Nondegenerate :=
  ConcreteWitness.adequacyRegime_nondegenerate

example :
    Witness.references.kernel.ReferenceUnique /\
      Witness.references.kernel.Nontrivial /\
      Not (Nonempty (Witness.model.Path .initial .failed)) /\
      FixedRoleClosure.problem.OneAssignmentOrbit :=
  ConcreteWitness.endpoint_and_role_occupancy_closure
