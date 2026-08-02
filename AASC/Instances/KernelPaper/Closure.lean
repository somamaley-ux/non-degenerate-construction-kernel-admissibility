import Mathlib.Logic.Equiv.Defs
import AASC.Instances.KernelPaper.Manuscript

/-!
# Explicit closure interfaces for the kernel manuscript

This file closes the remaining manuscript-definition gaps around derivation,
lower generation, status quotients, relabeling, continuation transport, and
the downstream fixed-domain interface.

Every non-structural premise is a visible field or theorem argument.  In
particular, a raw trace is not promoted to a governed construction, a
cross-domain map is not declared faithful without preservation equations, and
the reports/continuations used by downstream results are not hidden in a
kernel certificate.  Any certificate-named structure in the imported source
is transparent witness data with explicit fields, never a project axiom.
-/

namespace AASC
namespace Instances
namespace KernelPaper
namespace ManuscriptClosure

open AASC.TargetAdequacy
open Manuscript

universe u v w z u' v' w'

/-! ## Construction and derivation -/

/-- A governed construction carries its target and standing witnesses. -/
structure GovernedConstruction
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) where
  step : Step
  target : Target
  reference : R.ReferenceAt (R.source step) target
  standing : R.Standing step

/- A generic raw trace is governed only after an explicit construction witness
is provided for one of its steps. -/
structure RawTrace (Step : Type w) where
  trace : List Step

def RawTraceGovernanceClaim
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (trace : RawTrace Step) : Prop :=
  exists step, step ∈ trace.trace /\
    exists target, R.ReferenceAt (R.source step) target /\ R.Standing step

theorem raw_trace_governance_requires_explicit_witness
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (trace : RawTrace Step)
    (claim : RawTraceGovernanceClaim R trace) :
    exists step, step ∈ trace.trace /\
      R.ReferenceAt (R.source step) (R.targetOf (R.source step)) /\
      R.Standing step := by
  rcases claim with ⟨step, inTrace, target, reference, standing⟩
  exact ⟨step, inTrace, rfl, standing⟩

/-- A derivation is a governed construction whose fixed target is a
proposition-valued target supplied by the surrounding regime. -/
structure Derivation
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
  (R : Regime Act Target Step)
    (target : Target) where
  construction : GovernedConstruction R
  target_fixed : construction.target = target

theorem derivation_presupposes_standing
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {target : Target}
    (derivation : Derivation R target) :
    R.Standing derivation.construction.step :=
  derivation.construction.standing

theorem derivation_presupposes_admissibility
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {target : Target}
    (derivation : Derivation R target) :
    R.Admissible derivation.construction.step :=
  standing_requires_admissibility R derivation.construction.standing

theorem derivation_presupposes_reference
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {target : Target}
    (derivation : Derivation R target) :
    R.ReferenceAt
      (R.source derivation.construction.step)
      derivation.construction.target :=
  derivation.construction.reference

theorem derivation_presupposes_irreversibility
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    forall {original revised},
      Not (R.verdict original = R.verdict revised) ->
        Not (original = revised) :=
  irreversibility_necessity R

theorem derivation_presupposes_kernel
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {target : Target}
    (_derivation : Derivation R target) :
    DerivedKernelRoles R :=
  mechanization_boundary R

/-! ## Raw generation versus governance generation -/

/-- Raw generation is merely a map between data carriers. -/
structure RawGeneration (Input Output : Type z) where
  generate : Input -> Output

/-- A lower generator is required to start from an inhabited, non-standing
basis and to prove that its output is a faithful standing classifier. -/
structure LowerGovernanceGenerator
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (candidate : Step -> Prop) where
  basis : Step -> Prop
  basis_inhabited : exists step, basis step
  basis_governance_free : forall step, basis step -> Not (R.Standing step)
  generation : forall step, basis step -> candidate step
  faithful : DerivativeInvariant R candidate

theorem no_faithful_lower_generator
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {candidate : Step -> Prop}
    (generator : LowerGovernanceGenerator R candidate) :
    False := by
  rcases generator.basis_inhabited with ⟨step, basis⟩
  apply generator.basis_governance_free step basis
  exact (generator.faithful step).1 (generator.generation step basis)

theorem raw_generation_is_not_governance_generation
    {Input Output : Type z}
    (raw : RawGeneration Input Output) :
    exists generate : Input -> Output, generate = raw.generate :=
  ⟨raw.generate, rfl⟩

/-! ## Cross-domain transport -/

/-- Explicit maps and preservation equations for a transport from an external
regime into the fixed-domain regime. -/
structure CrossDomainTransport
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {Act' : Type u'}
    {Target' : Type v'}
    {Step' : Type w'}
    (R : Regime Act Target Step)
    (S : Regime Act' Target' Step') where
  actMap : Act' -> Act
  targetMap : Target' -> Target
  stepMap : Step' -> Step
  source_compat : forall step',
    actMap (S.source step') = R.source (stepMap step')
  destination_compat : forall step',
    actMap (S.destination step') = R.destination (stepMap step')
  target_compat : forall act',
    targetMap (S.targetOf act') = R.targetOf (actMap act')
  verdict_compat : forall step',
    R.verdict (stepMap step') = S.verdict step'

theorem cross_domain_transport_preserves_reference_and_standing
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {Act' : Type u'}
    {Target' : Type v'}
    {Step' : Type w'}
    {R : Regime Act Target Step}
    {S : Regime Act' Target' Step'}
    (transport : CrossDomainTransport R S)
    {act' : Act'}
    {step' : Step'}
    (_reference : S.ReferenceAt act' (S.targetOf act'))
    (standing : S.Standing step') :
    R.ReferenceAt
        (transport.actMap act')
        (transport.targetMap (S.targetOf act')) /\
      R.Standing (transport.stepMap step') := by
  constructor
  · change R.targetOf (transport.actMap act') =
      transport.targetMap (S.targetOf act')
    exact (transport.target_compat act').symm
  · change R.verdict (transport.stepMap step') = .advances
    exact (transport.verdict_compat step').trans standing

/-! ## Mutual closure and role-package minimality -/

def GovernedReference
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (step : Step)
    (target : Target) : Prop :=
  R.ReferenceAt (R.source step) target /\ R.Standing step

theorem standing_requires_reference
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    {step : Step}
    (_standing : R.Standing step) :
    exists target, R.ReferenceAt (R.source step) target := by
  rcases reference_necessity R (R.source step) with ⟨target, reference, _⟩
  exact ⟨target, reference⟩

theorem governed_reference_requires_irreversibility
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {step : Step}
    {target : Target}
    (_reference : GovernedReference R step target) :
    forall {original revised},
      Not (R.verdict original = R.verdict revised) ->
        Not (original = revised) :=
  irreversibility_necessity R

def GovernanceIrreversibility
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop :=
  forall {original revised},
    R.Failure original -> R.Admissible revised -> Not (original = revised)

theorem governance_irreversibility_is_admissibility_bounded
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    GovernanceIrreversibility R := by
  intro original revised _failure admissible same
  subst revised
  exact _failure (admissibility_requires_standing R admissible)

def MutualKernelClosure
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop :=
  (forall step, R.Admissible step -> R.Standing step) /\
    (forall step, R.Standing step ->
      exists target, R.ReferenceAt (R.source step) target) /\
    (forall {original revised},
      Not (R.verdict original = R.verdict revised) ->
        Not (original = revised)) /\
    (forall step, R.Standing step -> R.Admissible step)

theorem mutual_kernel_closure
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    MutualKernelClosure R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun step => admissibility_requires_standing R
  · exact fun step standing => standing_requires_reference R standing
  · exact irreversibility_necessity R
  · exact fun step => standing_requires_admissibility R

theorem kernel_role_package_is_minimal
    {small large : RolePackage}
    (small_complete : CompleteRolePackage small)
    (strict : StrictRoleSubpackage small large) :
    Not (CompleteRolePackage large) :=
  no_strict_complete_role_subpackage small_complete strict

/-! ## Status quotients and bivalence -/

structure StatusInterface (Step : Type u) (Status : Type v) where
  evaluated : Step -> Prop
  status : Step -> Status
  admittedStatus : Status
  rejectedStatus : Status
  licensed : Status -> Step -> Prop
  reportable : Status -> Prop
  reusable : Status -> Step -> Prop

def StatusEquivalent
    {Step : Type u}
    {Status : Type v}
    (I : StatusInterface Step Status)
    (left right : Status) : Prop :=
  (forall step, I.licensed left step <-> I.licensed right step) /\
    (I.reportable left <-> I.reportable right) /\
    (forall step, I.reusable left step <-> I.reusable right step)

def StatusGovernanceEffective
    {Step : Type u}
    {Status : Type v}
    (I : StatusInterface Step Status)
    (status : Status) : Prop :=
  Not (StatusEquivalent I status I.admittedStatus)

def StatusInert
    {Step : Type u}
    {Status : Type v}
    (I : StatusInterface Step Status)
    (status : Status) : Prop :=
  StatusEquivalent I status I.admittedStatus

theorem no_intermediate_status
    {Step : Type u}
    {Status : Type v}
    (I : StatusInterface Step Status)
    (status : Status) :
    StatusGovernanceEffective I status \/ StatusInert I status := by
  classical
  by_cases h : StatusGovernanceEffective I status
  · exact Or.inl h
  · exact Or.inr (Classical.byContradiction (fun notEquivalent => h notEquivalent))

theorem status_effective_and_inert_disjoint
    {Step : Type u}
    {Status : Type v}
    (I : StatusInterface Step Status)
    (status : Status) :
    Not (StatusGovernanceEffective I status /\ StatusInert I status) := by
  intro both
  exact both.1 both.2

/-! ## AMetric relabeling and boundary authority -/

/-- Transitivity of the relabeling action is kept explicit. -/
structure RelabelingSymmetry (Carrier : Type u) where
  transport : forall left right : Carrier, exists e : Equiv Carrier Carrier,
    e left = right

def RelabelingInvariant
    {Carrier : Type u}
    (predicate : Carrier -> Prop) : Prop :=
  forall e : Equiv Carrier Carrier, forall point,
    predicate (e point) <-> predicate point

theorem relabeling_invariant_is_constant
    {Carrier : Type u}
    (symmetry : RelabelingSymmetry Carrier)
    (predicate : Carrier -> Prop)
    (invariant : RelabelingInvariant predicate) :
    forall left right, predicate left <-> predicate right := by
  intro left right
  rcases symmetry.transport left right with ⟨e, h⟩
  simpa [h] using (invariant e left).symm

theorem relabeling_invariant_parameter_is_constant
    {Carrier : Type u}
    {Parameter : Type v}
    (symmetry : RelabelingSymmetry Carrier)
    (parameter : Carrier -> Parameter)
    (invariant : forall e : Equiv Carrier Carrier, forall point,
      parameter (e point) = parameter point) :
    forall left right, parameter left = parameter right := by
  intro left right
  rcases symmetry.transport left right with ⟨e, h⟩
  simpa [h] using (invariant e left).symm

structure AMetricBoundaryInterface (Carrier : Type u) where
  eligible : Carrier -> Prop
  relabeling : RelabelingSymmetry Carrier
  eligible_invariant : RelabelingInvariant eligible

theorem ametric_interface_forbids_nonconstant_parameter
    {Carrier : Type u}
    {Parameter : Type v}
    (boundary : AMetricBoundaryInterface Carrier)
    (parameter : Carrier -> Parameter)
    (parameter_invariant : forall e : Equiv Carrier Carrier, forall point,
      parameter (e point) = parameter point) :
    forall left right, parameter left = parameter right :=
  relabeling_invariant_parameter_is_constant
    boundary.relabeling parameter parameter_invariant

def BoundaryAction
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (action : Step -> Step) : Prop :=
  exists step, R.Failure step /\ R.Standing (action step)

def BoundaryActionFresh
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (action : Step -> Step) : Prop :=
  forall step, R.Failure step -> Not (action step = step)

theorem boundary_action_requires_fresh_evaluation
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (action : Step -> Step)
    (fresh : BoundaryActionFresh R action) :
    BoundaryAction R action ->
      exists step, R.Failure step /\ Not (action step = step) := by
  rintro ⟨step, failure, standing⟩
  exact ⟨step, failure, fresh step failure⟩

/-! ## Scope-preserving continuation and operators -/

structure ScopePreservingContinuation
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) where
  map : Step -> Step
  preserves_invariant : forall step, ActIdentity R step (map step)

theorem scope_preserving_invariance
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    (continuation : ScopePreservingContinuation R) :
    forall step, ActIdentity R step (continuation.map step) :=
  continuation.preserves_invariant

theorem scope_preserving_preserves_standing
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    (continuation : ScopePreservingContinuation R) :
    forall step,
      R.Standing step <-> R.Standing (continuation.map step) := by
  intro step
  have verdict := (continuation.preserves_invariant step).2.2.2.2
  change R.verdict step = .advances <->
    R.verdict (continuation.map step) = .advances
  rw [verdict]

def SameActInvariantRelation
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (relation : Step -> Step -> Prop) : Prop :=
  forall left right left' right',
    ActIdentity R left left' -> ActIdentity R right right' ->
      (relation left right <-> relation left' right')

theorem same_act_transport_closure
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    (relation : Step -> Step -> Prop)
    (invariant : SameActInvariantRelation R relation) :
    forall left right left' right',
      ActIdentity R left left' -> ActIdentity R right right' ->
        (relation left right <-> relation left' right') :=
  invariant

structure AdmissibleOperator
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) where
  domain : Step -> Prop
  domain_iff_admissible : forall step, domain step <-> R.Admissible step
  application : Step -> Step -> Prop

theorem admissible_operator_defined_on_standing
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    (operator : AdmissibleOperator R) :
    forall step, R.Standing step -> operator.domain step := by
  intro step standing
  exact (operator.domain_iff_admissible step).2
    (standing_requires_admissibility R standing)

/-! ## Reports and the main fixed-domain closure theorem -/

structure ConstructionalReport
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) where
  report : Step -> Prop
  support : Step -> Prop
  admissibility_relevant : Prop
  report_supported : forall step, report step -> support step

theorem constructional_report_preservation
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    (report : ConstructionalReport R) :
    forall step, report.report step -> report.support step :=
  report.report_supported

theorem report_support_exhaustion
    {Step : Type w}
    (report support : Step -> Prop) :
    (forall step, report step -> support step) \/
      exists step, report step /\ Not (support step) := by
  classical
  by_cases h : forall step, report step -> support step
  · exact Or.inl h
  · right
    exact Classical.byContradiction (fun noCounterexample =>
      h (fun step reported =>
        Classical.byContradiction (fun notSupported =>
          noCounterexample ⟨step, reported, notSupported⟩)))

theorem main_fixed_domain_exhaustion
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (nondegenerate : R.Nondegenerate)
    (licensed : Step -> Step -> Prop)
    (preserves_standing : forall source destination,
      R.Standing source -> licensed source destination ->
        R.Standing destination) :
    TargetAdequacyProfile R /\
      DerivedKernelRoles R /\
      AMetricBoundary R /\
      (forall step, R.Standing step <-> ReuseStable R licensed step) /\
      AdmissibleInterior R (fun step => R.Standing step) /\
      (forall source destination,
        R.Standing source -> licensed source destination ->
          R.Admissible destination) := by
  refine ⟨targetAdequacy R, targetAdequacy_forces_kernel_roles R, ?_, ?_, ?_, ?_⟩
  · exact ametricBoundary_of_nondegenerate R nondegenerate
  · exact standing_iff_reuseStable R licensed preserves_standing
  · intro step
    rfl
  · exact conservation_of_standing_preservation R licensed preserves_standing

theorem internal_mechanization_boundary
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (target : Target)
    (_derivation : Derivation R target) :
    DerivedKernelRoles R :=
  mechanization_boundary R

end ManuscriptClosure
end KernelPaper
end Instances
end AASC
