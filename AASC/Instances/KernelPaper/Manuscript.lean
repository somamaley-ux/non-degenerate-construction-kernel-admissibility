import AASC.Core.TargetAdequacy
import AASC.Core.BoundaryClosure
import AASC.Core.SameDomainRoutes
import AASC.Core.ExhaustionStrength
import AASC.Core.AmetricIdentityBoundary
import AASC.Instances.KernelPaper.Witness
import AASC.Instances.KernelPaper.RoleOccupancyClosure

/-!
# The complete kernel-paper spine

This file is the clean manuscript-facing layer for the latest kernel paper.

The important separation is deliberate:

* `RawStepSequence` contains only a trace;
* `TargetAdequacy.Regime` contains explicit target, endpoint, and verdict
  functions;
* kernel roles are constructed from those functions;
* continuation, route coverage, report deployment, and role occupancy are
  never smuggled into a certificate.  Certificate-named structures in the
  dependency closure are transparent witness packages: their data and proof
  fields are visible, and their consequences are proved by theorems.  When
  one of those structures is used, its maps and laws occur as visible theorem
  arguments or as fields of the corresponding data-bearing mathematical
  object.

Thus this file formalizes the manuscript's theorem spine without declaring an
axiom, opaque theorem, `sorry`, or conclusion-bearing project certificate.
Theorems about generic continuation and additional foundational conditions are
stated with their actual preservation hypotheses; they are not advertised as
consequences of objecthood alone.
-/

namespace AASC
namespace Instances
namespace KernelPaper
namespace Manuscript

open AASC.TargetAdequacy

universe u v w

/-! ## Fixed-domain raw data and neutral adequacy -/

/-- An ordered trace before any constructional interpretation is attached. -/
structure RawStepSequence (Act Step : Type u) where
  trace : List Step

/-- The four neutral adequacy clauses used by the manuscript. -/
structure TargetAdequacyProfile
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop where
  targetDeterminacy : forall act, exists target,
    R.ReferenceAt act target /\
      forall other, R.ReferenceAt act other -> other = target
  stepEvaluability : forall step, exists verdict,
    R.VerdictAt step verdict /\
      forall other, R.VerdictAt step other -> other = verdict
  actTimeFinality : forall step, Not (R.ActTimeFinalityFailure step)
  sameRegimeFidelity : forall step, Not (R.RedescriptionFidelityFailure step)

/-- Target adequacy is constructed from the raw functions of a regime. -/
theorem targetAdequacy
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    TargetAdequacyProfile R := by
  refine
    { targetDeterminacy := R.reference_exists_unique
      stepEvaluability := R.verdict_exists_unique
      actTimeFinality := fun step => R.not_actTimeFinalityFailure step
      sameRegimeFidelity := fun step => R.not_redescriptionFidelityFailure step }

/-- The result of the target-adequacy construction, with no stored kernel data. -/
structure DerivedKernelRoles
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop where
  referenceExistsUnique : forall act, exists target,
    R.ReferenceAt act target /\
      forall other, R.ReferenceAt act other -> other = target
  verdictExistsUnique : forall step, exists verdict,
    R.VerdictAt step verdict /\
      forall other, R.VerdictAt step other -> other = verdict
  admissibleIffStanding : forall step, R.Admissible step <-> R.Standing step
  standingFailureDisjoint : forall step, Not (R.Standing step /\ R.Failure step)
  actTimeIrreversible : forall {original revised},
    Not (R.verdict original = R.verdict revised) -> Not (original = revised)

/-- Target adequacy forces the four kernel roles at the representation level. -/
theorem targetAdequacy_forces_kernel_roles
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    DerivedKernelRoles R := by
  refine
    { referenceExistsUnique := R.reference_exists_unique
      verdictExistsUnique := R.verdict_exists_unique
      admissibleIffStanding := fun step => R.admissible_iff_standing step
      standingFailureDisjoint := fun step => R.standing_failure_disjoint step
      actTimeIrreversible := R.verdict_change_forces_distinct_step }

/-- The manuscript's non-degenerate target class is an actual witness pair. -/
abbrev NondegenerateConstruction
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop :=
  R.Nondegenerate

/-- The full constitutive theorem for the neutral target-adequate regime. -/
theorem construction_forces_kernel
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (nondegenerate : NondegenerateConstruction R) :
    TargetAdequacyProfile R /\
      DerivedKernelRoles R /\
      exists standing boundary,
        R.Standing standing /\ R.Failure boundary := by
  exact
    ⟨targetAdequacy R, targetAdequacy_forces_kernel_roles R,
      nondegenerate⟩

/-! ## The finite route map in Section 2 -/

/-- The five standard manuscript failure modes. -/
inductive StandardFailureMode where
  | targetLoss
  | stepStatusLoss
  | repairCollapse
  | illicitImport
  | governanceEquivalentCollapse
deriving DecidableEq, Repr

theorem standardFailureMode_exhaustion :
    forall mode : StandardFailureMode,
      mode = .targetLoss \/
      mode = .stepStatusLoss \/
      mode = .repairCollapse \/
      mode = .illicitImport \/
      mode = .governanceEquivalentCollapse := by
  intro mode
  cases mode with
  | targetLoss => exact Or.inl rfl
  | stepStatusLoss => exact Or.inr (Or.inl rfl)
  | repairCollapse => exact Or.inr (Or.inr (Or.inl rfl))
  | illicitImport => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | governanceEquivalentCollapse =>
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The manuscript's three neutral route coordinates. -/
inductive RouteCoordinate where
  | target
  | eligibility
  | actTime
deriving DecidableEq, Repr

theorem routeCoordinate_exhaustion :
    forall coordinate : RouteCoordinate,
      coordinate = .target \/ coordinate = .eligibility \/
        coordinate = .actTime := by
  intro coordinate
  cases coordinate with
  | target => exact Or.inl rfl
  | eligibility => exact Or.inr (Or.inl rfl)
  | actTime => exact Or.inr (Or.inr rfl)

/-! ## Act identity and governance equivalence -/

/-- The manuscript's admissibility-relevant equality of two concrete steps. -/
def ActIdentity
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (left right : Step) : Prop :=
  R.source left = R.source right /\
    R.destination left = R.destination right /\
    R.targetOf (R.source left) = R.targetOf (R.source right) /\
    R.targetOf (R.destination left) = R.targetOf (R.destination right) /\
    R.verdict left = R.verdict right

theorem actIdentity_refl
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (step : Step) :
    ActIdentity R step step := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Extensional fixed-domain governance equivalence. -/
def GovernanceEquivalent
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R S : Regime Act Target Step) : Prop :=
  (forall act, R.targetOf act = S.targetOf act) /\
  (forall step, R.source step = S.source step) /\
  (forall step, R.destination step = S.destination step) /\
  (forall step, R.verdict step = S.verdict step)

theorem governanceEquivalent_refl
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    GovernanceEquivalent R R := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem governanceEquivalent_symm
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R S : Regime Act Target Step}
    (equivalent : GovernanceEquivalent R S) :
    GovernanceEquivalent S R := by
  exact ⟨fun act => (equivalent.1 act).symm,
    fun step => (equivalent.2.1 step).symm,
    fun step => (equivalent.2.2.1 step).symm,
    fun step => (equivalent.2.2.2 step).symm⟩

theorem governanceEquivalent_trans
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R S T : Regime Act Target Step}
    (RS : GovernanceEquivalent R S)
    (ST : GovernanceEquivalent S T) :
    GovernanceEquivalent R T := by
  exact ⟨fun act => (RS.1 act).trans (ST.1 act),
    fun step => (RS.2.1 step).trans (ST.2.1 step),
    fun step => (RS.2.2.1 step).trans (ST.2.2.1 step),
    fun step => (RS.2.2.2 step).trans (ST.2.2.2 step)⟩

/-- A same-domain extension is strict only when a governed datum changes. -/
def StrictSameDomainExtension
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R S : Regime Act Target Step) : Prop :=
  TargetAdequacyProfile S /\
    ((exists act, Not (R.targetOf act = S.targetOf act)) \/
      (exists step, Not (R.source step = S.source step)) \/
      (exists step, Not (R.destination step = S.destination step)) \/
      (exists step, Not (R.verdict step = S.verdict step)))

theorem no_faithful_sameDomain_extension
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R S : Regime Act Target Step}
    (equivalent : GovernanceEquivalent R S) :
    Not (StrictSameDomainExtension R S) := by
  intro extension
  rcases extension with ⟨_, targetChange | sourceChange | destinationChange | verdictChange⟩
  · rcases targetChange with ⟨act, h⟩
    exact h (equivalent.1 act)
  · rcases sourceChange with ⟨step, h⟩
    exact h (equivalent.2.1 step)
  · rcases destinationChange with ⟨step, h⟩
    exact h (equivalent.2.2.1 step)
  · rcases verdictChange with ⟨step, h⟩
    exact h (equivalent.2.2.2 step)

theorem governanceEquivalent_replacement_has_kernel
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R S : Regime Act Target Step}
    (_equivalent : GovernanceEquivalent R S) :
    DerivedKernelRoles S :=
  targetAdequacy_forces_kernel_roles S

/-! ## Bivalence, AMetric boundary, and unique interior -/

inductive AdmissibilityStatus where
  | admissible
  | failure
deriving DecidableEq, Repr

noncomputable def statusOf
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (step : Step) : AdmissibilityStatus := by
  classical
  exact if R.Admissible step then .admissible else .failure

theorem statusOf_admissible_iff
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (step : Step) :
    statusOf R step = .admissible <-> R.Admissible step := by
  classical
  simp [statusOf]

theorem statusOf_failure_iff
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (step : Step) :
    statusOf R step = .failure <-> R.Failure step := by
  classical
  change statusOf R step = .failure <-> Not (R.Standing step)
  rw [← R.admissible_iff_standing step]
  simp [statusOf]

theorem admissibility_bivalent
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (step : Step) :
    statusOf R step = .admissible \/ statusOf R step = .failure := by
  cases statusOf R step <;> simp

/-- The AMetric boundary is the actual standing/failure split, not a metric. -/
def AMetricBoundary
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop :=
  exists standing boundary,
    R.Standing standing /\ R.Failure boundary

theorem ametricBoundary_of_nondegenerate
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (nondegenerate : R.Nondegenerate) :
    AMetricBoundary R :=
  nondegenerate

/-- An admissible interior is extensional standing, so two such interiors coincide. -/
def AdmissibleInterior
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (interior : Step -> Prop) : Prop :=
  forall step, interior step <-> R.Standing step

theorem unique_admissible_interior
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {left right : Step -> Prop}
    (leftInterior : AdmissibleInterior R left)
    (rightInterior : AdmissibleInterior R right) :
    forall step, left step <-> right step := by
  intro step
  exact (leftInterior step).trans (rightInterior step).symm

theorem no_distinct_faithful_interior
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {left right : Step -> Prop}
    (leftInterior : AdmissibleInterior R left)
    (rightInterior : AdmissibleInterior R right)
    (different : exists step, Not (left step <-> right step)) : False := by
  rcases different with ⟨step, h⟩
  exact h (unique_admissible_interior leftInterior rightInterior step)

/-! ## Continuation, reuse, and conservation

The manuscript's reuse and transport claims need a continuation relation.  The
relation is explicit here, and the preservation law is an explicit argument;
neither is placed inside a purported kernel certificate.
-/

def ReuseStable
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (licensed : Step -> Step -> Prop)
    (step : Step) : Prop :=
  R.Standing step /\
    forall later, licensed step later -> R.Admissible later

theorem standing_iff_reuseStable
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (licensed : Step -> Step -> Prop)
    (preservesStanding : forall source destination,
      R.Standing source -> licensed source destination ->
        R.Standing destination) :
    forall step, R.Standing step <-> ReuseStable R licensed step := by
  intro step
  constructor
  · intro standing
    refine ⟨standing, ?_⟩
    intro later continuation
    exact (R.admissible_iff_standing later).2
      (preservesStanding step later standing continuation)
  · intro stable
    exact stable.1

theorem conservation_of_standing_preservation
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (licensed : Step -> Step -> Prop)
    (preservesStanding : forall source destination,
      R.Standing source -> licensed source destination ->
        R.Standing destination) :
    forall source destination,
      R.Standing source -> licensed source destination ->
        R.Admissible destination := by
  intro source destination standing continuation
  exact (R.admissible_iff_standing destination).2
    (preservesStanding source destination standing continuation)

/-! ## Redescription and transport closure -/

theorem redescription_preserves_reference_and_standing
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    (redescription : R.Redescription)
    {act : Act}
    {target : Target}
    {step : Step}
    (reference : R.ReferenceAt act target)
    (standing : R.Standing step) :
    R.ReferenceAt (redescription.actForward act) target /\
      R.Standing (redescription.stepForward step) := by
  exact ⟨redescription.preserves_reference reference,
    redescription.preserves_standing standing⟩

def TargetInvariantRelation
    {Act : Type u}
    {Target : Type v}
    (R : Regime Act Target (Unit))
    (relation : Act -> Act -> Prop) : Prop :=
  forall left right left' right',
    R.targetOf left = R.targetOf left' ->
    R.targetOf right = R.targetOf right' ->
    (relation left right <-> relation left' right')

theorem transport_closure
    {Act : Type u}
    {Target : Type v}
    (R : Regime Act Target Unit)
    (relation : Act -> Act -> Prop)
    (invariant : TargetInvariantRelation R relation) :
    forall left right left' right',
      R.targetOf left = R.targetOf left' ->
      R.targetOf right = R.targetOf right' ->
      (relation left right <-> relation left' right') :=
  invariant

/-! ## Additional foundational conditions and the mechanization boundary -/

def DerivativeInvariant
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (candidate : Step -> Prop) : Prop :=
  forall step, candidate step <-> R.Standing step

def IndependentInvariant
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (candidate : Step -> Prop) : Prop :=
  exists step, Not (candidate step <-> R.Standing step)

theorem foundational_candidate_exhaustion
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (candidate : Step -> Prop) :
    DerivativeInvariant R candidate \/ IndependentInvariant R candidate := by
  classical
  by_cases h : IndependentInvariant R candidate
  · exact Or.inr h
  · left
    intro step
    exact Classical.byContradiction
      (fun notEquivalent => h ⟨step, notEquivalent⟩)

theorem no_independent_faithful_foundational_condition
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    {R : Regime Act Target Step}
    {candidate : Step -> Prop}
    (faithful : DerivativeInvariant R candidate) :
    Not (IndependentInvariant R candidate) := by
  intro independent
  rcases independent with ⟨step, difference⟩
  exact difference (faithful step)

/-- A named role carrier for the manuscript's four-role kernel. -/
inductive KernelRole where
  | admissibility
  | standing
  | reference
  | irreversibility
deriving DecidableEq, Repr

/-- A role package is a predicate on the independently named role carrier. -/
def RolePackage : Type := KernelRole -> Prop

def CompleteRolePackage (package : RolePackage) : Prop :=
  forall role, package role

def StrictRoleSubpackage (small large : RolePackage) : Prop :=
  (forall role, small role -> large role) /\
    exists role, large role /\ Not (small role)

theorem no_strict_complete_role_subpackage
    {small large : RolePackage}
    (complete : CompleteRolePackage small)
    (strict : StrictRoleSubpackage small large) :
    Not (CompleteRolePackage large) := by
  intro largeComplete
  rcases strict.2 with ⟨role, largeRole, notSmall⟩
  exact notSmall (complete role)

theorem complete_role_package_has_kernel_roles
    (package : RolePackage)
    (complete : CompleteRolePackage package) :
    package .admissibility /\
      package .standing /\
      package .reference /\
      package .irreversibility :=
  ⟨complete _, complete _, complete _, complete _⟩

/-- The structural tuple named KD in the manuscript. -/
structure KernelStructure
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) where
  governanceEquivalent : Regime Act Target Step -> Prop
  invariantBundle : Step -> Prop

def KernelStructure.canonical
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    KernelStructure R where
  governanceEquivalent S := GovernanceEquivalent R S
  invariantBundle step := R.Standing step

/-- A repair changes the original act, not just its later presentation. -/
theorem same_act_repair_impossible
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    {original revised : Step}
    (repair : R.Repair original revised) :
    Not (original = revised) :=
  R.repair_is_distinct repair

theorem admissibility_requires_standing
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    {step : Step}
    (admissible : R.Admissible step) :
    R.Standing step :=
  (R.admissible_iff_standing step).1 admissible

theorem standing_requires_admissibility
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    {step : Step}
    (standing : R.Standing step) :
    R.Admissible step :=
  (R.admissible_iff_standing step).2 standing

theorem no_standing_without_admissibility
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    {step : Step}
    (notStanding : Not (R.Standing step)) :
    Not (R.Admissible step) := by
  intro admissible
  exact notStanding (admissibility_requires_standing R admissible)

theorem reference_necessity
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    forall act, exists target,
      R.ReferenceAt act target /\
        forall other, R.ReferenceAt act other -> other = target :=
  (targetAdequacy_forces_kernel_roles R).referenceExistsUnique

theorem irreversibility_necessity
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    forall {original revised},
      Not (R.verdict original = R.verdict revised) ->
        Not (original = revised) :=
  (targetAdequacy_forces_kernel_roles R).actTimeIrreversible

theorem admissibility_is_joint_boundary
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    forall step, R.Admissible step <-> R.Standing step :=
  (targetAdequacy_forces_kernel_roles R).admissibleIffStanding

/-- A fixed-domain discriminator is either invariant or changes a governed datum. -/
def IdentityInvariantDiscriminator
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (discriminator : Step -> Prop) : Prop :=
  forall left right, ActIdentity R left right ->
    (discriminator left <-> discriminator right)

def ChangesGovernedClassification
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (discriminator : Step -> Prop) : Prop :=
  exists left right, ActIdentity R left right /\
    Not (discriminator left <-> discriminator right)

theorem boundary_closure_dichotomy
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step)
    (discriminator : Step -> Prop) :
    IdentityInvariantDiscriminator R discriminator \/
      ChangesGovernedClassification R discriminator := by
  classical
  by_cases invariant : IdentityInvariantDiscriminator R discriminator
  · exact Or.inl invariant
  · right
    exact Classical.byContradiction (fun noChange =>
      invariant (fun left right identity =>
        Classical.byContradiction (fun notEquivalent =>
          noChange ⟨left, right, identity, notEquivalent⟩)))

/-- A role omission is an explicit failure of one of the neutral kernel
clauses.  It is a predicate on a candidate regime, not a certificate that
silently supplies an omission. -/
def KernelRoleOmission
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop :=
  (Not (forall act, exists target,
    R.ReferenceAt act target /\
      forall other, R.ReferenceAt act other -> other = target)) \/
  (exists step, Not (R.Standing step)) \/
  (exists original revised : Step,
    Not (R.verdict original = R.verdict revised) /\
      original = revised)

/- A same-domain counterexample is a second regime on the same carriers. -/
structure SameRegimeFaithfulCounterexample
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R S : Regime Act Target Step) : Prop where
  targetAdequacy : TargetAdequacyProfile S
  missingRole : KernelRoleOmission S
  notGovernanceEquivalent : Not (GovernanceEquivalent R S)

theorem no_self_faithful_counterexample
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    Not (SameRegimeFaithfulCounterexample R R) := by
  intro counterexample
  exact counterexample.notGovernanceEquivalent (governanceEquivalent_refl R)

/-- The formal burden is either a lower-generation claim or a faithful counterexample. -/
def ObjectionBurden
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) : Prop :=
  (exists candidate : Step -> Prop, IndependentInvariant R candidate) \/
    exists S : Regime Act Target Step,
      SameRegimeFaithfulCounterexample R S

/-- Mechanization starts at explicit target/verdict data, where roles are derivable. -/
theorem mechanization_boundary
    {Act : Type u}
    {Target : Type v}
    {Step : Type w}
    (R : Regime Act Target Step) :
    DerivedKernelRoles R :=
  targetAdequacy_forces_kernel_roles R

/-! ## A concrete full-paper witness -/

namespace ConcreteWitness

open AASC.Instances.KernelPaper.Witness

def adequacyRegime :
    Regime ConstructionAct FixedScope
      (ConstructionAct × ConstructionAct) where
  source step := step.1
  destination step := step.2
  targetOf _ := .domain
  verdict step :=
    match step.2 with
    | .failed => .fails
    | .initial => .advances
    | .reused => .advances

theorem adequacyRegime_nondegenerate :
    adequacyRegime.Nondegenerate := by
  refine ⟨(.initial, .initial), (.initial, .failed), ?_, ?_⟩
  · rfl
  · intro standing
    cases standing

theorem adequacyRegime_targetAdequate :
    TargetAdequacyProfile adequacyRegime :=
  targetAdequacy adequacyRegime

theorem adequacyRegime_kernel_roles :
    DerivedKernelRoles adequacyRegime :=
  targetAdequacy_forces_kernel_roles adequacyRegime

theorem endpoint_and_role_occupancy_closure :
    Witness.references.kernel.ReferenceUnique /\
      Witness.references.kernel.Nontrivial /\
      Not (Nonempty (Witness.model.Path .initial .failed)) /\
      FixedRoleClosure.problem.OneAssignmentOrbit := by
  exact ⟨Witness.references.kernel_referenceUnique,
    (Witness.references.kernel_nontrivial_iff_exists_none).2
      ⟨.failed, .domain, rfl⟩,
    Witness.no_licensed_path_to_failure,
    FixedRoleClosure.oneAssignmentOrbit⟩

end ConcreteWitness

end Manuscript
end KernelPaper
end Instances
end AASC
