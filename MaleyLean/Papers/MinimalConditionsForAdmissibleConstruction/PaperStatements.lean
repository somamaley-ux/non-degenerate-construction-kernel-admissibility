import MaleyLean.Papers.BivalenceNonDegenerateReasoning.PaperStatements
import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.Verbatim.TheoremRegister

namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction

/-- A fixed-domain construction surface for the manuscript's local argument. -/
structure ConstructionRegime (Act Object : Type) where
  target : Act -> Object
  sameTarget : Object -> Object -> Prop
  admissible : Act -> Prop
  standing : Act -> Prop
  referenceFixed : Act -> Prop
  irreversibleFailure : Act -> Prop
  licensedContinuation : Act -> Act -> Prop
  targetIdentityFixed : Prop
  stepEligibilityFixed : Prop
  actTimeFailureStable : Prop
  boundaryFixed : Prop
  governedConstructionUse : Prop
  noRawTraceSuffices : Prop
  noSelectorImport : Prop
  noDomainShift : Prop
  noBookkeepingOnly : Prop

def KernelPackage {Act Object : Type} (R : ConstructionRegime Act Object) : Prop :=
  R.boundaryFixed /\
  (forall a : Act, R.standing a -> R.admissible a) /\
  (forall a : Act, R.referenceFixed a) /\
  (forall a : Act, R.irreversibleFailure a)

def TargetPhenomenon {Act Object : Type} (R : ConstructionRegime Act Object) : Prop :=
  R.targetIdentityFixed /\
  R.stepEligibilityFixed /\
  R.actTimeFailureStable /\
  R.governedConstructionUse

def FaithfulLowerGenerator {Act Object : Type} (R : ConstructionRegime Act Object) : Prop :=
  TargetPhenomenon R /\ Not (KernelPackage R)

def FaithfulSameDomainExtension {Act Object : Type} (R : ConstructionRegime Act Object) : Prop :=
  TargetPhenomenon R /\ R.noDomainShift /\ Not (KernelPackage R)

def GovernanceEquivalent {Act Object : Type}
    (R S : ConstructionRegime Act Object) : Prop :=
  (R.boundaryFixed <-> S.boundaryFixed) /\
  (forall a : Act, R.admissible a <-> S.admissible a) /\
  (forall a : Act, R.standing a <-> S.standing a) /\
  (forall a : Act, R.referenceFixed a <-> S.referenceFixed a) /\
  (forall a : Act, R.irreversibleFailure a <-> S.irreversibleFailure a)

def StrictlyBelowKernel {Act Object : Type}
    (R S : ConstructionRegime Act Object) : Prop :=
  TargetPhenomenon S /\ GovernanceEquivalent R S /\ Not (KernelPackage S)

def SameDomainKernelRealization {Act Object : Type}
    (R S : ConstructionRegime Act Object) : Prop :=
  TargetPhenomenon S /\ KernelPackage S /\ GovernanceEquivalent R S

def KernelUniqueOnFixedDomain {Act Object : Type}
    (R : ConstructionRegime Act Object) : Prop :=
  forall S : ConstructionRegime Act Object,
    SameDomainKernelRealization R S -> GovernanceEquivalent R S

def NoDerivationBelowKernel {Act Object : Type}
    (R : ConstructionRegime Act Object) : Prop :=
  forall S : ConstructionRegime Act Object, Not (StrictlyBelowKernel R S)

def ReuseStableStanding {Act Object : Type} (R : ConstructionRegime Act Object) (a : Act) :
    Prop :=
  R.standing a /\
  forall b : Act, R.licensedContinuation a b -> R.admissible b

/-- Three structural axes from which the manuscript's route map is derived. -/
inductive RouteAxis where
  | targetFixation
  | stepEligibility
  | actTimeStability
deriving DecidableEq, Repr

def RouteAxisExhaustion : Prop :=
  forall r : RouteAxis,
    r = RouteAxis.targetFixation \/
    r = RouteAxis.stepEligibility \/
    r = RouteAxis.actTimeStability

/-- Collapse routes for attempted kernel avoidance on the same fixed domain. -/
inductive CollapseRoute where
  | losesTargetPhenomenon
  | importsSelectorStructure
  | changesDomain
  | governanceEquivalent
  | bookkeepingOnly
deriving DecidableEq, Repr

def CollapseRouteExhaustion : Prop :=
  forall r : CollapseRoute,
    r = CollapseRoute.losesTargetPhenomenon \/
    r = CollapseRoute.importsSelectorStructure \/
    r = CollapseRoute.changesDomain \/
    r = CollapseRoute.governanceEquivalent \/
    r = CollapseRoute.bookkeepingOnly

def FixedDomainClosurePacket {Act Object : Type} (R : ConstructionRegime Act Object) :
    Prop :=
  (forall a : Act, R.admissible a \/ Not (R.admissible a)) /\
  R.noSelectorImport /\
  (forall a : Act, R.standing a <-> ReuseStableStanding R a) /\
  (forall P Q : Act -> Prop,
    (forall a : Act, P a <-> R.standing a) ->
    (forall a : Act, Q a <-> R.standing a) ->
    forall a : Act, P a <-> Q a) /\
  (forall a b : Act, Not (R.standing a) -> R.licensedContinuation a b -> Not (R.standing b))

def FoundationallyClosed {Act Object : Type} (R : ConstructionRegime Act Object) : Prop :=
  KernelPackage R /\ FixedDomainClosurePacket R

def ConsequenceLayerMechanization {Act Object : Type} (R : ConstructionRegime Act Object) :
    Prop :=
  FixedDomainClosurePacket R

def bivalenceGovernanceSystem
    {Act Object : Type}
    (R : ConstructionRegime Act Object) :
    BivalenceNonDegenerateReasoning.GovernanceSystem Act where
  standing := R.standing
  licensedContinuation := R.licensedContinuation
  governanceBearingNonDegenerateUse := R.governedConstructionUse
  reference := forall a : Act, R.referenceFixed a
  standingPersistence := forall a : Act, R.standing a -> R.admissible a
  irreversibility := forall a : Act, R.irreversibleFailure a
  priorGate := R.boundaryFixed
  failClosed := R.actTimeFailureStable
  blocksSilentRedescription := R.targetIdentityFixed
  scopeIntegrity := R.noDomainShift

theorem PaperConstructionForcesKernelStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_boundary : R.boundaryFixed)
    (h_standing : forall a : Act, R.standing a -> R.admissible a)
    (h_reference : forall a : Act, R.referenceFixed a)
    (h_irreversible : forall a : Act, R.irreversibleFailure a) :
    KernelPackage R := by
  exact And.intro h_boundary
    (And.intro h_standing (And.intro h_reference h_irreversible))

theorem PaperKernelNonDerivabilityStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R) :
    Not (FaithfulLowerGenerator R) := by
  intro h_lower
  exact h_lower.2 h_kernel

theorem PaperKernelPackageTransfersAcrossGovernanceEquivalenceStatement
    {Act Object : Type}
    (R S : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R)
    (h_equiv : GovernanceEquivalent R S) :
    KernelPackage S := by
  rcases h_kernel with
    ⟨h_boundary, h_standing_adm, h_reference, h_irreversible⟩
  rcases h_equiv with
    ⟨h_boundary_equiv, h_adm_equiv, h_standing_equiv,
      h_reference_equiv, h_irreversible_equiv⟩
  refine And.intro (h_boundary_equiv.mp h_boundary) ?_
  refine And.intro ?_ ?_
  · intro a hStandingS
    exact (h_adm_equiv a).mp
      (h_standing_adm a ((h_standing_equiv a).mpr hStandingS))
  refine And.intro ?_ ?_
  · intro a
    exact (h_reference_equiv a).mp (h_reference a)
  · intro a
    exact (h_irreversible_equiv a).mp (h_irreversible a)

theorem PaperNothingDerivableBelowKernelStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R) :
    NoDerivationBelowKernel R := by
  intro S h_below
  exact h_below.2.2
    (PaperKernelPackageTransfersAcrossGovernanceEquivalenceStatement
      R
      S
      h_kernel
      h_below.2.1)

theorem PaperNoFaithfulLowerGeneratorStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R) :
    Not (FaithfulLowerGenerator R) := by
  exact PaperKernelNonDerivabilityStatement R h_kernel

theorem PaperRouteAxisExhaustionStatement :
    RouteAxisExhaustion := by
  intro r
  cases r with
  | targetFixation => exact Or.inl rfl
  | stepEligibility => exact Or.inr (Or.inl rfl)
  | actTimeStability => exact Or.inr (Or.inr rfl)

theorem PaperCollapseRouteExhaustionStatement :
    CollapseRouteExhaustion := by
  intro r
  cases r with
  | losesTargetPhenomenon =>
      exact Or.inl rfl
  | importsSelectorStructure =>
      exact Or.inr (Or.inl rfl)
  | changesDomain =>
      exact Or.inr (Or.inr (Or.inl rfl))
  | governanceEquivalent =>
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | bookkeepingOnly =>
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem PaperRouteExhaustionStatement :
    RouteAxisExhaustion /\ CollapseRouteExhaustion := by
  exact And.intro PaperRouteAxisExhaustionStatement PaperCollapseRouteExhaustionStatement

theorem PaperNoFaithfulSameDomainExtensionStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R) :
    Not (FaithfulSameDomainExtension R) := by
  intro h_extension
  exact h_extension.2.2 h_kernel

theorem PaperDerivationDependsOnConstructionalStandingStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (a : Act)
    (h_standing_to_admissible : forall x : Act, R.standing x -> R.admissible x)
    (h_derivation_use : R.standing a) :
    R.admissible a := by
  exact h_standing_to_admissible a h_derivation_use

theorem PaperNoDeeperInvariantStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R)
    (_h_candidate :
      R.noSelectorImport \/ R.noDomainShift \/ GovernanceEquivalent R R \/ R.noBookkeepingOnly) :
    Not (FaithfulLowerGenerator R) := by
  exact PaperNoFaithfulLowerGeneratorStatement R h_kernel

theorem PaperMutualClosureStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R) :
    R.boundaryFixed /\
    (forall a : Act, R.standing a -> R.admissible a) /\
    (forall a : Act, R.referenceFixed a) /\
    (forall a : Act, R.irreversibleFailure a) := by
  exact h_kernel

theorem PaperUniquenessOfGovernanceWorkStatement
    {Act Object : Type}
    (R S : ConstructionRegime Act Object)
    (h_boundary : R.boundaryFixed <-> S.boundaryFixed)
    (h_adm : forall a : Act, R.admissible a <-> S.admissible a)
    (h_standing : forall a : Act, R.standing a <-> S.standing a)
    (h_reference : forall a : Act, R.referenceFixed a <-> S.referenceFixed a)
    (h_irreversible : forall a : Act, R.irreversibleFailure a <-> S.irreversibleFailure a) :
    GovernanceEquivalent R S := by
  exact And.intro h_boundary
    (And.intro h_adm
      (And.intro h_standing (And.intro h_reference h_irreversible)))

theorem PaperKernelUniquenessOnFixedDomainStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_unique :
      forall S : ConstructionRegime Act Object,
        SameDomainKernelRealization R S -> GovernanceEquivalent R S) :
    KernelUniqueOnFixedDomain R := by
  exact h_unique

theorem PaperFixedDomainClosurePacketStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_binary : forall a : Act, R.admissible a \/ Not (R.admissible a))
    (h_no_selector : R.noSelectorImport)
    (h_standing :
      forall a : Act, R.standing a <-> ReuseStableStanding R a)
    (h_unique :
      forall P Q : Act -> Prop,
        (forall a : Act, P a <-> R.standing a) ->
        (forall a : Act, Q a <-> R.standing a) ->
        forall a : Act, P a <-> Q a)
    (h_conservation :
      forall a b : Act,
        Not (R.standing a) -> R.licensedContinuation a b -> Not (R.standing b)) :
    FixedDomainClosurePacket R := by
  exact And.intro h_binary
    (And.intro h_no_selector
      (And.intro h_standing (And.intro h_unique h_conservation)))

theorem PaperTransportQuotientAndDomainOperatorsStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (C : Act -> Act)
    (h_scope :
      forall a : Act,
        R.standing a ->
        R.sameTarget (R.target a) (R.target (C a)))
    (a : Act)
    (h_standing : R.standing a) :
    R.sameTarget (R.target a) (R.target (C a)) := by
  exact h_scope a h_standing

theorem PaperFoundationalClosureStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R)
    (h_packet : FixedDomainClosurePacket R) :
    FoundationallyClosed R := by
  exact And.intro h_kernel h_packet

theorem PaperInternalMechanizationBoundaryStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_packet : FixedDomainClosurePacket R) :
    ConsequenceLayerMechanization R := by
  exact h_packet

theorem PaperGlobalSynthesisStatement
    {Act Object : Type}
    (R S : ConstructionRegime Act Object)
    (_hR : FoundationallyClosed R)
    (_hS : FoundationallyClosed S)
    (h_same :
      (R.boundaryFixed <-> S.boundaryFixed) /\
      (forall a : Act, R.admissible a <-> S.admissible a) /\
      (forall a : Act, R.standing a <-> S.standing a) /\
      (forall a : Act, R.referenceFixed a <-> S.referenceFixed a) /\
      (forall a : Act, R.irreversibleFailure a <-> S.irreversibleFailure a)) :
    GovernanceEquivalent R S := by
  exact h_same

theorem PaperBivalenceBridgeStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_boundary : R.boundaryFixed)
    (h_target : R.targetIdentityFixed)
    (h_scope : R.noDomainShift)
    (h_failClosed : R.actTimeFailureStable) :
    BivalenceNonDegenerateReasoning.AASCClass (bivalenceGovernanceSystem R) := by
  exact
    BivalenceNonDegenerateReasoning.PaperBivalenceOfNonDegenerateReasoningStatement
      (bivalenceGovernanceSystem R)
      h_boundary
      h_target
      h_scope
      h_failClosed

end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
