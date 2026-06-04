import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.V22PaperStatements

namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction

/-- V22 theorem-spine rows for the kernel paper A+ audit. -/
inductive KernelAPlusObligation where
  | rawStepSequence
  | targetAdequacy
  | targetAdequacyForcesKernel
  | governedConstruction
  | governanceEquivalence
  | invariantBundle
  | derivableFromBelow
  | sameRegimeCounterexample
  | burdenOfObjection
  | constructionForcesKernel
  | kernelNonDerivability
  | noLowerGenerator
  | noFaithfulSameDomainExtension
  | noDeeperInvariant
  | mutualClosure
  | minimality
  | governanceWorkUniqueness
  | noIntermediateStatus
  | bivalence
  | ametricBoundary
  | standingReuse
  | uniqueInterior
  | conservation
  | structuralRigidity
  | scopePreservingInvariance
  | transportClosure
  | quotientIdentity
  | foundationalExhaustion
  | foundationalClosure
  | mechanizationBoundary
  | globalSynthesis
deriving DecidableEq, Repr

def kernelAPlusObligationTitle : KernelAPlusObligation -> String
  | .rawStepSequence => "Raw step-sequence"
  | .targetAdequacy => "Kernel-neutral target adequacy"
  | .targetAdequacyForcesKernel => "Target adequacy forces the kernel roles"
  | .governedConstruction => "Governed construction and non-degenerate construction"
  | .governanceEquivalence => "Governance equivalence"
  | .invariantBundle => "Admissibility-relevant invariant bundle"
  | .derivableFromBelow => "Derivable from below"
  | .sameRegimeCounterexample => "Same-regime faithful counterexample"
  | .burdenOfObjection => "Burden of a successful objection"
  | .constructionForcesKernel => "Non-degenerate construction forces the kernel"
  | .kernelNonDerivability => "Kernel non-derivability"
  | .noLowerGenerator => "No faithful lower generator"
  | .noFaithfulSameDomainExtension =>
      "No faithful lower generator and no faithful same-domain extension"
  | .noDeeperInvariant => "No governance-effective deeper same-domain invariant"
  | .mutualClosure => "Mutual closure of the kernel"
  | .minimality => "Minimality of the kernel"
  | .governanceWorkUniqueness =>
      "Uniqueness of governance work, not of bookkeeping decomposition"
  | .noIntermediateStatus => "No intermediate admissibility state"
  | .bivalence => "Necessity and bivalence of admissibility"
  | .ametricBoundary => "AMetric boundary and non-parameterization"
  | .standingReuse => "Standing equals reuse-stable admissibility"
  | .uniqueInterior => "Extensional uniqueness of the admissible interior"
  | .conservation => "Conservation of standing"
  | .structuralRigidity => "Structural rigidity of the admissibility invariant"
  | .scopePreservingInvariance => "Scope-preserving invariance"
  | .transportClosure => "Transport closure"
  | .quotientIdentity => "Quotient identity"
  | .foundationalExhaustion => "Exhaustion of foundational conditions"
  | .foundationalClosure => "Foundational closure"
  | .mechanizationBoundary => "Internal mechanization boundary"
  | .globalSynthesis => "Global synthesis under corpus closures"

def kernelAPlusObligations : List KernelAPlusObligation :=
  [ .rawStepSequence
  , .targetAdequacy
  , .targetAdequacyForcesKernel
  , .governedConstruction
  , .governanceEquivalence
  , .invariantBundle
  , .derivableFromBelow
  , .sameRegimeCounterexample
  , .burdenOfObjection
  , .constructionForcesKernel
  , .kernelNonDerivability
  , .noLowerGenerator
  , .noFaithfulSameDomainExtension
  , .noDeeperInvariant
  , .mutualClosure
  , .minimality
  , .governanceWorkUniqueness
  , .noIntermediateStatus
  , .bivalence
  , .ametricBoundary
  , .standingReuse
  , .uniqueInterior
  , .conservation
  , .structuralRigidity
  , .scopePreservingInvariance
  , .transportClosure
  , .quotientIdentity
  , .foundationalExhaustion
  , .foundationalClosure
  , .mechanizationBoundary
  , .globalSynthesis
  ]

def kernelAPlusObligationTitles : List String :=
  kernelAPlusObligations.map kernelAPlusObligationTitle

theorem kernelAPlusObligationCount_eq :
    kernelAPlusObligations.length = 31 := by
  rfl

def kernelAPlusObligationTitlesDuplicateFreeBool : Bool :=
  kernelAPlusObligationTitles.length ==
    kernelAPlusObligationTitles.eraseDups.length

theorem kernelAPlusObligationTitlesDuplicateFreeBool_eq_true :
    kernelAPlusObligationTitlesDuplicateFreeBool = true := by
  rfl

def kernelAPlusObligationTitlesPopulatedBool : Bool :=
  kernelAPlusObligationTitles.all (fun title => !title.isEmpty)

theorem kernelAPlusObligationTitlesPopulatedBool_eq_true :
    kernelAPlusObligationTitlesPopulatedBool = true := by
  rfl

/--
Audit certificate for the fixed-domain consequence layer of the v22 kernel
paper.  The fields are the load-bearing objects the manuscript later cites:
kernel package, no-below result, binary/AMetric interface, standing reuse,
unique interior, conservation, and fixed-domain uniqueness.
-/
structure KernelAPlusAuditCertificate
    {Act Object : Type}
    (R : ConstructionRegime Act Object) where
  kernel : KernelPackage R
  closurePacket : FixedDomainClosurePacket R
  noBelowKernel : NoDerivationBelowKernel R
  interfaceShape : FixedDomainInterfaceShape R
  bivalence : R.boundaryFixed /\ AdmissibilityBivalent R
  ametricBoundary : NoBoundarySelectorImport R
  standingReuse : StandingReuseStableExactly R
  uniqueInterior : UniqueAdmissibleInterior R
  conservation : StandingConservationOnFixedDomain R
  fixedDomainUniqueness : KernelUniqueOnFixedDomain R

def KernelAPlusAuditCertificate.ofKernelPacketAndUniqueness
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_kernel : KernelPackage R)
    (h_packet : FixedDomainClosurePacket R)
    (h_unique : KernelUniqueOnFixedDomain R) :
    KernelAPlusAuditCertificate R where
  kernel := h_kernel
  closurePacket := h_packet
  noBelowKernel := PaperNothingDerivableBelowKernelStatement R h_kernel
  interfaceShape := PaperFixedDomainInterfaceShapeStatement R h_packet
  bivalence :=
    PaperNecessityAndBivalenceOfAdmissibilityStatement R h_kernel h_packet
  ametricBoundary := PaperAMetricBoundaryAndNonParameterizationStatement R h_packet
  standingReuse := PaperStandingEqualsReuseStableAdmissibilityStatement R h_packet
  uniqueInterior := PaperExtensionalUniquenessOfAdmissibleInteriorStatement R h_packet
  conservation := PaperConservationOfStandingStatement R h_packet
  fixedDomainUniqueness := h_unique

def KernelAPlusAuditCertificate.auditSurfaceComplete
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (_C : KernelAPlusAuditCertificate R) : Prop :=
  kernelAPlusObligations.length = 31 /\
  kernelAPlusObligationTitlesDuplicateFreeBool = true /\
  kernelAPlusObligationTitlesPopulatedBool = true /\
  KernelPackage R /\
  FixedDomainClosurePacket R /\
  NoDerivationBelowKernel R /\
  FixedDomainInterfaceShape R /\
  KernelUniqueOnFixedDomain R

theorem KernelAPlusAuditCertificate.auditSurfaceComplete_holds
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (C : KernelAPlusAuditCertificate R) :
    C.auditSurfaceComplete := by
  exact
    And.intro kernelAPlusObligationCount_eq
      (And.intro kernelAPlusObligationTitlesDuplicateFreeBool_eq_true
        (And.intro kernelAPlusObligationTitlesPopulatedBool_eq_true
          (And.intro C.kernel
            (And.intro C.closurePacket
              (And.intro C.noBelowKernel
                (And.intro C.interfaceShape C.fixedDomainUniqueness))))))

theorem KernelAPlusAuditCertificate.requires_bivalence
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (C : KernelAPlusAuditCertificate R) :
    R.boundaryFixed /\ AdmissibilityBivalent R := by
  exact C.bivalence

theorem KernelAPlusAuditCertificate.requires_ametric_boundary
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (C : KernelAPlusAuditCertificate R) :
    NoBoundarySelectorImport R := by
  exact C.ametricBoundary

theorem KernelAPlusAuditCertificate.requires_standing_reuse
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (C : KernelAPlusAuditCertificate R) :
    StandingReuseStableExactly R := by
  exact C.standingReuse

theorem KernelAPlusAuditCertificate.requires_unique_interior
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (C : KernelAPlusAuditCertificate R) :
    UniqueAdmissibleInterior R := by
  exact C.uniqueInterior

theorem KernelAPlusAuditCertificate.requires_conservation
    {Act Object : Type}
    {R : ConstructionRegime Act Object}
    (C : KernelAPlusAuditCertificate R) :
    StandingConservationOnFixedDomain R := by
  exact C.conservation

end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
