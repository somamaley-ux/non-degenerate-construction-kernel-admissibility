namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction
namespace Verbatim

/-- Verbatim manuscript title extracted from the supplied Erkenntnis source. -/
def manuscriptTitle : String :=
  "Non-Degenerate Construction and the Kernel of Admissibility"

/--
Human-facing role statement for this paper in the AASC corpus.

This is the kernel paper: it states the fixed-domain uniqueness result for
admissibility, standing, reference, and irreversibility, and records that no
same-domain, governance-equivalent construction can be derived beneath that
kernel.
-/
def manuscriptRole : String :=
  "Kernel paper: A+ closed fixed-domain uniqueness of the admissibility kernel; nothing governance-equivalent is derivable below it."

/-- Human-facing A+ strength claim recorded for the closed audit surface. -/
def manuscriptAuditStrength : String :=
  "A+ closed: 31 theorem-spine rows, 31 closed or audited, 0 residual gates, 0 hypothesis gates."

/-- Main section spine extracted from the supplied manuscript. -/
inductive SectionTag where
  | introduction
  | examplesAndDefinitions
  | kernelNecessity
  | routeExhaustion
  | rigidity
  | consequencesMechanizationAndConclusion
deriving DecidableEq, Repr

def sectionTitle : SectionTag -> String
  | .introduction =>
      "Introduction"
  | .examplesAndDefinitions =>
      "Examples and Definitions"
  | .kernelNecessity =>
      "Kernel Necessity and Non-Derivability"
  | .routeExhaustion =>
      "Route Exhaustion and No Lower Generator"
  | .rigidity =>
      "Mutual Closure and Fixed-Domain Rigidity"
  | .consequencesMechanizationAndConclusion =>
      "Consequences, Foundational Closure, and Mechanization"

/-- Paper-facing theorem-family register extracted from the manuscript. -/
inductive ResultTag where
  | constructionForcesKernel
  | kernelNonDerivability
  | nothingDerivableBelowKernel
  | kernelUniquenessOnFixedDomain
  | noLowerGenerator
  | routeExhaustion
  | noFaithfulSameDomainExtension
  | derivationDependsOnConstructionalStanding
  | noDeeperInvariant
  | mutualClosure
  | uniquenessOfGovernanceWork
  | fixedDomainClosurePacket
  | transportQuotientAndDomainOperators
  | foundationalClosure
  | internalMechanizationBoundary
  | globalSynthesis
deriving DecidableEq, Repr

def resultTitle : ResultTag -> String
  | .constructionForcesKernel =>
      "Construction Forces the Kernel"
  | .kernelNonDerivability =>
      "Kernel Non-Derivability"
  | .nothingDerivableBelowKernel =>
      "Nothing Derivable Below the Kernel"
  | .kernelUniquenessOnFixedDomain =>
      "Kernel Uniqueness on the Fixed Domain"
  | .noLowerGenerator =>
      "No Faithful Lower Generator"
  | .routeExhaustion =>
      "Route Exhaustion"
  | .noFaithfulSameDomainExtension =>
      "No Faithful Same-Domain Extension"
  | .derivationDependsOnConstructionalStanding =>
      "Derivation Depends on Constructional Standing"
  | .noDeeperInvariant =>
      "No Deeper Same-Domain Invariant"
  | .mutualClosure =>
      "Mutual Closure and Minimality of the Kernel"
  | .uniquenessOfGovernanceWork =>
      "Uniqueness of Governance Work"
  | .fixedDomainClosurePacket =>
      "Fixed-Domain Closure Packet"
  | .transportQuotientAndDomainOperators =>
      "Transport, Quotient Identity, and Domain-Defined Operators"
  | .foundationalClosure =>
      "Foundational Closure"
  | .internalMechanizationBoundary =>
      "Internal Mechanization Boundary"
  | .globalSynthesis =>
      "Global Synthesis under Corpus Closures"

/-- The four kernel roles named throughout the manuscript. -/
def kernelRoles : List String :=
  [ "admissibility"
  , "standing"
  , "reference"
  , "irreversibility"
  ]

/-- The route-exhaustion axes used to classify kernel-avoidance strategies. -/
def routeAxes : List String :=
  [ "target fixation"
  , "step eligibility"
  , "act-time stability"
  ]

theorem manuscriptHasRegisteredTitle :
    manuscriptTitle =
      "Non-Degenerate Construction and the Kernel of Admissibility" := by
  rfl

theorem manuscriptRoleStatesKernelUniqueness :
    manuscriptRole =
      "Kernel paper: A+ closed fixed-domain uniqueness of the admissibility kernel; nothing governance-equivalent is derivable below it." := by
  rfl

theorem manuscriptAuditStrengthStatesFinalClosure :
    manuscriptAuditStrength =
      "A+ closed: 31 theorem-spine rows, 31 closed or audited, 0 residual gates, 0 hypothesis gates." := by
  rfl

theorem manuscriptHasFixedDomainClosurePacketEntry :
    resultTitle .fixedDomainClosurePacket =
      "Fixed-Domain Closure Packet" := by
  rfl

end Verbatim
end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
