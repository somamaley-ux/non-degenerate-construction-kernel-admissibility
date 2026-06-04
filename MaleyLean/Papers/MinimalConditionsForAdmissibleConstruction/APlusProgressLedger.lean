import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.APlusSourceCrosswalk

namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction

/-- Coarse progress phases for the kernel paper A+ hardening pass. -/
inductive KernelAPlusProgressPhase where
  | theoremSpineMapped
  | auditHarnessMature
  | consequenceLayerClosed
  | hypothesisGatesIsolated
  | corpusClosureSeparated
  | finalAPlusClosure
deriving DecidableEq, Repr

def KernelAPlusProgressPhase.label : KernelAPlusProgressPhase -> String
  | .theoremSpineMapped => "V22 theorem spine mapped"
  | .auditHarnessMature => "Audit harness and source crosswalk mature"
  | .consequenceLayerClosed => "Fixed-domain consequence layer closed"
  | .hypothesisGatesIsolated => "Residual hypothesis gates isolated"
  | .corpusClosureSeparated => "Corpus-closure synthesis separated"
  | .finalAPlusClosure => "Final A+ closure"

def kernelAPlusRowsWithStatus
    (status : KernelAPlusFormalStatus) : List KernelAPlusSourceCrosswalkRow :=
  kernelAPlusSourceCrosswalk.filter
    (fun R => R.formalStatus == status)

def kernelAPlusDefinitionCarrierRows : List KernelAPlusSourceCrosswalkRow :=
  kernelAPlusRowsWithStatus .definitionCarrier

def kernelAPlusDirectLeanTheoremRows : List KernelAPlusSourceCrosswalkRow :=
  kernelAPlusRowsWithStatus .directLeanTheorem

def kernelAPlusConsequenceProjectionRows : List KernelAPlusSourceCrosswalkRow :=
  kernelAPlusRowsWithStatus .consequenceProjection

def kernelAPlusCorpusClosureSynthesisRows : List KernelAPlusSourceCrosswalkRow :=
  kernelAPlusRowsWithStatus .corpusClosureSynthesis

def kernelAPlusDefinitionCarrierLeanAnchors : List String :=
  kernelAPlusDefinitionCarrierRows.map (fun R => R.leanAnchor)

def kernelAPlusDirectLeanTheoremAnchors : List String :=
  kernelAPlusDirectLeanTheoremRows.map (fun R => R.leanAnchor)

def kernelAPlusConsequenceProjectionAnchors : List String :=
  kernelAPlusConsequenceProjectionRows.map (fun R => R.leanAnchor)

theorem kernelAPlusDefinitionCarrierRows_count_eq :
    kernelAPlusDefinitionCarrierRows.length = 7 := by
  rfl

theorem kernelAPlusDirectLeanTheoremRows_count_eq :
    kernelAPlusDirectLeanTheoremRows.length = 14 := by
  rfl

theorem kernelAPlusConsequenceProjectionRows_count_eq :
    kernelAPlusConsequenceProjectionRows.length = 10 := by
  rfl

theorem kernelAPlusProgressHypothesisGateRows_count_eq :
    kernelAPlusHypothesisGateRows.length = 0 := by
  rfl

theorem kernelAPlusProgressCorpusClosureRows_count_eq :
    kernelAPlusCorpusClosureSynthesisRows.length = 0 := by
  rfl

def kernelAPlusClosedOrAuditedRowCount : Nat :=
  kernelAPlusDefinitionCarrierRows.length +
  kernelAPlusDirectLeanTheoremRows.length +
  kernelAPlusConsequenceProjectionRows.length

theorem kernelAPlusClosedOrAuditedRowCount_eq :
    kernelAPlusClosedOrAuditedRowCount = 31 := by
  rfl

def kernelAPlusResidualGateRowCount : Nat :=
  kernelAPlusHypothesisGateRows.length +
  kernelAPlusCorpusClosureSynthesisRows.length

theorem kernelAPlusResidualGateRowCount_eq :
    kernelAPlusResidualGateRowCount = 0 := by
  rfl

def kernelAPlusAuditReadinessPercent : Nat := 100

/--
Mathematical closure percentage for the v22 spine, counting definition
carriers, direct Lean theorems, and consequence projections as closed/audited,
and leaving hypothesis gates plus corpus synthesis as residual gates.
-/
def kernelAPlusMathematicalClosurePercent : Nat :=
  kernelAPlusClosedOrAuditedRowCount * 100 / kernelAPlusObligations.length

theorem kernelAPlusMathematicalClosurePercent_eq :
    kernelAPlusMathematicalClosurePercent = 100 := by
  rfl

structure KernelAPlusProgressSnapshot where
  phase : KernelAPlusProgressPhase
  obligationRows : Nat
  definitionCarrierRows : Nat
  directLeanTheoremRows : Nat
  consequenceProjectionRows : Nat
  hypothesisGateRows : Nat
  corpusClosureRows : Nat
  closedOrAuditedRows : Nat
  residualGateRows : Nat
  auditReadinessPercent : Nat
  mathematicalClosurePercent : Nat
  sourceCrosswalkComplete : Prop

def kernelAPlusCurrentProgressSnapshot : KernelAPlusProgressSnapshot :=
  { phase := .finalAPlusClosure
    obligationRows := kernelAPlusObligations.length
    definitionCarrierRows := kernelAPlusDefinitionCarrierRows.length
    directLeanTheoremRows := kernelAPlusDirectLeanTheoremRows.length
    consequenceProjectionRows := kernelAPlusConsequenceProjectionRows.length
    hypothesisGateRows := kernelAPlusHypothesisGateRows.length
    corpusClosureRows := kernelAPlusCorpusClosureSynthesisRows.length
    closedOrAuditedRows := kernelAPlusClosedOrAuditedRowCount
    residualGateRows := kernelAPlusResidualGateRowCount
    auditReadinessPercent := kernelAPlusAuditReadinessPercent
    mathematicalClosurePercent := kernelAPlusMathematicalClosurePercent
    sourceCrosswalkComplete := kernelAPlusSourceCrosswalkAuditComplete }

def kernelAPlusCurrentProgressTuple :
    String × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  ( kernelAPlusCurrentProgressSnapshot.phase.label
  , kernelAPlusCurrentProgressSnapshot.obligationRows
  , kernelAPlusCurrentProgressSnapshot.closedOrAuditedRows
  , kernelAPlusCurrentProgressSnapshot.residualGateRows
  , kernelAPlusCurrentProgressSnapshot.definitionCarrierRows
  , kernelAPlusCurrentProgressSnapshot.directLeanTheoremRows
  , kernelAPlusCurrentProgressSnapshot.consequenceProjectionRows
  , kernelAPlusCurrentProgressSnapshot.hypothesisGateRows
  , kernelAPlusCurrentProgressSnapshot.corpusClosureRows )

theorem kernelAPlusCurrentProgressSnapshot_obligationRows_eq :
    kernelAPlusCurrentProgressSnapshot.obligationRows = 31 := by
  rfl

theorem kernelAPlusCurrentProgressSnapshot_closedOrAuditedRows_eq :
    kernelAPlusCurrentProgressSnapshot.closedOrAuditedRows = 31 := by
  rfl

theorem kernelAPlusCurrentProgressSnapshot_residualGateRows_eq :
    kernelAPlusCurrentProgressSnapshot.residualGateRows = 0 := by
  rfl

theorem kernelAPlusCurrentProgressSnapshot_auditReadinessPercent_eq :
    kernelAPlusCurrentProgressSnapshot.auditReadinessPercent = 100 := by
  rfl

theorem kernelAPlusCurrentProgressSnapshot_mathematicalClosurePercent_eq :
    kernelAPlusCurrentProgressSnapshot.mathematicalClosurePercent = 100 := by
  rfl

def kernelAPlusResidualGateLeanAnchors : List String :=
  kernelAPlusHypothesisGateLeanAnchors ++ kernelAPlusCorpusClosureLeanAnchors

theorem kernelAPlusResidualGateLeanAnchors_count_eq :
    kernelAPlusResidualGateLeanAnchors.length = 0 := by
  rfl

def kernelAPlusProgressAuditComplete : Prop :=
  kernelAPlusSourceCrosswalkAuditComplete /\
  kernelAPlusObligations.length = 31 /\
  kernelAPlusClosedOrAuditedRowCount = 31 /\
  kernelAPlusResidualGateRowCount = 0 /\
  kernelAPlusMathematicalClosurePercent = 100 /\
  kernelAPlusResidualGateLeanAnchors.length = 0

theorem kernelAPlusProgressAuditComplete_holds :
    kernelAPlusProgressAuditComplete := by
  exact
    And.intro kernelAPlusSourceCrosswalkAuditComplete_holds
      (And.intro kernelAPlusObligationCount_eq
        (And.intro kernelAPlusClosedOrAuditedRowCount_eq
          (And.intro kernelAPlusResidualGateRowCount_eq
            (And.intro kernelAPlusMathematicalClosurePercent_eq
              kernelAPlusResidualGateLeanAnchors_count_eq))))

end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
