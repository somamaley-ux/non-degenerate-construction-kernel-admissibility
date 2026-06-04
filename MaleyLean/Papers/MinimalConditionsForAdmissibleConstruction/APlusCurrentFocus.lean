import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.APlusResidualGateSupplyQueue

namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction

/--
Final focus/status object for the completed kernel A+ audit.

Earlier passes used this file to expose the first remaining residual gate.  Once
the residual queue is empty, the same audit slot records that no mathematical
gate remains and names the final closed theorem.
-/
structure KernelAPlusCurrentFocusBundle where
  phase : KernelAPlusProgressPhase
  residualGateCount : Nat
  finalClosed : Bool
  finalTheorem : String
  mathematicalClosurePercent : Nat
  deriving DecidableEq

def kernelAPlusCurrentFocusBundle : KernelAPlusCurrentFocusBundle :=
  { phase := .finalAPlusClosure
    residualGateCount := kernelAPlusResidualGateRowCount
    finalClosed := kernelAPlusFinalAPlusCurrentlyClosedBool
    finalTheorem := "PaperGlobalSynthesisUnderCorpusClosuresClosedStatement"
    mathematicalClosurePercent := kernelAPlusMathematicalClosurePercent }

theorem kernelAPlusCurrentFocusBundle_phase_eq :
    kernelAPlusCurrentFocusBundle.phase =
      KernelAPlusProgressPhase.finalAPlusClosure := by
  rfl

theorem kernelAPlusCurrentFocusBundle_residualGateCount_eq :
    kernelAPlusCurrentFocusBundle.residualGateCount = 0 := by
  rfl

theorem kernelAPlusCurrentFocusBundle_finalClosed_eq_true :
    kernelAPlusCurrentFocusBundle.finalClosed = true := by
  rfl

theorem kernelAPlusCurrentFocusBundle_finalTheorem_eq :
    kernelAPlusCurrentFocusBundle.finalTheorem =
      "PaperGlobalSynthesisUnderCorpusClosuresClosedStatement" := by
  rfl

theorem kernelAPlusCurrentFocusBundle_mathematicalClosurePercent_eq :
    kernelAPlusCurrentFocusBundle.mathematicalClosurePercent = 100 := by
  rfl

/-- Typed statement of the completed final synthesis target. -/
def kernelAPlusCurrentFocusTarget
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    : Prop :=
  KernelGlobalSynthesisUnderCorpusClosures R

theorem kernelAPlusCurrentFocusTarget_closes_with_final_a_plus_certificate
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (C : KernelAPlusAuditCertificate R) :
    kernelAPlusCurrentFocusTarget R := by
  exact
    kernelAPlusCallable_globalSynthesisClosed
      R C.kernel C.closurePacket C.fixedDomainUniqueness

def kernelAPlusCurrentFocusAuditComplete : Prop :=
  kernelAPlusCurrentFocusBundle.phase =
    KernelAPlusProgressPhase.finalAPlusClosure /\
  kernelAPlusCurrentFocusBundle.residualGateCount = 0 /\
  kernelAPlusCurrentFocusBundle.finalClosed = true /\
  kernelAPlusCurrentFocusBundle.mathematicalClosurePercent = 100 /\
  kernelAPlusFinalAPlusCurrentlyClosedBool = true

theorem kernelAPlusCurrentFocusAuditComplete_holds :
    kernelAPlusCurrentFocusAuditComplete := by
  exact
    And.intro kernelAPlusCurrentFocusBundle_phase_eq
      (And.intro kernelAPlusCurrentFocusBundle_residualGateCount_eq
        (And.intro kernelAPlusCurrentFocusBundle_finalClosed_eq_true
          (And.intro
            kernelAPlusCurrentFocusBundle_mathematicalClosurePercent_eq
            kernelAPlusFinalAPlusCurrentlyClosedBool_eq_true)))

end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
