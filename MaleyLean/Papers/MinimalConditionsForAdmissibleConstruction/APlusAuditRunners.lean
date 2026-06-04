import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.APlusResidualGateCallability
import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.APlusCurrentFocus

namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction

/-- Canonical focused audit runner files for the kernel paper A+ harness. -/
def kernelAPlusFocusedAuditRunnerFiles : List String :=
  [ "Checks/Axiom/MinimalConditionsAPlusAudit.lean"
  , "Checks/Axiom/MinimalConditionsAPlusSourceCrosswalkAudit.lean"
  , "Checks/Axiom/MinimalConditionsAPlusProgressLedgerAudit.lean"
  , "Checks/Axiom/MinimalConditionsAPlusResidualGateLedgerAudit.lean"
  , "Checks/Axiom/MinimalConditionsAPlusResidualGateCallabilityAudit.lean"
  , "Checks/Axiom/MinimalConditionsAPlusResidualGateSupplyQueueAudit.lean"
  , "Checks/Axiom/MinimalConditionsAPlusCurrentFocusAudit.lean"
  ]

/-- Aggregate audit runner for the kernel A+ surface. -/
def kernelAPlusAggregateAuditRunnerFiles : List String :=
  [ "Checks/Axiom/NonDegenerateConstructionAndKernelOfAdmissibilityAxiomCheck.lean" ]

def kernelAPlusAuditRunnerFiles : List String :=
  kernelAPlusFocusedAuditRunnerFiles ++ kernelAPlusAggregateAuditRunnerFiles

def kernelAPlusFocusedAuditRunnerFilesDuplicateFreeBool : Bool :=
  kernelAPlusFocusedAuditRunnerFiles.length ==
    kernelAPlusFocusedAuditRunnerFiles.eraseDups.length

def kernelAPlusAggregateAuditRunnerFilesDuplicateFreeBool : Bool :=
  kernelAPlusAggregateAuditRunnerFiles.length ==
    kernelAPlusAggregateAuditRunnerFiles.eraseDups.length

def kernelAPlusAuditRunnerFilesDuplicateFreeBool : Bool :=
  kernelAPlusAuditRunnerFiles.length ==
    kernelAPlusAuditRunnerFiles.eraseDups.length

def kernelAPlusFocusedAuditRunnerFilesPopulatedBool : Bool :=
  kernelAPlusFocusedAuditRunnerFiles.all (fun file => !file.isEmpty)

def kernelAPlusAuditRunnerFilesPopulatedBool : Bool :=
  kernelAPlusAuditRunnerFiles.all (fun file => !file.isEmpty)

theorem kernelAPlusFocusedAuditRunnerFiles_count_eq :
    kernelAPlusFocusedAuditRunnerFiles.length = 7 := by
  rfl

theorem kernelAPlusAggregateAuditRunnerFiles_count_eq :
    kernelAPlusAggregateAuditRunnerFiles.length = 1 := by
  rfl

theorem kernelAPlusAuditRunnerFiles_count_eq :
    kernelAPlusAuditRunnerFiles.length = 8 := by
  rfl

theorem kernelAPlusAuditRunnerFiles_decomposes :
    kernelAPlusAuditRunnerFiles =
      kernelAPlusFocusedAuditRunnerFiles ++
        kernelAPlusAggregateAuditRunnerFiles := by
  rfl

theorem kernelAPlusFocusedAuditRunnerFilesDuplicateFreeBool_eq_true :
    kernelAPlusFocusedAuditRunnerFilesDuplicateFreeBool = true := by
  rfl

theorem kernelAPlusAggregateAuditRunnerFilesDuplicateFreeBool_eq_true :
    kernelAPlusAggregateAuditRunnerFilesDuplicateFreeBool = true := by
  rfl

theorem kernelAPlusAuditRunnerFilesDuplicateFreeBool_eq_true :
    kernelAPlusAuditRunnerFilesDuplicateFreeBool = true := by
  rfl

theorem kernelAPlusFocusedAuditRunnerFilesPopulatedBool_eq_true :
    kernelAPlusFocusedAuditRunnerFilesPopulatedBool = true := by
  rfl

theorem kernelAPlusAuditRunnerFilesPopulatedBool_eq_true :
    kernelAPlusAuditRunnerFilesPopulatedBool = true := by
  rfl

def kernelAPlusAuditRunnerRegistryComplete : Prop :=
  kernelAPlusFocusedAuditRunnerFiles.length = 7 /\
  kernelAPlusAggregateAuditRunnerFiles.length = 1 /\
  kernelAPlusAuditRunnerFiles.length = 8 /\
  kernelAPlusAuditRunnerFiles =
    kernelAPlusFocusedAuditRunnerFiles ++
      kernelAPlusAggregateAuditRunnerFiles /\
  kernelAPlusAuditRunnerFilesDuplicateFreeBool = true /\
  kernelAPlusAuditRunnerFilesPopulatedBool = true

theorem kernelAPlusAuditRunnerRegistryComplete_holds :
    kernelAPlusAuditRunnerRegistryComplete := by
  exact
    And.intro kernelAPlusFocusedAuditRunnerFiles_count_eq
      (And.intro kernelAPlusAggregateAuditRunnerFiles_count_eq
        (And.intro kernelAPlusAuditRunnerFiles_count_eq
          (And.intro kernelAPlusAuditRunnerFiles_decomposes
            (And.intro kernelAPlusAuditRunnerFilesDuplicateFreeBool_eq_true
              kernelAPlusAuditRunnerFilesPopulatedBool_eq_true))))

end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
