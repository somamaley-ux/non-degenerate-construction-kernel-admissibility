import AASC.Instances.KernelPaper.Closure

/-!
This checks the literal scope of the published StatusInterface API.
It is NOT a counterexample to a linked, faithful, same-object neutral interface:
the published API contains no such link or neutrality predicate.
-/
namespace KernelUniversalAudit.InterfaceBoundary

open AASC.Instances.KernelPaper.ManuscriptClosure

inductive Code where
  | admitted | rejected | third
  deriving DecidableEq

/-- All three codes actually occur at evaluated steps. -/
def rawInterface : StatusInterface Code Code where
  evaluated := fun _ => True
  status := id
  admittedStatus := .admitted
  rejectedStatus := .rejected
  licensed := fun s _ => s = .admitted
  reportable := fun s => s ≠ .rejected
  reusable := fun s _ => s = .admitted

theorem every_code_occurs (s : Code) :
    ∃ step, rawInterface.evaluated step ∧ rawInterface.status step = s :=
  ⟨s, trivial, rfl⟩

theorem third_not_equivalent_admitted :
    ¬ StatusEquivalent rawInterface Code.third Code.admitted := by
  intro h
  have bad := (h.1 Code.admitted).2 rfl
  cases bad

theorem third_not_equivalent_rejected :
    ¬ StatusEquivalent rawInterface Code.third Code.rejected := by
  intro h
  have thirdReportable : rawInterface.reportable Code.third := by
    intro impossible
    cases impossible
  exact ((h.2.1).1 thirdReportable) rfl

theorem admitted_not_equivalent_rejected :
    ¬ StatusEquivalent rawInterface Code.admitted Code.rejected := by
  intro h
  have bad := (h.1 Code.admitted).1 rfl
  cases bad

/-- The published case split holds even with three distinct effect profiles. -/
theorem published_split_compatible_with_three_profiles :
    (StatusGovernanceEffective rawInterface Code.third ∨
      StatusInert rawInterface Code.third) ∧
    ¬ StatusEquivalent rawInterface Code.third Code.admitted ∧
    ¬ StatusEquivalent rawInterface Code.third Code.rejected ∧
    ¬ StatusEquivalent rawInterface Code.admitted Code.rejected :=
  ⟨no_intermediate_status rawInterface Code.third,
    third_not_equivalent_admitted, third_not_equivalent_rejected,
    admitted_not_equivalent_rejected⟩

/-- Two-profile exhaustion is false for the unrestricted published structure. -/
theorem unrestricted_two_profile_exhaustion_false :
    ¬ (∀ (I : StatusInterface Code Code) (s : Code),
      StatusEquivalent I s I.admittedStatus ∨
      StatusEquivalent I s I.rejectedStatus) := by
  intro universal
  rcases universal rawInterface Code.third with admitted | rejected
  · exact third_not_equivalent_admitted admitted
  · exact third_not_equivalent_rejected rejected

#print axioms published_split_compatible_with_three_profiles
#print axioms unrestricted_two_profile_exhaustion_false

end KernelUniversalAudit.InterfaceBoundary
