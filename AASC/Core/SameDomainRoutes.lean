import AASC.Core.BoundaryClosure

namespace AASC.DecisionVector

universe u

/-- Equal-length verdict vectors admit a computed, sound four-way profile. -/
theorem four_profile_exhaustion
    {canonical candidate : DecisionVector}
    (sameDomain : SameDomain canonical candidate) :
    exists code,
      classifyDifference canonical candidate = some code ∧
        code.Sound canonical candidate := by
  rcases classifyDifference_complete_of_sameDomain sameDomain with
    ⟨code, result⟩
  exact ⟨code, result, classifyDifference_sound result⟩

theorem no_unclassified_same_domain_candidate
    {canonical candidate : DecisionVector}
    (sameDomain : SameDomain canonical candidate)
    (unclassified : forall code,
      classifyDifference canonical candidate = some code ->
      code.Sound canonical candidate -> False) :
    False := by
  rcases four_profile_exhaustion sameDomain with ⟨code, result, sound⟩
  exact unclassified code result sound

/--
On the extensional governance table, exact coordinate identity leaves no fifth
behavioral route beyond the four decision profiles. Further distinctions with
the same verdict table are bookkeeping-equivalent.
-/
theorem no_fifth_same_domain_governance_route
    {Point : Type u}
    {canonical candidate : AASC.GovernanceRoute Point}
    (sameDomain : AASC.DecisionTable.SameDomain canonical candidate) :
    exists code,
      classifyDifference canonical.verdicts candidate.verdicts = some code ∧
        code.Sound canonical.verdicts candidate.verdicts := by
  exact four_profile_exhaustion
    (AASC.DecisionTable.verdicts_sameDomain sameDomain)

/-- Boundary closure is advertised only with standing and failure witnesses. -/
theorem boundary_closure
    {Point : Type u}
    {canonical candidate : AASC.GovernanceRoute Point}
    (nondegenerate : NondegenerateBoundary canonical.verdicts)
    (sameDomain : AASC.DecisionTable.SameDomain canonical candidate) :
    NondegenerateBoundary canonical.verdicts ∧
      exists code,
        classifyDifference canonical.verdicts candidate.verdicts = some code ∧
          code.Sound canonical.verdicts candidate.verdicts := by
  exact ⟨nondegenerate,
    no_fifth_same_domain_governance_route sameDomain⟩

end AASC.DecisionVector
