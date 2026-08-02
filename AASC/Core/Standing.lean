import AASC.Core.Reference

namespace AASC

universe u v w

namespace IncidenceSystem

/-- Data-bearing classification of one incidence locus. -/
inductive StandingStatus
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) : Type w where
  | standing (reference : X.Reference carrier scope)
  | failure (noIncidence : forall value, Not (X.incidence carrier scope value))

/-- Exact partial evaluation computes standing or failure with its evidence. -/
def classifyStanding
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) :
    R.incidenceSystem.StandingStatus carrier scope :=
  match hResult : R.referenceAt carrier scope with
  | none =>
      .failure ((R.referenceAt_eq_none_iff carrier scope).1 hResult)
  | some value =>
      .standing ⟨value, hResult⟩

theorem admissible_or_failure_of_partialReference
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) :
    R.incidenceSystem.AdmissibleAt carrier scope ∨
      (forall value,
        Not (R.incidenceSystem.incidence carrier scope value)) := by
  cases classifyStanding R carrier scope with
  | standing reference =>
      exact Or.inl ⟨reference.value, reference.isIncident⟩
  | failure noIncidence =>
      exact Or.inr noIncidence

theorem not_admissible_iff_failure
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) :
    Not (X.AdmissibleAt carrier scope) ↔
      forall value, Not (X.incidence carrier scope value) := by
  constructor
  · intro hNot value hIncidence
    exact hNot ⟨value, hIncidence⟩
  · intro hFailure hAdmissible
    rcases hAdmissible with ⟨value, hIncidence⟩
    exact hFailure value hIncidence

end IncidenceSystem

end AASC
