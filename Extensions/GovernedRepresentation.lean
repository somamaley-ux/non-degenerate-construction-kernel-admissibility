import AASC.Core.Incidence
import AASC.Core.Reference

/-!
# Representation-independent governed observations

The result relation is stated on actual objects and queries independently of
raw representations. Its determinacy says that two incident results at one
object/query are equal. A raw reader is arbitrary. Its particular outputs may
be used below only with witnesses that they satisfy that independently fixed
relation. Those witnesses assert result soundness; they do not assume equality
of representations, equality of outputs, or factorization through a decoder.

Global soundness is an explicit obligation about the actual original reader.
It is not derived from determinacy, and no theorem declares every raw reader
sound. For Option results, none must be a complete evaluated outcome of this
same relation. A computational none recording missing or pending evaluation is
not thereby a justified semantic result.
-/

namespace AASC.GovernedRepresentation

universe u v w r

section General

variable {Object : Type u} {Query : Type v} {Result : Type w}
variable {Raw : Type r}
variable {X : IncidenceSystem Object Query Result}

/-- Local output equality is derived from two independently incident results. -/
theorem output_eq_of_same_bearer_query
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Result)
    {left right : Raw} {leftQuery rightQuery : Query}
    (sameBearer : bearer left = bearer right)
    (sameQuery : leftQuery = rightQuery)
    (leftIncident : X.incidence (bearer left) leftQuery (observer left leftQuery))
    (rightIncident : X.incidence (bearer right) rightQuery (observer right rightQuery)) :
    observer left leftQuery = observer right rightQuery := by
  apply determinate (bearer left) leftQuery
    (observer left leftQuery) (observer right rightQuery) leftIncident
  rw [sameBearer, sameQuery]
  exact rightIncident

/-- All-query profile equality needs soundness for the two original profiles. -/
theorem profile_eq_of_same_bearer
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Result)
    {left right : Raw}
    (sameBearer : bearer left = bearer right)
    (leftSound : ∀ query, X.incidence (bearer left) query (observer left query))
    (rightSound : ∀ query, X.incidence (bearer right) query (observer right query)) :
    observer left = observer right := by
  funext query
  exact output_eq_of_same_bearer_query determinate bearer observer
    sameBearer rfl (leftSound query) (rightSound query)

/-- The uniform consequence when every actual original observer output is sound. -/
theorem all_profiles_eq_of_same_bearer
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Result)
    (originalSound : ∀ raw query,
      X.incidence (bearer raw) query (observer raw query)) :
    ∀ left right, bearer left = bearer right → observer left = observer right := by
  intro left right sameBearer
  exact profile_eq_of_same_bearer determinate bearer observer sameBearer
    (originalSound left) (originalSound right)

/-- Discordance at one object/query prevents both outputs from being justified. -/
theorem discordant_outputs_not_both_incident
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Result)
    {left right : Raw} {leftQuery rightQuery : Query}
    (sameBearer : bearer left = bearer right)
    (sameQuery : leftQuery = rightQuery)
    (different : observer left leftQuery ≠ observer right rightQuery) :
    ¬ (X.incidence (bearer left) leftQuery (observer left leftQuery) ∧
       X.incidence (bearer right) rightQuery (observer right rightQuery)) := by
  rintro ⟨leftIncident, rightIncident⟩
  exact different (output_eq_of_same_bearer_query determinate bearer observer
    sameBearer sameQuery leftIncident rightIncident)

/-- A known incident result rejects a discordant proposed result at its bearer. -/
theorem different_from_known_result_not_incident
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Result)
    {raw : Raw} {object : Object} {query : Query} {known : Result}
    (sameBearer : bearer raw = object)
    (knownIncident : X.incidence object query known)
    (different : observer raw query ≠ known) :
    ¬ X.incidence (bearer raw) query (observer raw query) := by
  intro proposedIncident
  apply different
  apply determinate object query (observer raw query) known
  · rw [← sameBearer]
    exact proposedIncident
  · exact knownIncident

end General

section CompleteOutcomeSemantics

variable {Object : Type u} {Query : Type v} {Output : Type w}

/-- The independently fixed complete outcome relation for a base result relation. -/
def completeOutcomeSystem
    (base : IncidenceSystem Object Query Output) :
    IncidenceSystem Object Query (Option Output) where
  incidence object query result :=
    match result with
    | some output => base.incidence object query output
    | none => ∀ output, ¬ base.incidence object query output

theorem completeOutcomeSystem_determinate
    (base : IncidenceSystem Object Query Output)
    (determinate : base.Determinate) :
    (completeOutcomeSystem base).Determinate := by
  intro object query left right leftIncident rightIncident
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightOutput =>
          exact False.elim (leftIncident rightOutput rightIncident)
  | some leftOutput =>
      cases right with
      | none => exact False.elim (rightIncident leftOutput leftIncident)
      | some rightOutput =>
          exact congrArg some
            (determinate object query leftOutput rightOutput leftIncident rightIncident)

theorem completeOutcome_some_incident_iff
    (base : IncidenceSystem Object Query Output)
    (object : Object) (query : Query) (output : Output) :
    (completeOutcomeSystem base).incidence object query (some output) ↔
      base.incidence object query output := by
  rfl

/-- A justified none requires absence of all base results, not an unfinished run. -/
theorem completeOutcome_none_incident_iff
    (base : IncidenceSystem Object Query Output)
    (object : Object) (query : Query) :
    (completeOutcomeSystem base).incidence object query none ↔
      ¬ base.AdmissibleAt object query := by
  constructor
  · intro absent
    rintro ⟨output, incident⟩
    exact absent output incident
  · intro notAdmissible output incident
    exact notAdmissible ⟨output, incident⟩

end CompleteOutcomeSemantics

section OptionalResults

variable {Object : Type u} {Query : Type v} {Output : Type w}
variable {Raw : Type r}
variable {X : IncidenceSystem Object Query (Option Output)}

/-- Complete evaluated optional results preserve the whole result, not only a bit. -/
theorem option_output_eq_of_same_bearer_query
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Option Output)
    {left right : Raw} {leftQuery rightQuery : Query}
    (sameBearer : bearer left = bearer right)
    (sameQuery : leftQuery = rightQuery)
    (leftIncident : X.incidence (bearer left) leftQuery (observer left leftQuery))
    (rightIncident : X.incidence (bearer right) rightQuery (observer right rightQuery)) :
    observer left leftQuery = observer right rightQuery :=
  output_eq_of_same_bearer_query determinate bearer observer
    sameBearer sameQuery leftIncident rightIncident

/-- Definedness is preserved because the full evaluated Option outcome agrees. -/
theorem option_definedness_iff_of_same_bearer_query
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Option Output)
    {left right : Raw} {leftQuery rightQuery : Query}
    (sameBearer : bearer left = bearer right)
    (sameQuery : leftQuery = rightQuery)
    (leftIncident : X.incidence (bearer left) leftQuery (observer left leftQuery))
    (rightIncident : X.incidence (bearer right) rightQuery (observer right rightQuery)) :
    (∃ output, observer left leftQuery = some output) ↔
      (∃ output, observer right rightQuery = some output) := by
  rw [option_output_eq_of_same_bearer_query determinate bearer observer
    sameBearer sameQuery leftIncident rightIncident]

theorem option_none_iff_of_same_bearer_query
    (determinate : X.Determinate)
    (bearer : Raw → Object)
    (observer : Raw → Query → Option Output)
    {left right : Raw} {leftQuery rightQuery : Query}
    (sameBearer : bearer left = bearer right)
    (sameQuery : leftQuery = rightQuery)
    (leftIncident : X.incidence (bearer left) leftQuery (observer left leftQuery))
    (rightIncident : X.incidence (bearer right) rightQuery (observer right rightQuery)) :
    (observer left leftQuery = none) ↔ (observer right rightQuery = none) := by
  rw [option_output_eq_of_same_bearer_query determinate bearer observer
    sameBearer sameQuery leftIncident rightIncident]

/-- A computational none conflicts with a known some unless it lacks soundness. -/
theorem none_not_incident_of_known_some
    (determinate : X.Determinate)
    {object : Object} {query : Query} {output : Output}
    (knownIncident : X.incidence object query (some output)) :
    ¬ X.incidence object query none := by
  intro noneIncident
  have impossible : (none : Option Output) = some output :=
    determinate object query none (some output) noneIncident knownIncident
  cases impossible

end OptionalResults

end AASC.GovernedRepresentation

#print axioms AASC.GovernedRepresentation.output_eq_of_same_bearer_query
#print axioms AASC.GovernedRepresentation.profile_eq_of_same_bearer
#print axioms AASC.GovernedRepresentation.all_profiles_eq_of_same_bearer
#print axioms AASC.GovernedRepresentation.discordant_outputs_not_both_incident
#print axioms AASC.GovernedRepresentation.different_from_known_result_not_incident
#print axioms AASC.GovernedRepresentation.option_output_eq_of_same_bearer_query
#print axioms AASC.GovernedRepresentation.option_definedness_iff_of_same_bearer_query
#print axioms AASC.GovernedRepresentation.option_none_iff_of_same_bearer_query
#print axioms AASC.GovernedRepresentation.none_not_incident_of_known_some

#print axioms AASC.GovernedRepresentation.completeOutcomeSystem_determinate
#print axioms AASC.GovernedRepresentation.completeOutcome_none_incident_iff
