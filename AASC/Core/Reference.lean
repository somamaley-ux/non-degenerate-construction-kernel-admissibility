import AASC.Core.Kernel

namespace AASC

universe u v w

namespace IncidenceSystem

/-- A carrier-scope locus, kept distinct from an incidence value. -/
abbrev Locus
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (_X : IncidenceSystem Carrier Scope Value) :=
  Carrier × Scope

/-- A reference is an incidence value together with its incidence proof. -/
structure Reference
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) where
  value : Value
  isIncident : X.incidence carrier scope value

abbrev ReferenceAt
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (locus : X.Locus) :=
  X.Reference locus.1 locus.2

theorem reference_eq_of_determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (hDeterminate : X.Determinate)
    {carrier : Carrier}
    {scope : Scope}
    (left right : X.Reference carrier scope) :
    left = right := by
  cases left with
  | mk leftValue leftIncident =>
      cases right with
      | mk rightValue rightIncident =>
          have hValue : leftValue = rightValue :=
            hDeterminate carrier scope leftValue rightValue
              leftIncident rightIncident
          cases hValue
          rfl

theorem referenceAt_subsingleton_of_determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (hDeterminate : X.Determinate)
    (locus : X.Locus)
    (left right : X.ReferenceAt locus) :
    left = right := by
  exact X.reference_eq_of_determinate hDeterminate left right

end IncidenceSystem

/-- Primitive partial reference data. Incidence is its graph, not a second field. -/
structure PartialReferenceSystem
    (Carrier : Type u)
    (Scope : Type v)
    (Value : Type w) where
  referenceAt : Carrier -> Scope -> Option Value

namespace PartialReferenceSystem

/-- The incidence relation represented by the graph of partial reference. -/
def incidenceSystem
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value) :
    IncidenceSystem Carrier Scope Value where
  incidence carrier scope value :=
    R.referenceAt carrier scope = some value

theorem determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value) :
    R.incidenceSystem.Determinate := by
  intro carrier scope left right hLeft hRight
  exact Option.some.inj (hLeft.symm.trans hRight)

theorem referenceAt_eq_none_iff
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) :
    R.referenceAt carrier scope = none <->
      forall value,
        Not (R.incidenceSystem.incidence carrier scope value) := by
  constructor
  · intro hNone value hIncidence
    cases hNone.symm.trans hIncidence
  · intro hFailure
    cases hResult : R.referenceAt carrier scope with
    | none => rfl
    | some value =>
        exact False.elim (hFailure value hResult)

theorem admissibleAt_iff_exists_result
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) :
    R.incidenceSystem.AdmissibleAt carrier scope <->
      exists value, R.referenceAt carrier scope = some value := by
  rfl

theorem nondegenerate_iff_exists_none
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value) :
    R.incidenceSystem.Nondegenerate <->
      exists carrier scope, R.referenceAt carrier scope = none := by
  constructor
  · rintro ⟨carrier, scope, hNotAdmissible⟩
    cases hResult : R.referenceAt carrier scope with
    | none => exact ⟨carrier, scope, hResult⟩
    | some value =>
        exact False.elim (hNotAdmissible ⟨value, hResult⟩)
  · rintro ⟨carrier, scope, hNone⟩
    refine ⟨carrier, scope, ?_⟩
    rintro ⟨value, hIncidence⟩
    cases hNone.symm.trans hIncidence

end PartialReferenceSystem

end AASC
