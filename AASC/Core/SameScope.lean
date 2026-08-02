import AASC.Core.Continuation

namespace AASC

universe u v w

namespace IncidenceSystem

/-- Two loci share an actual reference value. -/
def SharesReference
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (left right : X.Locus) : Prop :=
  exists value,
    X.incidence left.1 left.2 value ∧
    X.incidence right.1 right.2 value

theorem sharesReference_symm
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {left right : X.Locus}
    (h : X.SharesReference left right) :
    X.SharesReference right left := by
  rcases h with ⟨value, hLeft, hRight⟩
  exact ⟨value, hRight, hLeft⟩

theorem sharesReference_trans_of_determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (hDeterminate : X.Determinate)
    {first second third : X.Locus}
    (hFirst : X.SharesReference first second)
    (hSecond : X.SharesReference second third) :
    X.SharesReference first third := by
  rcases hFirst with ⟨leftValue, hFirstIncidence, hSecondLeft⟩
  rcases hSecond with ⟨rightValue, hSecondRight, hThirdIncidence⟩
  have hValue : leftValue = rightValue :=
    hDeterminate second.1 second.2 leftValue rightValue
      hSecondLeft hSecondRight
  cases hValue
  exact ⟨leftValue, hFirstIncidence, hThirdIncidence⟩

def SameScopeRelated
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (left right : X.Locus) : Prop :=
  left.2 = right.2 ∧ X.SharesReference left right

/-- Shared references separate carriers at a fixed scope. -/
def CarrierSeparating
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) : Prop :=
  forall left right scope value,
    X.incidence left scope value ->
    X.incidence right scope value ->
    left = right

theorem carrier_eq_of_sameScopeRelated
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (hSeparating : X.CarrierSeparating)
    {left right : X.Locus}
    (hRelated : X.SameScopeRelated left right) :
    left.1 = right.1 := by
  rcases hRelated with ⟨hScope, value, hLeft, hRight⟩
  exact hSeparating left.1 right.1 right.2 value
    (hScope ▸ hLeft) hRight

theorem sameScopeRelated_trans_of_determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (hDeterminate : X.Determinate)
    {first second third : X.Locus}
    (hFirst : X.SameScopeRelated first second)
    (hSecond : X.SameScopeRelated second third) :
    X.SameScopeRelated first third := by
  exact ⟨hFirst.1.trans hSecond.1,
    X.sharesReference_trans_of_determinate hDeterminate hFirst.2 hSecond.2⟩

end IncidenceSystem

end AASC
