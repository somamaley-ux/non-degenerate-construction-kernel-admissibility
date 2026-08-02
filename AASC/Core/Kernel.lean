import AASC.Core.Incidence

namespace AASC

universe u v w

/--
The relational governance object associated with incidence data. Standing is
tied extensionally to incidence; failure is tied extensionally to the absence
of every incidence at the same carrier and scope.
-/
structure Kernel
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) where
  standing : Carrier -> Scope -> Value -> Prop
  failure : Carrier -> Scope -> Prop
  standing_iff :
    forall carrier scope value,
      standing carrier scope value <-> X.incidence carrier scope value
  failure_iff :
    forall carrier scope,
      failure carrier scope <->
        forall value, Not (X.incidence carrier scope value)

namespace Kernel

def StandingAt
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    (carrier : Carrier)
    (scope : Scope) : Prop :=
  exists value, K.standing carrier scope value

def FailureAt
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    (carrier : Carrier)
    (scope : Scope) : Prop :=
  K.failure carrier scope

def ReferenceUnique
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X) : Prop :=
  forall carrier scope left right,
    K.standing carrier scope left ->
    K.standing carrier scope right ->
    left = right

def Nontrivial
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X) : Prop :=
  exists carrier scope, K.FailureAt carrier scope

theorem admissibleAt_iff_standingAt
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    (carrier : Carrier)
    (scope : Scope) :
    X.AdmissibleAt carrier scope <-> K.StandingAt carrier scope := by
  constructor
  · rintro ⟨value, hIncidence⟩
    exact ⟨value, (K.standing_iff carrier scope value).2 hIncidence⟩
  · rintro ⟨value, hStanding⟩
    exact ⟨value, (K.standing_iff carrier scope value).1 hStanding⟩

theorem reference_unique_of_determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    (hDeterminate : X.Determinate) :
    K.ReferenceUnique := by
  intro carrier scope left right hLeft hRight
  exact hDeterminate carrier scope left right
    ((K.standing_iff carrier scope left).1 hLeft)
    ((K.standing_iff carrier scope right).1 hRight)

theorem standing_failure_disjoint
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    (carrier : Carrier)
    (scope : Scope) :
    Not (K.StandingAt carrier scope ∧ K.FailureAt carrier scope) := by
  rintro ⟨⟨value, hStanding⟩, hFailure⟩
  exact (K.failure_iff carrier scope).1 hFailure value
    ((K.standing_iff carrier scope value).1 hStanding)

end Kernel

end AASC
