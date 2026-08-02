namespace AASC

universe u v w

/-- Primitive scoped incidence data. No governance predicates are stored here. -/
structure IncidenceSystem
    (Carrier : Type u)
    (Scope : Type v)
    (Value : Type w) where
  incidence : Carrier -> Scope -> Value -> Prop

namespace IncidenceSystem

/-- An incidence has at most one value at a fixed carrier and scope. -/
def Determinate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) : Prop :=
  forall carrier scope left right,
    X.incidence carrier scope left ->
    X.incidence carrier scope right ->
    left = right

/-- At least one value is incident at a fixed carrier and scope. -/
def AdmissibleAt
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) : Prop :=
  Exists (X.incidence carrier scope)

/-- A genuine boundary exists: some carrier-scope pair has no incidence. -/
def Nondegenerate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) : Prop :=
  exists carrier scope, Not (X.AdmissibleAt carrier scope)

/-- Every carrier-scope pair has an incidence. -/
def Total
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) : Prop :=
  forall carrier scope, X.AdmissibleAt carrier scope

end IncidenceSystem

end AASC
