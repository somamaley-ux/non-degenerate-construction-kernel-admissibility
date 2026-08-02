import AASC.Core.Standing

namespace AASC

universe u v w

namespace IncidenceSystem

/-- A continuation is a function between the incidence fibers of two loci. -/
structure Continuation
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (source target : X.Locus) where
  map : X.ReferenceAt source -> X.ReferenceAt target

def Continuation.identity
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (locus : X.Locus) :
    X.Continuation locus locus where
  map reference := reference

def Continuation.comp
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {first second third : X.Locus}
    (later : X.Continuation second third)
    (earlier : X.Continuation first second) :
    X.Continuation first third where
  map reference := later.map (earlier.map reference)

/-- A finite compositional chain of continuation maps. -/
inductive ContinuationPath
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) :
    X.Locus -> X.Locus -> Type (max u v w) where
  | refl (locus : X.Locus) : X.ContinuationPath locus locus
  | cons {first second third : X.Locus}
      (head : X.Continuation first second)
      (tail : X.ContinuationPath second third) :
      X.ContinuationPath first third

def ContinuationPath.toContinuation
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {source target : X.Locus}
    (path : X.ContinuationPath source target) :
    X.Continuation source target :=
  match path with
  | .refl locus => Continuation.identity X locus
  | .cons head tail =>
      Continuation.comp tail.toContinuation head

def ContinuationPath.map
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {source target : X.Locus}
    (path : X.ContinuationPath source target)
    (reference : X.ReferenceAt source) :
    X.ReferenceAt target :=
  path.toContinuation.map reference

/-- Literal-value transport along a scope change for one fixed carrier. -/
def ScopeTransport
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (source target : Scope) :=
  forall value, X.incidence carrier source value ->
    X.incidence carrier target value

def ScopeTransport.toContinuation
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {carrier : Carrier}
    {source target : Scope}
    (transport : X.ScopeTransport carrier source target) :
    X.Continuation (carrier, source) (carrier, target) where
  map reference := ⟨reference.value, transport reference.value reference.isIncident⟩

def ScopeTransport.identity
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier)
    (scope : Scope) :
    X.ScopeTransport carrier scope scope :=
  fun _ hIncidence => hIncidence

def ScopeTransport.comp
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {carrier : Carrier}
    {first second third : Scope}
    (later : X.ScopeTransport carrier second third)
    (earlier : X.ScopeTransport carrier first second) :
    X.ScopeTransport carrier first third :=
  fun value hIncidence => later value (earlier value hIncidence)

theorem failure_pulls_back_along_continuation
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {source target : X.Locus}
    (continuation : X.Continuation source target)
    (targetFailure : forall value,
      Not (X.incidence target.1 target.2 value)) :
    forall value, Not (X.incidence source.1 source.2 value) := by
  intro value hSource
  let targetReference := continuation.map ⟨value, hSource⟩
  exact targetFailure targetReference.value targetReference.isIncident

theorem no_continuation_from_standing_to_failure
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {source target : X.Locus}
    (sourceReference : X.ReferenceAt source)
    (targetFailure : forall value,
      Not (X.incidence target.1 target.2 value)) :
    Not (Nonempty (X.Continuation source target)) := by
  rintro ⟨continuation⟩
  let targetReference := continuation.map sourceReference
  exact targetFailure targetReference.value targetReference.isIncident

theorem failure_pulls_back_along_path
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {source target : X.Locus}
    (path : X.ContinuationPath source target)
    (targetFailure : forall value,
      Not (X.incidence target.1 target.2 value)) :
    forall value, Not (X.incidence source.1 source.2 value) := by
  exact X.failure_pulls_back_along_continuation
    path.toContinuation targetFailure

end IncidenceSystem

end AASC
