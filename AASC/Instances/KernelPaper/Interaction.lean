import AASC.Core.Exhaustion
import AASC.Core.SameScope
import AASC.Instances.KernelPaper.Model

namespace AASC.Instances.KernelPaper

universe u v w

namespace Model

/-- An active act carries an actual reference at its selected locus. -/
def Active
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (act : Act) : Prop :=
  Nonempty (M.Incidence.ReferenceAt (M.Locus act))

/--
A genuine interaction is an actual licensed step whose endpoints share a
reference at the same scope and whose construction acts are distinct.
-/
structure Interaction
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (source destination : Act) where
  step : M.Step source destination
  sharedReference : Reference
  sourceIncident : M.Incidence.incidence
    source (M.target source) sharedReference
  destinationIncident : M.Incidence.incidence
    destination (M.target destination) sharedReference
  sameScope : M.target source = M.target destination
  changesAct : Not (source = destination)

def Interaction.related
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (interaction : M.Interaction source destination) :
    M.Incidence.SameScopeRelated
      (M.Locus source) (M.Locus destination) :=
  ⟨interaction.sameScope,
    ⟨interaction.sharedReference,
      interaction.sourceIncident, interaction.destinationIncident⟩⟩

def Interaction.sourceReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (interaction : M.Interaction source destination) :
    M.Incidence.ReferenceAt (M.Locus source) :=
  ⟨interaction.sharedReference, interaction.sourceIncident⟩

def Interaction.targetReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (interaction : M.Interaction source destination) :
    M.Incidence.ReferenceAt (M.Locus destination) :=
  ⟨interaction.sharedReference, interaction.destinationIncident⟩

/-- Finite paths generated only from genuine same-scope interactions. -/
inductive InteractionPath
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) : Act -> Act -> Type (max u v w) where
  | refl (act : Act) : M.InteractionPath act act
  | cons {first second third : Act}
      (head : M.Interaction first second)
      (tail : M.InteractionPath second third) :
      M.InteractionPath first third

def InteractionPath.toPath
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.InteractionPath source destination) :
    M.Path source destination :=
  match path with
  | .refl act => Path.refl act
  | .cons head tail => Path.cons head.step tail.toPath

def InteractionPath.toContinuation
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.InteractionPath source destination) :
    M.Incidence.Continuation (M.Locus source) (M.Locus destination) :=
  path.toPath.toContinuation

def InteractionPath.mapReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.InteractionPath source destination)
    (reference : M.Incidence.ReferenceAt (M.Locus source)) :
    M.Incidence.ReferenceAt (M.Locus destination) :=
  path.toContinuation.map reference

/--
Interaction transport preserves the reference value. Each interaction shares
an actual reference at both ends, and determinacy identifies the transported
reference with that shared target reference.
-/
theorem InteractionPath.mapReference_value_eq
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.InteractionPath source destination)
    (reference : M.Incidence.ReferenceAt (M.Locus source)) :
    (path.mapReference reference).value = reference.value := by
  induction path with
  | refl act => rfl
  | cons head tail inductionHypothesis =>
      have sourceEq : reference = head.sourceReference :=
        M.Incidence.reference_eq_of_determinate
          M.references.determinate reference head.sourceReference
      let afterHead := (M.transport head.step).map reference
      have targetEq : afterHead = head.targetReference :=
        M.Incidence.reference_eq_of_determinate
          M.references.determinate afterHead head.targetReference
      change (tail.mapReference afterHead).value = reference.value
      calc
        (tail.mapReference afterHead).value = afterHead.value :=
          inductionHypothesis afterHead
        _ = head.targetReference.value := congrArg (fun ref => ref.value) targetEq
        _ = head.sourceReference.value := rfl
        _ = reference.value := congrArg (fun ref => ref.value) sourceEq.symm

theorem InteractionPath.sameScope
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.InteractionPath source destination) :
    M.target source = M.target destination := by
  induction path with
  | refl _ => rfl
  | cons head tail ih => exact head.sameScope.trans ih

/-- A positive generated path contains at least one actual interaction. -/
structure PositiveInteractionPath
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (source destination : Act) where
  next : Act
  head : M.Interaction source next
  tail : M.InteractionPath next destination

def PositiveInteractionPath.toInteractionPath
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.PositiveInteractionPath source destination) :
    M.InteractionPath source destination :=
  InteractionPath.cons path.head path.tail

/-- A route is an endpoint together with a positive interaction path generating it. -/
structure GeneratedRoute
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (source : Act) where
  destination : Act
  path : M.PositiveInteractionPath source destination

/-- Coverage is fixed by the endpoint of a real generated path. -/
def generatedRouteFamily
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (source : Act) : RouteFamily (M.GeneratedRoute source) Act where
  covers route candidate := route.destination = candidate

/--
Finite coverage of active endpoints by positive interaction routes. This
transparent evidence package classifies endpoints, not every parallel path to
an endpoint; all routes and classification fields are explicit.
-/
structure ActiveEndpointExhaustion
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (source : Act) where
  routes : List (M.GeneratedRoute source)
  classify : (candidate : Act) ->
    M.Incidence.ReferenceAt (M.Locus candidate) ->
    { route : M.GeneratedRoute source //
      route ∈ routes /\ route.destination = candidate }

theorem ActiveEndpointExhaustion.exhausts
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    (exhaustion : M.ActiveEndpointExhaustion source) :
    (M.generatedRouteFamily source).Exhausts
      exhaustion.routes M.Active := by
  intro candidate active
  rcases active with ⟨reference⟩
  let classified := exhaustion.classify candidate reference
  exact ⟨classified.1, classified.2.1, classified.2.2⟩

theorem ActiveEndpointExhaustion.route_for_active
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source candidate : Act}
    (exhaustion : M.ActiveEndpointExhaustion source)
    (active : M.Active candidate) :
    exists route, route ∈ exhaustion.routes /\
      route.destination = candidate := by
  exact exhaustion.exhausts candidate active

theorem ActiveEndpointExhaustion.active_sameScope
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source candidate : Act}
    (exhaustion : M.ActiveEndpointExhaustion source)
    (active : M.Active candidate) :
    M.target source = M.target candidate := by
  rcases exhaustion.route_for_active active with ⟨route, _, rfl⟩
  exact route.path.toInteractionPath.sameScope

def ActiveEndpointExhaustion.transportedReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source candidate : Act}
    (exhaustion : M.ActiveEndpointExhaustion source)
    (sourceReference : M.Incidence.ReferenceAt (M.Locus source))
    (candidateReference : M.Incidence.ReferenceAt (M.Locus candidate)) :
    M.Incidence.ReferenceAt (M.Locus candidate) :=
  let classified := exhaustion.classify candidate candidateReference
  classified.2.2 ▸
    classified.1.path.toInteractionPath.mapReference sourceReference

theorem ActiveEndpointExhaustion.transportedReference_eq
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source candidate : Act}
    (exhaustion : M.ActiveEndpointExhaustion source)
    (sourceReference : M.Incidence.ReferenceAt (M.Locus source))
    (candidateReference : M.Incidence.ReferenceAt (M.Locus candidate)) :
    exhaustion.transportedReference sourceReference candidateReference =
      candidateReference := by
  exact M.Incidence.reference_eq_of_determinate
    M.references.determinate
    (exhaustion.transportedReference sourceReference candidateReference)
    candidateReference

theorem ActiveEndpointExhaustion.routes_nonempty_of_active
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    (exhaustion : M.ActiveEndpointExhaustion source)
    (active : M.Active source) :
    Not (exhaustion.routes = []) := by
  intro hEmpty
  have hNotExhaustive := RouteFamily.empty_not_exhaustive_of_candidate
    (M.generatedRouteFamily source) M.Active source active
  exact hNotExhaustive (hEmpty ▸ exhaustion.exhausts)

end Model

end AASC.Instances.KernelPaper
