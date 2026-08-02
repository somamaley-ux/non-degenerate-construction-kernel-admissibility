import AASC.Instances.KernelPaper.Interaction

namespace AASC.Instances.KernelPaper

universe u v w

namespace Model

/-- A selected act together with an actual reference at its selected locus. -/
def OccupiedLocus
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) :=
  Sigma fun act => M.Incidence.ReferenceAt (M.Locus act)

/-- A positive interaction path constructs a reference at its destination. -/
def PositiveInteractionPath.destinationReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source destination : Act}
    (path : M.PositiveInteractionPath source destination) :
    M.Incidence.ReferenceAt (M.Locus destination) :=
  path.toInteractionPath.mapReference path.head.sourceReference

def GeneratedRoute.destinationReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    (route : M.GeneratedRoute source) :
    M.Incidence.ReferenceAt (M.Locus route.destination) :=
  route.path.destinationReference

/-- A generated route constructs its occupied current locus. -/
def GeneratedRoute.current
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    (route : M.GeneratedRoute source) : M.OccupiedLocus :=
  ⟨route.destination, route.destinationReference⟩

/-- The concrete occupied population produced by a finite route list. -/
def generatedCurrentPopulation
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    {source : Act}
    (routes : List (M.GeneratedRoute source)) : List M.OccupiedLocus :=
  routes.map GeneratedRoute.current

/-- Endpoint-level population by a listed positive generated route. -/
def PopulatedBy
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    {source : Act}
    (routes : List (M.GeneratedRoute source))
    (candidate : Act) : Prop :=
  exists route, route ∈ routes /\ route.destination = candidate

theorem GeneratedRoute.destination_active
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    (route : M.GeneratedRoute source) :
    M.Active route.destination :=
  ⟨route.destinationReference⟩

theorem GeneratedRoute.destinationReference_eq
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    (route : M.GeneratedRoute source)
    (reference : M.Incidence.ReferenceAt (M.Locus route.destination)) :
    route.destinationReference = reference :=
  M.Incidence.reference_eq_of_determinate
    M.references.determinate route.destinationReference reference

theorem populatedBy_active
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source candidate : Act}
    {routes : List (M.GeneratedRoute source)}
    (populated : M.PopulatedBy routes candidate) :
    M.Active candidate := by
  rcases populated with ⟨route, _, rfl⟩
  exact route.destination_active

theorem populatedBy_sameScope
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source candidate : Act}
    {routes : List (M.GeneratedRoute source)}
    (populated : M.PopulatedBy routes candidate) :
    M.target source = M.target candidate := by
  rcases populated with ⟨route, _, rfl⟩
  exact route.path.toInteractionPath.sameScope

theorem GeneratedRoute.current_mem_generatedCurrentPopulation
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source : Act}
    {routes : List (M.GeneratedRoute source)}
    (route : M.GeneratedRoute source)
    (member : route ∈ routes) :
    route.current ∈ M.generatedCurrentPopulation routes := by
  exact List.mem_map.mpr ⟨route, member, rfl⟩

def generatedDestinations
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    {source : Act}
    (routes : List (M.GeneratedRoute source)) : List Act :=
  routes.map GeneratedRoute.destination

/-- Destination uniqueness is optional and separate from sourcewise population. -/
def DestinationsNodup
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    {source : Act}
    (routes : List (M.GeneratedRoute source)) : Prop :=
  (M.generatedDestinations routes).Nodup

end Model

end AASC.Instances.KernelPaper
