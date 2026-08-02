import AASC.Instances.KernelPaper.Endpoint
import AASC.Instances.KernelPaper.CurrentLocus

namespace AASC.Instances.KernelPaper.Witness

inductive ConstructionAct where
  | initial
  | reused
  | failed
deriving DecidableEq, Repr

inductive FixedScope where
  | domain
deriving DecidableEq, Repr

inductive FixedReference where
  | target
deriving DecidableEq, Repr

def references : PartialReferenceSystem ConstructionAct FixedScope FixedReference where
  referenceAt act _ :=
    match act with
    | .initial => some .target
    | .reused => some .target
    | .failed => none

abbrev X := references.incidenceSystem

abbrev LicensedStep (source target : ConstructionAct) :=
  X.Continuation (source, .domain) (target, .domain)

def reuseStep : LicensedStep .initial .reused where
  map _ := ⟨.target, rfl⟩

def returnStep : LicensedStep .reused .initial where
  map _ := ⟨.target, rfl⟩

def failedToInitialStep : LicensedStep .failed .initial where
  map failedReference := by
    cases failedReference.isIncident

def transport
    {source target : ConstructionAct}
    (edge : LicensedStep source target) :
    X.Continuation (source, .domain) (target, .domain) :=
  edge

def model : Model ConstructionAct FixedScope FixedReference where
  references := references
  target _ := .domain
  Step := LicensedStep
  transport := transport

def initialStanding : model.StandingWitness where
  act := .initial
  reference := ⟨.target, rfl⟩

def reusedStanding : model.StandingWitness where
  act := .reused
  reference := ⟨.target, rfl⟩

def failureBoundary : model.BoundaryWitness where
  act := .failed
  isFailure := rfl

def admission : model.Admission where
  standing := initialStanding
  boundary := failureBoundary

def reusePath : model.Path .initial .reused :=
  Model.Path.cons reuseStep
    (Model.Path.refl ConstructionAct.reused)

theorem reusePath_preserves_reference :
    (reusePath.mapReference initialStanding.reference).value = .target := by
  rfl

theorem no_licensed_path_to_failure :
    Not (Nonempty (model.Path .initial .failed)) := by
  exact model.admitted_instance_has_no_path_to_boundary admission

theorem reverse_step_from_failure_exists :
    Nonempty (model.Step .failed .initial) :=
  ⟨failedToInitialStep⟩

def reuseInteraction : model.Interaction .initial .reused where
  step := reuseStep
  sharedReference := .target
  sourceIncident := rfl
  destinationIncident := rfl
  sameScope := rfl
  changesAct := by decide

def returnInteraction : model.Interaction .reused .initial where
  step := returnStep
  sharedReference := .target
  sourceIncident := rfl
  destinationIncident := rfl
  sameScope := rfl
  changesAct := by decide

def initialInteractionRoute : model.GeneratedRoute .initial where
  destination := .initial
  path := {
    next := .reused
    head := reuseInteraction
    tail := Model.InteractionPath.cons returnInteraction
      (Model.InteractionPath.refl ConstructionAct.initial)
  }

def reuseInteractionRoute : model.GeneratedRoute .initial where
  destination := .reused
  path := {
    next := .reused
    head := reuseInteraction
    tail := Model.InteractionPath.refl ConstructionAct.reused
  }

def interactionRoutes : List (model.GeneratedRoute .initial) :=
  [initialInteractionRoute, reuseInteractionRoute]

def activeEndpointExhaustion : model.ActiveEndpointExhaustion .initial where
  routes := interactionRoutes
  classify := by
    intro act reference
    cases act with
    | initial =>
        exact ⟨initialInteractionRoute,
          List.Mem.head [reuseInteractionRoute], rfl⟩
    | reused =>
        exact ⟨reuseInteractionRoute,
          List.Mem.tail initialInteractionRoute
            (List.Mem.head []), rfl⟩
    | failed =>
        cases reference.isIncident

def endpointInstance :
    EndpointInstance ConstructionAct FixedScope FixedReference where
  model := model
  admission := admission
  activeEndpoints := activeEndpointExhaustion

theorem interaction_routes_nonempty : Not (interactionRoutes = []) := by
  intro hEmpty
  have hMember : initialInteractionRoute ∈ interactionRoutes :=
    List.Mem.head [reuseInteractionRoute]
  rw [hEmpty] at hMember
  nomatch hMember

theorem every_active_act_has_generated_route :
    forall act, model.Active act ->
      exists route, route ∈ interactionRoutes /\
        route.destination = act /\
        model.target .initial = model.target act := by
  intro act active
  rcases activeEndpointExhaustion.route_for_active active with
    ⟨route, hMember, hDestination⟩
  refine ⟨route, hMember, hDestination, ?_⟩
  exact hDestination ▸ route.path.toInteractionPath.sameScope

theorem every_active_reference_agrees
    (act : ConstructionAct)
    (reference : model.Incidence.ReferenceAt (model.Locus act)) :
    activeEndpointExhaustion.transportedReference
      initialStanding.reference reference = reference :=
  endpointInstance.transported_reference_agrees act reference

theorem interaction_endpoint :
    references.kernel.ReferenceUnique /\
      references.kernel.Nontrivial /\
      Not (Nonempty (model.Path .initial .failed)) /\
      Not (ConstructionAct.initial = ConstructionAct.failed) /\
      (forall act, model.Active act ->
        model.target .initial = model.target act) := by
  rcases model.endpoint admission with
    ⟨hUnique, hNontrivial, hBoundary⟩
  refine ⟨hUnique, hNontrivial, hBoundary, by decide, ?_⟩
  intro act active
  exact activeEndpointExhaustion.active_sameScope active

def generatedCurrentPopulation : List model.OccupiedLocus :=
  model.generatedCurrentPopulation interactionRoutes

theorem generatedCurrentPopulation_length :
    generatedCurrentPopulation.length = 2 := by
  rfl

theorem interactionRoute_destinations_nodup :
    model.DestinationsNodup interactionRoutes := by
  change [ConstructionAct.initial, ConstructionAct.reused].Nodup
  decide

theorem initial_current_is_populated :
    initialInteractionRoute.current ∈ generatedCurrentPopulation := by
  exact initialInteractionRoute.current_mem_generatedCurrentPopulation
    (List.Mem.head [reuseInteractionRoute])

theorem reused_current_is_populated :
    reuseInteractionRoute.current ∈ generatedCurrentPopulation := by
  exact reuseInteractionRoute.current_mem_generatedCurrentPopulation
    (List.Mem.tail initialInteractionRoute (List.Mem.head []))

theorem reused_route_reference_agrees :
    reuseInteractionRoute.destinationReference = reusedStanding.reference :=
  reuseInteractionRoute.destinationReference_eq reusedStanding.reference

theorem kernel_paper_endpoint :
    references.kernel.ReferenceUnique ∧
      references.kernel.Nontrivial ∧
      Not (Nonempty (model.Path .initial .failed)) := by
  exact model.endpoint admission

end AASC.Instances.KernelPaper.Witness
