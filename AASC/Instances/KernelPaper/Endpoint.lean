import AASC.Instances.KernelPaper.Interaction

namespace AASC.Instances.KernelPaper

universe u v w

/--
An endpoint instance packages only mathematical input data: a model, admission
witnesses, and finite active-endpoint coverage by positive interaction routes.
Kernel and endpoint consequences remain theorems rather than fields.
-/
structure EndpointInstance
    (Act : Type u)
    (Scope : Type v)
    (Reference : Type w) where
  model : Model Act Scope Reference
  admission : model.Admission
  activeEndpoints : model.ActiveEndpointExhaustion admission.standing.act

namespace EndpointInstance

theorem endpoints_distinct
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (E : EndpointInstance Act Scope Reference) :
    Not (E.admission.standing.act =
      E.admission.boundary.act) := by
  intro hEqual
  apply E.model.no_path_from_standing_to_boundary
    E.admission.standing E.admission.boundary
  rw [hEqual]
  exact ⟨Model.Path.refl E.admission.boundary.act⟩

theorem active_generated_sameScope
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (E : EndpointInstance Act Scope Reference)
    (candidate : Act)
    (active : E.model.Active candidate) :
    exists route, route ∈ E.activeEndpoints.routes /\
      route.destination = candidate /\
      E.model.target E.admission.standing.act =
        E.model.target candidate := by
  rcases E.activeEndpoints.route_for_active active with
    ⟨route, hMember, hDestination⟩
  refine ⟨route, hMember, hDestination, ?_⟩
  exact hDestination ▸ route.path.toInteractionPath.sameScope

theorem transported_reference_agrees
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (E : EndpointInstance Act Scope Reference)
    (candidate : Act)
    (candidateReference : E.model.Incidence.ReferenceAt
      (E.model.Locus candidate)) :
    E.activeEndpoints.transportedReference
      E.admission.standing.reference candidateReference =
        candidateReference :=
  E.activeEndpoints.transportedReference_eq
    E.admission.standing.reference candidateReference

/--
The interaction endpoint: canonical kernel facts and boundary obstruction from
admission, plus endpoint distinction and the same-scope consequence of the
explicit active-endpoint certificate.
-/
theorem endpoint
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (E : EndpointInstance Act Scope Reference) :
    E.model.references.kernel.ReferenceUnique /\
      E.model.references.kernel.Nontrivial /\
      Not (Nonempty (E.model.Path
        E.admission.standing.act
        E.admission.boundary.act)) /\
      Not (E.admission.standing.act = E.admission.boundary.act) /\
      (forall candidate, E.model.Active candidate ->
        E.model.target E.admission.standing.act =
          E.model.target candidate) := by
  rcases E.model.endpoint E.admission with
    ⟨hUnique, hNontrivial, hBoundary⟩
  refine ⟨hUnique, hNontrivial, hBoundary, E.endpoints_distinct, ?_⟩
  intro candidate active
  exact E.activeEndpoints.active_sameScope active

end EndpointInstance

end AASC.Instances.KernelPaper
