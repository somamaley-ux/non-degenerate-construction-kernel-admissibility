import AASC.Core.Continuation
import AASC.Core.KernelNecessity

namespace AASC.Instances.KernelPaper

universe u v w

/--
Data-bearing reconstruction of the kernel paper's fixed-domain construction
surface. `Step` carries licensed edges; `transport` realizes each edge as a map
between the corresponding reference fibers.
-/
structure Model
    (Act : Type u)
    (Scope : Type v)
    (Reference : Type w) where
  references : PartialReferenceSystem Act Scope Reference
  target : Act -> Scope
  Step : Act -> Act -> Type (max u v w)
  transport : {source destination : Act} -> Step source destination ->
    references.incidenceSystem.Continuation
      (source, target source)
      (destination, target destination)

namespace Model

abbrev Incidence
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) :=
  M.references.incidenceSystem

abbrev Locus
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (act : Act) : M.Incidence.Locus :=
  (act, M.target act)

/-- Concrete evidence that one construction act has standing reference. -/
structure StandingWitness
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) where
  act : Act
  reference : M.Incidence.ReferenceAt (M.Locus act)

/-- Concrete evidence that one construction act reaches the failure boundary. -/
structure BoundaryWitness
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) where
  act : Act
  isFailure : M.references.referenceAt act (M.target act) = none

/-- Typed admission evidence for a nonempty, nontrivial corpus instance. -/
structure Admission
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) where
  standing : M.StandingWitness
  boundary : M.BoundaryWitness

/-- Finite generated paths from the model's actual licensed edges. -/
inductive Path
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference) : Act -> Act -> Type (max u v w) where
  | refl (act : Act) : M.Path act act
  | cons {first second third : Act}
      (head : M.Step first second)
      (tail : M.Path second third) :
      M.Path first third

def Path.toContinuation
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source target : Act}
    (path : M.Path source target) :
    M.Incidence.Continuation (M.Locus source) (M.Locus target) :=
  match path with
  | .refl act => IncidenceSystem.Continuation.identity M.Incidence (M.Locus act)
  | .cons head tail =>
      IncidenceSystem.Continuation.comp tail.toContinuation (M.transport head)

def Path.mapReference
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    {source target : Act}
    (path : M.Path source target)
    (reference : M.Incidence.ReferenceAt (M.Locus source)) :
    M.Incidence.ReferenceAt (M.Locus target) :=
  path.toContinuation.map reference

theorem no_step_from_standing_to_boundary
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    (standing : M.StandingWitness)
    (boundary : M.BoundaryWitness) :
    Not (Nonempty (M.Step standing.act boundary.act)) := by
  rintro ⟨edge⟩
  let targetReference := (M.transport edge).map standing.reference
  cases boundary.isFailure.symm.trans targetReference.isIncident

theorem no_path_from_standing_to_boundary
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    {M : Model Act Scope Reference}
    (standing : M.StandingWitness)
    (boundary : M.BoundaryWitness) :
    Not (Nonempty (M.Path standing.act boundary.act)) := by
  rintro ⟨path⟩
  let targetReference := path.mapReference standing.reference
  cases boundary.isFailure.symm.trans targetReference.isIncident

/--
The first corpus endpoint. Kernel facts are structural consequences of typed
admission; the path obstruction additionally uses the model's fiber maps.
-/
theorem endpoint
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (admission : M.Admission) :
    M.references.kernel.ReferenceUnique ∧
      M.references.kernel.Nontrivial ∧
      Not (Nonempty
        (M.Path admission.standing.act admission.boundary.act)) := by
  exact ⟨M.references.kernel_referenceUnique,
    ⟨(M.references.kernel_nontrivial_iff_exists_none).2
        ⟨admission.boundary.act,
          M.target admission.boundary.act,
          admission.boundary.isFailure⟩,
      M.no_path_from_standing_to_boundary
        admission.standing admission.boundary⟩⟩

theorem admitted_instance_has_no_path_to_boundary
    {Act : Type u}
    {Scope : Type v}
    {Reference : Type w}
    (M : Model Act Scope Reference)
    (admission : M.Admission) :
    Not (Nonempty
      (M.Path admission.standing.act admission.boundary.act)) := by
  exact M.no_path_from_standing_to_boundary
    admission.standing admission.boundary

end Model

end AASC.Instances.KernelPaper
