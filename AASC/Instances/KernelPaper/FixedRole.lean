import AASC.Core.Reference
import AASC.Core.SameScope

namespace AASC.Instances.KernelPaper

universe u v w

/--
An actual fixed-role realization: every occupant is assigned a role, every role
has a reference value, and the occupant is incident to that value at that role.

This is carrier-oriented occupancy. It is distinct from `SourceIdentityAssignment`,
where occupants themselves are reference values at one fixed package.
-/
structure FixedRoleOccupancy
    {Occupant : Type u}
    {Role : Type v}
    {Reference : Type w}
    (references : PartialReferenceSystem Occupant Role Reference) where
  roleOf : Occupant -> Role
  referenceOf : Role -> Reference
  occupies : forall occupant,
    references.referenceAt occupant (roleOf occupant) =
      some (referenceOf (roleOf occupant))

namespace FixedRoleOccupancy

/-- The assigned role carries an actual incident reference. -/
def occupiedReference
    {Occupant : Type u}
    {Role : Type v}
    {Reference : Type w}
    {references : PartialReferenceSystem Occupant Role Reference}
    (occupancy : FixedRoleOccupancy references)
    (occupant : Occupant) :
    references.incidenceSystem.Reference occupant (occupancy.roleOf occupant) :=
  ⟨occupancy.referenceOf (occupancy.roleOf occupant), occupancy.occupies occupant⟩

/-- Equal roles give two occupants incidence to the same role-indexed value. -/
theorem sharesReference_of_sameRole
    {Occupant : Type u}
    {Role : Type v}
    {Reference : Type w}
    {references : PartialReferenceSystem Occupant Role Reference}
    (occupancy : FixedRoleOccupancy references)
    {left right : Occupant}
    (sameRole : occupancy.roleOf left = occupancy.roleOf right) :
    references.incidenceSystem.SharesReference
      (left, occupancy.roleOf left) (right, occupancy.roleOf right) := by
  refine ⟨occupancy.referenceOf (occupancy.roleOf left),
    occupancy.occupies left, ?_⟩
  simpa [sameRole] using occupancy.occupies right

/--
Role injectivity follows from realized common references only when the incidence
system explicitly separates carriers. Carrier separation is not kernel data.
-/
theorem roleOf_injective_of_carrierSeparating
    {Occupant : Type u}
    {Role : Type v}
    {Reference : Type w}
    {references : PartialReferenceSystem Occupant Role Reference}
    (occupancy : FixedRoleOccupancy references)
    (separating : references.incidenceSystem.CarrierSeparating) :
    Function.Injective occupancy.roleOf := by
  intro left right sameRole
  exact separating left right (occupancy.roleOf left)
    (occupancy.referenceOf (occupancy.roleOf left))
    (occupancy.occupies left)
    (by simpa [sameRole] using occupancy.occupies right)

theorem no_distinct_shared_role_of_carrierSeparating
    {Occupant : Type u}
    {Role : Type v}
    {Reference : Type w}
    {references : PartialReferenceSystem Occupant Role Reference}
    (occupancy : FixedRoleOccupancy references)
    (separating : references.incidenceSystem.CarrierSeparating)
    (left right : Occupant)
    (distinct : Not (left = right)) :
    Not (occupancy.roleOf left = occupancy.roleOf right) :=
  fun sameRole =>
    distinct (occupancy.roleOf_injective_of_carrierSeparating separating sameRole)

end FixedRoleOccupancy

end AASC.Instances.KernelPaper
