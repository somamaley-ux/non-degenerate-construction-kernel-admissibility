import AASC.Instances.KernelPaper.FixedRole

namespace AASC.Instances.KernelPaper.FixedRoleWitness

/-- Each occupant is the reference value at every role. -/
def references : PartialReferenceSystem Bool Bool Bool where
  referenceAt occupant _ := some occupant

/-- Carrier separation is proved from the reference graph, not stored as a field. -/
theorem carrierSeparating :
    references.incidenceSystem.CarrierSeparating := by
  intro left right _ value leftIncident rightIncident
  exact Option.some.inj (leftIncident.trans rightIncident.symm)

/-- A concrete role realization with no injected uniqueness field. -/
def occupancy : FixedRoleOccupancy references where
  roleOf := id
  referenceOf := id
  occupies _ := rfl

theorem roleOf_injective : Function.Injective occupancy.roleOf :=
  occupancy.roleOf_injective_of_carrierSeparating carrierSeparating

theorem occupants_with_same_role_are_equal
    (left right : Bool)
    (sameRole : occupancy.roleOf left = occupancy.roleOf right) :
    left = right :=
  roleOf_injective sameRole

end AASC.Instances.KernelPaper.FixedRoleWitness
