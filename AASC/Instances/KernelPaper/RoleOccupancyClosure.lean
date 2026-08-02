import AASC.Core.RoleOccupancyGeneration
import AASC.Instances.KernelPaper.FixedRoleWitness

namespace AASC.Instances.KernelPaper.FixedRoleClosure

open AASC.RoleOccupancy

/--
The concrete fixed-role witness viewed as a role-occupancy problem. Eligibility
is equality in the actual partial-reference graph, not a role name.
-/
def problem : Problem Bool Bool Unit where
  occurs candidate := exists role,
    FixedRoleWitness.references.referenceAt candidate role = some candidate
  eligible role candidate :=
    FixedRoleWitness.references.referenceAt candidate role =
      some (FixedRoleWitness.occupancy.referenceOf role)
  compatible _ _ := True

/-- The identity assignment satisfies every literal pointwise constraint. -/
def identityPreassignment : problem.PreAssignment := by
  refine ⟨id, True.intro, ?_⟩
  intro constraint
  cases constraint with
  | distinct => exact fun _ _ equality => equality
  | occurring role => exact ⟨role, rfl⟩
  | eligible role => rfl

theorem identity_compatible : problem.Compatible identityPreassignment := by
  intro bridge
  exact True.intro

theorem every_candidate_live (candidate : Bool) : problem.IsLive candidate :=
  ⟨identityPreassignment, identity_compatible, candidate, rfl⟩

/-- Instantiation says pointwise occupation of the fixed role, nothing more. -/
def Instantiated (assignment : problem.PreAssignment) : Prop :=
  forall role, assignment.1 role = role

theorem identity_instantiated : Instantiated identityPreassignment :=
  fun _ => rfl

theorem instantiated_covers
    (assignment : problem.PreAssignment)
    (instantiated : Instantiated assignment) :
    problem.CoversLive assignment := by
  intro candidate _
  exact ⟨candidate, instantiated candidate⟩

/-- The unit bridge grammar is exhausted by its single, satisfied bridge. -/
theorem bridge_exhaustive
    (assignment : problem.PreAssignment)
    (_ : problem.CoversLive assignment) :
    Or (problem.Compatible assignment)
      (exists bridge, Not (problem.compatible bridge assignment.1)) := by
  left
  intro bridge
  exact True.intro

/-- Kernel protection excludes the literal failed-bridge proposition. -/
theorem kernel_excludes_incompatibility
    (bridge : Unit)
    (assignment : problem.PreAssignment)
    (_ : Instantiated assignment) :
    Not (Not (problem.compatible bridge assignment.1)) := by
  intro incompatible
  exact incompatible True.intro

theorem occupant_eq_role
    (assignment : problem.PreAssignment)
    (role : Bool) :
    assignment.1 role = role := by
  have eligible := Problem.occupant_eligible assignment role
  exact Option.some.inj eligible

/-- Rigid graph eligibility gives the orbit theorem; it is not assumed. -/
theorem orbit_complete
    (source target : problem.CompleteAssignment) :
    problem.LawfullyEquivalent source target := by
  refine ⟨LawfulTransformation.identity problem, ?_⟩
  intro role
  exact (occupant_eq_role target.1 role).trans
    (occupant_eq_role source.1 role).symm

/--
The corpus fixed-role witness is an inhabited single lawful occupancy orbit,
derived through the reusable kernel-constraint closure theorem.
-/
theorem oneAssignmentOrbit : problem.OneAssignmentOrbit :=
  problem.occupancy_constrained_into_existence Instantiated
    instantiated_covers
    ⟨identityPreassignment, identity_instantiated⟩
    bridge_exhaustive
    kernel_excludes_incompatibility
    orbit_complete

theorem completeAssignment_nonempty :
    Nonempty problem.CompleteAssignment :=
  oneAssignmentOrbit.1

/-- The identity coordinate change is the sole primitive needed here. -/
def primitiveSystem : PrimitiveSystem problem Unit where
  transformation _ := LawfulTransformation.identity problem

/-- Every complete assignment normalizes to the concrete identity seed. -/
theorem normalizes_to_identity
    (assignment : problem.CompleteAssignment) :
    PrimitiveSystem.GeneratedPath primitiveSystem
      assignment.1 identityPreassignment := by
  refine .step (.forward ()) ?_ (.refl identityPreassignment)
  intro role
  exact (occupant_eq_role identityPreassignment role).trans
    (occupant_eq_role assignment.1 role).symm

/-- The stronger conclusion: the single orbit is primitive-generated. -/
theorem oneGeneratedOrbit : primitiveSystem.OneGeneratedOrbit :=
  primitiveSystem.oneGeneratedOrbit_of_normalization
    completeAssignment_nonempty identityPreassignment normalizes_to_identity

theorem generatedOneAssignmentOrbit : problem.OneAssignmentOrbit :=
  PrimitiveSystem.oneAssignmentOrbit_of_generated oneGeneratedOrbit

end AASC.Instances.KernelPaper.FixedRoleClosure
