import AASC.Core.ConstraintClosure

namespace AASC.RoleOccupancy

universe u v w

/-- The pointwise constraints applied before joint compatibility is tested. -/
inductive PointwiseConstraint (Role : Type u) where
  | distinct
  | occurring (role : Role)
  | eligible (role : Role)

/-- The extensional data of a role-occupancy problem. -/
structure Problem
    (Role : Type u)
    (Candidate : Type v)
    (Bridge : Type w) where
  occurs : Candidate -> Prop
  eligible : Role -> Candidate -> Prop
  compatible : Bridge -> (Role -> Candidate) -> Prop

namespace Problem

/-- Every role map is raw input; pointwise constraints filter the maps. -/
def pointwiseProfile
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :
    AASC.ConstraintProfile (PointwiseConstraint Role) (Role -> Candidate) where
  accepts constraint assignment :=
    match constraint with
    | .distinct => Function.Injective assignment
    | .occurring role => problem.occurs (assignment role)
    | .eligible role => problem.eligible role (assignment role)

/-- An actual preassignment is the literal pointwise-constraint residue. -/
def PreAssignment
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :=
  problem.pointwiseProfile.Residue (fun _ => True)

def occupant
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (assignment : problem.PreAssignment) : Role -> Candidate :=
  assignment.1

theorem occupant_injective
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (assignment : problem.PreAssignment) :
    Function.Injective assignment.1 :=
  assignment.2.2 .distinct

theorem occupant_occurs
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (assignment : problem.PreAssignment)
    (role : Role) :
    problem.occurs (assignment.1 role) :=
  assignment.2.2 (.occurring role)

theorem occupant_eligible
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (assignment : problem.PreAssignment)
    (role : Role) :
    problem.eligible role (assignment.1 role) :=
  assignment.2.2 (.eligible role)

/-- Joint compatibility bridges are a second independent constraint profile. -/
def compatibilityProfile
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :
    AASC.ConstraintProfile Bridge problem.PreAssignment where
  accepts bridge assignment :=
    problem.compatible bridge assignment.1

def Compatible
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (assignment : problem.PreAssignment) : Prop :=
  problem.compatibilityProfile.Satisfies assignment

/-- A candidate is live exactly when a compatible preassignment uses it. -/
def IsLive
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (candidate : Candidate) : Prop :=
  exists assignment : problem.PreAssignment,
    problem.Compatible assignment /\
      exists role, assignment.1 role = candidate

def LiveResidue
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :=
  {candidate : Candidate // problem.IsLive candidate}

def CoversLive
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (assignment : problem.PreAssignment) : Prop :=
  forall candidate, problem.IsLive candidate ->
    exists role, assignment.1 role = candidate

/--
Complete assignments are the literal joint-compatibility residue among
preassignments that cover the extensionally generated live residue.
-/
def CompleteAssignment
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :=
  problem.compatibilityProfile.Residue problem.CoversLive

theorem occupant_live
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (assignment : problem.PreAssignment)
    (compatible : problem.Compatible assignment)
    (role : Role) :
    problem.IsLive (assignment.1 role) :=
  ⟨assignment, compatible, role, rfl⟩

theorem complete_exactly_live
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (assignment : problem.CompleteAssignment)
    (candidate : Candidate) :
    problem.IsLive candidate <->
      exists role, assignment.1.1 role = candidate := by
  constructor
  · exact assignment.2.1 candidate
  · rintro ⟨role, occupied⟩
    rw [← occupied]
    exact problem.occupant_live assignment.1 assignment.2.2 role

theorem complete_occupant_injective
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (assignment : problem.CompleteAssignment) :
    Function.Injective assignment.1.1 :=
  occupant_injective assignment.1

theorem no_complete_of_no_compatible
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (noneCompatible : forall assignment : problem.PreAssignment,
      Not (problem.Compatible assignment)) :
    Not (Nonempty problem.CompleteAssignment) := by
  rintro ⟨assignment⟩
  exact noneCompatible assignment.1 assignment.2.2

/--
Lawful assignment actions are the existing constraint actions specialized to
compatibility coordinates and extensional live coverage.
-/
abbrev AssignmentAction
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (Move : Type u) :=
  AASC.ConstraintAction Move problem.compatibilityProfile problem.CoversLive

end Problem

end AASC.RoleOccupancy
