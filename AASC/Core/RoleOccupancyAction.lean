import AASC.Core.RoleOccupancy

namespace AASC.RoleOccupancy

universe u v w

/--
A lawful change of coordinates moves roles, candidates, and compatibility
bridges together. Both directions and all inverse laws are data, so no
extensionality principle is needed to recover the reverse transformation.
-/
structure LawfulTransformation
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) where
  roleForward : Role -> Role
  roleBackward : Role -> Role
  role_left : forall role, roleBackward (roleForward role) = role
  role_right : forall role, roleForward (roleBackward role) = role
  candidateForward : Candidate -> Candidate
  candidateBackward : Candidate -> Candidate
  candidate_left : forall candidate,
    candidateBackward (candidateForward candidate) = candidate
  candidate_right : forall candidate,
    candidateForward (candidateBackward candidate) = candidate
  bridgeForward : Bridge -> Bridge
  bridgeBackward : Bridge -> Bridge
  bridge_left : forall bridge, bridgeBackward (bridgeForward bridge) = bridge
  bridge_right : forall bridge, bridgeForward (bridgeBackward bridge) = bridge
  occurs_forward_iff : forall candidate,
    problem.occurs (candidateForward candidate) <-> problem.occurs candidate
  occurs_backward_iff : forall candidate,
    problem.occurs (candidateBackward candidate) <-> problem.occurs candidate
  eligible_forward_iff : forall role candidate,
    problem.eligible (roleForward role) (candidateForward candidate) <->
      problem.eligible role candidate
  eligible_backward_iff : forall role candidate,
    problem.eligible (roleBackward role) (candidateBackward candidate) <->
      problem.eligible role candidate
  compatible_forward_iff : forall bridge assignment,
    problem.compatible (bridgeForward bridge)
      (fun role => candidateForward (assignment (roleBackward role))) <->
        problem.compatible bridge assignment
  compatible_backward_iff : forall bridge assignment,
    problem.compatible (bridgeBackward bridge)
      (fun role => candidateBackward (assignment (roleForward role))) <->
        problem.compatible bridge assignment

namespace LawfulTransformation

def identity
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :
    LawfulTransformation problem where
  roleForward := fun role => role
  roleBackward := fun role => role
  role_left := fun _ => rfl
  role_right := fun _ => rfl
  candidateForward := fun candidate => candidate
  candidateBackward := fun candidate => candidate
  candidate_left := fun _ => rfl
  candidate_right := fun _ => rfl
  bridgeForward := fun bridge => bridge
  bridgeBackward := fun bridge => bridge
  bridge_left := fun _ => rfl
  bridge_right := fun _ => rfl
  occurs_forward_iff := fun _ => Iff.rfl
  occurs_backward_iff := fun _ => Iff.rfl
  eligible_forward_iff := fun _ _ => Iff.rfl
  eligible_backward_iff := fun _ _ => Iff.rfl
  compatible_forward_iff := fun _ _ => Iff.rfl
  compatible_backward_iff := fun _ _ => Iff.rfl

def reverse
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (move : LawfulTransformation problem) :
    LawfulTransformation problem where
  roleForward := move.roleBackward
  roleBackward := move.roleForward
  role_left := move.role_right
  role_right := move.role_left
  candidateForward := move.candidateBackward
  candidateBackward := move.candidateForward
  candidate_left := move.candidate_right
  candidate_right := move.candidate_left
  bridgeForward := move.bridgeBackward
  bridgeBackward := move.bridgeForward
  bridge_left := move.bridge_right
  bridge_right := move.bridge_left
  occurs_forward_iff := move.occurs_backward_iff
  occurs_backward_iff := move.occurs_forward_iff
  eligible_forward_iff := move.eligible_backward_iff
  eligible_backward_iff := move.eligible_forward_iff
  compatible_forward_iff := move.compatible_backward_iff
  compatible_backward_iff := move.compatible_forward_iff

def compose
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (second first : LawfulTransformation problem) :
    LawfulTransformation problem where
  roleForward := fun role => second.roleForward (first.roleForward role)
  roleBackward := fun role => first.roleBackward (second.roleBackward role)
  role_left := by
    intro role
    rw [second.role_left, first.role_left]
  role_right := by
    intro role
    rw [first.role_right, second.role_right]
  candidateForward := fun candidate =>
    second.candidateForward (first.candidateForward candidate)
  candidateBackward := fun candidate =>
    first.candidateBackward (second.candidateBackward candidate)
  candidate_left := by
    intro candidate
    rw [second.candidate_left, first.candidate_left]
  candidate_right := by
    intro candidate
    rw [first.candidate_right, second.candidate_right]
  bridgeForward := fun bridge =>
    second.bridgeForward (first.bridgeForward bridge)
  bridgeBackward := fun bridge =>
    first.bridgeBackward (second.bridgeBackward bridge)
  bridge_left := by
    intro bridge
    rw [second.bridge_left, first.bridge_left]
  bridge_right := by
    intro bridge
    rw [first.bridge_right, second.bridge_right]
  occurs_forward_iff := by
    intro candidate
    exact Iff.trans (second.occurs_forward_iff _)
      (first.occurs_forward_iff _)
  occurs_backward_iff := by
    intro candidate
    exact Iff.trans (first.occurs_backward_iff _)
      (second.occurs_backward_iff _)
  eligible_forward_iff := by
    intro role candidate
    exact Iff.trans (second.eligible_forward_iff _ _)
      (first.eligible_forward_iff _ _)
  eligible_backward_iff := by
    intro role candidate
    exact Iff.trans (first.eligible_backward_iff _ _)
      (second.eligible_backward_iff _ _)
  compatible_forward_iff := by
    intro bridge assignment
    exact Iff.trans
      (second.compatible_forward_iff (first.bridgeForward bridge)
        (fun role => first.candidateForward
          (assignment (first.roleBackward role))))
      (first.compatible_forward_iff bridge assignment)
  compatible_backward_iff := by
    intro bridge assignment
    exact Iff.trans
      (first.compatible_backward_iff (second.bridgeBackward bridge)
        (fun role => second.candidateBackward
          (assignment (second.roleForward role))))
      (second.compatible_backward_iff bridge assignment)

/-- Pointwise transport of every occupied role, without function equality. -/
def Maps
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (move : LawfulTransformation problem)
    (source target : problem.PreAssignment) : Prop :=
  forall role,
    target.1 (move.roleForward role) =
      move.candidateForward (source.1 role)

theorem maps_identity
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    (assignment : problem.PreAssignment) :
    (identity problem).Maps assignment assignment :=
  fun _ => rfl

theorem maps_reverse
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    {move : LawfulTransformation problem}
    {source target : problem.PreAssignment}
    (mapped : move.Maps source target) :
    move.reverse.Maps target source := by
  intro role
  have atBackward := mapped (move.roleBackward role)
  rw [move.role_right] at atBackward
  have pulledBack := congrArg move.candidateBackward atBackward
  rw [move.candidate_left] at pulledBack
  exact pulledBack.symm

theorem maps_compose
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    {firstMove secondMove : LawfulTransformation problem}
    {first second third : problem.PreAssignment}
    (firstMapped : firstMove.Maps first second)
    (secondMapped : secondMove.Maps second third) :
    (secondMove.compose firstMove).Maps first third := by
  intro role
  change third.1 (secondMove.roleForward (firstMove.roleForward role)) =
    secondMove.candidateForward
      (firstMove.candidateForward (first.1 role))
  rw [secondMapped (firstMove.roleForward role), firstMapped role]

end LawfulTransformation

namespace Problem

/-- Complete assignments are equivalent only through an explicit lawful move. -/
def LawfullyEquivalent
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (source target : problem.CompleteAssignment) : Prop :=
  exists move : LawfulTransformation problem,
    move.Maps source.1 target.1

theorem lawfullyEquivalent_refl
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (assignment : problem.CompleteAssignment) :
    problem.LawfullyEquivalent assignment assignment :=
  ⟨LawfulTransformation.identity problem,
    LawfulTransformation.maps_identity assignment.1⟩

theorem lawfullyEquivalent_symm
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    {source target : problem.CompleteAssignment}
    (related : problem.LawfullyEquivalent source target) :
    problem.LawfullyEquivalent target source := by
  rcases related with ⟨move, mapped⟩
  exact ⟨move.reverse, LawfulTransformation.maps_reverse mapped⟩

theorem lawfullyEquivalent_trans
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {problem : Problem Role Candidate Bridge}
    {first second third : problem.CompleteAssignment}
    (firstToSecond : problem.LawfullyEquivalent first second)
    (secondToThird : problem.LawfullyEquivalent second third) :
    problem.LawfullyEquivalent first third := by
  rcases firstToSecond with ⟨firstMove, firstMapped⟩
  rcases secondToThird with ⟨secondMove, secondMapped⟩
  exact ⟨secondMove.compose firstMove,
    LawfulTransformation.maps_compose firstMapped secondMapped⟩

/-- The complete occupancy residue exists and has one lawful orbit. -/
def OneAssignmentOrbit
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) : Prop :=
  Nonempty problem.CompleteAssignment /\
    forall first second : problem.CompleteAssignment,
      problem.LawfullyEquivalent first second

/--
The canonical obstruction space for role occupancy. Occurrence is literal
live coverage, survival is literal compatibility, and an obstruction is a
specific compatibility bridge that the assignment fails.
-/
def compatibilitySpace
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge) :
    AASC.ConstraintSpace problem.PreAssignment Bridge where
  occurs := problem.CoversLive
  survives := problem.Compatible
  obstructs bridge assignment :=
    Not (problem.compatible bridge assignment.1)

/--
Existence with every mathematical burden exposed. In particular,
`instantiated_covers` cannot be replaced by a label saying that the seed is
complete, and `bridge_exhaustive` must classify an actual failed bridge.
-/
theorem completeAssignment_nonempty_of_instantiation
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (instantiated : problem.PreAssignment -> Prop)
    (instantiated_covers : forall assignment,
      instantiated assignment -> problem.CoversLive assignment)
    (seed : exists assignment, instantiated assignment)
    (bridge_exhaustive : forall assignment,
      problem.CoversLive assignment ->
        Or (problem.Compatible assignment)
          (exists bridge,
            Not (problem.compatible bridge assignment.1)))
    (kernel_excludes_incompatibility : forall bridge assignment,
      instantiated assignment ->
        Not (Not (problem.compatible bridge assignment.1))) :
    Nonempty problem.CompleteAssignment := by
  let space := problem.compatibilitySpace
  have nonemptySpace : Nonempty space.Residue :=
    space.residue_nonempty_of_instantiation instantiated
      instantiated_covers seed bridge_exhaustive
      kernel_excludes_incompatibility
  exact nonemptySpace

/--
Kernel protection produces an actual complete assignment through the
canonical bridge-obstruction space. A separately derived transformation
theorem then proves that every two complete assignments share one lawful
orbit. The final premise is deliberately visible: it is where a concrete
generator decomposition or normalization proof belongs.
-/
theorem occupancy_constrained_into_existence
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (instantiated : problem.PreAssignment -> Prop)
    (instantiated_covers : forall assignment,
      instantiated assignment -> problem.CoversLive assignment)
    (seed : exists assignment, instantiated assignment)
    (bridge_exhaustive : forall assignment,
      problem.CoversLive assignment ->
        Or (problem.Compatible assignment)
          (exists bridge,
            Not (problem.compatible bridge assignment.1)))
    (kernel_excludes_incompatibility : forall bridge assignment,
      instantiated assignment ->
        Not (Not (problem.compatible bridge assignment.1)))
    (orbit_complete : forall
      first second : problem.CompleteAssignment,
      problem.LawfullyEquivalent first second) :
    problem.OneAssignmentOrbit := by
  have nonemptyComplete : Nonempty problem.CompleteAssignment :=
    problem.completeAssignment_nonempty_of_instantiation instantiated
      instantiated_covers seed bridge_exhaustive
      kernel_excludes_incompatibility
  exact ⟨nonemptyComplete, orbit_complete⟩

end Problem

end AASC.RoleOccupancy
