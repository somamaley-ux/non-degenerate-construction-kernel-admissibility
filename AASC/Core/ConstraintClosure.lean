import AASC.Core.ConstraintResidue

namespace AASC

universe u v w

/-- A family of independently stated constraints on raw candidates. -/
structure ConstraintProfile (Index : Type u) (Candidate : Type v) where
  accepts : Index -> Candidate -> Prop

namespace ConstraintProfile

/-- A candidate satisfies the whole constraint profile. -/
def Satisfies
    {Index : Type u}
    {Candidate : Type v}
    (profile : ConstraintProfile Index Candidate)
    (candidate : Candidate) : Prop :=
  forall index, profile.accepts index candidate

/-- The occurring candidates left after every constraint is imposed. -/
def Residue
    {Index : Type u}
    {Candidate : Type v}
    (profile : ConstraintProfile Index Candidate)
    (occurs : Candidate -> Prop) :=
  {candidate : Candidate // occurs candidate /\ profile.Satisfies candidate}

/-- All constraints except the selected one hold. -/
def SatisfiesExcept
    {Index : Type u}
    {Candidate : Type v}
    (profile : ConstraintProfile Index Candidate)
    (removed : Index)
    (candidate : Candidate) : Prop :=
  forall index, Not (index = removed) -> profile.accepts index candidate

/--
A constraint is independently essential when deleting it reopens a concrete
occurring rival that satisfies every remaining constraint.
-/
def EssentialAt
    {Index : Type u}
    {Candidate : Type v}
    (profile : ConstraintProfile Index Candidate)
    (occurs : Candidate -> Prop)
    (removed : Index) : Prop :=
  exists candidate,
    occurs candidate /\
      profile.SatisfiesExcept removed candidate /\
      Not (profile.accepts removed candidate)

/-- Every constraint in the profile has a deletion rival. -/
def Independent
    {Index : Type u}
    {Candidate : Type v}
    (profile : ConstraintProfile Index Candidate)
    (occurs : Candidate -> Prop) : Prop :=
  forall index, profile.EssentialAt occurs index

theorem essentialAt_reopens_rival
    {Index : Type u}
    {Candidate : Type v}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    {removed : Index}
    (essential : profile.EssentialAt occurs removed) :
    exists candidate,
      occurs candidate /\
        profile.SatisfiesExcept removed candidate /\
        Not (profile.Satisfies candidate) := by
  rcases essential with
    ⟨candidate, candidateOccurs, satisfiesOthers, failsRemoved⟩
  exact ⟨candidate, candidateOccurs, satisfiesOthers,
    fun satisfies => failsRemoved (satisfies removed)⟩

end ConstraintProfile

namespace ConstraintSpace

/--
An instantiated seed is distinct from the raw generated candidate universe.
It occurs among the raw candidates, and kernel protection excludes every
obstruction from that seed. Other generated candidates may remain obstructed,
which is what makes deletion rivals possible.
-/
theorem residue_nonempty_of_instantiation
    {Candidate : Type u}
    {Obstruction : Type v}
    (space : ConstraintSpace Candidate Obstruction)
    (instantiated : Candidate -> Prop)
    (instantiated_occurs : forall candidate,
      instantiated candidate -> space.occurs candidate)
    (seed : exists candidate, instantiated candidate)
    (classifies : forall candidate, space.occurs candidate ->
      Or (space.survives candidate)
        (exists obstruction, space.obstructs obstruction candidate))
    (kernel_excludes : forall obstruction candidate,
      instantiated candidate ->
        Not (space.obstructs obstruction candidate)) :
    Nonempty space.Residue := by
  rcases seed with ⟨candidate, isInstantiated⟩
  have occurs := instantiated_occurs candidate isInstantiated
  rcases classifies candidate occurs with survives | obstructed
  · exact ⟨⟨candidate, occurs, survives⟩⟩
  · rcases obstructed with ⟨obstruction, blocked⟩
    exact False.elim
      (kernel_excludes obstruction candidate isInstantiated blocked)

end ConstraintSpace

/--
An explicit action of redescriptions on candidates. The algebraic laws make
orbit equivalence genuine, while the preservation laws make the action lawful
for the independently defined occurrence predicate and constraint profile.
-/
structure ConstraintAction
    {Index : Type u}
    (Move : Type v)
    {Candidate : Type w}
    (profile : ConstraintProfile Index Candidate)
    (occurs : Candidate -> Prop) where
  act : Move -> Candidate -> Candidate
  identity : Move
  inverse : Move -> Move
  compose : Move -> Move -> Move
  identity_act : forall candidate, act identity candidate = candidate
  compose_act : forall first second candidate,
    act (compose first second) candidate = act first (act second candidate)
  inverse_act : forall move candidate,
    act (inverse move) (act move candidate) = candidate
  occurs_iff : forall move candidate,
    occurs (act move candidate) <-> occurs candidate
  accepts_iff : forall move index candidate,
    profile.accepts index (act move candidate) <->
      profile.accepts index candidate

namespace ConstraintAction

/-- Two candidates are in the same orbit when an admitted move connects them. -/
def Orbit
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs)
    (source target : Candidate) : Prop :=
  exists move, action.act move source = target

theorem orbit_refl
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs)
    (candidate : Candidate) :
    action.Orbit candidate candidate :=
  ⟨action.identity, action.identity_act candidate⟩

theorem orbit_symm
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs)
    {source target : Candidate}
    (related : action.Orbit source target) :
    action.Orbit target source := by
  rcases related with ⟨move, moved⟩
  refine ⟨action.inverse move, ?_⟩
  rw [← moved]
  exact action.inverse_act move source

theorem orbit_trans
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs)
    {first second third : Candidate}
    (firstToSecond : action.Orbit first second)
    (secondToThird : action.Orbit second third) :
    action.Orbit first third := by
  rcases firstToSecond with ⟨firstMove, firstMoved⟩
  rcases secondToThird with ⟨secondMove, secondMoved⟩
  refine ⟨action.compose secondMove firstMove, ?_⟩
  rw [action.compose_act, firstMoved, secondMoved]

theorem satisfies_iff
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs)
    (move : Move)
    (candidate : Candidate) :
    profile.Satisfies (action.act move candidate) <->
      profile.Satisfies candidate := by
  constructor
  · intro movedSatisfies index
    exact (action.accepts_iff move index candidate).mp
      (movedSatisfies index)
  · intro satisfies index
    exact (action.accepts_iff move index candidate).mpr
      (satisfies index)

/-- A lawful action transports the literal constrained residue. -/
def actOnResidue
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs)
    (move : Move)
    (candidate : profile.Residue occurs) : profile.Residue occurs :=
  ⟨action.act move candidate.1,
    (action.occurs_iff move candidate.1).mpr candidate.2.1,
    (action.satisfies_iff move candidate.1).mpr candidate.2.2⟩

/-- The residue exists and all of its inhabitants form one lawful orbit. -/
def OneOrbit
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    (action : ConstraintAction Move profile occurs) : Prop :=
  Nonempty (profile.Residue occurs) /\
    forall first second : profile.Residue occurs,
      action.Orbit first.1 second.1

theorem oneOrbit_nonempty
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {profile : ConstraintProfile Index Candidate}
    {occurs : Candidate -> Prop}
    {action : ConstraintAction Move profile occurs}
    (closure : action.OneOrbit) :
    Nonempty (profile.Residue occurs) :=
  closure.1

end ConstraintAction

/--
The reusable closure theorem. A kernel-protected instantiated seed is first
located in the independently generated candidate universe. Exhaustive
classification and obstruction exclusion produce an inhabited residue; an
independently proved lawful action then turns uniqueness into a singleton-orbit
statement rather than a label.
-/
theorem constrained_into_existence
    {Index : Type u}
    {Move : Type v}
    {Candidate : Type w}
    {Obstruction : Type u}
    (space : ConstraintSpace Candidate Obstruction)
    (profile : ConstraintProfile Index Candidate)
    (survival_agrees : forall candidate,
      space.survives candidate <-> profile.Satisfies candidate)
    (instantiated : Candidate -> Prop)
    (instantiated_occurs : forall candidate,
      instantiated candidate -> space.occurs candidate)
    (seed : exists candidate, instantiated candidate)
    (classifies : forall candidate, space.occurs candidate ->
      Or (space.survives candidate)
        (exists obstruction, space.obstructs obstruction candidate))
    (kernel_excludes : forall obstruction candidate,
      instantiated candidate ->
        Not (space.obstructs obstruction candidate))
    (action : ConstraintAction Move profile space.occurs)
    (orbit_complete : forall
      first second : profile.Residue space.occurs,
      action.Orbit first.1 second.1) :
    action.OneOrbit := by
  have nonemptySpace : Nonempty space.Residue :=
    space.residue_nonempty_of_instantiation instantiated
      instantiated_occurs seed classifies kernel_excludes
  have nonemptyProfile : Nonempty (profile.Residue space.occurs) := by
    rcases nonemptySpace with ⟨⟨candidate, occurs, survives⟩⟩
    exact ⟨⟨candidate, occurs, (survival_agrees candidate).mp survives⟩⟩
  exact ⟨nonemptyProfile, orbit_complete⟩

end AASC
