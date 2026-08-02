import AASC.Core.RoleOccupancyAction

namespace AASC.RoleOccupancy

universe u v w x

/-- Independently declared primitive lawful transformations. -/
structure PrimitiveSystem
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    (problem : Problem Role Candidate Bridge)
    (Generator : Type x) where
  transformation : Generator -> LawfulTransformation problem

/-- Every primitive may be used in either mathematically proved direction. -/
inductive SignedGenerator (Generator : Type x) where
  | forward (generator : Generator)
  | backward (generator : Generator)

namespace SignedGenerator

def inverse {Generator : Type x} :
    SignedGenerator Generator -> SignedGenerator Generator
  | .forward generator => .backward generator
  | .backward generator => .forward generator

end SignedGenerator

namespace PrimitiveSystem

def letterTransformation
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator) :
    SignedGenerator Generator -> LawfulTransformation problem
  | .forward generator => system.transformation generator
  | .backward generator => (system.transformation generator).reverse

def LetterMaps
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator)
    (letter : SignedGenerator Generator)
    (source target : problem.PreAssignment) : Prop :=
  (system.letterTransformation letter).Maps source target

theorem letterMaps_inverse
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {letter : SignedGenerator Generator}
    {source target : problem.PreAssignment}
    (mapped : system.LetterMaps letter source target) :
    system.LetterMaps letter.inverse target source := by
  cases letter with
  | forward generator =>
      exact LawfulTransformation.maps_reverse mapped
  | backward generator =>
      exact LawfulTransformation.maps_reverse mapped

/-- A generated path is a finite chain of actual primitive transformations. -/
inductive GeneratedPath
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator) :
    problem.PreAssignment -> problem.PreAssignment -> Prop where
  | refl (assignment : problem.PreAssignment) :
      GeneratedPath system assignment assignment
  | step
      {source middle target : problem.PreAssignment}
      (letter : SignedGenerator Generator)
      (mapped : system.LetterMaps letter source middle)
      (tail : GeneratedPath system middle target) :
      GeneratedPath system source target

namespace GeneratedPath

theorem trans
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {first second third : problem.PreAssignment}
    (firstToSecond : GeneratedPath system first second)
    (secondToThird : GeneratedPath system second third) :
    GeneratedPath system first third := by
  induction firstToSecond with
  | refl assignment => exact secondToThird
  | step letter mapped tail inductionHypothesis =>
      exact .step letter mapped (inductionHypothesis secondToThird)

theorem symm
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {source target : problem.PreAssignment}
    (path : GeneratedPath system source target) :
    GeneratedPath system target source := by
  induction path with
  | refl assignment => exact .refl assignment
  | step letter mapped tail inductionHypothesis =>
      exact inductionHypothesis.trans
        (.step letter.inverse
          (PrimitiveSystem.letterMaps_inverse mapped) (.refl _))

/-- Forgetting the primitive derivation yields one explicit lawful move. -/
theorem toLawfulTransformation
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {source target : problem.PreAssignment}
    (path : GeneratedPath system source target) :
    exists move : LawfulTransformation problem, move.Maps source target := by
  induction path with
  | refl assignment =>
      exact ⟨LawfulTransformation.identity problem,
        LawfulTransformation.maps_identity assignment⟩
  | step letter mapped tail inductionHypothesis =>
      rcases inductionHypothesis with ⟨tailMove, tailMapped⟩
      exact ⟨tailMove.compose (system.letterTransformation letter),
        LawfulTransformation.maps_compose mapped tailMapped⟩

end GeneratedPath

def GeneratedEquivalent
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator)
    (source target : problem.CompleteAssignment) : Prop :=
  GeneratedPath system source.1 target.1

theorem generatedEquivalent_refl
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator)
    (assignment : problem.CompleteAssignment) :
    system.GeneratedEquivalent assignment assignment :=
  .refl assignment.1

theorem generatedEquivalent_symm
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {source target : problem.CompleteAssignment}
    (related : system.GeneratedEquivalent source target) :
    system.GeneratedEquivalent target source :=
  related.symm

theorem generatedEquivalent_trans
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {first second third : problem.CompleteAssignment}
    (firstToSecond : system.GeneratedEquivalent first second)
    (secondToThird : system.GeneratedEquivalent second third) :
    system.GeneratedEquivalent first third :=
  firstToSecond.trans secondToThird

theorem generated_implies_lawful
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    {source target : problem.CompleteAssignment}
    (generated : system.GeneratedEquivalent source target) :
    problem.LawfullyEquivalent source target :=
  generated.toLawfulTransformation

def OneGeneratedOrbit
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator) : Prop :=
  Nonempty problem.CompleteAssignment /\
    forall first second : problem.CompleteAssignment,
      system.GeneratedEquivalent first second

/-- Normalization to one fixed preassignment derives pairwise generated orbit closure. -/
theorem oneGeneratedOrbit_of_normalization
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    (system : PrimitiveSystem problem Generator)
    (nonempty : Nonempty problem.CompleteAssignment)
    (anchor : problem.PreAssignment)
    (normalizes : forall assignment : problem.CompleteAssignment,
      GeneratedPath system assignment.1 anchor) :
    system.OneGeneratedOrbit := by
  refine ⟨nonempty, ?_⟩
  intro first second
  exact (normalizes first).trans (normalizes second).symm

theorem oneAssignmentOrbit_of_generated
    {Role : Type u}
    {Candidate : Type v}
    {Bridge : Type w}
    {Generator : Type x}
    {problem : Problem Role Candidate Bridge}
    {system : PrimitiveSystem problem Generator}
    (generated : system.OneGeneratedOrbit) :
    problem.OneAssignmentOrbit := by
  exact ⟨generated.1, fun first second =>
    generated_implies_lawful (generated.2 first second)⟩

end PrimitiveSystem

end AASC.RoleOccupancy
