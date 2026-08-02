namespace AASC

universe u v

/-- A candidate survives, or a concrete obstruction explains its rejection. -/
structure ConstraintSpace
    (Candidate : Type u)
    (Obstruction : Type v) where
  occurs : Candidate -> Prop
  survives : Candidate -> Prop
  obstructs : Obstruction -> Candidate -> Prop

namespace ConstraintSpace

/-- The literal subtype left after the constraints have been applied. -/
def Residue
    {Candidate : Type u}
    {Obstruction : Type v}
    (S : ConstraintSpace Candidate Obstruction) :=
  {candidate : Candidate // S.occurs candidate /\ S.survives candidate}

/--
Constraint generation by exclusion: a raw seed exists, classification is
exhaustive on occurring candidates, and occurrence excludes obstruction, so a
survivor remains.
-/
theorem residue_nonempty
    {Candidate : Type u}
    {Obstruction : Type v}
    (S : ConstraintSpace Candidate Obstruction)
    (seed : exists candidate, S.occurs candidate)
    (classifies : forall candidate, S.occurs candidate ->
      S.survives candidate \/
        exists obstruction, S.obstructs obstruction candidate)
    (excluded : forall obstruction candidate, S.occurs candidate ->
      Not (S.obstructs obstruction candidate)) :
    Nonempty S.Residue := by
  rcases seed with ⟨candidate, occurs⟩
  rcases classifies candidate occurs with survives | obstructed
  · exact ⟨⟨candidate, occurs, survives⟩⟩
  · rcases obstructed with ⟨obstruction, blocked⟩
    exact False.elim (excluded obstruction candidate occurs blocked)

theorem residue_implies_candidate
    {Candidate : Type u}
    {Obstruction : Type v}
    {S : ConstraintSpace Candidate Obstruction} :
    Nonempty S.Residue -> Nonempty Candidate := by
  rintro ⟨⟨candidate, _, _⟩⟩
  exact ⟨candidate⟩

end ConstraintSpace

/--
A transparent data package containing a survivor is exactly residue
inhabitation.  Its candidate and proof fields are explicit; this structure is
not an axiom, opaque theorem, or stored conclusion.
-/
structure ResidueCertificate
    {Candidate : Type u}
    {Obstruction : Type v}
    (S : ConstraintSpace Candidate Obstruction) where
  candidate : Candidate
  occurs : S.occurs candidate
  constrained : S.survives candidate

theorem residueCertificate_iff_residue
    {Candidate : Type u}
    {Obstruction : Type v}
    (S : ConstraintSpace Candidate Obstruction) :
    Nonempty (ResidueCertificate S) <-> Nonempty S.Residue := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨⟨certificate.candidate, certificate.occurs,
      certificate.constrained⟩⟩
  · rintro ⟨⟨candidate, occurs, constrained⟩⟩
    exact ⟨⟨candidate, occurs, constrained⟩⟩

end AASC
