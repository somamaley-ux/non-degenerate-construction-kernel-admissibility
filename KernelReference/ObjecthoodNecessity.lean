import KernelReference.IncidenceNecessity
import KernelReference.NecessityRealization
import KernelReference.Authorization

/-!
# Constructed kernel and authorization from original incidence semantics

This assembly takes original subjects, complete uses, dependent witnesses, and
an independently supplied incidence relation. The original regime's verdict is
constructed from qualification, and its semantic correctness is proved. No
adequacy, agreement, role package, or global soundness field is a premise.

For this regime the use is realization of an original witness. A practical
success criterion must supply its own witness relation (a one-point result type
can represent any such original predicate); existence of some experimental
outcome does not imply a separately chosen successful outcome.

The universal realization criterion tests arbitrary proposed encodings. It does
not assert that every physically existing reporter answers its subject correctly.
The manuscript defends the interpretation of the primitive semantic data as
actual determinate incidence. No observer or optional governance flag is used.
-/

namespace AASC.KernelReference.ObjecthoodNecessity

open IncidenceNecessity
open AASC.Instances.KernelPaper.Manuscript

universe u v w r s t

variable {E : Type u} {Use : Type v} {Value : Use → Type w}
variable (J : Incidence E Use Value)

/-- Complete original questions are fixed independently of their verdicts.
The identity maps concern assessment of these questions, not a claim that
physical constructions have no change of state. -/
noncomputable def canonicalRegime :
    TargetAdequacy.Regime (E × Use) (E × Use) (E × Use) where
  source := id
  destination := id
  targetOf := id
  verdict point := if assess J point.1 point.2 then .advances else .fails

theorem canonical_standing_iff_original_qualification (e : E) (q : Use) :
    (canonicalRegime J).Standing (e, q) ↔ Qualified J e q := by
  change (if assess J e q then TargetAdequacy.StepVerdict.advances else
    TargetAdequacy.StepVerdict.fails) = .advances ↔ Qualified J e q
  cases h : assess J e q
  · have absent := (assess_false_iff_no_incidence J e q).mp h
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨value, incident⟩
      exact False.elim (absent value incident)
  · simpa using (assess_true_iff J e q).mp h

theorem canonical_admission_iff_original_qualification (e : E) (q : Use) :
    (canonicalRegime J).Admissible (e, q) ↔ Qualified J e q :=
  ((canonicalRegime J).admissible_iff_standing (e, q)).trans
    (canonical_standing_iff_original_qualification J e q)

/-- The represented four-role profile has a proved original semantic realization.
This construction does not assume a separate failed locus. -/
theorem original_incidence_constructs_kernel
    (actual : ∃ e q value, J e q value) :
    DerivedKernelRoles (canonicalRegime J) ∧
    (∀ e q, (canonicalRegime J).Standing (e, q) ↔ Qualified J e q) ∧
    (∀ e q, (canonicalRegime J).Admissible (e, q) ↔ Qualified J e q) ∧
    (∃ point, (canonicalRegime J).Standing point) := by
  obtain ⟨e, q, value, incident⟩ := actual
  exact ⟨targetAdequacy_forces_kernel_roles (canonicalRegime J),
    canonical_standing_iff_original_qualification J,
    canonical_admission_iff_original_qualification J,
    (e, q), (canonical_standing_iff_original_qualification J e q).mpr ⟨value, incident⟩⟩

/-- A completely specified interpretation of candidate presentations, independent
of their output verdict. Identity information has to concern semantic subjects. -/
theorem exact_identity_recovers_original_qualification
    {Presentation : Type r} {Code : Type s}
    (original : Presentation → E) (encode : Presentation → Code)
    (identityRead : Code → E → Prop)
    (identityExact : NecessityRealization.Exact original encode
      NecessityRealization.identityProfile identityRead) :
    ∃ read, NecessityRealization.Exact original encode (Qualified J) read :=
  NecessityRealization.identity_reader_supports_every_profile
    original encode identityRead identityExact (Qualified J)

/-- Constructed semantic kernel plus the universal necessary-and-sufficient
criterion for every proposed original-observation encoding. The criterion is a
conclusion about the candidate, not a supplied adequacy certificate. -/
theorem objecthood_necessity_semantic
    (actual : ∃ e q value, J e q value)
    {Presentation : Type r} {Code : Type s} {Query : Type t}
    (original : Presentation → E) (encode : Presentation → Code)
    (profile : E → Query → Prop) :
    DerivedKernelRoles (canonicalRegime J) ∧
    (∀ e q, (canonicalRegime J).Standing (e, q) ↔ Qualified J e q) ∧
    (∃ e q, assess J e q = true) ∧
    (∀ e q, ∃! verdict, VerdictIncident J e q verdict) ∧
    (∀ left right : E,
      (∀ P : E → Prop, P left → P right) ↔ left = right) ∧
    ((∃ read, NecessityRealization.Exact original encode profile read) ↔
      NecessityRealization.PreservesOriginalProfile original encode profile) ∧
    ((¬ ∃ read, NecessityRealization.Exact original encode profile read) ↔
      NecessityRealization.FibreCollision original encode profile) := by
  have kernel := original_incidence_constructs_kernel J actual
  have work := actual_incidence_forces_canonical_work J actual
  exact ⟨kernel.1, kernel.2.1, work.1, work.2.1,
    uniform_transfer_iff_identity,
    NecessityRealization.exists_exact_reader_iff original encode profile,
    NecessityRealization.no_exact_reader_iff_fibre_collision original encode profile⟩

/-! ## Coupling the authorization cut to actual original warrant -/

section Authorization

variable {Node : Type r}

/-- Target authority is interpreted by actual original qualification. This is
an interpretation into the original incidence relation, not a label declared
sound, and carries no kernel conclusion. -/
def incidenceInterpretation (subject : Node → E) :
    _root_.KernelReference.Authorization.Interpretation Node E Use where
  statement := subject
  suppliesWarrant := Qualified J

/-- The finite cut locates an actual qualified original use. Its kernel
realization and semantic standing are then constructed by the earlier theorem. -/
theorem finite_authorization_cut_has_original_kernel
    [Finite Node]
    (G : _root_.KernelReference.Authorization.SupportGraph Node)
    (subject : Node → E) {conclusion : Node} {q : Use} {value : Value q}
    (warrant : J (subject conclusion) q value) :
    ∃ cut use witness,
      G.Ancestor cut conclusion ∧
      _root_.KernelReference.Authorization.GloballyMinimalAuthority G
        (incidenceInterpretation J subject) cut ∧
      ((G.Premise cut ∧
        (incidenceInterpretation J subject).Authority cut) ∨
        _root_.KernelReference.Authorization.IntroducingRule G
          (incidenceInterpretation J subject) cut) ∧
      J (subject cut) use witness ∧
      (canonicalRegime J).Standing (subject cut, use) ∧
      DerivedKernelRoles (canonicalRegime J) := by
  have authoritative : (incidenceInterpretation J subject).Authority conclusion :=
    ⟨q, value, warrant⟩
  obtain ⟨cut, ancestor, minimal, alternative⟩ :=
    _root_.KernelReference.Authorization.finite_authorization_cut G
      (incidenceInterpretation J subject) authoritative
  obtain ⟨use, witness, incident⟩ := minimal.1
  exact ⟨cut, use, witness, ancestor, minimal, alternative, incident,
    (canonical_standing_iff_original_qualification J (subject cut) use).mpr
      ⟨witness, incident⟩,
    targetAdequacy_forces_kernel_roles (canonicalRegime J)⟩

end Authorization

#print axioms canonical_standing_iff_original_qualification
#print axioms canonical_admission_iff_original_qualification
#print axioms original_incidence_constructs_kernel
#print axioms exact_identity_recovers_original_qualification
#print axioms objecthood_necessity_semantic
#print axioms finite_authorization_cut_has_original_kernel

end AASC.KernelReference.ObjecthoodNecessity
