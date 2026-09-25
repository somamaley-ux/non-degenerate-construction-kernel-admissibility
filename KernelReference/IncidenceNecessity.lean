import KernelReference.Foundation
import Mathlib.Logic.ExistsUnique

/-!
# Necessity from independently specified incidence

The primitive data are a semantic original-subject type `E`, a use type, a
dependent result type, and an arbitrary incidence relation `J`. They contain
no adequacy clauses, verdict field, agreement equation, or reporter-soundness
certificate. A positive incidence supplies positive qualification. Classical
logic supplies a complete semantic qualification verdict even when no observer
can compute it. Result values may remain multiple.

Identity probes and the universal transfer theorem concern semantic identity,
not spelling or a choice of physical coordinates. An arbitrary proposed reader
can fail the independently specified incidence tests. Such a failure does not
change the original incidence. Concrete physical interpretations must identify
their actual original subjects, uses, and relation; the results do not infer a
physical law or validate a reporter merely from its existence.
-/

namespace AASC.KernelReference.IncidenceNecessity

universe u v w x

variable {E : Type u} {Use : Type v} {Value : Use → Type w}

/-- Raw incidence, independently specified before any proposed assessment. -/
abbrev Incidence (E : Type u) (Use : Type v) (Value : Use → Type w) :=
  (e : E) → (q : Use) → Value q → Prop

variable (J : Incidence E Use Value)

def Qualified (e : E) (q : Use) : Prop := ∃ value, J e q value

/-- A settled refusal excludes every value at the original subject and use.
It is stronger than silence or failure to compute an answer. -/
def VerdictIncident (e : E) (q : Use) : Bool → Prop
  | true => Qualified J e q
  | false => ∀ value, ¬ J e q value

/-- Constructive positive qualification: an actual incidence supplies its own
witness. Neither excluded middle nor a failed locus is needed. -/
theorem actual_incidence_qualifies {e : E} {q : Use} {value : Value q}
    (actual : J e q value) : Qualified J e q := ⟨value, actual⟩

/-- The incompatibility of an actual qualified incidence and a complete refusal
is constructive; Boolean completion is a separate classical existence result. -/
theorem qualification_excludes_refusal {e : E} {q : Use}
    (actual : Qualified J e q) : ¬ VerdictIncident J e q false := by
  obtain ⟨value, hv⟩ := actual
  intro absent
  exact absent value hv
/-- Classical complete semantic assessment. This is not asserted to be executable;
its existence does not derive excluded middle or assert deterministic dynamics. -/
noncomputable def assess (e : E) (q : Use) : Bool := by
  classical
  exact decide (Qualified J e q)

theorem assess_true_iff (e : E) (q : Use) :
    assess J e q = true ↔ Qualified J e q := by
  classical
  exact decide_eq_true_iff

theorem assess_false_iff_no_incidence (e : E) (q : Use) :
    assess J e q = false ↔ ∀ value, ¬ J e q value := by
  classical
  simp only [assess, decide_eq_false_iff_not, Qualified, not_exists]

theorem actual_incidence_gives_positive {e : E} {q : Use} {value : Value q}
    (actual : J e q value) : assess J e q = true :=
  (assess_true_iff J e q).mpr ⟨value, actual⟩

theorem verdict_incident_unique {e : E} {q : Use} {left right : Bool}
    (hl : VerdictIncident J e q left) (hr : VerdictIncident J e q right) :
    left = right := by
  cases left <;> cases right
  · rfl
  · obtain ⟨value, hv⟩ := hr
    exact False.elim (hl value hv)
  · obtain ⟨value, hv⟩ := hl
    exact False.elim (hr value hv)
  · rfl

theorem canonical_verdict_incident (e : E) (q : Use) :
    VerdictIncident J e q (assess J e q) := by
  cases hb : assess J e q
  · exact (assess_false_iff_no_incidence J e q).mp hb
  · exact (assess_true_iff J e q).mp hb

/-- Eligibility has a unique complete outcome without any assumption that
the independently supplied result relation is single-valued. -/
theorem complete_assessment_exists_unique (e : E) (q : Use) :
    ∃! verdict, VerdictIncident J e q verdict := by
  exact ⟨assess J e q, canonical_verdict_incident J e q,
    fun verdict hv => verdict_incident_unique J hv (canonical_verdict_incident J e q)⟩

theorem verdict_incident_iff_canonical (e : E) (q : Use) (verdict : Bool) :
    VerdictIncident J e q verdict ↔ verdict = assess J e q := by
  constructor
  · intro h
    exact verdict_incident_unique J h (canonical_verdict_incident J e q)
  · rintro rfl
    exact canonical_verdict_incident J e q

/-- A specific value claim is tested at its original ground; qualification
does not select one value from a potentially multivalued result relation. -/
noncomputable def canonicalAnswer (e : E) (q : Use) (value : Value q) : Bool := by
  classical
  exact decide (J e q value)

theorem canonical_answer_true_iff (e : E) (q : Use) (value : Value q) :
    canonicalAnswer J e q value = true ↔ J e q value := by
  classical
  exact decide_eq_true_iff

theorem canonical_answer_false_iff (e : E) (q : Use) (value : Value q) :
    canonicalAnswer J e q value = false ↔ ¬ J e q value := by
  classical
  exact decide_eq_false_iff_not

/-! ## Actual readers, tested against the original relation -/

abbrev AnswerReader := (e : E) → (q : Use) → Value q → Bool

def SoundAt (reader : AnswerReader (E := E) (Value := Value)) (e : E) (q : Use) : Prop :=
  ∀ value, reader e q value = true → J e q value

def CompleteAt (reader : AnswerReader (E := E) (Value := Value)) (e : E) (q : Use) : Prop :=
  ∀ value, J e q value → reader e q value = true

def ExactAt (reader : AnswerReader (E := E) (Value := Value)) (e : E) (q : Use) : Prop :=
  ∀ value, reader e q value = true ↔ J e q value

def SurplusAt (reader : AnswerReader (E := E) (Value := Value)) (e : E) (q : Use) : Prop :=
  ∃ value, reader e q value = true ∧ ¬ J e q value

def OmissionAt (reader : AnswerReader (E := E) (Value := Value)) (e : E) (q : Use) : Prop :=
  ∃ value, J e q value ∧ reader e q value ≠ true

theorem sound_iff_no_surplus (reader : AnswerReader (E := E) (Value := Value))
    (e : E) (q : Use) : SoundAt J reader e q ↔ ¬ SurplusAt J reader e q := by
  classical
  constructor
  · rintro hs ⟨value, read, absent⟩
    exact absent (hs value read)
  · intro noSurplus value read
    by_cases present : J e q value
    · exact present
    · exact False.elim (noSurplus ⟨value, read, present⟩)

theorem complete_iff_no_omission (reader : AnswerReader (E := E) (Value := Value))
    (e : E) (q : Use) : CompleteAt J reader e q ↔ ¬ OmissionAt J reader e q := by
  classical
  constructor
  · rintro hc ⟨value, actual, absent⟩
    exact absent (hc value actual)
  · intro noOmission value actual
    by_cases present : reader e q value = true
    · exact present
    · exact False.elim (noOmission ⟨value, actual, present⟩)

/-- The exact failure criterion uses independently witnessed surplus or
omission, rather than a certificate field asserting global correctness. -/
theorem exact_iff_no_defects (reader : AnswerReader (E := E) (Value := Value))
    (e : E) (q : Use) :
    ExactAt J reader e q ↔ ¬ SurplusAt J reader e q ∧ ¬ OmissionAt J reader e q := by
  constructor
  · intro he
    exact ⟨(sound_iff_no_surplus J reader e q).mp (fun value => (he value).mp),
      (complete_iff_no_omission J reader e q).mp (fun value => (he value).mpr)⟩
  · rintro ⟨hs, hc⟩ value
    exact ⟨(sound_iff_no_surplus J reader e q).mpr hs value,
      (complete_iff_no_omission J reader e q).mpr hc value⟩

/-- Failure of exactness has an original-ground surplus or omission witness.
The witness extraction uses classical logic and is not a search algorithm. -/
theorem nonexact_iff_witnessed_defect (reader : AnswerReader (E := E) (Value := Value))
    (e : E) (q : Use) :
    ¬ ExactAt J reader e q ↔ SurplusAt J reader e q ∨ OmissionAt J reader e q := by
  classical
  constructor
  · intro notExact
    by_cases surplus : SurplusAt J reader e q
    · exact Or.inl surplus
    · by_cases omission : OmissionAt J reader e q
      · exact Or.inr omission
      · exact False.elim (notExact ((exact_iff_no_defects J reader e q).mpr ⟨surplus, omission⟩))
  · rintro (surplus | omission) exactReader
    · exact ((exact_iff_no_defects J reader e q).mp exactReader).1 surplus
    · exact ((exact_iff_no_defects J reader e q).mp exactReader).2 omission
theorem canonical_reader_exact (e : E) (q : Use) :
    ExactAt J (canonicalAnswer J) e q := canonical_answer_true_iff J e q

/-! ## Original identity and limits on transferring grounds -/

section Identity

variable {Claim : Type x}

/-- This is a theorem about all possible original-ground predicates, not an
assumption that a particular domain predicate separates every pair of claims. -/
theorem uniform_transfer_iff_identity (original replacement : Claim) :
    (∀ P : Claim → Prop, P original → P replacement) ↔ original = replacement := by
  constructor
  · intro transfer
    exact transfer (fun claim => original = claim) rfl
  · rintro rfl P hp
    exact hp

theorem different_original_has_separating_ground {original replacement : Claim}
    (different : original ≠ replacement) :
    ∃ P : Claim → Prop, P original ∧ ¬ P replacement :=
  ⟨fun claim => original = claim, rfl, different⟩

theorem no_uniform_transfer_to_different_original {original replacement : Claim}
    (different : original ≠ replacement) :
    ¬ (∀ P : Claim → Prop, P original → P replacement) :=
  fun transfer => different ((uniform_transfer_iff_identity original replacement).mp transfer)

/-- Semantic equality questions already separate different original subjects.
Their truth does not require a physical observer or decidable equality. -/
theorem equality_probes_separate (left right : Claim) :
    (∀ probe, (left = probe ↔ right = probe)) ↔ left = right := by
  constructor
  · intro probes
    exact (probes left).mp rfl |>.symm
  · rintro rfl probe
    rfl

end Identity

/-- Retention of the original relation is constructive and prior to any
classical Boolean representation of its qualification. -/
theorem identical_original_preserves_incidence {original replacement : E}
    (retained : original = replacement) (q : Use) (value : Value q) :
    J original q value ↔ J replacement q value := by
  cases retained
  rfl
theorem identical_original_retains_assessment {original replacement : E}
    (retained : original = replacement) (q : Use) :
    assess J original q = assess J replacement q := congrArg (fun e => assess J e q) retained

/-- A success under different data cannot change the original negative
qualification while retaining the original semantic subject and use. -/
theorem changed_qualification_forces_distinct_original {original replacement : E} {q : Use}
    (originalFailed : ¬ Qualified J original q)
    (replacementQualified : Qualified J replacement q) : original ≠ replacement := by
  rintro rfl
  exact originalFailed replacementQualified

theorem same_original_cannot_have_contrary_complete_verdicts {original replacement : E}
    (retained : original = replacement) {q : Use} {left right : Bool}
    (hl : VerdictIncident J original q left)
    (hr : VerdictIncident J replacement q right) : left = right := by
  subst replacement
  exact verdict_incident_unique J hl hr

section OriginalRecords

variable {Occurrence : Type u} {Material : Type v} {Conditions : Type w} {Target : Type x}
    {Use' : Type} {Value' : Use' → Type}

/-- The original identity coordinates are fixed without using a verdict. The
result concerns retention of those data, not the recoverability of evidence or
an arrow of time. Any identity-preserving history extension retains this answer. -/
theorem retained_original_record_preserves_assessment
    (J' : Incidence (Foundation.OriginalPerformance Occurrence Material Conditions Target)
      Use' Value')
    {original later : Foundation.OriginalPerformance Occurrence Material Conditions Target}
    (retained : Foundation.OriginalPerformance.RetainsOriginal original later) (q : Use') :
    assess J' original q = assess J' later q :=
  identical_original_retains_assessment J'
    ((Foundation.OriginalPerformance.retainsOriginal_iff_eq original later).mp retained) q

/-- Original-record retention preserves the actual incidence constructively.
No historical memory or temporal order is among the premises. -/
theorem retained_original_record_preserves_incidence
    (J' : Incidence (Foundation.OriginalPerformance Occurrence Material Conditions Target)
      Use' Value')
    {original later : Foundation.OriginalPerformance Occurrence Material Conditions Target}
    (retained : Foundation.OriginalPerformance.RetainsOriginal original later)
    (q : Use') (value : Value' q) : J' original q value ↔ J' later q value :=
  identical_original_preserves_incidence J'
    ((Foundation.OriginalPerformance.retainsOriginal_iff_eq original later).mp retained) q value
end OriginalRecords

/-- Constructed semantic necessities from raw incidence and a positive witness.
No A1-A4 fields, verdict field, result functionality, observer, or reporter
soundness is an input. The universal transfer clause is about fixed original
semantic grounds; domain-specific transport can have separately proved rules. -/
theorem actual_incidence_forces_canonical_work
    (actual : ∃ e q value, J e q value) :
    (∃ e q, assess J e q = true) ∧
    (∀ e q, ∃! verdict, VerdictIncident J e q verdict) ∧
    (∀ e q, ExactAt J (canonicalAnswer J) e q) ∧
    (∀ original replacement : E,
      (∀ P : E → Prop, P original → P replacement) ↔ original = replacement) ∧
    (∀ original replacement : E, ∀ q,
      ¬ Qualified J original q → Qualified J replacement q → original ≠ replacement) := by
  obtain ⟨e, q, value, hactual⟩ := actual
  exact ⟨⟨e, q, actual_incidence_gives_positive J hactual⟩,
    complete_assessment_exists_unique J, canonical_reader_exact J,
    uniform_transfer_iff_identity,
    fun _ _ _ failed qualified => changed_qualification_forces_distinct_original J failed qualified⟩

/-! ## Nonvacuous examples -/

namespace Examples

/-- Both result values genuinely occur. The qualification question is still
settled; the model does not infer a unique result value from this fact. -/
def twoOutcomes : Incidence Unit Unit (fun _ => Bool) := fun _ _ _ => True

theorem both_values_incident : twoOutcomes () () false ∧ twoOutcomes () () true :=
  ⟨trivial, trivial⟩

/-- Non-degeneracy needs a positive incidence, not an extra failed locus. -/
theorem twoOutcomes_no_failed_locus : ∀ e q, Qualified twoOutcomes e q :=
  fun _ _ => ⟨true, trivial⟩
theorem result_relation_not_single_valued :
    ¬ (∀ e q (a b : Bool), twoOutcomes e q a → twoOutcomes e q b → a = b) := by
  intro functionality
  have bad : false = true := functionality () () false true trivial trivial
  cases bad

theorem multivalued_incidence_has_unique_qualification :
    ∃! verdict, VerdictIncident twoOutcomes () () verdict :=
  complete_assessment_exists_unique twoOutcomes () ()

theorem actual_incidence_survives_false_refusal :
    twoOutcomes () () true ∧ assess twoOutcomes () () = true ∧
      ¬ VerdictIncident twoOutcomes () () false := by
  exact ⟨trivial, actual_incidence_gives_positive twoOutcomes (value := true) trivial,
    fun negative => negative true trivial⟩

/-- This relation supplies a genuine positive locus and a false value claim
at that very same ground. -/
def trueOnly : Incidence Unit Unit (fun _ => Bool) := fun _ _ value => value = true

def indiscriminateReader : AnswerReader (E := Unit) (Value := fun _ : Unit => Bool) :=
  fun _ _ _ => true

theorem surplus_reader_does_not_change_actual_incidence :
    trueOnly () () true ∧ SurplusAt trueOnly indiscriminateReader () () := by
  exact ⟨rfl, false, rfl, by change ¬ (false = true); decide⟩

theorem surplus_reader_not_exact : ¬ ExactAt trueOnly indiscriminateReader () () := by
  intro exactReader
  exact ((exact_iff_no_defects trueOnly indiscriminateReader () ()).mp exactReader).1
    surplus_reader_does_not_change_actual_incidence.2

/-- A changed ground may preserve a particular relation by a domain theorem;
this is compatible with failure of unconditional transfer of every predicate. -/
theorem particular_ground_can_transfer_without_identity :
    (fun _ : Bool => True) false → (fun _ : Bool => True) true := id

theorem arbitrary_ground_cannot_transfer_between_booleans :
    ¬ (∀ P : Bool → Prop, P false → P true) :=
  no_uniform_transfer_to_different_original (by decide)

end Examples

end AASC.KernelReference.IncidenceNecessity
