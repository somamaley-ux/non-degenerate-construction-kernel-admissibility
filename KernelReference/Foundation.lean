import AASC.Core.DeterminateObjecthood
import AASC.Instances.KernelPaper.Manuscript

/-!
# Manuscript-facing foundations for the v50 reference edition

Positive incidence, a witnessed failure boundary, and their conjunction are
distinct. Original performance data are fixed without a verdict coordinate.
The observation results below concern independently specified tasks and actual
readers; they do not encode the four-role conclusion as an input field.

These results expose mathematical consequences of explicitly interpreted data.
They do not replace Proposition 2.4's constitutive justification of that
interpretation for actual physical or mathematical objecthood.
-/

namespace AASC.KernelReference.Foundation

universe u v w x y z

section Incidence

variable {Carrier : Type u} {Query : Type v} {Value : Type w}

/-- Positive nonvacuity: an actual incidence exists. No failure is required. -/
def HasActualIncidence (X : IncidenceSystem Carrier Query Value) : Prop :=
  ∃ carrier query value, X.incidence carrier query value

/-- A proper rejection boundary is a separate existence claim. -/
def HasFailureBoundary (X : IncidenceSystem Carrier Query Value) : Prop :=
  ∃ carrier query, ∀ value, ¬ X.incidence carrier query value

/-- Both witnesses, only for conclusions that require both polarities. -/
def HasBothWitnesses (X : IncidenceSystem Carrier Query Value) : Prop :=
  HasActualIncidence X ∧ HasFailureBoundary X

theorem failureBoundary_iff_legacy_nondegenerate
    (X : IncidenceSystem Carrier Query Value) :
    HasFailureBoundary X ↔ X.Nondegenerate := by
  constructor
  · rintro ⟨carrier, query, absent⟩
    exact ⟨carrier, query, fun ⟨value, incident⟩ => absent value incident⟩
  · rintro ⟨carrier, query, absent⟩
    exact ⟨carrier, query, fun value incident => absent ⟨value, incident⟩⟩

theorem actualIncidence_iff_admissible_locus
    (X : IncidenceSystem Carrier Query Value) :
    HasActualIncidence X ↔ ∃ carrier query, X.AdmissibleAt carrier query := by
  rfl

theorem actualIncidence_of_reference
    {X : IncidenceSystem Carrier Query Value} {locus : X.Locus}
    (reference : X.ReferenceAt locus) : HasActualIncidence X :=
  ⟨locus.1, locus.2, reference.value, reference.isIncident⟩

/-- Local positive qualification needs neither failure nor a decision procedure. -/
theorem actual_reference_qualifies
    {X : IncidenceSystem Carrier Query Value} {locus : X.Locus}
    (reference : X.ReferenceAt locus) :
    X.AdmissibleAt locus.1 locus.2 ∧
      (kernelOfIncidence X).StandingAt locus.1 locus.2 :=
  ⟨X.admissibleAt_of_reference reference,
    X.canonicalKernel_standingAt_of_reference reference⟩

theorem actualIncidence_has_canonical_standing
    {X : IncidenceSystem Carrier Query Value} (actual : HasActualIncidence X) :
    ∃ carrier query, (kernelOfIncidence X).StandingAt carrier query := by
  rcases actual with ⟨carrier, query, value, incident⟩
  exact ⟨carrier, query,
    (actual_reference_qualifies (X := X)
      (locus := (carrier, query)) ⟨value, incident⟩).2⟩

/-- Result uniqueness is added explicitly; positive incidence alone does not imply it. -/
theorem determinate_actual_reference
    {X : IncidenceSystem Carrier Query Value}
    (determinate : X.Determinate) {locus : X.Locus}
    (reference : X.ReferenceAt locus) :
    X.AdmissibleAt locus.1 locus.2 ∧
      (kernelOfIncidence X).StandingAt locus.1 locus.2 ∧
      (kernelOfIncidence X).ReferenceUnique :=
  ⟨(actual_reference_qualifies reference).1,
    (actual_reference_qualifies reference).2,
    (kernelOfIncidence X).reference_unique_of_determinate determinate⟩

end Incidence

section LegacyRegime

variable {Act : Type u} {Target : Type v} {Step : Type w}

def HasSuccessfulUse (R : TargetAdequacy.Regime Act Target Step) : Prop :=
  ∃ step, R.Standing step

def HasFailedUse (R : TargetAdequacy.Regime Act Target Step) : Prop :=
  ∃ step, R.Failure step

theorem legacy_regime_nondegenerate_iff_both
    (R : TargetAdequacy.Regime Act Target Step) :
    R.Nondegenerate ↔ HasSuccessfulUse R ∧ HasFailedUse R := by
  constructor
  · rintro ⟨standing, failed, hs, hf⟩
    exact ⟨⟨standing, hs⟩, ⟨failed, hf⟩⟩
  · rintro ⟨⟨standing, hs⟩, ⟨failed, hf⟩⟩
    exact ⟨standing, failed, hs, hf⟩

end LegacyRegime

/-- Original data contain no verdict or agreement-of-results field. -/
structure OriginalPerformance
    (Occurrence : Type u) (Material : Type v) (Conditions : Type w)
    (Target : Type x) where
  occurrence : Occurrence
  material : Material
  conditions : Conditions
  target : Target
deriving DecidableEq

namespace OriginalPerformance

variable {Occurrence : Type u} {Material : Type v} {Conditions : Type w}
    {Target : Type x}

/-- Faithful retention of the independently specified original data. -/
def RetainsOriginal
    (left right : OriginalPerformance Occurrence Material Conditions Target) : Prop :=
  left.occurrence = right.occurrence ∧ left.material = right.material ∧
    left.conditions = right.conditions ∧ left.target = right.target

theorem retainsOriginal_iff_eq
    (left right : OriginalPerformance Occurrence Material Conditions Target) :
    RetainsOriginal left right ↔ left = right := by
  constructor
  · cases left with
    | mk lo lm lc lt =>
      cases right with
      | mk ro rm rc rt =>
        rintro ⟨ho, hm, hc, ht⟩
        cases ho
        cases hm
        cases hc
        cases ht
        rfl
  · intro same
    subst right
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem changed_occurrence_not_retained
    {left right : OriginalPerformance Occurrence Material Conditions Target}
    (changed : left.occurrence ≠ right.occurrence) :
    ¬ RetainsOriginal left right :=
  fun retained => changed retained.1

theorem changed_conditions_not_retained
    {left right : OriginalPerformance Occurrence Material Conditions Target}
    (changed : left.conditions ≠ right.conditions) :
    ¬ RetainsOriginal left right :=
  fun retained => changed retained.2.2.1

/-- The same original data retain each independently defined use condition. -/
theorem qualification_preserved
    {Use : Type y}
    (qualifies : OriginalPerformance Occurrence Material Conditions Target → Use → Prop)
    {left right : OriginalPerformance Occurrence Material Conditions Target}
    (same : RetainsOriginal left right) (use : Use) :
    qualifies left use ↔ qualifies right use := by
  rw [(retainsOriginal_iff_eq left right).1 same]

/-- A newly qualifying performance cannot replace the failed original data. -/
theorem new_success_does_not_replace_original
    {Use : Type y}
    (qualifies : OriginalPerformance Occurrence Material Conditions Target → Use → Prop)
    {original later : OriginalPerformance Occurrence Material Conditions Target}
    {use : Use} (failed : ¬ qualifies original use) (succeeded : qualifies later use) :
    ¬ RetainsOriginal original later := by
  intro same
  exact failed ((qualification_preserved qualifies same use).2 succeeded)

/-- Output agreement also requires determinacy of the independently fixed result. -/
theorem incident_answers_agree
    {Query : Type y} {Value : Type z}
    (X : IncidenceSystem
      (OriginalPerformance Occurrence Material Conditions Target) Query Value)
    (determinate : X.Determinate)
    {left right : OriginalPerformance Occurrence Material Conditions Target}
    (same : RetainsOriginal left right) {query : Query} {a b : Value}
    (leftIncident : X.incidence left query a)
    (rightIncident : X.incidence right query b) : a = b := by
  have sameData := (retainsOriginal_iff_eq left right).1 same
  subst right
  exact determinate left query a b leftIncident rightIncident

end OriginalPerformance

namespace ObservationWork

variable {Scenario : Type u} {Question : Type v} {Answer : Type w}

/-- Completeness is an explicit relation between original task and actual reader. -/
def CompleteFor (required : Scenario → Question → Answer → Prop)
    (read : Scenario → Question → Option Answer) : Prop :=
  ∀ scenario question answer,
    required scenario question answer → read scenario question = some answer

/-- A missing answer is witnessed against the independently specified task. -/
def MissingRequiredAnswer (required : Scenario → Question → Answer → Prop)
    (read : Scenario → Question → Option Answer) : Prop :=
  ∃ scenario question answer,
    required scenario question answer ∧ read scenario question ≠ some answer

theorem missing_work_excludes_complete_realization
    {required : Scenario → Question → Answer → Prop}
    {read : Scenario → Question → Option Answer}
    (missing : MissingRequiredAnswer required read) : ¬ CompleteFor required read := by
  rintro complete
  rcases missing with ⟨scenario, question, answer, requiredAnswer, missingAnswer⟩
  exact missingAnswer (complete scenario question answer requiredAnswer)

/-- A code erasing a demanded distinction cannot support a complete reader.
This is a task-relative deletion theorem, not a four-name coverage postulate. -/
theorem required_distinction_cannot_be_erased
    {Code : Type x} (required : Scenario → Question → Answer → Prop)
    (encode : Scenario → Code) (decode : Code → Question → Option Answer)
    {left right : Scenario} {question : Question} {a b : Answer}
    (leftRequired : required left question a)
    (rightRequired : required right question b) (different : a ≠ b)
    (erased : encode left = encode right) :
    ¬ CompleteFor required (fun scenario query => decode (encode scenario) query) := by
  intro complete
  have leftAnswer := complete left question a leftRequired
  have rightAnswer := complete right question b rightRequired
  change decode (encode left) question = some a at leftAnswer
  change decode (encode right) question = some b at rightAnswer
  rw [erased] at leftAnswer
  exact different (Option.some.inj (leftAnswer.symm.trans rightAnswer))

end ObservationWork

namespace Examples

/-- A positive, determinate system without a rejection boundary. -/
def positiveOnly : IncidenceSystem Unit Unit Unit where
  incidence _ _ _ := True

theorem positiveOnly_actual : HasActualIncidence positiveOnly :=
  ⟨(), (), (), True.intro⟩

theorem positiveOnly_determinate : positiveOnly.Determinate := by
  intro _ _ left right _ _
  cases left
  cases right
  rfl

theorem positiveOnly_no_failureBoundary : ¬ HasFailureBoundary positiveOnly := by
  rintro ⟨_, _, absent⟩
  exact absent () True.intro

theorem positiveOnly_not_legacy_nondegenerate : ¬ positiveOnly.Nondegenerate :=
  fun h => positiveOnly_no_failureBoundary
    ((failureBoundary_iff_legacy_nondegenerate positiveOnly).2 h)

/-- A boundary by itself need not supply any actual positive incidence. -/
def failureOnly : IncidenceSystem Unit Unit Unit where
  incidence _ _ _ := False

theorem failureOnly_boundary : HasFailureBoundary failureOnly :=
  ⟨(), (), fun _ h => h⟩

theorem failureOnly_no_actual : ¬ HasActualIncidence failureOnly := by
  rintro ⟨_, _, _, impossible⟩
  exact impossible

/-! A finite construction model with explicit input data and relation.
Its relation is illustrative mathematical data, not a derived physical law. -/

inductive Trial where
  | first | repaired | assisted
deriving DecidableEq

inductive Joint where
  | loose | secured
deriving DecidableEq

inductive Support where
  | unassisted | finger
deriving DecidableEq

abbrev Performance := OriginalPerformance Trial Joint Support Unit

def first : Performance := ⟨.first, .loose, .unassisted, ()⟩
def repaired : Performance := ⟨.repaired, .secured, .unassisted, ()⟩
def assisted : Performance := ⟨.assisted, .loose, .finger, ()⟩

def Carries (performance : Performance) : Prop :=
  performance.material = .secured ∨ performance.conditions = .finger

def UnsupportedCrossing (performance : Performance) : Prop :=
  Carries performance ∧ performance.conditions = .unassisted

instance (performance : Performance) : Decidable (Carries performance) :=
  inferInstanceAs (Decidable
    (performance.material = .secured ∨ performance.conditions = .finger))

instance (performance : Performance) : Decidable (UnsupportedCrossing performance) :=
  inferInstanceAs (Decidable
    (Carries performance ∧ performance.conditions = .unassisted))

theorem first_fails_original_use : ¬ UnsupportedCrossing first := by decide
theorem repaired_succeeds_new_use : UnsupportedCrossing repaired := by decide
theorem assisted_carries : Carries assisted := by decide
theorem assisted_fails_unsupported_use : ¬ UnsupportedCrossing assisted := by decide

theorem repaired_does_not_retain_original :
    ¬ OriginalPerformance.RetainsOriginal first repaired := by
  exact OriginalPerformance.changed_occurrence_not_retained (by decide)

theorem assisted_changes_conditions :
    ¬ OriginalPerformance.RetainsOriginal first assisted := by
  exact OriginalPerformance.changed_conditions_not_retained (by decide)

/-- Every original performance has its own determinate incidence. -/
def occurrenceSystem : IncidenceSystem Performance Unit Performance where
  incidence performance _ value := value = performance

theorem occurrenceSystem_determinate : occurrenceSystem.Determinate := by
  intro performance _ left right hl hr
  exact hl.trans hr.symm

theorem failed_trial_occurrence_has_standing :
    (kernelOfIncidence occurrenceSystem).StandingAt first () :=
  (actual_reference_qualifies (X := occurrenceSystem)
    (locus := (first, ())) ⟨first, rfl⟩).2

/-- Report warrant is fixed by the original trial, not the report's inscription. -/
def ReportWarrant (performance : Performance) (reported : Bool) : Prop :=
  reported = decide (UnsupportedCrossing performance)

theorem negative_report_of_first_is_warranted : ReportWarrant first false := by
  unfold ReportWarrant
  decide
theorem success_report_of_first_is_unwarranted : ¬ ReportWarrant first true := by
  unfold ReportWarrant
  decide
theorem success_report_of_repaired_is_warranted : ReportWarrant repaired true := by
  unfold ReportWarrant
  decide

/-- Agreement of reports cannot identify their original performance. -/
theorem equal_report_does_not_identify_original :
    ReportWarrant first false ∧ ReportWarrant assisted false ∧
      ¬ OriginalPerformance.RetainsOriginal first assisted :=
  ⟨negative_report_of_first_is_warranted, by unfold ReportWarrant; decide,
    assisted_changes_conditions⟩

/-- A concrete legacy regime computes its verdict from the supplied use relation. -/
def trialRegime : TargetAdequacy.Regime Unit Unit Performance where
  source _ := ()
  destination _ := ()
  targetOf _ := ()
  verdict performance := if UnsupportedCrossing performance then .advances else .fails

/-- A failed use coexists with the entire derived legacy role profile.
The profile's interpretation remains the scope of its original theorem. -/
theorem ordinary_failed_trial_and_full_regime_profile :
    Instances.KernelPaper.Manuscript.DerivedKernelRoles trialRegime ∧
      ¬ trialRegime.Standing first ∧ trialRegime.Standing repaired := by
  refine ⟨Instances.KernelPaper.Manuscript.targetAdequacy_forces_kernel_roles trialRegime,
    ?_, ?_⟩
  · simp [TargetAdequacy.Regime.Standing, TargetAdequacy.Regime.VerdictAt,
      trialRegime, first_fails_original_use]
  · simp [TargetAdequacy.Regime.Standing, TargetAdequacy.Regime.VerdictAt,
      trialRegime, repaired_succeeds_new_use]

theorem trialRegime_has_both_witnesses :
    HasSuccessfulUse trialRegime ∧ HasFailedUse trialRegime := by
  exact ⟨⟨repaired, ordinary_failed_trial_and_full_regime_profile.2.2⟩,
    ⟨first, ordinary_failed_trial_and_full_regime_profile.2.1⟩⟩

/-- Erasing trial identity while an original task asks for it is a real loss. -/
def identityTask (performance : Performance) (_ : Unit) (trial : Trial) : Prop :=
  trial = performance.occurrence

theorem erasing_trial_identity_loses_required_work
    (reader : Unit → Unit → Option Trial) :
    ¬ ObservationWork.CompleteFor identityTask (fun _ query => reader () query) := by
  exact ObservationWork.required_distinction_cannot_be_erased identityTask
    (fun _ => ()) reader (left := first) (right := repaired) (question := ())
    (a := .first) (b := .repaired) rfl rfl (by decide) rfl

end Examples

end AASC.KernelReference.Foundation

#print axioms AASC.KernelReference.Foundation.failureBoundary_iff_legacy_nondegenerate
#print axioms AASC.KernelReference.Foundation.actualIncidence_iff_admissible_locus
#print axioms AASC.KernelReference.Foundation.actual_reference_qualifies
#print axioms AASC.KernelReference.Foundation.actualIncidence_has_canonical_standing
#print axioms AASC.KernelReference.Foundation.determinate_actual_reference
#print axioms AASC.KernelReference.Foundation.legacy_regime_nondegenerate_iff_both
#print axioms AASC.KernelReference.Foundation.OriginalPerformance.retainsOriginal_iff_eq
#print axioms AASC.KernelReference.Foundation.OriginalPerformance.new_success_does_not_replace_original
#print axioms AASC.KernelReference.Foundation.OriginalPerformance.incident_answers_agree
#print axioms AASC.KernelReference.Foundation.ObservationWork.missing_work_excludes_complete_realization
#print axioms AASC.KernelReference.Foundation.ObservationWork.required_distinction_cannot_be_erased
#print axioms AASC.KernelReference.Foundation.Examples.positiveOnly_actual
#print axioms AASC.KernelReference.Foundation.Examples.positiveOnly_determinate
#print axioms AASC.KernelReference.Foundation.Examples.positiveOnly_no_failureBoundary
#print axioms AASC.KernelReference.Foundation.Examples.failureOnly_no_actual
#print axioms AASC.KernelReference.Foundation.Examples.repaired_does_not_retain_original
#print axioms AASC.KernelReference.Foundation.Examples.assisted_changes_conditions
#print axioms AASC.KernelReference.Foundation.Examples.failed_trial_occurrence_has_standing
#print axioms AASC.KernelReference.Foundation.Examples.success_report_of_first_is_unwarranted
#print axioms AASC.KernelReference.Foundation.Examples.equal_report_does_not_identify_original
#print axioms AASC.KernelReference.Foundation.Examples.ordinary_failed_trial_and_full_regime_profile
#print axioms AASC.KernelReference.Foundation.Examples.erasing_trial_identity_loses_required_work
