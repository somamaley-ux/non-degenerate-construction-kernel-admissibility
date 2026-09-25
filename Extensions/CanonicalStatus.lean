import AASC.Core.Standing

/-!
# Equality of canonical status at a fixed determinate locus

The theorem is about the actual semantic status type, not arbitrary raw codes.
At one determinate carrier/scope, its inhabitants are equal. All total and
partial consumers therefore preserve their observations without additional
consumer-specific invariance premises. A separate theorem records exactly
which polarity fibres are inhabited; a subsingleton semantic fibre is never
mistaken for two simultaneously inhabited local classes.
-/

namespace AASC.CanonicalStatus

universe u v w z

variable {Carrier : Type u} {Scope : Type v} {Value : Type w}
variable {X : IncidenceSystem Carrier Scope Value}
variable {carrier : Carrier} {scope : Scope}

theorem status_eq_of_determinate
    (determinate : X.Determinate)
    (left right : X.StandingStatus carrier scope) :
    left = right := by
  cases left with
  | standing leftReference =>
      cases right with
      | standing rightReference =>
          have sameReference :=
            X.reference_eq_of_determinate determinate leftReference rightReference
          cases sameReference
          rfl
      | failure noIncidence =>
          exact False.elim
            (noIncidence leftReference.value leftReference.isIncident)
  | failure noIncidence =>
      cases right with
      | standing rightReference =>
          exact False.elim
            (noIncidence rightReference.value rightReference.isIncident)
      | failure otherNoIncidence =>
          rfl

theorem status_subsingleton_of_determinate
    (determinate : X.Determinate) :
    Subsingleton (X.StandingStatus carrier scope) :=
  ⟨status_eq_of_determinate determinate⟩

/-- Every total observation of actual same-locus semantic status agrees. -/
theorem total_consumer_invariant
    (determinate : X.Determinate)
    {Output : Sort z}
    (consumer : X.StandingStatus carrier scope → Output)
    (left right : X.StandingStatus carrier scope) :
    consumer left = consumer right :=
  congrArg consumer (status_eq_of_determinate determinate left right)

/-- Status-indexed result types are preserved by transport along status equality. -/
theorem dependent_output_consumer_invariant
    (determinate : X.Determinate)
    (Output : X.StandingStatus carrier scope → Sort z)
    (consumer : (status : X.StandingStatus carrier scope) → Output status)
    (left right : X.StandingStatus carrier scope) :
    HEq (consumer left) (consumer right) := by
  cases status_eq_of_determinate determinate left right
  rfl

/-- The dependent Option result preserves both its value and failure by transport. -/
theorem dependent_option_consumer_invariant
    (determinate : X.Determinate)
    (Output : X.StandingStatus carrier scope → Type z)
    (consumer : (status : X.StandingStatus carrier scope) → Option (Output status))
    (left right : X.StandingStatus carrier scope) :
    HEq (consumer left) (consumer right) := by
  cases status_eq_of_determinate determinate left right
  rfl

/-- Predicate-valued domains are preserved without a decidability premise. -/
theorem domain_invariant
    (determinate : X.Determinate)
    (domain : X.StandingStatus carrier scope → Prop)
    (left right : X.StandingStatus carrier scope) :
    domain left ↔ domain right := by
  cases status_eq_of_determinate determinate left right
  rfl

/-- Partial observations preserve the complete Option result, including none. -/
theorem partial_consumer_invariant
    (determinate : X.Determinate)
    {Output : Type z}
    (consumer : X.StandingStatus carrier scope → Option Output)
    (left right : X.StandingStatus carrier scope) :
    consumer left = consumer right :=
  total_consumer_invariant determinate consumer left right

theorem partial_definedness_invariant
    (determinate : X.Determinate)
    {Output : Type z}
    (consumer : X.StandingStatus carrier scope → Option Output)
    (left right : X.StandingStatus carrier scope) :
    (∃ output, consumer left = some output) ↔
      (∃ output, consumer right = some output) := by
  rw [partial_consumer_invariant determinate consumer left right]

/-- Arbitrary proposition-domain dependent partial consumers also agree. -/
theorem dependent_partial_consumer_invariant
    (determinate : X.Determinate)
    {Output : Sort z}
    (domain : X.StandingStatus carrier scope → Prop)
    (consumer : (status : X.StandingStatus carrier scope) → domain status → Output)
    (left right : X.StandingStatus carrier scope)
    (leftInDomain : domain left) (rightInDomain : domain right) :
    consumer left leftInDomain = consumer right rightInDomain := by
  cases status_eq_of_determinate determinate left right
  rfl

def polarity : X.StandingStatus carrier scope → Bool
  | .standing _ => true
  | .failure _ => false

def PolarityFiber
    (X : IncidenceSystem Carrier Scope Value)
    (carrier : Carrier) (scope : Scope) (bit : Bool) :=
  {status : X.StandingStatus carrier scope // polarity status = bit}

theorem positive_fiber_iff :
    Nonempty (PolarityFiber X carrier scope true) ↔
      X.AdmissibleAt carrier scope := by
  constructor
  · rintro ⟨⟨status, positive⟩⟩
    cases status with
    | standing reference => exact ⟨reference.value, reference.isIncident⟩
    | failure noIncidence => cases positive
  · rintro ⟨value, incident⟩
    exact ⟨⟨.standing ⟨value, incident⟩, rfl⟩⟩

theorem negative_fiber_iff :
    Nonempty (PolarityFiber X carrier scope false) ↔
      ¬ X.AdmissibleAt carrier scope := by
  constructor
  · rintro ⟨⟨status, negative⟩⟩
    cases status with
    | standing reference => cases negative
    | failure noIncidence =>
        rintro ⟨value, incident⟩
        exact noIncidence value incident
  · intro notAdmissible
    exact ⟨⟨.failure (fun value incident => notAdmissible ⟨value, incident⟩), rfl⟩⟩

theorem fixed_locus_not_both_polarities :
    ¬ (Nonempty (PolarityFiber X carrier scope true) ∧
      Nonempty (PolarityFiber X carrier scope false)) := by
  rintro ⟨positive, negative⟩
  exact (negative_fiber_iff.mp negative) (positive_fiber_iff.mp positive)

/-- Classical existence does not supply a computable evaluator. -/
theorem status_nonempty :
    Nonempty (X.StandingStatus carrier scope) := by
  classical
  by_cases admitted : X.AdmissibleAt carrier scope
  · rcases positive_fiber_iff.mpr admitted with ⟨⟨status, positive⟩⟩
    exact ⟨status⟩
  · rcases negative_fiber_iff.mpr admitted with ⟨⟨status, negative⟩⟩
    exact ⟨status⟩

theorem exactly_one_status_at_determinate_locus
    (determinate : X.Determinate) :
    ∃ status : X.StandingStatus carrier scope,
      ∀ other, other = status := by
  rcases status_nonempty (X := X) (carrier := carrier) (scope := scope) with ⟨status⟩
  exact ⟨status, fun other => status_eq_of_determinate determinate other status⟩

/-- Represented tags in any explicitly selected collection of complete loci. -/
def RepresentedPolarity
    (X : IncidenceSystem Carrier Scope Value)
    (selected : Carrier → Scope → Prop) (bit : Bool) : Prop :=
  ∃ carrier scope, selected carrier scope ∧
    Nonempty (PolarityFiber X carrier scope bit)

theorem represented_positive_iff
    (selected : Carrier → Scope → Prop) :
    RepresentedPolarity X selected true ↔
      ∃ carrier scope, selected carrier scope ∧ X.AdmissibleAt carrier scope := by
  constructor
  · rintro ⟨carrier, scope, included, positive⟩
    exact ⟨carrier, scope, included, positive_fiber_iff.mp positive⟩
  · rintro ⟨carrier, scope, included, admitted⟩
    exact ⟨carrier, scope, included, positive_fiber_iff.mpr admitted⟩

theorem represented_negative_iff
    (selected : Carrier → Scope → Prop) :
    RepresentedPolarity X selected false ↔
      ∃ carrier scope, selected carrier scope ∧ ¬ X.AdmissibleAt carrier scope := by
  constructor
  · rintro ⟨carrier, scope, included, negative⟩
    exact ⟨carrier, scope, included, negative_fiber_iff.mp negative⟩
  · rintro ⟨carrier, scope, included, failed⟩
    exact ⟨carrier, scope, included, negative_fiber_iff.mpr failed⟩

theorem represented_both_iff
    (selected : Carrier → Scope → Prop) :
    (RepresentedPolarity X selected true ∧ RepresentedPolarity X selected false) ↔
      (∃ carrier scope, selected carrier scope ∧ X.AdmissibleAt carrier scope) ∧
      (∃ carrier scope, selected carrier scope ∧ ¬ X.AdmissibleAt carrier scope) := by
  rw [represented_positive_iff, represented_negative_iff]

theorem represented_any_iff_selected_nonempty
    (selected : Carrier → Scope → Prop) :
    (∃ bit, RepresentedPolarity X selected bit) ↔
      ∃ carrier scope, selected carrier scope := by
  constructor
  · rintro ⟨bit, carrier, scope, included, status⟩
    exact ⟨carrier, scope, included⟩
  · rintro ⟨carrier, scope, included⟩
    rcases status_nonempty (X := X) (carrier := carrier) (scope := scope) with ⟨status⟩
    exact ⟨polarity status, carrier, scope, included, ⟨⟨status, rfl⟩⟩⟩

theorem represented_only_positive_iff
    (selected : Carrier → Scope → Prop) :
    (RepresentedPolarity X selected true ∧ ¬ RepresentedPolarity X selected false) ↔
      (∃ carrier scope, selected carrier scope) ∧
      (∀ carrier scope, selected carrier scope → X.AdmissibleAt carrier scope) := by
  classical
  constructor
  · rintro ⟨positive, noNegative⟩
    rcases positive with ⟨carrier, scope, included, status⟩
    refine ⟨⟨carrier, scope, included⟩, ?_⟩
    intro otherCarrier otherScope otherIncluded
    exact Classical.byContradiction (fun notAdmitted => noNegative
      ⟨otherCarrier, otherScope, otherIncluded, negative_fiber_iff.mpr notAdmitted⟩)
  · rintro ⟨⟨carrier, scope, included⟩, allAdmitted⟩
    constructor
    · exact ⟨carrier, scope, included,
        positive_fiber_iff.mpr (allAdmitted carrier scope included)⟩
    · rintro ⟨otherCarrier, otherScope, otherIncluded, negative⟩
      exact (negative_fiber_iff.mp negative)
        (allAdmitted otherCarrier otherScope otherIncluded)

theorem represented_only_negative_iff
    (selected : Carrier → Scope → Prop) :
    (RepresentedPolarity X selected false ∧ ¬ RepresentedPolarity X selected true) ↔
      (∃ carrier scope, selected carrier scope) ∧
      (∀ carrier scope, selected carrier scope → ¬ X.AdmissibleAt carrier scope) := by
  constructor
  · rintro ⟨negative, noPositive⟩
    rcases negative with ⟨carrier, scope, included, status⟩
    refine ⟨⟨carrier, scope, included⟩, ?_⟩
    intro otherCarrier otherScope otherIncluded admitted
    exact noPositive
      ⟨otherCarrier, otherScope, otherIncluded, positive_fiber_iff.mpr admitted⟩
  · rintro ⟨⟨carrier, scope, included⟩, allFailed⟩
    constructor
    · exact ⟨carrier, scope, included,
        negative_fiber_iff.mpr (allFailed carrier scope included)⟩
    · rintro ⟨otherCarrier, otherScope, otherIncluded, positive⟩
      exact (allFailed otherCarrier otherScope otherIncluded)
        (positive_fiber_iff.mp positive)

theorem no_selected_loci_no_polarity
    (selected : Carrier → Scope → Prop)
    (empty : ∀ carrier scope, ¬ selected carrier scope)
    (bit : Bool) : ¬ RepresentedPolarity X selected bit := by
  rintro ⟨carrier, scope, included, status⟩
  exact empty carrier scope included

/-!
Polarity count: an empty selected collection represents zero tags; an inhabited
collection with only positive (respectively negative) loci represents one;
both tags are represented exactly under `represented_both_iff`. These facts do
not collapse the full dependent collection of objects and their observations
to two classes: substantive carrier/scope data remain part of the object.
-/

end AASC.CanonicalStatus

#print axioms AASC.CanonicalStatus.status_eq_of_determinate
#print axioms AASC.CanonicalStatus.total_consumer_invariant
#print axioms AASC.CanonicalStatus.partial_consumer_invariant
#print axioms AASC.CanonicalStatus.dependent_partial_consumer_invariant
#print axioms AASC.CanonicalStatus.exactly_one_status_at_determinate_locus
#print axioms AASC.CanonicalStatus.represented_both_iff

#print axioms AASC.CanonicalStatus.dependent_output_consumer_invariant
#print axioms AASC.CanonicalStatus.dependent_option_consumer_invariant
