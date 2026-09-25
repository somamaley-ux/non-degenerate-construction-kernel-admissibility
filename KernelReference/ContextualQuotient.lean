import Mathlib.Logic.Equiv.Defs

/-!
# Canonical quotients of arbitrary original observation profiles

The original observation family and each coordinate's result type are fixed
inputs. No finiteness, binary range, or factorization certificate is assumed.
The quotient, its universal property, profile-image realization and uniquely
commuting exact classifications are constructed from equality of observations.

The partial-operation results first derive domain and output congruence when
the original input observations contain the domain test and every pulled-back
optional output coordinate. Their membership is established for each original
context separately; pairwise preservation is a conclusion. Quotient descent
then follows. This criterion does not assume that an arbitrary selected family
is complete or automatically generate an entire many-sorted context grammar.
-/

namespace AASC.KernelReference.ContextualQuotient

universe u v w u' v' w' z z'

variable {X : Type u} {Query : Type v} {Value : Query → Type w}

/-- Indistinguishability by every original observation, with its original result type. -/
def Equivalent (observe : X → (q : Query) → Value q) (x y : X) : Prop :=
  ∀ q, observe x q = observe y q

def observationSetoid (observe : X → (q : Query) → Value q) : Setoid X where
  r := Equivalent observe
  iseqv := ⟨fun _ _ => rfl,
    fun h q => (h q).symm,
    fun h₁ h₂ q => (h₁ q).trans (h₂ q)⟩

abbrev CanonicalQuotient (observe : X → (q : Query) → Value q) :=
  Quotient (observationSetoid observe)

def classify (observe : X → (q : Query) → Value q) (x : X) :
    CanonicalQuotient observe := Quotient.mk _ x

theorem equivalent_iff_profile_eq (observe : X → (q : Query) → Value q)
    (x y : X) : Equivalent observe x y ↔ observe x = observe y := by
  constructor
  · exact fun h => funext h
  · intro h q
    exact congrFun h q

theorem classify_eq_iff (observe : X → (q : Query) → Value q) (x y : X) :
    classify observe x = classify observe y ↔ Equivalent observe x y :=
  ⟨fun h => Quotient.exact h,
    fun h => Quotient.sound (s := observationSetoid observe) h⟩

theorem classify_surjective (observe : X → (q : Query) → Value q) :
    Function.Surjective (classify observe) := by
  intro a
  exact Quotient.inductionOn a (fun x => ⟨x, rfl⟩)

/-- A class-constant original map descends by the quotient eliminator. -/
def descend (observe : X → (q : Query) → Value q)
    {Y : Type z} (f : X → Y)
    (constant : ∀ x y, Equivalent observe x y → f x = f y) :
    CanonicalQuotient observe → Y := Quotient.lift f constant

theorem descend_classify (observe : X → (q : Query) → Value q)
    {Y : Type z} (f : X → Y)
    (constant : ∀ x y, Equivalent observe x y → f x = f y) (x : X) :
    descend observe f constant (classify observe x) = f x := rfl

/-- The factorization equation is proved, not supplied as a certificate field. -/
theorem unique_factorization (observe : X → (q : Query) → Value q)
    {Y : Type z} (f : X → Y)
    (constant : ∀ x y, Equivalent observe x y → f x = f y) :
    ∃! reduced : CanonicalQuotient observe → Y,
      ∀ x, reduced (classify observe x) = f x := by
  refine ⟨descend observe f constant, fun _ => rfl, ?_⟩
  intro other commutes
  funext a
  exact Quotient.inductionOn a commutes

/-- Every original coordinate is recovered on the quotient, without changing its codomain. -/
def readCoordinate (observe : X → (q : Query) → Value q) (q : Query) :
    CanonicalQuotient observe → Value q :=
  descend observe (fun x => observe x q) (fun _ _ h => h q)

theorem coordinate_recovery (observe : X → (q : Query) → Value q)
    (x : X) (q : Query) :
    readCoordinate observe q (classify observe x) = observe x q := rfl

/-- A surjective classifier with exactly the original fibers is uniquely isomorphic
to the canonical quotient over the original inputs. No isomorphism is assumed. -/
theorem unique_exact_classifier
    (observe : X → (q : Query) → Value q)
    {E : Type z} (p : X → E) (onto : Function.Surjective p)
    (fibers : ∀ x y, p x = p y ↔ Equivalent observe x y) :
    ∃! e : CanonicalQuotient observe ≃ E,
      ∀ x, e (classify observe x) = p x := by
  let reduced := descend observe p (fun x y h => (fibers x y).2 h)
  have injective : Function.Injective reduced := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y h
    exact Quotient.sound ((fibers x y).1 h)
  have surjective : Function.Surjective reduced := by
    intro y
    obtain ⟨x, hx⟩ := onto y
    exact ⟨classify observe x, hx⟩
  let e : CanonicalQuotient observe ≃ E :=
    Equiv.ofBijective reduced ⟨injective, surjective⟩
  have commutes : ∀ x, e (classify observe x) = p x := fun _ => rfl
  refine ⟨e, commutes, ?_⟩
  intro other hother
  apply Equiv.ext
  intro a
  exact Quotient.inductionOn a (fun x => (hother x).trans (commutes x).symm)

/-- The actual image of the independently fixed dependent observation profile. -/
def ObservedProfiles (observe : X → (q : Query) → Value q) :=
  { profile : (q : Query) → Value q // ∃ x, observe x = profile }

def profileImageMap (observe : X → (q : Query) → Value q) (x : X) :
    ObservedProfiles observe := ⟨observe x, x, rfl⟩

theorem canonical_profile_realization
    (observe : X → (q : Query) → Value q) :
    ∃! e : CanonicalQuotient observe ≃ ObservedProfiles observe,
      ∀ x, e (classify observe x) = profileImageMap observe x := by
  apply unique_exact_classifier observe (profileImageMap observe)
  · intro profile
    obtain ⟨x, hx⟩ := profile.property
    exact ⟨x, Subtype.ext hx⟩
  · intro x y
    constructor
    · intro h q
      exact congrFun (congrArg Subtype.val h) q
    · intro h
      exact Subtype.ext (funext h)

/-- Two exact surjective classifiers of the same observations have one commuting
isomorphism. This is uniqueness of classification, not uniqueness of an occupant. -/
theorem unique_classifier_isomorphism
    (observe : X → (q : Query) → Value q)
    {E : Type z} {F : Type z'} (p : X → E) (r : X → F)
    (pOnto : Function.Surjective p) (rOnto : Function.Surjective r)
    (pFibers : ∀ x y, p x = p y ↔ Equivalent observe x y)
    (rFibers : ∀ x y, r x = r y ↔ Equivalent observe x y) :
    ∃! e : E ≃ F, ∀ x, e (p x) = r x := by
  obtain ⟨ep, hp, _⟩ := unique_exact_classifier observe p pOnto pFibers
  obtain ⟨er, hr, _⟩ := unique_exact_classifier observe r rOnto rFibers
  let e : E ≃ F := ep.symm.trans er
  have commutes : ∀ x, e (p x) = r x := by
    intro x
    change er (ep.symm (p x)) = r x
    rw [← hp x, ep.symm_apply_apply, hr]
  refine ⟨e, commutes, ?_⟩
  intro other hother
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := pOnto y
  exact (hother x).trans (commutes x).symm

section PartialOperations

variable {Y : Type u'} {OutQuery : Type v'} {OutValue : OutQuery → Type w'}

/-- The lemma premises preserve both the old domain and all original output observations. -/
theorem partial_output_classes_agree
    (observeIn : X → (q : Query) → Value q)
    (observeOut : Y → (q : OutQuery) → OutValue q) (f : X → Option Y)
    (domainCongruence : ∀ x y, Equivalent observeIn x y →
      (f x = none ↔ f y = none))
    (outputCongruence : ∀ x y a b, Equivalent observeIn x y →
      f x = some a → f y = some b → Equivalent observeOut a b)
    (x y : X) (equivalent : Equivalent observeIn x y) :
    Option.map (classify observeOut) (f x) =
      Option.map (classify observeOut) (f y) := by
  cases hx : f x with
  | none =>
    have hy := (domainCongruence x y equivalent).1 hx
    rw [hy]
  | some a =>
    cases hy : f y with
    | none =>
      have hxnone := (domainCongruence x y equivalent).2 hy
      rw [hx] at hxnone
      cases hxnone
    | some b =>
      exact congrArg some (Quotient.sound
        (outputCongruence x y a b equivalent hx hy))

/-- Existence and uniqueness of the partial quotient operation follow from the
separately stated congruence lemma, including original definedness. -/
theorem unique_partial_descent
    (observeIn : X → (q : Query) → Value q)
    (observeOut : Y → (q : OutQuery) → OutValue q) (f : X → Option Y)
    (domainCongruence : ∀ x y, Equivalent observeIn x y →
      (f x = none ↔ f y = none))
    (outputCongruence : ∀ x y a b, Equivalent observeIn x y →
      f x = some a → f y = some b → Equivalent observeOut a b) :
    ∃! reduced : CanonicalQuotient observeIn → Option (CanonicalQuotient observeOut),
      ∀ x, reduced (classify observeIn x) = Option.map (classify observeOut) (f x) :=
  unique_factorization observeIn (fun x => Option.map (classify observeOut) (f x))
    (partial_output_classes_agree observeIn observeOut f domainCongruence outputCongruence)

theorem partial_descent_domain_image
    (observeIn : X → (q : Query) → Value q)
    (observeOut : Y → (q : OutQuery) → OutValue q) (f : X → Option Y)
    (reduced : CanonicalQuotient observeIn → Option (CanonicalQuotient observeOut))
    (commutes : ∀ x,
      reduced (classify observeIn x) = Option.map (classify observeOut) (f x))
    (a : CanonicalQuotient observeIn) :
    reduced a ≠ none ↔ ∃ x y, classify observeIn x = a ∧ f x = some y := by
  constructor
  · intro defined
    obtain ⟨x, rfl⟩ := classify_surjective observeIn a
    cases hx : f x with
    | none =>
      have absent : reduced (classify observeIn x) = none := by
        rw [commutes, hx]
        rfl
      exact False.elim (defined absent)
    | some y => exact ⟨x, y, rfl, hx⟩
  · rintro ⟨x, y, rfl, hx⟩
    rw [commutes, hx]
    intro h
    cases h

/-! ## Explicit observation-context closure derives congruence -/

/-- An actual original coordinate, with its fixed interpretation, realizes this
observation. The family is not enlarged after a conflicting result is found. -/
def RepresentedObservation
    (observe : X → (q : Query) → Value q) {Result : Type z}
    (test : X → Result) : Prop :=
  ∃ coordinate : Query, ∃ read : Value coordinate → Result,
    ∀ x, read (observe x coordinate) = test x

theorem represented_observation_agrees
    (observe : X → (q : Query) → Value q) {Result : Type z}
    (test : X → Result) (represented : RepresentedObservation observe test)
    {x y : X} (equivalent : Equivalent observe x y) : test x = test y := by
  obtain ⟨coordinate, read, hread⟩ := represented
  exact (hread x).symm.trans ((congrArg read (equivalent coordinate)).trans (hread y))

/-- Domain and output tests must already be available as original input
contexts. Their separate interpretation equations derive pairwise congruence. -/
theorem original_contexts_derive_partial_congruence
    (observeIn : X → (q : Query) → Value q)
    (observeOut : Y → (q : OutQuery) → OutValue q) (f : X → Option Y)
    (domainContext : RepresentedObservation observeIn (fun x => (f x).isSome))
    (outputContexts : ∀ q, RepresentedObservation observeIn
      (fun x => Option.map (fun result => observeOut result q) (f x))) :
    (∀ x y, Equivalent observeIn x y → (f x = none ↔ f y = none)) ∧
    (∀ x y a b, Equivalent observeIn x y →
      f x = some a → f y = some b → Equivalent observeOut a b) := by
  constructor
  · intro x y equivalent
    have domains := represented_observation_agrees observeIn
      (fun x => (f x).isSome) domainContext equivalent
    cases hx : f x <;> cases hy : f y <;> simp_all
  · intro x y a b equivalent hx hy q
    have outputs := represented_observation_agrees observeIn
      (fun x => Option.map (fun result => observeOut result q) (f x))
      (outputContexts q) equivalent
    change Option.map (fun result => observeOut result q) (f x) =
      Option.map (fun result => observeOut result q) (f y) at outputs
    rw [hx, hy] at outputs
    exact Option.some.inj outputs

/-- Exact partial descent from the original context tests, rather than an
assumed pairwise operation-preservation equation. -/
theorem unique_partial_descent_of_original_contexts
    (observeIn : X → (q : Query) → Value q)
    (observeOut : Y → (q : OutQuery) → OutValue q) (f : X → Option Y)
    (domainContext : RepresentedObservation observeIn (fun x => (f x).isSome))
    (outputContexts : ∀ q, RepresentedObservation observeIn
      (fun x => Option.map (fun result => observeOut result q) (f x))) :
    ∃! reduced : CanonicalQuotient observeIn → Option (CanonicalQuotient observeOut),
      ∀ x, reduced (classify observeIn x) = Option.map (classify observeOut) (f x) := by
  obtain ⟨domains, outputs⟩ := original_contexts_derive_partial_congruence
    observeIn observeOut f domainContext outputContexts
  exact unique_partial_descent observeIn observeOut f domains outputs

/-!
For a many-argument operation this criterion applies to each one-hole context
with the other original standing arguments fixed, or directly to an already
specified tuple observation family. The theorem does not assert that a short
list of primitive observations contains these contexts. That coverage must be
proved for the original family; otherwise descent remains unestablished.
-/

end PartialOperations

#print axioms equivalent_iff_profile_eq
#print axioms classify_eq_iff
#print axioms unique_factorization
#print axioms coordinate_recovery
#print axioms unique_exact_classifier
#print axioms canonical_profile_realization
#print axioms unique_classifier_isomorphism
#print axioms partial_output_classes_agree
#print axioms unique_partial_descent
#print axioms partial_descent_domain_image
#print axioms represented_observation_agrees
#print axioms original_contexts_derive_partial_congruence
#print axioms unique_partial_descent_of_original_contexts

end AASC.KernelReference.ContextualQuotient
