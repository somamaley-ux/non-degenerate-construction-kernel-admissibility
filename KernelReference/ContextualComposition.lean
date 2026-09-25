import KernelReference.ContextualQuotient
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

/-!
# Finite heterogeneous contextual composition

The original observation family at each input sort must interpret the domain
test and every pulled-back optional output coordinate of each one-hole context.
The other arguments range over all original standing values, not a selected
list of named constants. Pairwise tuple congruence is derived by finitely many
coordinate replacements; it is not an input field.

The product classifier and the equivalence between the tuple quotient and the
product of sort quotients are constructed. The quotient equivalence itself
allows arbitrary index types. Operation congruence uses a finite index type,
including an empty one, and thus covers every finite heterogeneous arity.

These theorems do not certify that a chosen physical task's observation family
is complete. Its interpretation and the specified one-hole context witnesses
remain original-domain obligations.
-/

namespace AASC.KernelReference.ContextualComposition

open ContextualQuotient

universe u v w z u' v' w' z'

section Products

variable {I : Type u} {X : I → Type v} {Query : I → Type w}
    {Value : (i : I) → Query i → Type z}
    (observe : (i : I) → X i → (q : Query i) → Value i q)

/-- The original component observations, retaining their sort tags. -/
def tupleObserve (args : (i : I) → X i) (q : Sigma Query) : Value q.1 q.2 :=
  observe q.1 (args q.1) q.2

def ComponentEquivalent (left right : (i : I) → X i) : Prop :=
  ∀ i, Equivalent (observe i) (left i) (right i)

theorem tuple_equivalent_iff (left right : (i : I) → X i) :
    Equivalent (tupleObserve observe) left right ↔
      ComponentEquivalent observe left right := by
  constructor
  · intro h i q
    exact h ⟨i, q⟩
  · intro h q
    exact h q.1 q.2

/-- The tuple of the original component quotient classes. -/
def classifyTuple (args : (i : I) → X i) :
    (i : I) → CanonicalQuotient (observe i) :=
  fun i => classify (observe i) (args i)

theorem classifyTuple_eq_iff (left right : (i : I) → X i) :
    classifyTuple observe left = classifyTuple observe right ↔
      ComponentEquivalent observe left right := by
  constructor
  · intro same i
    exact (classify_eq_iff (observe i) (left i) (right i)).mp (congrFun same i)
  · intro equivalent
    exact funext (fun i => (classify_eq_iff (observe i) (left i) (right i)).mpr
      (equivalent i))

/-- Representatives are chosen only to prove surjectivity. No inhabitance of
an input sort is assumed; empty products and empty component sorts are allowed. -/
theorem classifyTuple_surjective : Function.Surjective (classifyTuple observe) := by
  classical
  intro classes
  have witnesses : ∀ i, ∃ x : X i, classify (observe i) x = classes i :=
    fun i => classify_surjective (observe i) (classes i)
  refine ⟨fun i => Classical.choose (witnesses i), ?_⟩
  exact funext (fun i => Classical.choose_spec (witnesses i))

/-- The product of sort quotients is derived as the exact quotient of tuples,
with the unique comparison forced by the original classification maps. -/
theorem unique_tuple_quotient_equiv :
    ∃! e : CanonicalQuotient (tupleObserve observe) ≃
        ((i : I) → CanonicalQuotient (observe i)),
      ∀ args, e (classify (tupleObserve observe) args) = classifyTuple observe args := by
  apply unique_exact_classifier (tupleObserve observe) (classifyTuple observe)
    (classifyTuple_surjective observe)
  intro left right
  exact (classifyTuple_eq_iff observe left right).trans
    (tuple_equivalent_iff observe left right).symm

noncomputable def tupleQuotientEquiv :
    CanonicalQuotient (tupleObserve observe) ≃
      ((i : I) → CanonicalQuotient (observe i)) :=
  Classical.choose (unique_tuple_quotient_equiv observe)

theorem tupleQuotientEquiv_classify (args : (i : I) → X i) :
    tupleQuotientEquiv observe (classify (tupleObserve observe) args) =
      classifyTuple observe args :=
  (Classical.choose_spec (unique_tuple_quotient_equiv observe)).1 args

end Products

section FiniteReplacement

variable {I : Type u} [Fintype I] [DecidableEq I] {X : I → Type v}

/-- Finite replacement is proved independently of observation semantics.
Every coordinate has its own carrier and its own comparison relation. -/
theorem finite_coordinate_replacement {Result : Type z'}
    (relation : (i : I) → X i → X i → Prop)
    (F : ((i : I) → X i) → Result)
    (oneHole : ∀ base i a b, relation i a b →
      F (Function.update base i a) = F (Function.update base i b))
    {left right : (i : I) → X i}
    (equivalent : ∀ i, relation i (left i) (right i)) : F left = F right := by
  let patch (s : Finset I) : (i : I) → X i :=
    fun i => if i ∈ s then right i else left i
  have allPatches : ∀ s : Finset I, F (patch s) = F left := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [patch]
    | @insert i s fresh ih =>
      have restore : Function.update (patch s) i (left i) = patch s := by
        apply Function.update_eq_self_iff.mpr
        simp [patch, fresh]
      have advance : Function.update (patch s) i (right i) = patch (insert i s) := by
        funext j
        by_cases same : j = i
        · subst j
          simp [patch]
        · simp [patch, same]
      have step := oneHole (patch s) i (left i) (right i) (equivalent i)
      rw [restore, advance] at step
      exact step.symm.trans ih
  have finished := allPatches Finset.univ
  simpa [patch] using finished.symm

end FiniteReplacement

section ObservedRelations

variable {I : Type u} [Fintype I] [DecidableEq I]
    {X : I → Type v} {Query : I → Type w}
    {Value : (i : I) → Query i → Type z}

/-- Fixed observed relations and other observations also respect finite
component replacement, when their original one-hole tests are represented. -/
theorem finite_tuple_observation_agrees {Result : Type z'}
    (observe : (i : I) → X i → (q : Query i) → Value i q)
    (test : ((i : I) → X i) → Result)
    (contexts : ∀ base i, RepresentedObservation (observe i)
      (fun x => test (Function.update base i x)))
    {left right : (i : I) → X i}
    (equivalent : ComponentEquivalent observe left right) :
    test left = test right := by
  apply finite_coordinate_replacement (fun i => Equivalent (observe i)) test
    (left := left) (right := right) ?_ equivalent
  intro base i a b same
  exact represented_observation_agrees (observe i)
    (fun x => test (Function.update base i x)) (contexts base i) same

end ObservedRelations

section PartialOperations

variable {I : Type u} [Fintype I] [DecidableEq I]
    {X : I → Type v} {Query : I → Type w}
    {Value : (i : I) → Query i → Type z}
    {Y : Type u'} {OutQuery : Type v'} {OutValue : OutQuery → Type w'}
    (observe : (i : I) → X i → (q : Query i) → Value i q)
    (observeOut : Y → (q : OutQuery) → OutValue q)
    (f : ((i : I) → X i) → Option Y)
    (domainContexts : ∀ base i, RepresentedObservation (observe i)
      (fun x => (f (Function.update base i x)).isSome))
    (outputContexts : ∀ base i q, RepresentedObservation (observe i)
      (fun x => Option.map (fun y => observeOut y q) (f (Function.update base i x))))

include domainContexts outputContexts

omit [Fintype I] in
/-- Each one-hole context derives agreement of the output class, including
definedness, from its original observation interpretations. -/
theorem one_hole_output_classes_agree
    (base : (i : I) → X i) (i : I) (a b : X i)
    (equivalent : Equivalent (observe i) a b) :
    Option.map (classify observeOut) (f (Function.update base i a)) =
      Option.map (classify observeOut) (f (Function.update base i b)) := by
  obtain ⟨domains, outputs⟩ := original_contexts_derive_partial_congruence
    (observe i) observeOut (fun x => f (Function.update base i x))
    (domainContexts base i) (outputContexts base i)
  exact partial_output_classes_agree (observe i) observeOut
    (fun x => f (Function.update base i x)) domains outputs a b equivalent

/-- All finite argument replacements are derived from the separately
interpreted one-hole original contexts. No tuple congruence is assumed. -/
theorem finite_tuple_output_classes_agree
    (left right : (i : I) → X i)
    (equivalent : ComponentEquivalent observe left right) :
    Option.map (classify observeOut) (f left) =
      Option.map (classify observeOut) (f right) := by
  exact finite_coordinate_replacement
    (fun i => Equivalent (observe i))
    (fun args => Option.map (classify observeOut) (f args))
    (one_hole_output_classes_agree observe observeOut f domainContexts outputContexts)
    equivalent

theorem finite_tuple_partial_congruence :
    (∀ left right, ComponentEquivalent observe left right →
      (f left = none ↔ f right = none)) ∧
    (∀ left right a b, ComponentEquivalent observe left right →
      f left = some a → f right = some b → Equivalent observeOut a b) := by
  constructor
  · intro left right equivalent
    have agreed := finite_tuple_output_classes_agree observe observeOut f
      domainContexts outputContexts left right equivalent
    cases hl : f left <;> cases hr : f right <;> simp_all
  · intro left right a b equivalent hl hr
    have agreed := finite_tuple_output_classes_agree observe observeOut f
      domainContexts outputContexts left right equivalent
    rw [hl, hr] at agreed
    exact (classify_eq_iff observeOut a b).mp (Option.some.inj agreed)

/-- The induced operation on the tuple quotient is constructed from the
original one-hole tests, including its old application domain. -/
theorem unique_tuple_partial_descent :
    ∃! reduced : CanonicalQuotient (tupleObserve observe) →
        Option (CanonicalQuotient observeOut),
      ∀ args, reduced (classify (tupleObserve observe) args) =
        Option.map (classify observeOut) (f args) := by
  obtain ⟨domains, outputs⟩ := finite_tuple_partial_congruence observe observeOut f
    domainContexts outputContexts
  apply unique_partial_descent (tupleObserve observe) observeOut f
  · intro left right equivalent
    exact domains left right ((tuple_equivalent_iff observe left right).mp equivalent)
  · intro left right a b equivalent hl hr
    exact outputs left right a b
      ((tuple_equivalent_iff observe left right).mp equivalent) hl hr

/-- The induced operation has the manuscript's product-of-sort-quotients
domain. The tuple/product equivalence is constructed above, not postulated. -/
theorem unique_product_partial_descent :
    ∃! reduced : ((i : I) → CanonicalQuotient (observe i)) →
        Option (CanonicalQuotient observeOut),
      ∀ args, reduced (classifyTuple observe args) =
        Option.map (classify observeOut) (f args) := by
  obtain ⟨tupleReduced, tupleCommutes, _⟩ := unique_tuple_partial_descent
    observe observeOut f domainContexts outputContexts
  let reduced := fun classes => tupleReduced ((tupleQuotientEquiv observe).symm classes)
  have commutes : ∀ args, reduced (classifyTuple observe args) =
      Option.map (classify observeOut) (f args) := by
    intro args
    change tupleReduced ((tupleQuotientEquiv observe).symm
      (classifyTuple observe args)) = _
    rw [← tupleQuotientEquiv_classify observe args, Equiv.symm_apply_apply]
    exact tupleCommutes args
  refine ⟨reduced, commutes, ?_⟩
  intro other otherCommutes
  funext classes
  obtain ⟨args, rfl⟩ := classifyTuple_surjective observe classes
  exact (otherCommutes args).trans (commutes args).symm

omit domainContexts outputContexts [Fintype I] [DecidableEq I] in
/-- The original definedness answer is recovered on every tuple. This includes
nullary operations and excludes a new value for an old undefined application. -/
theorem product_partial_descent_definedness
    (reduced : ((i : I) → CanonicalQuotient (observe i)) →
      Option (CanonicalQuotient observeOut))
    (commutes : ∀ args, reduced (classifyTuple observe args) =
      Option.map (classify observeOut) (f args))
    (args : (i : I) → X i) :
    reduced (classifyTuple observe args) = none ↔ f args = none := by
  rw [commutes]
  cases f args <;> simp

omit domainContexts outputContexts [Fintype I] [DecidableEq I] in
/-- The descended operation is defined exactly on the image of the old
application domain; no previously undefined application acquires a value. -/
theorem product_partial_descent_domain_image
    (reduced : ((i : I) → CanonicalQuotient (observe i)) →
      Option (CanonicalQuotient observeOut))
    (commutes : ∀ args, reduced (classifyTuple observe args) =
      Option.map (classify observeOut) (f args))
    (classes : (i : I) → CanonicalQuotient (observe i)) :
    reduced classes ≠ none ↔
      ∃ args y, classifyTuple observe args = classes ∧ f args = some y := by
  constructor
  · intro defined
    obtain ⟨args, rfl⟩ := classifyTuple_surjective observe classes
    cases h : f args with
    | none =>
      have absent : reduced (classifyTuple observe args) = none := by
        rw [commutes, h]
        rfl
      exact False.elim (defined absent)
    | some y => exact ⟨args, y, rfl, h⟩
  · rintro ⟨args, y, rfl, h⟩
    rw [commutes, h]
    intro impossible
    cases impossible

end PartialOperations

#print axioms tuple_equivalent_iff
#print axioms classifyTuple_eq_iff
#print axioms classifyTuple_surjective
#print axioms unique_tuple_quotient_equiv
#print axioms tupleQuotientEquiv_classify
#print axioms finite_coordinate_replacement
#print axioms finite_tuple_observation_agrees
#print axioms one_hole_output_classes_agree
#print axioms finite_tuple_output_classes_agree
#print axioms finite_tuple_partial_congruence
#print axioms unique_tuple_partial_descent
#print axioms unique_product_partial_descent
#print axioms product_partial_descent_definedness
#print axioms product_partial_descent_domain_image

end AASC.KernelReference.ContextualComposition
