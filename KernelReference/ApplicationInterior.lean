import Mathlib.Data.Fin.Basic

/-!
# Licensed applications, the full interior, and finite generated closure

`X s` is the fixed standing carrier at sort `s`. Operations retain their own
partial graphs. Licensed application means membership in those graphs, not
merely standing of an argument. Finite closure is generated below, not supplied
as an axiom or a field asserting closedness.
-/

namespace KernelReference.ApplicationInterior

universe u v

variable {SortIndex : Type u} (X : SortIndex → Type v)

abbrev Presentation := Sigma X

/-- A finite-arity typed partial operation with its original graph. -/
structure Operation where
  arity : Nat
  inputSort : Fin arity → SortIndex
  outputSort : SortIndex
  evaluate : ((i : Fin arity) → X (inputSort i)) → Option (X outputSort)

namespace Operation

variable {X}

abbrev Inputs (operation : Operation X) :=
  (i : Fin operation.arity) → X (operation.inputSort i)

/-- Identity is an explicit operation, not permission for arbitrary application. -/
def identity (sort : SortIndex) : Operation X where
  arity := 1
  inputSort _ := sort
  outputSort := sort
  evaluate args := some (args 0)

end Operation

variable {X}

structure RawApplication (X : SortIndex → Type v) where
  operation : Operation X
  arguments : operation.Inputs

def Licensed (allowed : Operation X → Prop) (request : RawApplication X) : Prop :=
  allowed request.operation ∧ ∃ value, request.operation.evaluate request.arguments = some value

abbrev Application (allowed : Operation X → Prop) :=
  {request : RawApplication X // Licensed allowed request}

/-- The domain witness supplies a result in the fixed operation graph. -/
noncomputable def evaluate {allowed : Operation X → Prop}
    (application : Application allowed) : Presentation X :=
  ⟨application.val.operation.outputSort, Classical.choose application.property.2⟩

theorem evaluation_has_original_graph {allowed : Operation X → Prop}
    (application : Application allowed) :
    application.val.operation.evaluate application.val.arguments =
      some (Classical.choose application.property.2) :=
  Classical.choose_spec application.property.2

theorem licensed_result_unique {allowed : Operation X → Prop}
    (application : Application allowed)
    {left right : X application.val.operation.outputSort}
    (hl : application.val.operation.evaluate application.val.arguments = some left)
    (hr : application.val.operation.evaluate application.val.arguments = some right) :
    left = right :=
  Option.some.inj (hl.symm.trans hr)

/-- A proposed result graph using only original operation pairs has no larger domain.
The premise checks each proposed pair, rather than assuming domain inclusion. -/
theorem licensed_domain_maximal (allowed : Operation X → Prop)
    (candidate : (request : RawApplication X) → X request.operation.outputSort → Prop)
    (sound : ∀ request value, candidate request value →
      allowed request.operation ∧ request.operation.evaluate request.arguments = some value) :
    ∀ request, (∃ value, candidate request value) → Licensed allowed request := by
  rintro request ⟨value, proposed⟩
  obtain ⟨admitted, originalPair⟩ := sound request value proposed
  exact ⟨admitted, value, originalPair⟩

/-- Soundness and exhaustiveness determine the complete application domain. -/
theorem full_application_domain_unique (allowed : Operation X → Prop)
    (domain : RawApplication X → Prop)
    (sound : ∀ request, domain request → Licensed allowed request)
    (exhaustive : ∀ request, Licensed allowed request → domain request) :
    domain = Licensed allowed := by
  funext request
  exact propext ⟨sound request, exhaustive request⟩

def identityRequest (sort : SortIndex) (value : X sort) : RawApplication X :=
  ⟨Operation.identity sort, fun _ => value⟩

theorem identity_application_licensed (allowed : Operation X → Prop)
    (identities : ∀ sort, allowed (Operation.identity sort))
    (sort : SortIndex) (value : X sort) : Licensed allowed (identityRequest sort value) :=
  ⟨identities sort, value, rfl⟩

theorem identity_application_evaluates (allowed : Operation X → Prop)
    (identities : ∀ sort, allowed (Operation.identity sort))
    (sort : SortIndex) (value : X sort) :
    evaluate ⟨identityRequest sort value,
      identity_application_licensed allowed identities sort value⟩ = ⟨sort, value⟩ := by
  have h := evaluation_has_original_graph
    (⟨identityRequest sort value,
      identity_application_licensed allowed identities sort value⟩ : Application allowed)
  change some value = some _ at h
  have hv := Option.some.inj h
  exact congrArg (fun v => (⟨sort, v⟩ : Presentation X)) hv.symm

theorem unary_composition_domain {A : Type u} {B C : Type v}
    (f : A → Option B) (g : B → Option C) (x : A) :
    (∃ output, (f x).bind g = some output) ↔
      ∃ middle, f x = some middle ∧ ∃ output, g middle = some output := by
  cases f x <;> simp

/-- Equality of old graphs excludes new values at their old undefined inputs. -/
theorem unchanged_graph_preserves_undefined {A : Type u} {B : Type v}
    (old revised : A → Option B)
    (sameGraph : ∀ input output, old input = some output ↔ revised input = some output)
    {input : A} (undefined : old input = none) : revised input = none := by
  cases h : revised input with
  | none => rfl
  | some output =>
      have oldValue := (sameGraph input output).2 h
      rw [undefined] at oldValue
      cases oldValue

def Closed (allowed : Operation X → Prop) (region : Presentation X → Prop) : Prop :=
  ∀ operation, allowed operation → ∀ arguments : operation.Inputs,
    (∀ i, region ⟨operation.inputSort i, arguments i⟩) →
    ∀ value, operation.evaluate arguments = some value → region ⟨operation.outputSort, value⟩

/-- The least closure is constructed by finite uses of the original operations. -/
inductive Generated (allowed : Operation X → Prop) (seed : Presentation X → Prop) :
    Presentation X → Prop
  | seed {point} : seed point → Generated allowed seed point
  | apply (operation : Operation X) : allowed operation →
      (arguments : operation.Inputs) →
      (∀ i, Generated allowed seed ⟨operation.inputSort i, arguments i⟩) →
      {value : X operation.outputSort} → operation.evaluate arguments = some value →
      Generated allowed seed ⟨operation.outputSort, value⟩

theorem generated_contains_seed {allowed : Operation X → Prop}
    {seed : Presentation X → Prop} {point : Presentation X} (h : seed point) :
    Generated allowed seed point := .seed h

theorem generated_closed (allowed : Operation X → Prop) (seed : Presentation X → Prop) :
    Closed allowed (Generated allowed seed) := by
  intro operation admitted arguments ih value result
  exact Generated.apply operation admitted arguments ih result

theorem generated_least {allowed : Operation X → Prop}
    {seed region : Presentation X → Prop}
    (closed : Closed allowed region) (contains : ∀ point, seed point → region point)
    {point : Presentation X} (generated : Generated allowed seed point) : region point := by
  induction generated with
  | seed h => exact contains _ h
  | apply operation admitted arguments prior result ih =>
      exact closed operation admitted arguments ih _ result

theorem least_closed_extension_unique (allowed : Operation X → Prop)
    (seed region : Presentation X → Prop)
    (closed : Closed allowed region) (contains : ∀ point, seed point → region point)
    (least : ∀ candidate, Closed allowed candidate →
      (∀ point, seed point → candidate point) → ∀ point, region point → candidate point) :
    region = Generated allowed seed := by
  funext point
  exact propext ⟨least _ (generated_closed allowed seed)
    (fun _ h => Generated.seed h) point, generated_least closed contains⟩

theorem full_interior_closed (allowed : Operation X → Prop) :
    Closed allowed (fun _ => True) := by
  intro _ _ _ _ _ _
  trivial

theorem full_interior_greatest_closed (allowed : Operation X → Prop) :
    Closed allowed (fun _ => True) ∧
      ∀ region, Closed allowed region → ∀ point, region point → True :=
  ⟨full_interior_closed allowed, fun _ _ _ _ => True.intro⟩

theorem generated_full_interior (allowed : Operation X → Prop) :
    Generated allowed (fun _ => True) = (fun _ => True) := by
  funext point
  exact propext ⟨fun _ => True.intro, fun h => Generated.seed h⟩

/-- Finite stages include old elements and every licensed finite-arity output. -/
inductive AtStage (allowed : Operation X → Prop) (seed : Presentation X → Prop) :
    Nat → Presentation X → Prop
  | seed {point} : seed point → AtStage allowed seed 0 point
  | retain {stage point} : AtStage allowed seed stage point →
      AtStage allowed seed (stage + 1) point
  | apply {stage} (operation : Operation X) : allowed operation →
      (arguments : operation.Inputs) →
      (∀ i, AtStage allowed seed stage ⟨operation.inputSort i, arguments i⟩) →
      {value : X operation.outputSort} → operation.evaluate arguments = some value →
      AtStage allowed seed (stage + 1) ⟨operation.outputSort, value⟩

theorem stage_monotone {allowed : Operation X → Prop} {seed : Presentation X → Prop}
    {n m : Nat} {point : Presentation X} (hnm : n ≤ m)
    (h : AtStage allowed seed n point) : AtStage allowed seed m point := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact AtStage.retain ih

theorem finite_family_has_stage_bound (n : Nat) (stage : Fin n → Nat) :
    ∃ bound, ∀ i, stage i ≤ bound := by
  induction n with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨bound, hb⟩ := ih (fun i => stage i.succ)
      refine ⟨max (stage 0) bound, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Nat.le_max_left _ _
      · exact (hb j).trans (Nat.le_max_right _ _)

theorem stage_implies_generated {allowed : Operation X → Prop}
    {seed : Presentation X → Prop} {n : Nat} {point : Presentation X}
    (h : AtStage allowed seed n point) : Generated allowed seed point := by
  induction h with
  | seed h => exact Generated.seed h
  | retain h ih => exact ih
  | apply operation admitted arguments prior result ih =>
      exact Generated.apply operation admitted arguments ih result

/-- The finite arities supply one common stage for all inputs; nullary uses are included. -/
theorem generated_implies_finite_stage {allowed : Operation X → Prop}
    {seed : Presentation X → Prop} {point : Presentation X}
    (h : Generated allowed seed point) : ∃ n, AtStage allowed seed n point := by
  classical
  induction h with
  | seed h => exact ⟨0, AtStage.seed h⟩
  | apply operation admitted arguments prior result ih =>
      let levels : Fin operation.arity → Nat := fun i => Classical.choose (ih i)
      obtain ⟨bound, hb⟩ := finite_family_has_stage_bound operation.arity levels
      refine ⟨bound + 1, AtStage.apply operation admitted arguments ?_ result⟩
      intro i
      exact stage_monotone (hb i) (Classical.choose_spec (ih i))

theorem generated_iff_finite_stage (allowed : Operation X → Prop)
    (seed : Presentation X → Prop) (point : Presentation X) :
    Generated allowed seed point ↔ ∃ n, AtStage allowed seed n point :=
  ⟨generated_implies_finite_stage, fun ⟨_, h⟩ => stage_implies_generated h⟩

/-! The ambient statement makes explicit which points count as standing. -/

section AmbientInterior

variable {Ambient : Type u} (standing : Ambient → Prop)

def FullInterior (region : Ambient → Prop) : Prop :=
  (∀ point, region point → standing point) ∧ (∀ point, standing point → region point)

theorem full_interior_unique {region : Ambient → Prop}
    (full : FullInterior standing region) : region = standing := by
  funext point
  exact propext ⟨full.1 point, full.2 point⟩

theorem full_interior_nonempty_iff {region : Ambient → Prop}
    (full : FullInterior standing region) :
    (∃ point, region point) ↔ ∃ point, standing point := by
  rw [full_interior_unique standing full]

end AmbientInterior

namespace Examples

abbrev BoolCarrier (_ : Unit) := Bool

def truthConstant : Operation BoolCarrier where
  arity := 0
  inputSort i := Fin.elim0 i
  outputSort := ()
  evaluate _ := some true

def exampleAllowed (operation : Operation BoolCarrier) : Prop :=
  operation = Operation.identity () ∨ operation = truthConstant

theorem example_identity_available (sort : Unit) :
    exampleAllowed (Operation.identity (X := BoolCarrier) sort) := by
  cases sort
  exact Or.inl rfl

/-- A licensed nullary operation enters closure even from an empty seed. -/
theorem empty_seed_generates_nullary :
    Generated exampleAllowed (fun _ => False) ⟨(), true⟩ := by
  exact Generated.apply truthConstant (Or.inr rfl)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) rfl

theorem true_region_closed :
    Closed exampleAllowed (fun point => point.2 = true) := by
  intro operation admitted arguments prior value result
  rcases admitted with rfl | rfl
  · change some (arguments (0 : Fin 1)) = some value at result
    exact (Option.some.inj result).symm.trans (prior (0 : Fin 1))
  · change some true = some value at result
    exact (Option.some.inj result).symm

/-- Full standing carriers do not imply that an arbitrary seed generates them. -/
theorem empty_seed_does_not_generate_full :
    ¬ Generated exampleAllowed (fun _ => False) ⟨(), false⟩ := by
  intro generated
  have h : false = true := generated_least true_region_closed
    (fun _ h => False.elim h) generated
  cases h

end Examples

end KernelReference.ApplicationInterior

#print axioms KernelReference.ApplicationInterior.evaluation_has_original_graph
#print axioms KernelReference.ApplicationInterior.licensed_result_unique
#print axioms KernelReference.ApplicationInterior.full_application_domain_unique
#print axioms KernelReference.ApplicationInterior.identity_application_licensed
#print axioms KernelReference.ApplicationInterior.identity_application_evaluates
#print axioms KernelReference.ApplicationInterior.unary_composition_domain
#print axioms KernelReference.ApplicationInterior.unchanged_graph_preserves_undefined
#print axioms KernelReference.ApplicationInterior.generated_closed
#print axioms KernelReference.ApplicationInterior.generated_least
#print axioms KernelReference.ApplicationInterior.least_closed_extension_unique
#print axioms KernelReference.ApplicationInterior.full_interior_greatest_closed
#print axioms KernelReference.ApplicationInterior.generated_full_interior
#print axioms KernelReference.ApplicationInterior.finite_family_has_stage_bound
#print axioms KernelReference.ApplicationInterior.generated_implies_finite_stage
#print axioms KernelReference.ApplicationInterior.generated_iff_finite_stage
#print axioms KernelReference.ApplicationInterior.full_interior_unique
#print axioms KernelReference.ApplicationInterior.full_interior_nonempty_iff

#print axioms KernelReference.ApplicationInterior.Examples.example_identity_available
#print axioms KernelReference.ApplicationInterior.Examples.empty_seed_generates_nullary
#print axioms KernelReference.ApplicationInterior.Examples.true_region_closed
#print axioms KernelReference.ApplicationInterior.Examples.empty_seed_does_not_generate_full

#print axioms KernelReference.ApplicationInterior.licensed_domain_maximal
