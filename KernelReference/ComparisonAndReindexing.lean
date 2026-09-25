import KernelReference.Authorization
import KernelReference.ContextualQuotient

/-!
# Semantic comparison, finite zigzags, and lawful reindexing

The semantic comparison is built from every coordinate of the independently
fixed observation profile. Its proof-valued arrows form a thin groupoid. A
primitive instruction family need not generate all those arrows; it does so
exactly under the explicit finite-zigzag completeness condition. Symmetric
comparison paths are not directed execution paths.

Reindexing starts from a node equivalence, preservation/reflection of the
actual dependency edges, and preservation of the local checks. It constructs
the complete-predecessor retained extension and derives support preservation.
No global support-preservation field is assumed. Concrete uses must establish
that the node identification preserves their original occurrences and uses.
These results construct neither new role occupants nor unique occupants.
-/

namespace AASC.KernelReference.ComparisonAndReindexing

universe u v w u' v'

section Comparison

variable {X : Type u} {Query : Type v} {Value : Query → Type w}
variable (observe : X → (q : Query) → Value q)

/-- One proof-valued arrow exactly when all original observations agree. -/
abbrev SemanticArrow (x y : X) := ContextualQuotient.Equivalent observe x y

def comparisonIdentity (x : X) : SemanticArrow observe x x := fun _ => rfl

def comparisonInverse {x y : X} (h : SemanticArrow observe x y) :
    SemanticArrow observe y x := fun q => (h q).symm

def comparisonCompose {x y z : X}
    (h : SemanticArrow observe x y) (k : SemanticArrow observe y z) :
    SemanticArrow observe x z := fun q => (h q).trans (k q)

theorem comparison_arrow_unique {x y : X} (h k : SemanticArrow observe x y) : h = k :=
  Subsingleton.elim _ _

theorem comparison_identity_left {x y : X} (h : SemanticArrow observe x y) :
    comparisonCompose observe (comparisonIdentity observe x) h = h := Subsingleton.elim _ _

theorem comparison_identity_right {x y : X} (h : SemanticArrow observe x y) :
    comparisonCompose observe h (comparisonIdentity observe y) = h := Subsingleton.elim _ _

theorem comparison_associative {a b c d : X}
    (h : SemanticArrow observe a b) (k : SemanticArrow observe b c)
    (l : SemanticArrow observe c d) :
    comparisonCompose observe (comparisonCompose observe h k) l =
      comparisonCompose observe h (comparisonCompose observe k l) := Subsingleton.elim _ _

theorem comparison_inverse_left {x y : X} (h : SemanticArrow observe x y) :
    comparisonCompose observe (comparisonInverse observe h) h = comparisonIdentity observe y :=
  Subsingleton.elim _ _

theorem comparison_inverse_right {x y : X} (h : SemanticArrow observe x y) :
    comparisonCompose observe h (comparisonInverse observe h) = comparisonIdentity observe x :=
  Subsingleton.elim _ _

theorem semantic_comparison_equivalence : Equivalence (SemanticArrow observe) :=
  ⟨comparisonIdentity observe, comparisonInverse observe, comparisonCompose observe⟩

/-- Every comparison preserving the original profile is included, even without
assuming that the proposed relation already satisfies groupoid laws. -/
theorem semantic_comparison_maximal (other : X → X → Prop)
    (preserves : ∀ x y, other x y → ∀ q, observe x q = observe y q) :
    ∀ x y, other x y → SemanticArrow observe x y := preserves

/-- Finite undirected primitive paths, including the length-zero path. -/
abbrev Zigzag (step : X → X → Prop) :=
  Relation.ReflTransGen (fun x y => step x y ∨ step y x)

theorem zigzag_inverse {step : X → X → Prop} {x y : X} (h : Zigzag step x y) :
    Zigzag step y x := by
  induction h with
  | refl => exact .refl
  | tail path edge ih =>
      exact ih.head (edge.elim Or.inr Or.inl)

theorem primitive_zigzag_preserves_profile (step : X → X → Prop)
    (primitivePreserves : ∀ x y, step x y → SemanticArrow observe x y)
    {x y : X} (path : Zigzag step x y) : SemanticArrow observe x y := by
  induction path with
  | refl => exact comparisonIdentity observe _
  | @tail y z path edge ih =>
      rcases edge with forward | backward
      · exact comparisonCompose observe ih (primitivePreserves _ _ forward)
      · exact comparisonCompose observe ih
          (comparisonInverse observe (primitivePreserves _ _ backward))

def GeneratorComplete (step : X → X → Prop) : Prop :=
  ∀ x y, SemanticArrow observe x y → Zigzag step x y

/-- Equality with the semantic classes needs precisely the converse inclusion:
every semantically equivalent pair has an actual finite primitive zigzag. -/
theorem generated_classes_eq_iff_complete (step : X → X → Prop)
    (primitivePreserves : ∀ x y, step x y → SemanticArrow observe x y) :
    (∀ x y, Zigzag step x y ↔ SemanticArrow observe x y) ↔ GeneratorComplete observe step := by
  constructor
  · intro exact x y equivalent
    exact (exact x y).mpr equivalent
  · intro complete x y
    exact ⟨primitive_zigzag_preserves_profile observe step primitivePreserves,
      complete x y⟩

/-- The criterion also holds as literal equality of the two relations. -/
theorem generated_relation_eq_iff_complete (step : X → X → Prop)
    (primitivePreserves : ∀ x y, step x y → SemanticArrow observe x y) :
    Zigzag step = SemanticArrow observe ↔ GeneratorComplete observe step := by
  constructor
  · intro same x y h
    rw [same]
    exact h
  · intro complete
    funext x y
    exact propext ((generated_classes_eq_iff_complete observe step primitivePreserves).mpr complete x y)

theorem empty_generators_zigzag_iff_eq (x y : X) :
    Zigzag (fun _ _ : X => False) x y ↔ x = y := by
  constructor
  · intro path
    induction path with
    | refl => rfl
    | tail path edge ih => exact edge.elim False.elim False.elim
  · rintro rfl
    exact .refl

end Comparison

section Reindexing

open _root_.KernelReference.Authorization

variable {Node : Type u} {NewNode : Type v}
variable (G : SupportGraph Node) (H : SupportGraph NewNode) (rename : Node ≃ NewNode)
variable (edgeIff : ∀ a b, H.edge (rename a) (rename b) ↔ G.edge a b)

/-- Full predecessor completeness is derived from the equivalence and the
edge biconditional, rather than supplied as a global support certificate. -/
def retainedExtensionOfEquiv
    (oldLocal : Node → Prop) (newLocal : NewNode → Prop)
    (localIff : ∀ n, newLocal (rename n) ↔ oldLocal n) :
    RetainedExtension G H oldLocal newLocal where
  embed := rename
  injective := rename.injective
  local_iff := localIff
  edge_forward := fun {p n} hp => (edgeIff p n).mpr hp
  predecessors_complete := by
    intro q n hq
    refine ⟨rename.symm q, (rename.apply_symm_apply q).symm, ?_⟩
    apply (edgeIff (rename.symm q) n).mp
    simpa only [rename.apply_symm_apply] using hq

include edgeIff

theorem ancestors_preserved_and_reflected (a b : Node) :
    H.Ancestor (rename a) (rename b) ↔ G.Ancestor a b := by
  constructor
  · intro path
    have backwards : ∀ x y, H.edge x y → G.edge (rename.symm x) (rename.symm y) := by
      intro x y edge
      apply (edgeIff (rename.symm x) (rename.symm y)).mp
      simpa only [rename.apply_symm_apply] using edge
    have transported := path.lift rename.symm backwards
    simpa only [rename.symm_apply_apply] using transported
  · intro path
    exact path.lift rename (fun a b h => (edgeIff a b).mpr h)

theorem support_preserved_by_reindexing
    (oldLocal : Node → Prop) (newLocal : NewNode → Prop)
    (localIff : ∀ n, newLocal (rename n) ↔ oldLocal n) (n : Node) :
    Supported H newLocal (rename n) ↔ Supported G oldLocal n :=
  retained_support_iff (retainedExtensionOfEquiv G H rename edgeIff oldLocal newLocal localIff) n

/-- All the original ancestor checks are transported; checking a selected
subset of favorable ancestors would not establish this equivalence. -/
theorem complete_local_evidence_preserved
    (oldLocal : Node → Prop) (newLocal : NewNode → Prop)
    (localIff : ∀ n, newLocal (rename n) ↔ oldLocal n) (n : Node) :
    (∀ b, H.Ancestor b (rename n) → newLocal b) ↔
      (∀ a, G.Ancestor a n → oldLocal a) := by
  constructor
  · intro checked a ancestor
    exact (localIff a).mp (checked (rename a)
      ((ancestors_preserved_and_reflected G H rename edgeIff a n).mpr ancestor))
  · intro checked b ancestor
    have oldAncestor : G.Ancestor (rename.symm b) n := by
      apply (ancestors_preserved_and_reflected G H rename edgeIff (rename.symm b) n).mp
      simpa only [rename.apply_symm_apply] using ancestor
    have result := (localIff (rename.symm b)).mpr (checked _ oldAncestor)
    simpa only [rename.apply_symm_apply] using result

omit edgeIff

/-- Eligibility and joint compatibility supply local check preservation
separately. No conclusion about global support is a premise. -/
theorem role_data_preserves_local_check
    (oldEligible oldCompatible : Node → Prop)
    (newEligible newCompatible : NewNode → Prop)
    (eligibilityIff : ∀ n, newEligible (rename n) ↔ oldEligible n)
    (compatibilityIff : ∀ n, newCompatible (rename n) ↔ oldCompatible n) (n : Node) :
    (newEligible (rename n) ∧ newCompatible (rename n)) ↔
      (oldEligible n ∧ oldCompatible n) :=
  and_congr (eligibilityIff n) (compatibilityIff n)

include edgeIff

theorem role_reindexing_preserves_support
    (oldEligible oldCompatible : Node → Prop)
    (newEligible newCompatible : NewNode → Prop)
    (eligibilityIff : ∀ n, newEligible (rename n) ↔ oldEligible n)
    (compatibilityIff : ∀ n, newCompatible (rename n) ↔ oldCompatible n) (n : Node) :
    Supported H (fun x => newEligible x ∧ newCompatible x) (rename n) ↔
      Supported G (fun x => oldEligible x ∧ oldCompatible x) n :=
  support_preserved_by_reindexing G H rename edgeIff _ _
    (role_data_preserves_local_check rename oldEligible oldCompatible
      newEligible newCompatible eligibilityIff compatibilityIff) n

theorem role_reindexing_preserves_complete_evidence
    (oldEligible oldCompatible : Node → Prop)
    (newEligible newCompatible : NewNode → Prop)
    (eligibilityIff : ∀ n, newEligible (rename n) ↔ oldEligible n)
    (compatibilityIff : ∀ n, newCompatible (rename n) ↔ oldCompatible n) (n : Node) :
    (∀ b, H.Ancestor b (rename n) → newEligible b ∧ newCompatible b) ↔
      (∀ a, G.Ancestor a n → oldEligible a ∧ oldCompatible a) :=
  complete_local_evidence_preserved G H rename edgeIff _ _
    (role_data_preserves_local_check rename oldEligible oldCompatible
      newEligible newCompatible eligibilityIff compatibilityIff) n

end Reindexing

namespace Examples

def constantProfile (_ : Bool) (_ : Unit) : Unit := ()

theorem comparison_does_not_supply_generators :
    SemanticArrow constantProfile false true ∧
      ¬ Zigzag (fun _ _ : Bool => False) false true := by
  refine ⟨fun _ => rfl, ?_⟩
  intro path
  have bad : false = true := (empty_generators_zigzag_iff_eq false true).mp path
  cases bad

theorem constant_profile_empty_generators_not_complete :
    ¬ GeneratorComplete constantProfile (fun _ _ : Bool => False) := by
  intro complete
  exact comparison_does_not_supply_generators.2
    (complete false true comparison_does_not_supply_generators.1)

def forwardStep (a b : Bool) : Prop := a = false ∧ b = true

/-- Reversal is legal for semantic comparison, but not thereby an executable
primitive step or directed path. -/
theorem undirected_comparison_not_directed_execution :
    Zigzag forwardStep true false ∧ ¬ Relation.ReflTransGen forwardStep true false := by
  refine ⟨.single (Or.inr ⟨rfl, rfl⟩), ?_⟩
  intro directed
  have noOutgoing : ∀ b, ¬ forwardStep true b := by
    intro b h
    cases h.1
  have bad : false = true := (Relation.reflTransGen_iff_eq noOutgoing).mp directed
  cases bad


open _root_.KernelReference.Authorization

/-- Independent source records; no unlisted predecessor is introduced. -/
def discreteGraph : SupportGraph Bool where
  edge _ _ := False
  acyclic n h := by
    cases h with
    | single impossible => exact impossible
    | tail previous impossible => exact impossible

def flipNames : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

/-- A nonidentity renaming transports eligibility and compatibility checks,
then obtains global support through the theorem rather than assuming it. -/
theorem nonidentity_role_reindexing :
    Supported discreteGraph (fun b => True ∧ b = true) (flipNames false) ↔
      Supported discreteGraph (fun b => True ∧ b = false) false := by
  apply role_reindexing_preserves_support discreteGraph discreteGraph flipNames
    (fun _ _ => Iff.rfl) (fun _ => True) (fun b => b = false)
    (fun _ => True) (fun b => b = true) (fun _ => Iff.rfl)
  intro b
  cases b <;> simp [flipNames]

theorem reindexed_positive_record :
    Supported discreteGraph (fun b => True ∧ b = true) (flipNames false) := by
  apply nonidentity_role_reindexing.mpr
  exact Supported.intro false ⟨trivial, rfl⟩ (fun _ impossible => False.elim impossible)

end Examples

end AASC.KernelReference.ComparisonAndReindexing
