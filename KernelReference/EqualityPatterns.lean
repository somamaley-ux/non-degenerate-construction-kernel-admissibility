import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

/-!
Equality-only finite proposal interfaces. Full permutation symmetry is an
explicit property of this interface, not inferred from object determinacy.
The tuple index is finite; the carrier need not be finite or inhabited.
-/
namespace AASC.KernelReference.EqualityPatterns

universe u v w

def SamePattern {I : Type u} {P : Type v} (x y : I → P) : Prop :=
  ∀ i j, x i = x j ↔ y i = y j

theorem permutation_preserves_pattern {I : Type u} {P : Type v}
    (x : I → P) (e : Equiv.Perm P) : SamePattern x (e ∘ x) := by
  intro i j
  exact e.injective.eq_iff.symm

noncomputable def rangeMap {I : Type u} {P : Type v} (x y : I → P)
    (a : Set.range x) : Set.range y :=
  ⟨y (Classical.choose a.property), ⟨Classical.choose a.property, rfl⟩⟩

theorem rangeMap_at {I : Type u} {P : Type v} {x y : I → P}
    (same : SamePattern x y) (i : I) :
    rangeMap x y ⟨x i, ⟨i, rfl⟩⟩ = ⟨y i, ⟨i, rfl⟩⟩ := by
  apply Subtype.ext
  exact (same _ i).mp (Classical.choose_spec (show ∃ j, x j = x i from ⟨i, rfl⟩))

theorem rangeMap_bijective {I : Type u} {P : Type v} {x y : I → P}
    (same : SamePattern x y) : Function.Bijective (rangeMap x y) := by
  constructor
  · intro a b equal
    rcases a with ⟨a, ⟨i, rfl⟩⟩
    rcases b with ⟨b, ⟨j, rfl⟩⟩
    rw [rangeMap_at same i, rangeMap_at same j] at equal
    exact Subtype.ext ((same i j).mpr (congrArg Subtype.val equal))
  · rintro ⟨b, ⟨i, rfl⟩⟩
    exact ⟨⟨x i, ⟨i, rfl⟩⟩, rangeMap_at same i⟩

/-- A bijection of finite subsets extends to a permutation, even on an
    infinite carrier, by completing it on their finite union. -/
theorem finite_partial_equiv_extends {P : Type v} {s t : Set P}
    (hs : s.Finite) (ht : t.Finite) (e : s ≃ t) :
    ∃ p : Equiv.Perm P, ∀ a : s, p a = e a := by
  classical
  let U := s ∪ t
  have hU : U.Finite := hs.union ht
  letI : Finite U := hU.to_subtype
  let left : {a : U // a.val ∈ s} ≃ s :=
    { toFun := fun a => ⟨a.val.val, a.property⟩
      invFun := fun a => ⟨⟨a.val, Or.inl a.property⟩, a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let right : {a : U // a.val ∈ t} ≃ t :=
    { toFun := fun a => ⟨a.val.val, a.property⟩
      invFun := fun a => ⟨⟨a.val, Or.inr a.property⟩, a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let localEquiv := left.trans (e.trans right.symm)
  let localPerm : Equiv.Perm U := localEquiv.extendSubtype
  let fullPerm : Equiv.Perm P := localPerm.extendDomain (Equiv.refl U)
  refine ⟨fullPerm, ?_⟩
  intro a
  have localValue := localEquiv.extendSubtype_apply_of_mem
    (⟨a.val, Or.inl a.property⟩ : U) a.property
  have fullValue := localPerm.extendDomain_apply_image (Equiv.refl U)
    (⟨a.val, Or.inl a.property⟩ : U)
  change fullPerm a.val = (e a).val
  change fullPerm a.val = (localPerm ⟨a.val, Or.inl a.property⟩).val at fullValue
  rw [fullValue]
  exact congrArg Subtype.val localValue

/-- Equal realized equality patterns are precisely simultaneous permutation
    orbits. No permutation is postulated as a witness in the hypothesis. -/
theorem samePattern_iff_permutation {I : Type u} [Finite I] {P : Type v}
    (x y : I → P) :
    SamePattern x y ↔ ∃ p : Equiv.Perm P, ∀ i, p (x i) = y i := by
  constructor
  · intro same
    let e : Set.range x ≃ Set.range y := Equiv.ofBijective _ (rangeMap_bijective same)
    rcases finite_partial_equiv_extends (Set.finite_range x) (Set.finite_range y) e
      with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro i
    have result := hp ⟨x i, ⟨i, rfl⟩⟩
    exact result.trans (congrArg Subtype.val (rangeMap_at same i))
  · rintro ⟨p, hp⟩ i j
    constructor
    · intro equal
      rw [← hp i, ← hp j, equal]
    · intro equal
      exact p.injective ((hp i).trans (equal.trans (hp j).symm))

def patternSetoid (I : Type u) (P : Type v) : Setoid (I → P) where
  r := SamePattern
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h i j => (h i j).symm
      trans := fun h k i j => (h i j).trans (k i j) }

def Invariant {I : Type u} {P : Type v} {Z : Type w} (f : (I → P) → Z) : Prop :=
  ∀ (p : Equiv.Perm P) x, f (p ∘ x) = f x

/-- Every invariant scalar observation has exactly one factor through the
    quotient of realized equality patterns. -/
theorem invariant_unique_factorization {I : Type u} [Finite I] {P : Type v}
    {Z : Type w} (f : (I → P) → Z) (invariant : Invariant f) :
    ∃! g : Quotient (patternSetoid I P) → Z,
      ∀ x, g (Quotient.mk _ x) = f x := by
  have respects : ∀ x y, SamePattern x y → f x = f y := by
    intro x y same
    rcases (samePattern_iff_permutation x y).mp same with ⟨p, hp⟩
    have tuple : p ∘ x = y := funext hp
    rw [← tuple]
    exact (invariant p x).symm
  refine ⟨Quotient.lift f respects, ?_, ?_⟩
  · intro x
    rfl
  · intro g hg
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact hg x

theorem pattern_factor_is_invariant {I : Type u} {P : Type v} {Z : Type w}
    (g : Quotient (patternSetoid I P) → Z) :
    Invariant (fun x => g (Quotient.mk _ x)) := by
  intro p x
  exact congrArg g (Quotient.sound (fun i j => p.injective.eq_iff))

theorem invariant_unary_constant {P : Type v} {Z : Type w}
    (f : P → Z) (invariant : ∀ (p : Equiv.Perm P) a, f (p a) = f a)
    (a b : P) : f a = f b := by
  classical
  have h := invariant (Equiv.swap a b) a
  simpa only [Equiv.swap_apply_left] using h.symm

theorem no_permutation_fixed_point {P : Type v} [Nontrivial P] :
    ¬ ∃ a : P, ∀ p : Equiv.Perm P, p a = a := by
  classical
  rintro ⟨a, fixed⟩
  obtain ⟨b, different⟩ := exists_ne a
  have equal := fixed (Equiv.swap a b)
  exact different (by simpa only [Equiv.swap_apply_left] using equal)


/-- Two distinct ordered pairs have the same equality pattern, so an invariant
binary observation has one value on all off-diagonal pairs. -/
theorem invariant_binary_off_diagonal_constant {P : Type v} {Z : Type w}
    (f : P → P → Z)
    (invariant : ∀ (p : Equiv.Perm P) a b, f (p a) (p b) = f a b)
    {a b c d : P} (ab : a ≠ b) (cd : c ≠ d) : f a b = f c d := by
  let left : Bool → P := fun flag => if flag then b else a
  let right : Bool → P := fun flag => if flag then d else c
  have pattern : SamePattern left right := by
    intro i j
    cases i <;> cases j <;>
      simp [left, right, ab, cd, Ne.symm ab, Ne.symm cd]
  obtain ⟨p, hp⟩ := (samePattern_iff_permutation left right).mp pattern
  have ha : p a = c := hp false
  have hb : p b = d := hp true
  have result := invariant p a b
  rw [ha, hb] at result
  exact result.symm

theorem invariant_binary_diagonal_constant {P : Type v} {Z : Type w}
    (f : P → P → Z)
    (invariant : ∀ (p : Equiv.Perm P) a b, f (p a) (p b) = f a b)
    (a b : P) : f a a = f b b :=
  invariant_unary_constant (fun x => f x x) (fun p x => invariant p x x) a b

noncomputable def binaryPatternValue {P : Type v} {Z : Type w}
    (diagonal offDiagonal : Z) (a b : P) : Z := by
  classical
  exact if a = b then diagonal else offDiagonal

/-- Both binary patterns occur on a nontrivial carrier. Their values are uniquely
fixed by the original observation; no numerical scale is selected by symmetry. -/
theorem invariant_binary_unique_normal_form {P : Type v} [Nontrivial P]
    {Z : Type w} (f : P → P → Z)
    (invariant : ∀ (p : Equiv.Perm P) a b, f (p a) (p b) = f a b) :
    ∃! values : Z × Z,
      ∀ a b, f a b = binaryPatternValue values.1 values.2 a b := by
  classical
  obtain ⟨a, b, different⟩ := exists_pair_ne P
  have realizes : ∀ c d,
      f c d = binaryPatternValue (f a a) (f a b) c d := by
    intro c d
    by_cases same : c = d
    · subst d
      simpa [binaryPatternValue] using invariant_binary_diagonal_constant f invariant c a
    · simpa [binaryPatternValue, same] using
        invariant_binary_off_diagonal_constant f invariant same different
  refine ⟨(f a a, f a b), realizes, ?_⟩
  intro values hvalues
  apply Prod.ext
  · simpa [binaryPatternValue] using (hvalues a a).symm
  · simpa [binaryPatternValue, different] using (hvalues a b).symm

/-- Invariance under the transposition of two distinct points already conflicts
with strict total order. Transitivity is used to derive the forbidden self-loop. -/
theorem no_invariant_strict_total_order {P : Type v} [Nontrivial P]
    (lt : P → P → Prop)
    (invariant : ∀ (p : Equiv.Perm P) a b, lt (p a) (p b) ↔ lt a b)
    (irreflexive : ∀ a, ¬ lt a a)
    (transitive : ∀ {a b c}, lt a b → lt b c → lt a c)
    (totalOnDistinct : ∀ a b, a ≠ b → lt a b ∨ lt b a) : False := by
  classical
  obtain ⟨a, b, different⟩ := exists_pair_ne P
  have swapped : lt b a ↔ lt a b := by
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using
      invariant (Equiv.swap a b) a b
  rcases totalOnDistinct a b different with forward | backward
  · exact irreflexive a (transitive forward (swapped.mpr forward))
  · exact irreflexive a (transitive (swapped.mp backward) backward)

/-- A specified partition is realized by a tuple exactly when equality of its
entries is the equivalence relation of that partition. -/
def RealizesPartition {I : Type u} {P : Type v} (partition : Setoid I)
    (tuple : I → P) : Prop :=
  ∀ i j, partition.r i j ↔ tuple i = tuple j

/-- Realization assigns a distinct carrier element to each block. The embedding
is derived from a realization, and conversely constructs a realization. -/
theorem partition_realized_iff_embedding {I : Type u} {P : Type v}
    (partition : Setoid I) :
    (∃ tuple : I → P, RealizesPartition partition tuple) ↔
      Nonempty (Quotient partition ↪ P) := by
  constructor
  · rintro ⟨tuple, realizes⟩
    let reduced : Quotient partition → P :=
      Quotient.lift tuple (fun i j related => (realizes i j).mp related)
    have injective : Function.Injective reduced := by
      intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro i j same
      exact Quotient.sound ((realizes i j).mpr same)
    exact ⟨⟨reduced, injective⟩⟩
  · rintro ⟨embedding⟩
    refine ⟨fun i => embedding (Quotient.mk partition i), ?_⟩
    intro i j
    constructor
    · intro related
      exact congrArg embedding (Quotient.sound related)
    · intro same
      exact Quotient.exact (embedding.injective same)

/-- A partition with finitely many blocks is realized on a finite carrier
precisely when its block count fits. This also applies to every partition of
a finite tuple index; choosing a Fintype enumeration adds no realization premise. -/
theorem partition_realized_iff_block_count {I : Type u}
    {P : Type v} [Fintype P] (partition : Setoid I) [Fintype (Quotient partition)] :
    (∃ tuple : I → P, RealizesPartition partition tuple) ↔
      Fintype.card (Quotient partition) ≤ Fintype.card P :=
  (partition_realized_iff_embedding partition).trans Function.Embedding.nonempty_iff_card_le

#print axioms invariant_binary_off_diagonal_constant
#print axioms invariant_binary_diagonal_constant
#print axioms invariant_binary_unique_normal_form
#print axioms no_invariant_strict_total_order
#print axioms partition_realized_iff_embedding
#print axioms partition_realized_iff_block_count

#print axioms finite_partial_equiv_extends
#print axioms samePattern_iff_permutation
#print axioms invariant_unique_factorization
#print axioms pattern_factor_is_invariant
#print axioms invariant_unary_constant
#print axioms no_permutation_fixed_point

end AASC.KernelReference.EqualityPatterns
