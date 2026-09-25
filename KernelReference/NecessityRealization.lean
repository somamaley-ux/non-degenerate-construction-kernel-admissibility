import Mathlib.Logic.Equiv.Defs

/-!
# Exact realization of original identity and incidence predicates

The primitive data are original objects, presentations with an independently
fixed interpretation, an encoding, and an arbitrary family of original
predicates. No kernel-role fields or correct-reader certificate are stored.
An exact reader is a property to be tested, and its existence is characterized
by the actual fibers of the encoding. A canonical relational reader is
constructed without choice.

Identity probes concern equality with an already identified original object.
They neither select an object nor assert that identity is experimentally
decidable. Distinct presentations may denote the same original object.
All predicates and readers here are semantic propositions; none of the
existence results asserts an effective decision procedure.
-/

namespace AASC.KernelReference.NecessityRealization

universe u v w z u' v' w'

variable {X : Type u} {Presentation : Type v} {Code : Type w}
    {Query : Type z}

/-- Full preservation and reflection of the independently specified predicates. -/
def Exact (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (read : Code → Query → Prop) : Prop :=
  ∀ presentation query,
    read (encode presentation) query ↔ profile (original presentation) query

/-- Equal codes must not erase a distinction in the original predicate family. -/
def PreservesOriginalProfile (original : Presentation → X)
    (encode : Presentation → Code) (profile : X → Query → Prop) : Prop :=
  ∀ left right, encode left = encode right →
    ∀ query, profile (original left) query ↔ profile (original right) query

/-- The relational reader constructed directly from the original data.
Its value outside the realized code image is false. -/
def canonicalReader (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (code : Code) (query : Query) : Prop :=
  ∃ presentation, encode presentation = code ∧
    profile (original presentation) query

theorem exact_reader_preserves_original_profile
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (read : Code → Query → Prop)
    (exact : Exact original encode profile read) :
    PreservesOriginalProfile original encode profile := by
  intro left right sameCode query
  calc
    profile (original left) query ↔ read (encode left) query := (exact left query).symm
    _ ↔ read (encode right) query := by rw [sameCode]
    _ ↔ profile (original right) query := exact right query

theorem canonical_reader_exact
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop)
    (preserved : PreservesOriginalProfile original encode profile) :
    Exact original encode profile (canonicalReader original encode profile) := by
  intro presentation query
  constructor
  · rintro ⟨other, sameCode, incident⟩
    exact (preserved other presentation sameCode query).1 incident
  · intro incident
    exact ⟨presentation, rfl, incident⟩

theorem canonical_reader_exact_iff
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) :
    Exact original encode profile (canonicalReader original encode profile) ↔
      PreservesOriginalProfile original encode profile :=
  ⟨exact_reader_preserves_original_profile original encode profile _,
    canonical_reader_exact original encode profile⟩

/-- Existence of an exact realization is concluded from the original fiber test. -/
theorem exists_exact_reader_iff
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) :
    (∃ read, Exact original encode profile read) ↔
      PreservesOriginalProfile original encode profile := by
  constructor
  · rintro ⟨read, exact⟩
    exact exact_reader_preserves_original_profile original encode profile read exact
  · intro preserved
    exact ⟨canonicalReader original encode profile,
      canonical_reader_exact original encode profile preserved⟩

/-! ## Explicit defects of an encoding or of a proposed reader -/

/-- A specific original predicate changes truth value inside one code fiber. -/
def FibreCollision (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) : Prop :=
  ∃ left right query, encode left = encode right ∧
    ((profile (original left) query ∧ ¬ profile (original right) query) ∨
      (¬ profile (original left) query ∧ profile (original right) query))

theorem fibre_collision_excludes_exact_reader
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop)
    (collision : FibreCollision original encode profile) :
    ¬ ∃ read, Exact original encode profile read := by
  rintro ⟨read, exact⟩
  obtain ⟨left, right, query, sameCode, discordant⟩ := collision
  have agreement :=
    exact_reader_preserves_original_profile original encode profile read exact
      left right sameCode query
  rcases discordant with ⟨yes, no⟩ | ⟨no, yes⟩
  · exact no (agreement.1 yes)
  · exact no (agreement.2 yes)

/-- Classical witness extraction is used only in this converse obstruction test. -/
theorem no_exact_reader_iff_fibre_collision
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) :
    (¬ ∃ read, Exact original encode profile read) ↔
      FibreCollision original encode profile := by
  classical
  constructor
  · intro absent
    by_contra noCollision
    apply absent
    apply (exists_exact_reader_iff original encode profile).2
    intro left right sameCode query
    constructor
    · intro leftHolds
      by_contra rightFails
      exact noCollision ⟨left, right, query, sameCode, Or.inl ⟨leftHolds, rightFails⟩⟩
    · intro rightHolds
      by_contra leftFails
      exact noCollision ⟨left, right, query, sameCode, Or.inr ⟨leftFails, rightHolds⟩⟩
  · exact fibre_collision_excludes_exact_reader original encode profile

def Omission (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (read : Code → Query → Prop) : Prop :=
  ∃ presentation query,
    profile (original presentation) query ∧ ¬ read (encode presentation) query

def Surplus (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (read : Code → Query → Prop) : Prop :=
  ∃ presentation query,
    read (encode presentation) query ∧ ¬ profile (original presentation) query

/-- Exactness rules out both missed original facts and unsupported extra facts. -/
theorem exact_iff_no_omission_or_surplus
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (read : Code → Query → Prop) :
    Exact original encode profile read ↔
      ¬ Omission original encode profile read ∧
      ¬ Surplus original encode profile read := by
  classical
  constructor
  · intro exact
    constructor
    · rintro ⟨presentation, query, required, missing⟩
      exact missing ((exact presentation query).2 required)
    · rintro ⟨presentation, query, supplied, unsupported⟩
      exact unsupported ((exact presentation query).1 supplied)
  · rintro ⟨noOmission, noSurplus⟩ presentation query
    constructor
    · intro supplied
      by_contra unsupported
      exact noSurplus ⟨presentation, query, supplied, unsupported⟩
    · intro required
      by_contra missing
      exact noOmission ⟨presentation, query, required, missing⟩

theorem not_exact_iff_omission_or_surplus
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (read : Code → Query → Prop) :
    ¬ Exact original encode profile read ↔
      Omission original encode profile read ∨ Surplus original encode profile read := by
  classical
  rw [exact_iff_no_omission_or_surplus]
  constructor
  · intro notBoth
    by_cases omitted : Omission original encode profile read
    · exact Or.inl omitted
    · apply Or.inr
      by_contra noSurplus
      exact notBoth ⟨omitted, noSurplus⟩
  · rintro (omitted | surplus) ⟨noOmission, noSurplus⟩
    · exact noOmission omitted
    · exact noSurplus surplus

/-! ## The realized image fixes precisely the scope of reader uniqueness -/

def RealizedCodes (encode : Presentation → Code) :=
  { code : Code // ∃ presentation, encode presentation = code }

theorem exact_readers_agree_on_realized_image
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop) (left right : Code → Query → Prop)
    (leftExact : Exact original encode profile left)
    (rightExact : Exact original encode profile right)
    (code : RealizedCodes encode) (query : Query) :
    left code.val query ↔ right code.val query := by
  obtain ⟨presentation, sameCode⟩ := code.property
  rw [← sameCode]
  exact (leftExact presentation query).trans (rightExact presentation query).symm

theorem unique_reader_on_realized_image
    (original : Presentation → X) (encode : Presentation → Code)
    (profile : X → Query → Prop)
    (preserved : PreservesOriginalProfile original encode profile) :
    ∃! read : RealizedCodes encode → Query → Prop,
      ∀ presentation query,
        read ⟨encode presentation, presentation, rfl⟩ query ↔
          profile (original presentation) query := by
  let read : RealizedCodes encode → Query → Prop :=
    fun code query => canonicalReader original encode profile code.val query
  have exact := canonical_reader_exact original encode profile preserved
  refine ⟨read, exact, ?_⟩
  intro other correct
  funext code query
  obtain ⟨presentation, sameCode⟩ := code.property
  have sameSubtype : code = ⟨encode presentation, presentation, rfl⟩ :=
    Subtype.ext sameCode.symm
  rw [sameSubtype]
  exact propext ((correct presentation query).trans (exact presentation query).symm)

/-! ## Identity is a derived specialization, not a four-role input package -/

def identityProfile (object : X) (anchor : X) : Prop := object = anchor

def PreservesOriginalIdentity (original : Presentation → X)
    (encode : Presentation → Code) : Prop :=
  ∀ left right, encode left = encode right → original left = original right

theorem identity_profile_preserved_iff
    (original : Presentation → X) (encode : Presentation → Code) :
    PreservesOriginalProfile original encode identityProfile ↔
      PreservesOriginalIdentity original encode := by
  constructor
  · intro preserved left right sameCode
    exact (preserved left right sameCode (original right)).2 rfl
  · intro preserved left right sameCode anchor
    rw [preserved left right sameCode]

theorem exists_identity_reader_iff
    (original : Presentation → X) (encode : Presentation → Code) :
    (∃ read, Exact original encode identityProfile read) ↔
      PreservesOriginalIdentity original encode :=
  (exists_exact_reader_iff original encode identityProfile).trans
    (identity_profile_preserved_iff original encode)

/-- The original interpretation is uniquely reconstructed on the actual code image.
Unlike the relational existence theorem, constructing this function uses choice. -/
theorem unique_original_reconstruction
    (original : Presentation → X) (encode : Presentation → Code)
    (preserved : PreservesOriginalIdentity original encode) :
    ∃! reconstruct : RealizedCodes encode → X,
      ∀ presentation,
        reconstruct ⟨encode presentation, presentation, rfl⟩ = original presentation := by
  classical
  let reconstruct : RealizedCodes encode → X :=
    fun code => original (Classical.choose code.property)
  have commutes : ∀ presentation,
      reconstruct ⟨encode presentation, presentation, rfl⟩ = original presentation := by
    intro presentation
    exact preserved _ presentation (Classical.choose_spec
      (show ∃ other, encode other = encode presentation from ⟨presentation, rfl⟩))
  refine ⟨reconstruct, commutes, ?_⟩
  intro other correct
  funext code
  obtain ⟨presentation, sameCode⟩ := code.property
  have sameSubtype : code = ⟨encode presentation, presentation, rfl⟩ :=
    Subtype.ext sameCode.symm
  rw [sameSubtype, correct, commutes]

/-- Exact identity retention is also equivalent to unique original reconstruction. -/
theorem unique_original_reconstruction_iff
    (original : Presentation → X) (encode : Presentation → Code) :
    (∃! reconstruct : RealizedCodes encode → X,
      ∀ presentation,
        reconstruct ⟨encode presentation, presentation, rfl⟩ = original presentation) ↔
      PreservesOriginalIdentity original encode := by
  constructor
  · rintro ⟨reconstruct, commutes, _⟩ left right sameCode
    have sameSubtype :
        (⟨encode left, left, rfl⟩ : RealizedCodes encode) =
        ⟨encode right, right, rfl⟩ := Subtype.ext sameCode
    exact (commutes left).symm.trans
      ((congrArg reconstruct sameSubtype).trans (commutes right))
  · exact unique_original_reconstruction original encode

/-- Every already specified predicate is recoverable when original identity is retained.
This is semantic recovery, with no computability or empirical access claim. -/
theorem original_identity_supports_every_profile
    (original : Presentation → X) (encode : Presentation → Code)
    (preserved : PreservesOriginalIdentity original encode)
    (profile : X → Query → Prop) :
    ∃ read, Exact original encode profile read := by
  apply (exists_exact_reader_iff original encode profile).2
  intro left right sameCode query
  rw [preserved left right sameCode]

/-- An exact identity reader entails recovery of each arbitrary original observable. -/
theorem identity_reader_supports_every_profile
    (original : Presentation → X) (encode : Presentation → Code)
    (identityRead : Code → X → Prop)
    (exact : Exact original encode identityProfile identityRead)
    (profile : X → Query → Prop) :
    ∃ read, Exact original encode profile read :=
  original_identity_supports_every_profile original encode
    ((exists_identity_reader_iff original encode).1 ⟨identityRead, exact⟩) profile

/-- Neither the choice of an anchor nor a preferred occupant is inferred. -/
theorem identity_probes_reindex
    {Y : Type u'} (change : X ≃ Y) (object anchor : X) :
    identityProfile (change object) (change anchor) ↔ identityProfile object anchor :=
  change.injective.eq_iff

/-! ## Arbitrary dependent output observations are captured by point predicates -/

section OutputPoints

variable {OutputQuery : Type u'} {Value : OutputQuery → Type v'}

def outputPointProfile (observe : X → (query : OutputQuery) → Value query)
    (object : X) (point : Sigma Value) : Prop :=
  observe object point.1 = point.2

theorem output_point_profile_agrees_iff
    (observe : X → (query : OutputQuery) → Value query) (left right : X) :
    (∀ point, outputPointProfile observe left point ↔
      outputPointProfile observe right point) ↔
    (∀ query, observe left query = observe right query) := by
  constructor
  · intro same query
    exact (same ⟨query, observe right query⟩).2 rfl
  · intro same point
    unfold outputPointProfile
    rw [same point.1]

/-- Classification of all outputs is concluded from the relational reader criterion. -/
theorem exists_output_point_reader_iff
    (original : Presentation → X) (encode : Presentation → Code)
    (observe : X → (query : OutputQuery) → Value query) :
    (∃ read, Exact original encode (outputPointProfile observe) read) ↔
    (∀ left right, encode left = encode right →
      ∀ query, observe (original left) query = observe (original right) query) := by
  rw [exists_exact_reader_iff]
  constructor
  · intro preserved left right sameCode
    exact (output_point_profile_agrees_iff observe _ _).1
      (preserved left right sameCode)
  · intro preserved left right sameCode
    exact (output_point_profile_agrees_iff observe _ _).2
      (preserved left right sameCode)

end OutputPoints

/-! ## Removing storage versus removing recoverable original work -/

theorem erasure_loses_original_work_iff
    {Reduced : Type u'} (original : Presentation → X)
    (encode : Presentation → Code) (erase : Code → Reduced)
    (profile : X → Query → Prop) :
    (¬ ∃ read, Exact original (fun presentation => erase (encode presentation)) profile read) ↔
      FibreCollision original (fun presentation => erase (encode presentation)) profile :=
  no_exact_reader_iff_fibre_collision original (fun presentation => erase (encode presentation))
    profile

/-- If the initial encoding preserves the original profile, a later loss has a
witness whose previously distinct codes were merged by the erasure. -/
theorem erasure_of_exact_encoding_has_new_collision
    {Reduced : Type u'} (original : Presentation → X)
    (encode : Presentation → Code) (erase : Code → Reduced)
    (profile : X → Query → Prop)
    (preserved : PreservesOriginalProfile original encode profile)
    (lost : ¬ ∃ read,
      Exact original (fun presentation => erase (encode presentation)) profile read) :
    ∃ left right query,
      encode left ≠ encode right ∧ erase (encode left) = erase (encode right) ∧
      ((profile (original left) query ∧ ¬ profile (original right) query) ∨
        (¬ profile (original left) query ∧ profile (original right) query)) := by
  obtain ⟨left, right, query, merged, discordant⟩ :=
    (erasure_loses_original_work_iff original encode erase profile).1 lost
  refine ⟨left, right, query, ?_, merged, discordant⟩
  intro alreadyEqual
  have agreement := preserved left right alreadyEqual query
  rcases discordant with ⟨yes, no⟩ | ⟨no, yes⟩
  · exact no (agreement.1 yes)
  · exact no (agreement.2 yes)

/-- A field that is reconstructed on actual presentations can disappear from storage
without losing any original work performed by its reader. -/
theorem reconstructed_storage_preserves_exactness
    {Reduced : Type u'} (original : Presentation → X)
    (encode : Presentation → Code) (erase : Code → Reduced)
    (restore : Reduced → Code)
    (restored : ∀ presentation, restore (erase (encode presentation)) = encode presentation)
    (profile : X → Query → Prop) (read : Code → Query → Prop)
    (exact : Exact original encode profile read) :
    Exact original (fun presentation => erase (encode presentation)) profile
      (fun code query => read (restore code) query) := by
  intro presentation query
  change read (restore (erase (encode presentation))) query ↔
    profile (original presentation) query
  rw [restored presentation]
  exact exact presentation query

/-! ## Concrete witnesses distinguish objecthood, representation, and qualification -/

namespace Examples

def redundantOriginal (presentation : Bool × Bool) : Bool := presentation.1

theorem redundant_presentations_need_not_be_injective :
    (∃ read : Bool → Bool → Prop,
      Exact redundantOriginal Prod.fst identityProfile read) ∧
      ¬ Function.Injective (Prod.fst : Bool × Bool → Bool) := by
  constructor
  · exact (exists_identity_reader_iff redundantOriginal Prod.fst).2
      (fun _ _ sameCode => sameCode)
  · intro injective
    have impossible := injective (a₁ := (false, false)) (a₂ := (false, true)) rfl
    have := congrArg Prod.snd impossible
    contradiction

/-- Equal incidence answers do not identify distinct original objects. -/
theorem constant_answers_do_not_retain_identity :
    (∃ read : Unit → Unit → Prop,
      Exact (id : Bool → Bool) (fun _ => ()) (fun _ _ => True) read) ∧
      ¬ ∃ read : Unit → Bool → Prop,
        Exact (id : Bool → Bool) (fun _ => ()) identityProfile read := by
  constructor
  · exact ⟨fun _ _ => True, fun _ _ => Iff.rfl⟩
  · intro reader
    have preserved := (exists_identity_reader_iff (id : Bool → Bool) (fun _ => ())).1 reader
    have impossible := preserved false true rfl
    contradiction

/-- A false reader cannot remove an independently actual original incidence. -/
theorem bad_reader_leaves_original_incidence_actual :
    (∃ object : Unit, (fun (_ : Unit) (_ : Unit) => True) object ()) ∧
    Omission (id : Unit → Unit) id (fun _ (_ : Unit) => True) (fun _ _ => False) ∧
    ¬ Exact (id : Unit → Unit) id (fun _ (_ : Unit) => True) (fun _ _ => False) := by
  refine ⟨⟨(), True.intro⟩, ⟨(), (), True.intro, not_false⟩, ?_⟩
  intro exact
  exact (exact () ()).2 True.intro

/-- Coverage without reflection admits unsupported answers; exactness detects them. -/
theorem positive_coverage_does_not_exclude_surplus :
    (∀ object : Unit, ∀ query : Bool, query = true →
      (fun (_ : Unit) (_ : Bool) => True) object query) ∧
    Surplus (id : Unit → Unit) id (fun _ query => query = true) (fun _ _ => True) ∧
    ¬ Exact (id : Unit → Unit) id (fun _ query => query = true) (fun _ (_ : Bool) => True) := by
  refine ⟨fun _ _ _ => True.intro, ⟨(), false, True.intro, by decide⟩, ?_⟩
  intro exact
  have impossible := (exact () false).1 True.intro
  contradiction

theorem deleting_constant_storage_keeps_all_original_predicates
    (profile : Bool → Query → Prop) :
    ∃ read : Bool → Query → Prop,
      Exact (id : Bool → Bool) (fun object => (object, ())) profile
        (fun code query => read code.1 query) ∧
      Exact (id : Bool → Bool) id profile read := by
  exact ⟨profile, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end Examples

#print axioms exact_reader_preserves_original_profile
#print axioms canonical_reader_exact
#print axioms exists_exact_reader_iff
#print axioms fibre_collision_excludes_exact_reader
#print axioms no_exact_reader_iff_fibre_collision
#print axioms exact_iff_no_omission_or_surplus
#print axioms not_exact_iff_omission_or_surplus
#print axioms exact_readers_agree_on_realized_image
#print axioms unique_reader_on_realized_image
#print axioms exists_identity_reader_iff
#print axioms unique_original_reconstruction
#print axioms unique_original_reconstruction_iff
#print axioms original_identity_supports_every_profile
#print axioms identity_reader_supports_every_profile
#print axioms identity_probes_reindex
#print axioms output_point_profile_agrees_iff
#print axioms exists_output_point_reader_iff
#print axioms erasure_loses_original_work_iff
#print axioms erasure_of_exact_encoding_has_new_collision
#print axioms reconstructed_storage_preserves_exactness
#print axioms Examples.redundant_presentations_need_not_be_injective
#print axioms Examples.constant_answers_do_not_retain_identity
#print axioms Examples.bad_reader_leaves_original_incidence_actual
#print axioms Examples.positive_coverage_does_not_exclude_surplus
#print axioms Examples.deleting_constant_storage_keeps_all_original_predicates

end AASC.KernelReference.NecessityRealization
