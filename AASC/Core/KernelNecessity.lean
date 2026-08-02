import AASC.Core.Reference

namespace AASC

universe u v w

/-- The kernel is constructed directly from the primitive incidence relation. -/
def kernelOfIncidence
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) : Kernel X where
  standing carrier scope value := X.incidence carrier scope value
  failure carrier scope := forall value, Not (X.incidence carrier scope value)
  standing_iff _ _ _ := Iff.rfl
  failure_iff _ _ := Iff.rfl

theorem kernel_exists
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value) :
    Nonempty (Kernel X) := by
  exact ⟨kernelOfIncidence X⟩

/--
Kernel necessity at the primitive level. Determinacy proves unique standing
reference, while witnessed non-degeneracy proves a genuine failure boundary.
Neither conclusion is supplied as a premise or structure field.
-/
theorem kernel_necessity
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (hDeterminate : X.Determinate)
    (hNondegenerate : X.Nondegenerate) :
    exists K : Kernel X, K.ReferenceUnique ∧ K.Nontrivial := by
  let K := kernelOfIncidence X
  refine ⟨K, K.reference_unique_of_determinate hDeterminate, ?_⟩
  rcases hNondegenerate with ⟨carrier, scope, hNoIncidence⟩
  refine ⟨carrier, scope, ?_⟩
  apply (K.failure_iff carrier scope).2
  intro value hIncidence
  exact hNoIncidence ⟨value, hIncidence⟩

/-- The canonical kernel of a partial reference system. -/
def PartialReferenceSystem.kernel
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value) :
    Kernel R.incidenceSystem :=
  kernelOfIncidence R.incidenceSystem

theorem PartialReferenceSystem.kernel_referenceUnique
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value) :
    R.kernel.ReferenceUnique := by
  exact R.kernel.reference_unique_of_determinate R.determinate

theorem PartialReferenceSystem.kernel_nontrivial_iff_exists_none
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value) :
    R.kernel.Nontrivial <->
      exists carrier scope, R.referenceAt carrier scope = none := by
  constructor
  · rintro ⟨carrier, scope, hFailure⟩
    exact ⟨carrier, scope,
      (R.referenceAt_eq_none_iff carrier scope).2
        ((R.kernel.failure_iff carrier scope).1 hFailure)⟩
  · rintro ⟨carrier, scope, hNone⟩
    refine ⟨carrier, scope, ?_⟩
    exact (R.kernel.failure_iff carrier scope).2
      ((R.referenceAt_eq_none_iff carrier scope).1 hNone)

/-- Partial reference computes the local statuses; a witnessed `none` gives nontriviality. -/
theorem kernel_necessity_of_partialReference
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (R : PartialReferenceSystem Carrier Scope Value)
    (hBoundary : exists carrier scope,
      R.referenceAt carrier scope = none) :
    exists K : Kernel R.incidenceSystem,
      K.ReferenceUnique ∧ K.Nontrivial := by
  exact ⟨R.kernel, R.kernel_referenceUnique,
    (R.kernel_nontrivial_iff_exists_none).2 hBoundary⟩

end AASC
