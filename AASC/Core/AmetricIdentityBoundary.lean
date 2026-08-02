import AASC.Core.DeterminateObjecthood

/-!
# AMetric identity boundary

Determinate objects carry an identity description as their primitive
standing-bearing form.  `none` is the non-object boundary; an actual object is
incident only with itself.  No metric, ordering, or temporal data occur.
-/

namespace AASC.AmetricIdentityBoundary

universe u

/-- Primitive identity incidence for actual objects and the non-object boundary. -/
def system (Object : Type u) : IncidenceSystem (Option Object) Unit Object where
  incidence carrier _ value := carrier = some value

/-- Every actual object has its literal identity reference. -/
def reference {Object : Type u} (object : Object) :
    (system Object).ReferenceAt (some object, ()) :=
  ⟨object, rfl⟩

theorem determinate (Object : Type u) : (system Object).Determinate := by
  intro carrier _ referenceA referenceB incidenceA incidenceB
  exact Option.some.inj (incidenceA.symm.trans incidenceB)

theorem nondegenerate (Object : Type u) : (system Object).Nondegenerate := by
  refine ⟨none, (), ?_⟩
  rintro ⟨value, incidence⟩
  change (none : Option Object) = some value at incidence
  cases incidence

/-- Identity-form standing is independent of any further redescription. -/
theorem standing {Object : Type u} (object : Object) :
    (kernelOfIncidence (system Object)).StandingAt (some object) () :=
  AASC.IncidenceSystem.canonicalKernel_standingAt_of_reference
    (reference object)

/--
The identity description instantiates determinate, nondegenerate objecthood
without introducing any additional manifest form.
-/
theorem objecthood {Object : Type u} (object : Object) :
    (system Object).AdmissibleAt (some object) () /\
      (kernelOfIncidence (system Object)).StandingAt (some object) () /\
      (kernelOfIncidence (system Object)).ReferenceUnique /\
      (kernelOfIncidence (system Object)).Nontrivial /\
      Asymmetric
        (kernelOfIncidence (system Object)).StandingToFailure /\
      exists boundary : (system Object).Locus,
        (kernelOfIncidence (system Object)).FailureAt
            boundary.1 boundary.2 /\
          (kernelOfIncidence (system Object)).StandingToFailure
            (some object, ()) boundary /\
          Not (Nonempty
            ((system Object).Continuation (some object, ()) boundary)) :=
  (system Object).determinateNondegenerateObjecthood
    (determinate Object) (reference object) (nondegenerate Object)

end AASC.AmetricIdentityBoundary
