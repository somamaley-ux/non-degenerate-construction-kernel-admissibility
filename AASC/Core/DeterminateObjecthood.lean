import AASC.Core.EndpointUse
import AASC.Core.Irreversibility

namespace AASC

universe u v w x

namespace Kernel

/--
The direction from an occupied locus to an unoccupied locus.  This is derived
from standing and failure in a kernel; it does not store a transition claim.
-/
def StandingToFailure
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    (source target : X.Locus) : Prop :=
  K.StandingAt source.1 source.2 ∧ K.FailureAt target.1 target.2

/-- Standing-to-failure direction cannot also run in reverse. -/
theorem standingToFailure_asymmetric
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X) :
    Asymmetric K.StandingToFailure := by
  intro source target hForward hBackward
  exact K.standing_failure_disjoint source.1 source.2
    ⟨hForward.1, hBackward.2⟩

/--
No continuation of incidence references can map an occupied source into a
failure target.
-/
theorem noContinuation_of_standingToFailure
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (K : Kernel X)
    {source target : X.Locus}
    (direction : K.StandingToFailure source target) :
    Not (Nonempty (X.Continuation source target)) := by
  rcases direction.1 with ⟨value, hStanding⟩
  exact X.no_continuation_from_standing_to_failure
    ⟨value, (K.standing_iff source.1 source.2 value).1 hStanding⟩
    ((K.failure_iff target.1 target.2).1 direction.2)

end Kernel

namespace IncidenceSystem

/-- An actual reference makes its locus admissible. -/
theorem admissibleAt_of_reference
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {locus : X.Locus}
    (reference : X.ReferenceAt locus) :
    X.AdmissibleAt locus.1 locus.2 :=
  ⟨reference.value, reference.isIncident⟩

/-- An actual reference has standing in the kernel computed from incidence. -/
theorem canonicalKernel_standingAt_of_reference
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {locus : X.Locus}
    (reference : X.ReferenceAt locus) :
    (kernelOfIncidence X).StandingAt locus.1 locus.2 := by
  exact ((kernelOfIncidence X).admissibleAt_iff_standingAt
    locus.1 locus.2).1 (X.admissibleAt_of_reference reference)

/--
A nondegenerate incidence system has an actual failure locus in its canonical
kernel.
-/
theorem canonicalKernel_failure_of_nondegenerate
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    (hNondegenerate : X.Nondegenerate) :
    exists locus : X.Locus,
      (kernelOfIncidence X).FailureAt locus.1 locus.2 := by
  rcases hNondegenerate with ⟨carrier, scope, hNotAdmissible⟩
  refine ⟨(carrier, scope), ?_⟩
  exact ((kernelOfIncidence X).failure_iff carrier scope).2
    ((X.not_admissible_iff_failure carrier scope).1 hNotAdmissible)

/--
Constitutive kernel theorem for determinate, nondegenerate objecthood.

An actual object-state reference supplies admissibility and standing.
Determinacy supplies unique reference.  Nondegeneracy supplies an actual
failure locus, and the resulting standing-to-failure direction is asymmetric
and admits no incidence-preserving continuation.
-/
theorem determinateNondegenerateObjecthood
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (hDeterminate : X.Determinate)
    {endpoint : X.Locus}
    (reference : X.ReferenceAt endpoint)
    (hNondegenerate : X.Nondegenerate) :
    X.AdmissibleAt endpoint.1 endpoint.2 ∧
      (kernelOfIncidence X).StandingAt endpoint.1 endpoint.2 ∧
      (kernelOfIncidence X).ReferenceUnique ∧
      (kernelOfIncidence X).Nontrivial ∧
      Asymmetric (kernelOfIncidence X).StandingToFailure ∧
      exists boundary : X.Locus,
        (kernelOfIncidence X).FailureAt boundary.1 boundary.2 ∧
        (kernelOfIncidence X).StandingToFailure endpoint boundary ∧
        Not (Nonempty (X.Continuation endpoint boundary)) := by
  let K := kernelOfIncidence X
  have hAdmissible : X.AdmissibleAt endpoint.1 endpoint.2 :=
    X.admissibleAt_of_reference reference
  have hStanding : K.StandingAt endpoint.1 endpoint.2 :=
    (K.admissibleAt_iff_standingAt endpoint.1 endpoint.2).1 hAdmissible
  have hUnique : K.ReferenceUnique :=
    K.reference_unique_of_determinate hDeterminate
  rcases X.canonicalKernel_failure_of_nondegenerate hNondegenerate with
    ⟨boundary, hFailure⟩
  have hDirection : K.StandingToFailure endpoint boundary :=
    ⟨hStanding, hFailure⟩
  refine ⟨hAdmissible, hStanding, hUnique, ?_,
    K.standingToFailure_asymmetric, boundary, hFailure, hDirection, ?_⟩
  · exact ⟨boundary.1, boundary.2, hFailure⟩
  · exact K.noContinuation_of_standingToFailure hDirection

end IncidenceSystem

namespace PartialReferenceSystem

/--
Object/state endpoint reports instantiate the same kernel independently of
whether the report is realized or defeated.  The graph computes determinacy;
an actual published report supplies local incidence; and an actual `none`
supplies the nondegenerate boundary.
-/
theorem determinateNondegenerateEndpointObjecthood
    {Object : Type u}
    {State : Type v}
    {E : EndpointInterface.{w, x}}
    (reports : PartialReferenceSystem Object State (EndpointReport E))
    {object : Object}
    {state : State}
    {report : EndpointReport E}
    (published : reports.referenceAt object state = some report)
    (boundary : exists boundaryObject boundaryState,
      reports.referenceAt boundaryObject boundaryState = none) :
    reports.incidenceSystem.AdmissibleAt object state ∧
      reports.kernel.StandingAt object state ∧
      reports.kernel.ReferenceUnique ∧
      reports.kernel.Nontrivial ∧
      Asymmetric reports.kernel.StandingToFailure ∧
      exists boundaryLocus : reports.incidenceSystem.Locus,
        reports.kernel.FailureAt boundaryLocus.1 boundaryLocus.2 ∧
        reports.kernel.StandingToFailure (object, state) boundaryLocus ∧
        Not (Nonempty (reports.incidenceSystem.Continuation
          (object, state) boundaryLocus)) := by
  exact reports.incidenceSystem.determinateNondegenerateObjecthood
    reports.determinate
    (show reports.incidenceSystem.ReferenceAt (object, state) from
      ⟨report, published⟩)
    ((reports.nondegenerate_iff_exists_none).2 boundary)

/--
Polarity neutrality at the incidence level: every actual endpoint report,
positive or negative, is both admissible and standing in the canonical kernel.
-/
theorem endpointReport_admissibleAndStanding
    {Object : Type u}
    {State : Type v}
    {E : EndpointInterface.{w, x}}
    (reports : PartialReferenceSystem Object State (EndpointReport E))
    {object : Object}
    {state : State}
    {report : EndpointReport E}
    (published : reports.referenceAt object state = some report) :
    reports.incidenceSystem.AdmissibleAt object state ∧
      reports.kernel.StandingAt object state := by
  have reference : reports.incidenceSystem.Reference object state :=
    ⟨report, published⟩
  have hAdmissible : reports.incidenceSystem.AdmissibleAt object state :=
    ⟨reference.value, reference.isIncident⟩
  exact ⟨hAdmissible,
    (reports.kernel.admissibleAt_iff_standingAt object state).1 hAdmissible⟩

end PartialReferenceSystem

end AASC
