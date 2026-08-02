import AASC.Core.Continuation
import AASC.Core.KernelNecessity

namespace AASC

universe u v w x

/-- A target family whose fibers are the possible positive endpoint images. -/
structure EndpointInterface where
  Target : Type u
  Image : Target -> Type v

/-- A report contains either an actual image witness or an actual refutation. -/
inductive EndpointReport (E : EndpointInterface.{u, v}) : Type (max u v) where
  | realized (target : E.Target) (witness : E.Image target)
  | defeated (target : E.Target) (refutation : E.Image target -> False)

/-- Finality is terminality for an independently supplied act transition. -/
def FinalAt
    {Act : Type w}
    (step : Act -> Act -> Prop)
    (act : Act) : Prop :=
  forall later, step act later -> False

/--
A same-carrier redescription consists of mutually inverse maps on every target
image. The target index cannot silently change.
-/
structure EndpointRedescription (E : EndpointInterface.{u, v}) where
  forward : forall target, E.Image target -> E.Image target
  backward : forall target, E.Image target -> E.Image target
  left_inverse : forall target witness,
    backward target (forward target witness) = witness
  right_inverse : forall target witness,
    forward target (backward target witness) = witness

namespace EndpointReport

/-- Both positive and negative reports transport under lawful redescription. -/
def redescribe
    {E : EndpointInterface.{u, v}}
    (redescription : EndpointRedescription E) :
    EndpointReport E -> EndpointReport E
  | .realized target witness =>
      .realized target (redescription.forward target witness)
  | .defeated target refutation =>
      .defeated target
        (fun witness => refutation (redescription.backward target witness))

end EndpointReport

/--
An official endpoint use is an actual published report with downstream
continuation maps and terminality. Kernel consequences are derived below.
-/
structure OfficialEndpointUse
    {Act : Type w}
    {Scope : Type x}
    (E : EndpointInterface.{u, v})
    (reports : PartialReferenceSystem Act Scope (EndpointReport E))
    (step : Act -> Act -> Prop) where
  act : Act
  scope : Scope
  report : EndpointReport E
  published : reports.referenceAt act scope = some report
  downstream : List reports.incidenceSystem.Locus
  downstream_nonempty : exists locus, locus ∈ downstream
  reuse : forall locus, locus ∈ downstream ->
    reports.incidenceSystem.Continuation (act, scope) locus
  reuse_preserves : forall locus (member : locus ∈ downstream),
    ((reuse locus member).map
      { value := report, isIncident := published }).value = report
  finality : FinalAt step act

namespace OfficialEndpointUse

def publishedReference
    {Act : Type w}
    {Scope : Type x}
    {E : EndpointInterface.{u, v}}
    {reports : PartialReferenceSystem Act Scope (EndpointReport E)}
    {step : Act -> Act -> Prop}
    (use : OfficialEndpointUse E reports step) :
    reports.incidenceSystem.Reference use.act use.scope where
  value := use.report
  isIncident := use.published

theorem kernelStanding
    {Act : Type w}
    {Scope : Type x}
    {E : EndpointInterface.{u, v}}
    {reports : PartialReferenceSystem Act Scope (EndpointReport E)}
    {step : Act -> Act -> Prop}
    (use : OfficialEndpointUse E reports step) :
    reports.kernel.StandingAt use.act use.scope := by
  exact (reports.kernel.admissibleAt_iff_standingAt use.act use.scope).1
    ⟨use.report, use.published⟩

theorem kernelReferenceUnique
    {Act : Type w}
    {Scope : Type x}
    {E : EndpointInterface.{u, v}}
    {reports : PartialReferenceSystem Act Scope (EndpointReport E)}
    {step : Act -> Act -> Prop}
    (_use : OfficialEndpointUse E reports step) :
    reports.kernel.ReferenceUnique :=
  reports.kernel_referenceUnique

def reusedReference
    {Act : Type w}
    {Scope : Type x}
    {E : EndpointInterface.{u, v}}
    {reports : PartialReferenceSystem Act Scope (EndpointReport E)}
    {step : Act -> Act -> Prop}
    (use : OfficialEndpointUse E reports step)
    (locus : reports.incidenceSystem.Locus)
    (member : locus ∈ use.downstream) :
    reports.incidenceSystem.ReferenceAt locus :=
  (use.reuse locus member).map use.publishedReference

theorem reusedReport_eq
    {Act : Type w}
    {Scope : Type x}
    {E : EndpointInterface.{u, v}}
    {reports : PartialReferenceSystem Act Scope (EndpointReport E)}
    {step : Act -> Act -> Prop}
    (use : OfficialEndpointUse E reports step)
    (locus : reports.incidenceSystem.Locus)
    (member : locus ∈ use.downstream) :
    (use.reusedReference locus member).value = use.report :=
  use.reuse_preserves locus member

theorem noLaterStep
    {Act : Type w}
    {Scope : Type x}
    {E : EndpointInterface.{u, v}}
    {reports : PartialReferenceSystem Act Scope (EndpointReport E)}
    {step : Act -> Act -> Prop}
    (use : OfficialEndpointUse E reports step)
    {later : Act}
    (laterStep : step use.act later) : False :=
  use.finality later laterStep

end OfficialEndpointUse

/-- An official use whose published report realizes one fixed target. -/
structure OfficialRealizationUse
    {Act : Type w}
    {Scope : Type x}
    (E : EndpointInterface.{u, v})
    (reports : PartialReferenceSystem Act Scope (EndpointReport E))
    (step : Act -> Act -> Prop)
    (target : E.Target) where
  use : OfficialEndpointUse E reports step
  witness : E.Image target
  reportsRealization : use.report = .realized target witness

/-- An official use whose published report refutes one fixed target image. -/
structure OfficialDefeatUse
    {Act : Type w}
    {Scope : Type x}
    (E : EndpointInterface.{u, v})
    (reports : PartialReferenceSystem Act Scope (EndpointReport E))
    (step : Act -> Act -> Prop)
    (target : E.Target) where
  use : OfficialEndpointUse E reports step
  refutation : E.Image target -> False
  reportsDefeat : use.report = .defeated target refutation

namespace OfficialDefeatUse

/-- A refutation always has a fully mathematical singleton official use. -/
def publishedSingletonReports
    {E : EndpointInterface.{u, v}}
    {target : E.Target}
    (refutation : E.Image target -> False) :
    PartialReferenceSystem Unit Unit (EndpointReport E) where
  referenceAt _ _ := some (.defeated target refutation)

def publishedSingleton
    {E : EndpointInterface.{u, v}}
    {target : E.Target}
    (refutation : E.Image target -> False) :
    OfficialDefeatUse E (publishedSingletonReports refutation)
      (fun _ _ => False) target where
  use := {
    act := ()
    scope := ()
    report := .defeated target refutation
    published := rfl
    downstream := [((), ())]
    downstream_nonempty := ⟨((), ()), List.Mem.head []⟩
    reuse := by
      intro locus member
      cases locus with
      | mk carrier scope =>
          cases carrier
          cases scope
          exact IncidenceSystem.Continuation.identity
            (publishedSingletonReports refutation).incidenceSystem ((), ())
    reuse_preserves := by
      intro locus member
      cases locus with
      | mk carrier scope =>
          cases carrier
          cases scope
          rfl
    finality := by intro later impossible; exact impossible
  }
  refutation := refutation
  reportsDefeat := rfl

end OfficialDefeatUse

end AASC
