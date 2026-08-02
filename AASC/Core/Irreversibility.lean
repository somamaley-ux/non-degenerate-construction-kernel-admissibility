import AASC.Core.SameScope

namespace AASC

universe u v w

def Asymmetric
    {Scope : Type v}
    (step : Scope -> Scope -> Prop) : Prop :=
  forall {source target}, step source target -> Not (step target source)

namespace IncidenceSystem

/-- A directed kernel step combines scope direction with shared incidence. -/
def DirectedKernelStep
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    (X : IncidenceSystem Carrier Scope Value)
    (step : Scope -> Scope -> Prop)
    (source target : X.Locus) : Prop :=
  source.1 = target.1 ∧
  step source.2 target.2 ∧
  X.SharesReference source target

theorem directedKernelStep_irreversible
    {Carrier : Type u}
    {Scope : Type v}
    {Value : Type w}
    {X : IncidenceSystem Carrier Scope Value}
    {step : Scope -> Scope -> Prop}
    (hAsymmetric : Asymmetric step)
    {source target : X.Locus}
    (hForward : X.DirectedKernelStep step source target) :
    Not (X.DirectedKernelStep step target source) := by
  intro hBackward
  exact hAsymmetric hForward.2.1 hBackward.2.1

end IncidenceSystem

end AASC
