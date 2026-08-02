import AASC.Core.DeterminateObjecthood

namespace AASC

universe u v w

namespace TargetAdequacy

/-- The three observable outcomes of evaluating a construction step. -/
inductive StepVerdict where
  | advances
  | fails
  | departs
deriving DecidableEq

/--
Raw mathematical data needed to evaluate steps toward determinate targets.
Targets and verdicts are functions, so their values are data rather than
propositional labels attached after the fact.
-/
structure Regime (Act : Type u) (Target : Type v) (Step : Type w) where
  source : Step -> Act
  destination : Step -> Act
  targetOf : Act -> Target
  verdict : Step -> StepVerdict

namespace Regime

variable {Act : Type u} {Target : Type v} {Step : Type w}

/-- An act references a target exactly when the target evaluator returns it. -/
def ReferenceAt (R : Regime Act Target Step) (act : Act) (target : Target) : Prop :=
  R.targetOf act = target

/-- A verdict is the evaluated verdict of a concrete step. -/
def VerdictAt
    (R : Regime Act Target Step)
    (step : Step)
    (verdict : StepVerdict) : Prop :=
  R.verdict step = verdict

/-- Standing is literal successful advancement of the fixed target. -/
def Standing (R : Regime Act Target Step) (step : Step) : Prop :=
  R.VerdictAt step .advances

/-- Admissibility is the gate admitting exactly standing-bearing steps. -/
def Admissible (R : Regime Act Target Step) (step : Step) : Prop :=
  R.verdict step = .advances

/-- Failure is the observable absence of standing, including target departure. -/
def Failure (R : Regime Act Target Step) (step : Step) : Prop :=
  Not (R.Standing step)

/--
Nondegeneracy requires an actual standing step and an actual boundary step.
It is not an abstract flag and does not assert any endpoint-fiber proposition.
-/
def Nondegenerate (R : Regime Act Target Step) : Prop :=
  exists standing boundary,
    R.Standing standing /\ R.Failure boundary

/-- Every act has one explicit target reference. -/
theorem reference_exists_unique
    (R : Regime Act Target Step)
    (act : Act) :
    exists target,
      R.ReferenceAt act target /\
        forall other, R.ReferenceAt act other -> other = target := by
  refine ⟨R.targetOf act, rfl, ?_⟩
  intro other referenced
  exact referenced.symm

/-- Determinate reference is computed from the target function. -/
theorem reference_unique
    (R : Regime Act Target Step)
    {act : Act}
    {left right : Target}
    (leftReference : R.ReferenceAt act left)
    (rightReference : R.ReferenceAt act right) :
    left = right := by
  exact leftReference.symm.trans rightReference

/-- Every concrete step has one explicit evaluation. -/
theorem verdict_exists_unique
    (R : Regime Act Target Step)
    (step : Step) :
    exists verdict,
      R.VerdictAt step verdict /\
        forall other, R.VerdictAt step other -> other = verdict := by
  refine ⟨R.verdict step, rfl, ?_⟩
  intro other evaluated
  exact evaluated.symm

/-- Admissibility and standing coincide by their observable verdict. -/
theorem admissible_iff_standing
    (R : Regime Act Target Step)
    (step : Step) :
    R.Admissible step <-> R.Standing step := by
  rfl

/-- Standing and failure are disjoint at the same step. -/
theorem standing_failure_disjoint
    (R : Regime Act Target Step)
    (step : Step) :
    Not (R.Standing step /\ R.Failure step) := by
  rintro ⟨standing, failure⟩
  exact failure standing

/--
A changed act-time verdict cannot be a retroactive reclassification of the
same step object. It necessarily identifies a distinct step.
-/
theorem verdict_change_forces_distinct_step
    (R : Regime Act Target Step)
    {original revised : Step}
    (changed : Not (R.verdict original = R.verdict revised)) :
    Not (original = revised) := by
  intro sameStep
  subst revised
  exact changed rfl

/-- A repair is a later step on the same endpoints with a changed verdict. -/
def Repair
    (R : Regime Act Target Step)
    (original revised : Step) : Prop :=
  R.source original = R.source revised /\
    R.destination original = R.destination revised /\
    Not (R.verdict original = R.verdict revised)

/-- Every actual repair is numerically distinct from the original act. -/
theorem repair_is_distinct
    (R : Regime Act Target Step)
    {original revised : Step}
    (repair : R.Repair original revised) :
    Not (original = revised) :=
  R.verdict_change_forces_distinct_step repair.2.2

/--
A redescription consists of reversible maps on acts and steps. Fidelity is
expressed by literal preservation equations for endpoints, targets, and
verdicts.
-/
structure Redescription (R : Regime Act Target Step) where
  actForward : Act -> Act
  actBackward : Act -> Act
  act_left_inverse : forall act, actBackward (actForward act) = act
  act_right_inverse : forall act, actForward (actBackward act) = act
  stepForward : Step -> Step
  stepBackward : Step -> Step
  step_left_inverse : forall step, stepBackward (stepForward step) = step
  step_right_inverse : forall step, stepForward (stepBackward step) = step
  source_preserved : forall step,
    actForward (R.source step) = R.source (stepForward step)
  destination_preserved : forall step,
    actForward (R.destination step) = R.destination (stepForward step)
  target_preserved : forall act,
    R.targetOf (actForward act) = R.targetOf act
  verdict_preserved : forall step,
    R.verdict (stepForward step) = R.verdict step

namespace Redescription

/-- The identity maps give a lawful same-regime redescription. -/
def identity (R : Regime Act Target Step) : R.Redescription where
  actForward act := act
  actBackward act := act
  act_left_inverse _ := rfl
  act_right_inverse _ := rfl
  stepForward step := step
  stepBackward step := step
  step_left_inverse _ := rfl
  step_right_inverse _ := rfl
  source_preserved _ := rfl
  destination_preserved _ := rfl
  target_preserved _ := rfl
  verdict_preserved _ := rfl

/-- A referenced target is preserved under an actual lawful redescription. -/
theorem preserves_reference
    {R : Regime Act Target Step}
    (redescription : R.Redescription)
    {act : Act}
    {target : Target}
    (reference : R.ReferenceAt act target) :
    R.ReferenceAt (redescription.actForward act) target := by
  unfold ReferenceAt
  exact (redescription.target_preserved act).trans reference

/-- Standing is invariant under an actual lawful redescription. -/
theorem preserves_standing
    {R : Regime Act Target Step}
    (redescription : R.Redescription)
    {step : Step}
    (standing : R.Standing step) :
    R.Standing (redescription.stepForward step) := by
  unfold Standing VerdictAt at standing ⊢
  exact (redescription.verdict_preserved step).trans standing

/-- Failure is invariant under an actual lawful redescription. -/
theorem preserves_failure
    {R : Regime Act Target Step}
    (redescription : R.Redescription)
    {step : Step}
    (failure : R.Failure step) :
    R.Failure (redescription.stepForward step) := by
  intro standing
  apply failure
  unfold Standing VerdictAt at standing ⊢
  exact (redescription.verdict_preserved step).symm.trans standing

end Redescription

/-- The destination act is evaluated against a different target. -/
def TargetChanged
    (R : Regime Act Target Step)
    (step : Step) : Prop :=
  Not (R.targetOf (R.source step) = R.targetOf (R.destination step))

/-- No verdict exists for a concrete step. -/
def StepUnevaluable
    (R : Regime Act Target Step)
    (step : Step) : Prop :=
  Not (exists verdict, R.VerdictAt step verdict)

/-- The same numerical step is assigned a changed act-time verdict. -/
def ActTimeFinalityFailure
    (R : Regime Act Target Step)
    (step : Step) : Prop :=
  exists revised,
    revised = step /\
      Not (R.verdict revised = R.verdict step)

/-- A purported lawful redescription changes target or verdict data. -/
def RedescriptionFidelityFailure
    (R : Regime Act Target Step)
    (step : Step) : Prop :=
  exists redescription : R.Redescription,
    Not (R.targetOf (redescription.actForward (R.source step)) =
      R.targetOf (R.source step)) \/
    Not (R.verdict (redescription.stepForward step) = R.verdict step)

/-- The four observable failure branches used by the manuscript's exhaustion. -/
def AdequacyViolation
    (R : Regime Act Target Step)
    (step : Step) : Prop :=
  R.TargetChanged step \/
    R.StepUnevaluable step \/
    R.ActTimeFinalityFailure step \/
    R.RedescriptionFidelityFailure step

theorem not_stepUnevaluable
    (R : Regime Act Target Step)
    (step : Step) :
    Not (R.StepUnevaluable step) := by
  intro unevaluable
  exact unevaluable ⟨R.verdict step, rfl⟩

theorem not_actTimeFinalityFailure
    (R : Regime Act Target Step)
    (step : Step) :
    Not (R.ActTimeFinalityFailure step) := by
  rintro ⟨revised, sameStep, changed⟩
  subst revised
  exact changed rfl

theorem not_redescriptionFidelityFailure
    (R : Regime Act Target Step)
    (step : Step) :
    Not (R.RedescriptionFidelityFailure step) := by
  rintro ⟨redescription, targetFailure | verdictFailure⟩
  · exact targetFailure (redescription.target_preserved (R.source step))
  · exact verdictFailure (redescription.verdict_preserved step)

/--
On a same-target step, none of the four adequacy failures occurs. Thus any
theorem assigning one of these failures to a negative report needs additional
domain behavior beyond target adequacy itself.
-/
theorem no_adequacyViolation_of_sameTarget
    (R : Regime Act Target Step)
    (step : Step)
    (sameTarget :
      R.targetOf (R.source step) = R.targetOf (R.destination step)) :
    Not (R.AdequacyViolation step) := by
  rintro (targetChanged | unevaluable | finalityFailure | fidelityFailure)
  · exact targetChanged sameTarget
  · exact R.not_stepUnevaluable step unevaluable
  · exact R.not_actTimeFinalityFailure step finalityFailure
  · exact R.not_redescriptionFidelityFailure step fidelityFailure

/--
The explicit target-adequacy data instantiate the full kernel consequence
profile. The result derives unique reference, total and unique step
evaluation, standing/admissibility coincidence, and act-time irreversibility.
-/
theorem fullKernel_of_targetAdequacy
    (R : Regime Act Target Step) :
    (forall act, exists target,
      R.ReferenceAt act target /\
        forall other, R.ReferenceAt act other -> other = target) /\
      (forall step, exists verdict,
        R.VerdictAt step verdict /\
          forall other, R.VerdictAt step other -> other = verdict) /\
      (forall step, R.Admissible step <-> R.Standing step) /\
      (forall {original revised},
        Not (R.verdict original = R.verdict revised) ->
          Not (original = revised)) := by
  exact ⟨R.reference_exists_unique,
    R.verdict_exists_unique,
    R.admissible_iff_standing,
    R.verdict_change_forces_distinct_step⟩

/--
For a nondegenerate regime, the kernel consequence profile also contains
actual standing and failure witnesses. Nothing is supplied by a certificate.
-/
theorem nondegenerate_targetAdequacy_instantiatesKernel
    (R : Regime Act Target Step)
    (nondegenerate : R.Nondegenerate) :
    (forall act, exists target,
      R.ReferenceAt act target /\
        forall other, R.ReferenceAt act other -> other = target) /\
      (forall step, exists verdict,
        R.VerdictAt step verdict /\
          forall other, R.VerdictAt step other -> other = verdict) /\
      (forall step, R.Admissible step <-> R.Standing step) /\
      (forall {original revised},
        Not (R.verdict original = R.verdict revised) ->
          Not (original = revised)) /\
      exists standing boundary,
        R.Standing standing /\ R.Failure boundary := by
  rcases R.fullKernel_of_targetAdequacy with
    ⟨reference, evaluation, standing, irreversible⟩
  exact ⟨reference, evaluation, standing, irreversible, nondegenerate⟩

end Regime

end TargetAdequacy

end AASC
