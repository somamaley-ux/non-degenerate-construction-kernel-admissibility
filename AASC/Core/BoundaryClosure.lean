namespace AASC

universe u

abbrev BooleanClassifier (Point : Type u) := Point -> Bool

namespace BooleanClassifier

def GovernanceEquivalent
    {Point : Type u}
    (canonical candidate : BooleanClassifier Point) : Prop :=
  forall point, candidate point = canonical point

def NoFalsePositives
    {Point : Type u}
    (canonical candidate : BooleanClassifier Point) : Prop :=
  forall point, candidate point = true -> canonical point = true

def NoFalseNegatives
    {Point : Type u}
    (canonical candidate : BooleanClassifier Point) : Prop :=
  forall point, canonical point = true -> candidate point = true

theorem governanceEquivalent_of_sound_complete
    {Point : Type u}
    {canonical candidate : BooleanClassifier Point}
    (sound : NoFalsePositives canonical candidate)
    (complete : NoFalseNegatives canonical candidate) :
    GovernanceEquivalent canonical candidate := by
  intro point
  cases hCanonical : canonical point <;> cases hCandidate : candidate point
  · rfl
  · have hImpossible := sound point hCandidate
    rw [hCanonical] at hImpossible
    cases hImpossible
  · have hImpossible := complete point hCanonical
    rw [hCandidate] at hImpossible
    cases hImpossible
  · rfl

end BooleanClassifier

/-- A finite decision procedure represented by its ordered decision table. -/
abbrev DecisionVector := List Bool

namespace DecisionVector

def SameDomain (canonical candidate : DecisionVector) : Prop :=
  canonical.length = candidate.length

inductive NoFalsePositive : DecisionVector -> DecisionVector -> Prop where
  | nil : NoFalsePositive [] []
  | bothFalse {canonical candidate}
      (tail : NoFalsePositive canonical candidate) :
      NoFalsePositive (false :: canonical) (false :: candidate)
  | canonicalOnly {canonical candidate}
      (tail : NoFalsePositive canonical candidate) :
      NoFalsePositive (true :: canonical) (false :: candidate)
  | bothTrue {canonical candidate}
      (tail : NoFalsePositive canonical candidate) :
      NoFalsePositive (true :: canonical) (true :: candidate)

inductive NoFalseNegative : DecisionVector -> DecisionVector -> Prop where
  | nil : NoFalseNegative [] []
  | bothFalse {canonical candidate}
      (tail : NoFalseNegative canonical candidate) :
      NoFalseNegative (false :: canonical) (false :: candidate)
  | candidateOnly {canonical candidate}
      (tail : NoFalseNegative canonical candidate) :
      NoFalseNegative (false :: canonical) (true :: candidate)
  | bothTrue {canonical candidate}
      (tail : NoFalseNegative canonical candidate) :
      NoFalseNegative (true :: canonical) (true :: candidate)

inductive FalsePositive : DecisionVector -> DecisionVector -> Prop where
  | here {canonical candidate} :
      FalsePositive (false :: canonical) (true :: candidate)
  | there {canonical candidate}
      {canonicalHead candidateHead : Bool}
      (tail : FalsePositive canonical candidate) :
      FalsePositive (canonicalHead :: canonical) (candidateHead :: candidate)

inductive FalseNegative : DecisionVector -> DecisionVector -> Prop where
  | here {canonical candidate} :
      FalseNegative (true :: canonical) (false :: candidate)
  | there {canonical candidate}
      {canonicalHead candidateHead : Bool}
      (tail : FalseNegative canonical candidate) :
      FalseNegative (canonicalHead :: canonical) (candidateHead :: candidate)

theorem NoFalsePositive.refute
    {canonical candidate : DecisionVector}
    (noPositive : NoFalsePositive canonical candidate)
    (positive : FalsePositive canonical candidate) : False := by
  induction positive with
  | here => cases noPositive
  | there tail inductionHypothesis =>
      cases noPositive with
      | bothFalse noTail => exact inductionHypothesis noTail
      | canonicalOnly noTail => exact inductionHypothesis noTail
      | bothTrue noTail => exact inductionHypothesis noTail

theorem NoFalseNegative.refute
    {canonical candidate : DecisionVector}
    (noNegative : NoFalseNegative canonical candidate)
    (negative : FalseNegative canonical candidate) : False := by
  induction negative with
  | here => cases noNegative
  | there tail inductionHypothesis =>
      cases noNegative with
      | bothFalse noTail => exact inductionHypothesis noTail
      | candidateOnly noTail => exact inductionHypothesis noTail
      | bothTrue noTail => exact inductionHypothesis noTail

inductive DifferenceCode where
  | equivalent
  | extendsStanding
  | restrictsStanding
  | replacesBoundary
deriving DecidableEq, Repr

def DifferenceCode.prepend
    (code : DifferenceCode)
    (canonicalHead candidateHead : Bool) : DifferenceCode :=
  match canonicalHead, candidateHead with
  | false, false => code
  | true, true => code
  | false, true =>
      match code with
      | .equivalent => .extendsStanding
      | .extendsStanding => .extendsStanding
      | .restrictsStanding => .replacesBoundary
      | .replacesBoundary => .replacesBoundary
  | true, false =>
      match code with
      | .equivalent => .restrictsStanding
      | .extendsStanding => .replacesBoundary
      | .restrictsStanding => .restrictsStanding
      | .replacesBoundary => .replacesBoundary

def DifferenceCode.Sound
    (code : DifferenceCode)
    (canonical candidate : DecisionVector) : Prop :=
  match code with
  | .equivalent =>
      NoFalsePositive canonical candidate ∧
        NoFalseNegative canonical candidate
  | .extendsStanding =>
      FalsePositive canonical candidate ∧
        NoFalseNegative canonical candidate
  | .restrictsStanding =>
      NoFalsePositive canonical candidate ∧
        FalseNegative canonical candidate
  | .replacesBoundary =>
      FalsePositive canonical candidate ∧
        FalseNegative canonical candidate

theorem DifferenceCode.prepend_sound
    {canonical candidate : DecisionVector} :
    (code : DifferenceCode) ->
    (canonicalHead candidateHead : Bool) ->
    code.Sound canonical candidate ->
    (code.prepend canonicalHead candidateHead).Sound
      (canonicalHead :: canonical) (candidateHead :: candidate)
  | .equivalent, false, false, ⟨noPositive, noNegative⟩ =>
      ⟨.bothFalse noPositive, .bothFalse noNegative⟩
  | .extendsStanding, false, false, ⟨positive, noNegative⟩ =>
      ⟨.there positive, .bothFalse noNegative⟩
  | .restrictsStanding, false, false, ⟨noPositive, negative⟩ =>
      ⟨.bothFalse noPositive, .there negative⟩
  | .replacesBoundary, false, false, ⟨positive, negative⟩ =>
      ⟨.there positive, .there negative⟩
  | .equivalent, true, true, ⟨noPositive, noNegative⟩ =>
      ⟨.bothTrue noPositive, .bothTrue noNegative⟩
  | .extendsStanding, true, true, ⟨positive, noNegative⟩ =>
      ⟨.there positive, .bothTrue noNegative⟩
  | .restrictsStanding, true, true, ⟨noPositive, negative⟩ =>
      ⟨.bothTrue noPositive, .there negative⟩
  | .replacesBoundary, true, true, ⟨positive, negative⟩ =>
      ⟨.there positive, .there negative⟩
  | .equivalent, false, true, ⟨_, noNegative⟩ =>
      ⟨.here, .candidateOnly noNegative⟩
  | .extendsStanding, false, true, ⟨_, noNegative⟩ =>
      ⟨.here, .candidateOnly noNegative⟩
  | .restrictsStanding, false, true, ⟨_, negative⟩ =>
      ⟨.here, .there negative⟩
  | .replacesBoundary, false, true, ⟨_, negative⟩ =>
      ⟨.here, .there negative⟩
  | .equivalent, true, false, ⟨noPositive, _⟩ =>
      ⟨.canonicalOnly noPositive, .here⟩
  | .extendsStanding, true, false, ⟨positive, _⟩ =>
      ⟨.there positive, .here⟩
  | .restrictsStanding, true, false, ⟨noPositive, _⟩ =>
      ⟨.canonicalOnly noPositive, .here⟩
  | .replacesBoundary, true, false, ⟨positive, _⟩ =>
      ⟨.there positive, .here⟩

/-- `none` denotes a genuine domain-length change. -/
def classifyDifference :
    (canonical : DecisionVector) -> DecisionVector -> Option DifferenceCode
  | [] => fun candidate =>
      match candidate with
      | [] => some .equivalent
      | _ :: _ => none
  | canonicalHead :: canonical => fun candidate =>
      match candidate with
      | [] => none
      | candidateHead :: candidate =>
          Option.map
            (fun code => code.prepend canonicalHead candidateHead)
            (classifyDifference canonical candidate)

theorem classifyDifference_sound
    {canonical candidate : DecisionVector}
    {code : DifferenceCode}
    (result : classifyDifference canonical candidate = some code) :
    code.Sound canonical candidate := by
  induction canonical generalizing candidate code with
  | nil =>
      cases candidate with
      | nil =>
          rw [classifyDifference] at result
          cases Option.some.inj result
          exact ⟨.nil, .nil⟩
      | cons => cases result
  | cons canonicalHead canonical inductionHypothesis =>
      cases candidate with
      | nil => cases result
      | cons candidateHead candidate =>
          change Option.map
            (fun tailCode => tailCode.prepend canonicalHead candidateHead)
            (classifyDifference canonical candidate) = some code at result
          cases hTail : classifyDifference canonical candidate with
          | none =>
              rw [hTail] at result
              cases result
          | some tailCode =>
              rw [hTail] at result
              have codeEq :
                  tailCode.prepend canonicalHead candidateHead = code :=
                Option.some.inj result
              cases codeEq
              exact DifferenceCode.prepend_sound
                tailCode canonicalHead candidateHead
                (inductionHypothesis hTail)

theorem classifyDifference_complete_of_sameDomain
    {canonical candidate : DecisionVector}
    (sameDomain : SameDomain canonical candidate) :
    exists code, classifyDifference canonical candidate = some code := by
  induction canonical generalizing candidate with
  | nil =>
      cases candidate with
      | nil => exact ⟨.equivalent, rfl⟩
      | cons head tail => cases sameDomain
  | cons canonicalHead canonical inductionHypothesis =>
      cases candidate with
      | nil => cases sameDomain
      | cons candidateHead candidate =>
          have tailSame : SameDomain canonical candidate :=
            Nat.succ.inj sameDomain
          rcases inductionHypothesis tailSame with ⟨tailCode, tailResult⟩
          refine ⟨tailCode.prepend canonicalHead candidateHead, ?_⟩
          change Option.map
            (fun code => code.prepend canonicalHead candidateHead)
            (classifyDifference canonical candidate) =
              some (tailCode.prepend canonicalHead candidateHead)
          rw [tailResult]
          rfl

theorem eq_of_noFalsePositive_noFalseNegative :
    {canonical candidate : DecisionVector} ->
      NoFalsePositive canonical candidate ->
      NoFalseNegative canonical candidate ->
      canonical = candidate
  | [], [], .nil, .nil => rfl
  | false :: canonical, false :: candidate,
      .bothFalse noPositive, .bothFalse noNegative => by
        cases eq_of_noFalsePositive_noFalseNegative noPositive noNegative
        rfl
  | true :: canonical, true :: candidate,
      .bothTrue noPositive, .bothTrue noNegative => by
        cases eq_of_noFalsePositive_noFalseNegative noPositive noNegative
        rfl

inductive HasDecision (verdict : Bool) : DecisionVector -> Prop where
  | here {tail : DecisionVector} : HasDecision verdict (verdict :: tail)
  | there {head : Bool} {tail : DecisionVector}
      (witness : HasDecision verdict tail) :
      HasDecision verdict (head :: tail)

def complement : DecisionVector -> DecisionVector
  | [] => []
  | head :: tail => (!head) :: complement tail

theorem complement_length :
    (vector : DecisionVector) ->
      (complement vector).length = vector.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (complement_length tail)

theorem falsePositive_complement_of_hasFalse
    {vector : DecisionVector}
    (failure : HasDecision false vector) :
    FalsePositive vector (complement vector) := by
  induction failure with
  | here => exact .here
  | there witness inductionHypothesis => exact .there inductionHypothesis

theorem falseNegative_complement_of_hasTrue
    {vector : DecisionVector}
    (standing : HasDecision true vector) :
    FalseNegative vector (complement vector) := by
  induction standing with
  | here => exact .here
  | there witness inductionHypothesis => exact .there inductionHypothesis

structure NondegenerateBoundary (canonical : DecisionVector) : Prop where
  standing : HasDecision true canonical
  failure : HasDecision false canonical

end DecisionVector

/-- An extensional governance table with an explicitly aligned coordinate list. -/
structure DecisionTable (Point : Type u) where
  coordinates : List Point
  verdicts : DecisionVector
  aligned : coordinates.length = verdicts.length
  unique : coordinates.Nodup

namespace DecisionTable

def SameDomain {Point : Type u}
    (canonical candidate : DecisionTable Point) : Prop :=
  canonical.coordinates = candidate.coordinates

theorem verdicts_sameDomain
    {Point : Type u}
    {canonical candidate : DecisionTable Point}
    (sameDomain : SameDomain canonical candidate) :
    DecisionVector.SameDomain canonical.verdicts candidate.verdicts := by
  unfold DecisionVector.SameDomain
  rw [← canonical.aligned, ← candidate.aligned, sameDomain]

end DecisionTable

/-- Governance behavior is the extensional coordinate-and-verdict table. -/
abbrev GovernanceRoute (Point : Type u) := DecisionTable Point

/-- Metadata may present a governance route but is not part of its behavior. -/
structure RoutePresentation (Metadata : Type u) (Point : Type u) where
  metadata : Metadata
  governance : GovernanceRoute Point

namespace RoutePresentation

def BookkeepingEquivalent
    {Metadata Point : Type u}
    (left right : RoutePresentation Metadata Point) : Prop :=
  left.governance = right.governance

theorem metadata_erased
    {Metadata Point : Type u}
    {left right : RoutePresentation Metadata Point}
    (sameGovernance : left.governance = right.governance) :
    BookkeepingEquivalent left right :=
  sameGovernance

end RoutePresentation

end AASC
