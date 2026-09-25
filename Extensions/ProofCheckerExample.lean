import Init

/-!
# A structurally verified implication-elimination checker

The inference relation is defined independently of the executable checker.
Checker soundness and completeness are proved from its recursion and the
inference rules. Determinacy and complete negative outcomes are consequences.
-/

namespace AASC.ProofCheckerExample

inductive Formula where
  | atom : Nat → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

inductive ProofTree where
  | hyp : Nat → ProofTree
  | mp : ProofTree → ProofTree → ProofTree
  deriving DecidableEq, Repr

abbrev Context := List Formula

/-- Independent result incidence for a fixed context and original proof tree. -/
inductive Derives (context : Context) : ProofTree → Formula → Prop where
  | hyp {index : Nat} {formula : Formula}
      (lookup : context[index]? = some formula) :
      Derives context (.hyp index) formula
  | mp {left right : ProofTree} {antecedent conclusion : Formula}
      (major : Derives context left (.imp antecedent conclusion))
      (minor : Derives context right antecedent) :
      Derives context (.mp left right) conclusion

/-- Terminating structural checker; none means this tree has no derivable result. -/
def check (context : Context) : ProofTree → Option Formula
  | .hyp index => context[index]?
  | .mp left right =>
      match check context left, check context right with
      | some (.imp antecedent conclusion), some argument =>
          if argument = antecedent then some conclusion else none
      | _, _ => none

/-- Every successful recursive check establishes the independent inference relation. -/
theorem check_sound (context : Context) (tree : ProofTree) :
    ∀ {formula : Formula}, check context tree = some formula →
      Derives context tree formula := by
  induction tree with
  | hyp index =>
      intro formula result
      exact Derives.hyp result
  | mp left right leftIH rightIH =>
      intro formula result
      cases leftResult : check context left with
      | none => simp [check, leftResult] at result
      | some leftFormula =>
          cases leftFormula with
          | atom number => simp [check, leftResult] at result
          | imp antecedent conclusion =>
              cases rightResult : check context right with
              | none => simp [check, leftResult, rightResult] at result
              | some argument =>
                  by_cases argumentEq : argument = antecedent
                  · have conclusionEq : conclusion = formula := by
                      exact Option.some.inj
                        (by simpa [check, leftResult, rightResult, argumentEq] using result)
                    cases conclusionEq
                    exact Derives.mp (leftIH leftResult)
                      (by cases argumentEq; exact rightIH rightResult)
                  · simp [check, leftResult, rightResult, argumentEq] at result

/-- Every inference derivation is recognized by the original checker. -/
theorem check_complete {context : Context} {tree : ProofTree} {formula : Formula}
    (derivation : Derives context tree formula) :
    check context tree = some formula := by
  induction derivation with
  | hyp lookup => exact lookup
  | mp major minor majorIH minorIH =>
      simp [check, majorIH, minorIH]

/-- Exact correctness is derived, not stored as a checker field. -/
theorem check_some_iff {context : Context} {tree : ProofTree} {formula : Formula} :
    check context tree = some formula ↔ Derives context tree formula :=
  ⟨check_sound context tree, check_complete⟩

/-- Determinacy follows from the independently defined inference rules. -/
theorem derives_determinate
    {context : Context} {tree : ProofTree} {first second : Formula}
    (firstDerivation : Derives context tree first)
    (secondDerivation : Derives context tree second) :
    first = second :=
  Option.some.inj ((check_complete firstDerivation).symm.trans
    (check_complete secondDerivation))

/-- A completed none certifies absence of every derivable result. -/
theorem check_none_iff {context : Context} {tree : ProofTree} :
    check context tree = none ↔ ¬ ∃ formula, Derives context tree formula := by
  constructor
  · intro absent witness
    cases witness with
    | intro formula derivation =>
        have present := check_complete derivation
        rw [absent] at present
        cases present
  · intro absent
    cases result : check context tree with
    | none => rfl
    | some formula =>
        exact False.elim (absent ⟨formula, check_sound context tree result⟩)

/-- The complete semantic optional result, independent of checker output equality. -/
def CompleteOutcome (context : Context) (tree : ProofTree) : Option Formula → Prop
  | some formula => Derives context tree formula
  | none => ¬ ∃ formula, Derives context tree formula

theorem check_complete_outcome (context : Context) (tree : ProofTree) :
    CompleteOutcome context tree (check context tree) := by
  cases result : check context tree with
  | none => exact check_none_iff.mp result
  | some formula => exact check_sound context tree result

/-- Any two separately warranted complete outcomes at one fixed bearer agree. -/
theorem complete_outcome_determinate
    {context : Context} {tree : ProofTree} {first second : Option Formula}
    (firstSound : CompleteOutcome context tree first)
    (secondSound : CompleteOutcome context tree second) : first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some formula => exact False.elim (firstSound ⟨formula, secondSound⟩)
  | some firstFormula =>
      cases second with
      | none => exact False.elim (secondSound ⟨firstFormula, firstSound⟩)
      | some secondFormula =>
          exact congrArg some (derives_determinate firstSound secondSound)

/-- Context and original tree are fixed independently of their checked result. -/
abbrev Bearer := Context × ProofTree

def parsedCheck {Raw : Type u} (parse : Raw → Bearer) (raw : Raw) : Option Formula :=
  check (parse raw).1 (parse raw).2

/-- Parsing and the verified recursion supply the result's incidence directly. -/
theorem parsedCheck_sound {Raw : Type u} (parse : Raw → Bearer) (raw : Raw) :
    CompleteOutcome (parse raw).1 (parse raw).2 (parsedCheck parse raw) :=
  check_complete_outcome (parse raw).1 (parse raw).2

/-- Different parsers can identify the same original bearer before checking. -/
theorem parsed_check_agreement
    {LeftRaw : Type u} {RightRaw : Type v}
    (leftParse : LeftRaw → Bearer) (rightParse : RightRaw → Bearer)
    (left : LeftRaw) (right : RightRaw)
    (sameBearer : leftParse left = rightParse right) :
    parsedCheck leftParse left = parsedCheck rightParse right := by
  apply complete_outcome_determinate (parsedCheck_sound leftParse left)
  rw [sameBearer]
  exact parsedCheck_sound rightParse right

/-- Arbitrary readers agree when each original output is separately warranted. -/
theorem warranted_reader_agreement
    {LeftRaw : Type u} {RightRaw : Type v}
    (leftParse : LeftRaw → Bearer) (rightParse : RightRaw → Bearer)
    (leftRead : LeftRaw → Option Formula) (rightRead : RightRaw → Option Formula)
    (left : LeftRaw) (right : RightRaw)
    (sameBearer : leftParse left = rightParse right)
    (leftSound : CompleteOutcome (leftParse left).1 (leftParse left).2 (leftRead left))
    (rightSound : CompleteOutcome (rightParse right).1 (rightParse right).2 (rightRead right)) :
    leftRead left = rightRead right := by
  apply complete_outcome_determinate leftSound
  rw [sameBearer]
  exact rightSound

end AASC.ProofCheckerExample

#print axioms AASC.ProofCheckerExample.check_sound
#print axioms AASC.ProofCheckerExample.check_complete
#print axioms AASC.ProofCheckerExample.check_some_iff
#print axioms AASC.ProofCheckerExample.derives_determinate
#print axioms AASC.ProofCheckerExample.check_none_iff
#print axioms AASC.ProofCheckerExample.check_complete_outcome
#print axioms AASC.ProofCheckerExample.complete_outcome_determinate
#print axioms AASC.ProofCheckerExample.parsedCheck_sound
#print axioms AASC.ProofCheckerExample.parsed_check_agreement
#print axioms AASC.ProofCheckerExample.warranted_reader_agreement
