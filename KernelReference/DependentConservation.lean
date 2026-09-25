import Init

/-!
# Conservation for query-indexed result families

The bearer, complete query, result family and incidence relation are supplied
independently. Determinacy and the two individual incidence witnesses imply
agreement; no representation agreement or factorization equation is an input.

This extends the common-result-type support to the dependent result families
used in manuscript Sections 6.1--6.3. It does not formalize the constitutive
objecthood argument or establish a physical domain's incidence premises.
-/

namespace AASC.KernelReference.DependentConservation

universe u v w r s

variable {Bearer : Type u} {Query : Type v} {Value : Query → Type w}

/-- Uniqueness concerns the particular original result incidence. -/
def Determinate (J : (b : Bearer) → (q : Query) → Value q → Prop) : Prop :=
  ∀ b q x y, J b q x → J b q y → x = y

/-- Equality transport changes only the type index of an existing result. -/
def transportResult {q q' : Query} (h : q = q') (value : Value q) : Value q' :=
  h ▸ value

theorem transportResult_rfl (q : Query) (value : Value q) :
    transportResult rfl value = value := rfl

theorem incidence_transport
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    {b b' : Bearer} {q q' : Query} (hb : b = b') (hq : q = q')
    {value : Value q} (incident : J b q value) :
    J b' q' (transportResult hq value) := by
  cases hb
  cases hq
  exact incident

/-- Local conservation, including transport between equal query indices. -/
theorem output_eq_of_same_bearer_query
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J)
    {b b' : Bearer} {q q' : Query} {left : Value q} {right : Value q'}
    (sameBearer : b = b') (sameQuery : q = q')
    (leftIncident : J b q left) (rightIncident : J b' q' right) :
    transportResult sameQuery left = right := by
  exact determinate b' q' _ _
    (incidence_transport J sameBearer sameQuery leftIncident) rightIncident

/-- No finiteness or generated-syntax assumption is needed for dependent profiles. -/
theorem profile_eq_of_same_bearer
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J)
    {b b' : Bearer} (sameBearer : b = b')
    (left right : (q : Query) → Value q)
    (leftSound : ∀ q, J b q (left q))
    (rightSound : ∀ q, J b' q (right q)) :
    left = right := by
  funext q
  exact output_eq_of_same_bearer_query J determinate sameBearer rfl
    (leftSound q) (rightSound q)

/-- Independently implemented representation families may have different raw types. -/
theorem all_profiles_eq_of_same_bearer
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J)
    {LeftRep : Type r} {RightRep : Type s}
    (leftBearer : LeftRep → Bearer) (rightBearer : RightRep → Bearer)
    (leftReader : LeftRep → (q : Query) → Value q)
    (rightReader : RightRep → (q : Query) → Value q)
    (leftSound : ∀ a q, J (leftBearer a) q (leftReader a q))
    (rightSound : ∀ a q, J (rightBearer a) q (rightReader a q)) :
    ∀ a a', leftBearer a = rightBearer a' → leftReader a = rightReader a' := by
  intro a a' sameBearer
  exact profile_eq_of_same_bearer J determinate sameBearer
    (leftReader a) (rightReader a') (leftSound a) (rightSound a')

theorem discordance_excludes_joint_incidence
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J)
    {b b' : Bearer} {q q' : Query} {left : Value q} {right : Value q'}
    (sameBearer : b = b') (sameQuery : q = q')
    (discordant : transportResult sameQuery left ≠ right) :
    ¬ (J b q left ∧ J b' q' right) := by
  intro both
  exact discordant (output_eq_of_same_bearer_query J determinate
    sameBearer sameQuery both.1 both.2)

theorem discordant_answer_not_incident
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J)
    {b b' : Bearer} {q q' : Query} {left : Value q} {right : Value q'}
    (sameBearer : b = b') (sameQuery : q = q')
    (leftIncident : J b q left)
    (discordant : transportResult sameQuery left ≠ right) :
    ¬ J b' q' right := by
  intro rightIncident
  exact discordance_excludes_joint_incidence J determinate sameBearer
    sameQuery discordant ⟨leftIncident, rightIncident⟩

/-- A semantic absent outcome requires absence of every original base incidence. -/
def CompleteOutcome
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (b : Bearer) (q : Query) : Option (Value q) → Prop
  | some value => J b q value
  | none => ∀ value, ¬ J b q value

theorem completeOutcome_some_iff
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (b : Bearer) (q : Query) (value : Value q) :
    CompleteOutcome J b q (some value) ↔ J b q value := Iff.rfl

theorem completeOutcome_none_iff
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (b : Bearer) (q : Query) :
    CompleteOutcome J b q none ↔ ∀ value, ¬ J b q value := Iff.rfl

theorem completeOutcome_determinate
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J) :
    Determinate (CompleteOutcome J) := by
  intro b q left right leftIncident rightIncident
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some value => exact False.elim (leftIncident value rightIncident)
  | some value =>
    cases right with
    | none => exact False.elim (rightIncident value leftIncident)
    | some value' =>
      exact congrArg some (determinate b q value value' leftIncident rightIncident)

theorem complete_outcome_conservation
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    (determinate : Determinate J)
    {b b' : Bearer} {q q' : Query}
    {left : Option (Value q)} {right : Option (Value q')}
    (sameBearer : b = b') (sameQuery : q = q')
    (leftIncident : CompleteOutcome J b q left)
    (rightIncident : CompleteOutcome J b' q' right) :
    transportResult (Value := fun q => Option (Value q)) sameQuery left = right :=
  output_eq_of_same_bearer_query (CompleteOutcome J)
    (completeOutcome_determinate J determinate) sameBearer sameQuery
    leftIncident rightIncident

theorem known_result_excludes_absent_outcome
    (J : (b : Bearer) → (q : Query) → Value q → Prop)
    {b : Bearer} {q : Query} {value : Value q}
    (incident : J b q value) : ¬ CompleteOutcome J b q none := by
  intro absent
  exact absent value incident

#print axioms output_eq_of_same_bearer_query
#print axioms profile_eq_of_same_bearer
#print axioms all_profiles_eq_of_same_bearer
#print axioms discordance_excludes_joint_incidence
#print axioms discordant_answer_not_incident
#print axioms completeOutcome_determinate
#print axioms completeOutcome_none_iff
#print axioms complete_outcome_conservation
#print axioms known_result_excludes_absent_outcome

end AASC.KernelReference.DependentConservation
