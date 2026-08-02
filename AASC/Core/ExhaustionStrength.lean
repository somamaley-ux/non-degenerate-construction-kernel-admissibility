import AASC.Core.SameDomainRoutes

namespace AASC.DecisionVector

/-- The one-coordinate positive endpoint table. -/
def positiveSingleton : DecisionVector := [true]

/-- The same-domain table in which that endpoint loses standing. -/
def negativeSingleton : DecisionVector := [false]

theorem positive_negative_singleton_sameDomain :
    SameDomain positiveSingleton negativeSingleton := by
  rfl

theorem classify_positive_negative_singleton :
    classifyDifference positiveSingleton negativeSingleton =
      some .restrictsStanding := by
  rfl

theorem positive_negative_singleton_classification_sound :
    DifferenceCode.Sound .restrictsStanding
      positiveSingleton negativeSingleton :=
  classifyDifference_sound classify_positive_negative_singleton

theorem positive_negative_singleton_falseNegative :
    FalseNegative positiveSingleton negativeSingleton :=
  .here

/-- Fixed-domain exhaustion classifies a negative endpoint table; it does
not by itself exclude that table or restore the positive verdict. -/
theorem fixedDomainExhaustion_allows_negative_endpoint :
    SameDomain positiveSingleton negativeSingleton /\
      classifyDifference positiveSingleton negativeSingleton =
        some .restrictsStanding /\
      DifferenceCode.Sound .restrictsStanding
        positiveSingleton negativeSingleton /\
      FalseNegative positiveSingleton negativeSingleton :=
  ⟨positive_negative_singleton_sameDomain,
    classify_positive_negative_singleton,
    positive_negative_singleton_classification_sound,
    positive_negative_singleton_falseNegative⟩

/-- There can be no theorem saying that same-domain status alone preserves
all positive standing: the singleton negative table is a concrete counterexample. -/
theorem not_all_sameDomain_routes_preserveStanding :
    Not (forall canonical candidate : DecisionVector,
      SameDomain canonical candidate -> NoFalseNegative canonical candidate) := by
  intro preserves
  exact (preserves positiveSingleton negativeSingleton
    positive_negative_singleton_sameDomain).refute
      positive_negative_singleton_falseNegative

end AASC.DecisionVector
