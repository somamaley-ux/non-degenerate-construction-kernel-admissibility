namespace AASC

universe u v

/-- Independently interpreted route predicates over candidates. -/
structure RouteFamily (Route : Type u) (Candidate : Type v) where
  covers : Route -> Candidate -> Prop

namespace RouteFamily

/-- A concrete finite route list covers every independently selected candidate. -/
def Exhausts
    {Route : Type u}
    {Candidate : Type v}
    (family : RouteFamily Route Candidate)
    (routes : List Route)
    (candidate : Candidate -> Prop) : Prop :=
  forall item, candidate item ->
    exists route, route ∈ routes ∧ family.covers route item

theorem singleton_exhausts_of_uniform_cover
    {Route : Type u}
    {Candidate : Type v}
    (family : RouteFamily Route Candidate)
    (route : Route)
    (candidate : Candidate -> Prop)
    (hCover : forall item, candidate item -> family.covers route item) :
    family.Exhausts [route] candidate := by
  intro item hCandidate
  exact ⟨route, by simp, hCover item hCandidate⟩

theorem empty_not_exhaustive_of_candidate
    {Route : Type u}
    {Candidate : Type v}
    (family : RouteFamily Route Candidate)
    (candidate : Candidate -> Prop)
    (item : Candidate)
    (hCandidate : candidate item) :
    Not (family.Exhausts [] candidate) := by
  intro hExhausts
  rcases hExhausts item hCandidate with ⟨route, hMember, _⟩
  nomatch hMember

end RouteFamily

end AASC
