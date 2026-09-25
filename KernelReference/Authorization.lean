import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# Finite semantic authorization and grounded support

This module formalizes the finite dependency arguments of the v50 reference
manuscript. An edge runs from a required predecessor to its dependent node.
Authority is supplied by the interpretation and its target-use warrant relation,
not by a node label or by assuming the desired global soundness conclusion.

The authorization theorem locates a globally minimal authoritative ancestor.
The separate list theorem selects the first authority on a particular path;
no theorem identifies all such pathwise first nodes with global minima.

These are structural results about the explicitly supplied interpretations.
They do not prove that an arbitrary interpretation genuinely supplies physical
or mathematical warrant, nor do they mechanize the constitutive argument.
-/

namespace KernelReference.Authorization

universe u v w

/-- An acyclic support graph. Finiteness is imposed on the theorems needing it. -/
structure SupportGraph (Node : Type u) where
  edge : Node → Node → Prop
  acyclic : ∀ n, ¬ Relation.TransGen edge n n

namespace SupportGraph

variable {Node : Type u} (G : SupportGraph Node)

abbrev Ancestor := Relation.ReflTransGen G.edge
abbrev StrictAncestor := Relation.TransGen G.edge

/-- A premise has no required predecessor in the declared complete graph. -/
def Premise (n : Node) : Prop := ∀ p, ¬ G.edge p n

theorem ancestor_wellFounded [Finite Node] : WellFounded G.StrictAncestor := by
  letI : Std.Irrefl G.StrictAncestor := ⟨G.acyclic⟩
  exact Finite.wellFounded_of_trans_of_irrefl G.StrictAncestor

theorem edge_wellFounded [Finite Node] : WellFounded G.edge :=
  Subrelation.wf (fun h => Relation.TransGen.single h) G.ancestor_wellFounded

end SupportGraph

/-- Explicit semantics, separate from the graph and from any assertion of
soundness. `suppliesWarrant` is a domain relation requiring its own justification. -/
structure Interpretation (Node : Type u) (Statement : Type v) (TargetUse : Type w) where
  statement : Node → Statement
  suppliesWarrant : Statement → TargetUse → Prop

namespace Interpretation

variable {Node : Type u} {Statement : Type v} {TargetUse : Type w}

def Authority (I : Interpretation Node Statement TargetUse) (n : Node) : Prop :=
  ∃ use, I.suppliesWarrant (I.statement n) use

end Interpretation

variable {Node : Type u} {Statement : Type v} {TargetUse : Type w}
variable (G : SupportGraph Node) (I : Interpretation Node Statement TargetUse)

/-- The conclusion introduces authority while none of its required immediate
predecessors has target authority. The node has an actual incoming dependency. -/
def IntroducingRule (n : Node) : Prop :=
  I.Authority n ∧ (∃ p, G.edge p n) ∧ ∀ p, G.edge p n → ¬ I.Authority p

/-- Stronger than first-on-one-path: there is no authoritative strict ancestor
anywhere in the complete supporting graph. -/
def GloballyMinimalAuthority (n : Node) : Prop :=
  I.Authority n ∧ ∀ p, G.StrictAncestor p n → ¬ I.Authority p

/-- Restrict to the ancestors of the warranted conclusion and select a minimum.
No agreement equation or pre-existing cut is assumed. -/
theorem exists_minimal_authority_ancestor [Finite Node] {conclusion : Node}
    (hconclusion : I.Authority conclusion) :
    ∃ n, G.Ancestor n conclusion ∧ GloballyMinimalAuthority G I n := by
  let S : Set Node := {n | G.Ancestor n conclusion ∧ I.Authority n}
  have hS : S.Nonempty := ⟨conclusion, Relation.ReflTransGen.refl, hconclusion⟩
  obtain ⟨n, hn, hmin⟩ := G.ancestor_wellFounded.has_min S hS
  refine ⟨n, hn.1, hn.2, ?_⟩
  intro p hpn hp
  have hpS : p ∈ S := ⟨hpn.to_reflTransGen.trans hn.1, hp⟩
  exact hmin p hpS hpn

/-- The finite semantic authorization-cut lemma (manuscript 4.2): authority
occurs either at a premise or at an inference introducing it. -/
theorem finite_authorization_cut [Finite Node] {conclusion : Node}
    (hconclusion : I.Authority conclusion) :
    ∃ n, G.Ancestor n conclusion ∧ GloballyMinimalAuthority G I n ∧
      ((G.Premise n ∧ I.Authority n) ∨ IntroducingRule G I n) := by
  classical
  obtain ⟨n, hnc, hn, hmin⟩ := exists_minimal_authority_ancestor G I hconclusion
  refine ⟨n, hnc, ⟨hn, hmin⟩, ?_⟩
  by_cases hp : G.Premise n
  · exact Or.inl ⟨hp, hn⟩
  · right
    have incoming : ∃ p, G.edge p n := by
      simpa only [SupportGraph.Premise, not_forall, not_not] using hp
    exact ⟨hn, incoming, fun p hpn => hmin p (.single hpn)⟩

/-- Governance-free here excludes actual warranted premises and actual
authority-introducing inferences; it is not a syntactic vocabulary condition. -/
def GovernanceFree : Prop :=
  (∀ n, G.Premise n → ¬ I.Authority n) ∧ ∀ n, ¬ IntroducingRule G I n

theorem governance_free_has_no_warrant [Finite Node]
    (hfree : GovernanceFree G I) (conclusion : Node) : ¬ I.Authority conclusion := by
  intro hc
  obtain ⟨n, _, _, hp | hr⟩ := finite_authorization_cut G I hc
  · exact hfree.1 n hp.1 hp.2
  · exact hfree.2 n hr

/-- First authority on one finite path/list. The prefix restriction is local
to this list; it does not assert absence of authority on other incoming paths. -/
theorem first_authority_on_list (path : List Node)
    (h : ∃ n ∈ path, I.Authority n) :
    ∃ pre n post, path = pre ++ n :: post ∧ I.Authority n ∧
      ∀ p ∈ pre, ¬ I.Authority p := by
  classical
  induction path with
  | nil => simp at h
  | cons a tail ih =>
      by_cases ha : I.Authority a
      · exact ⟨[], a, tail, rfl, ha, by simp⟩
      · have ht : ∃ n ∈ tail, I.Authority n := by
          obtain ⟨n, hn, hna⟩ := h
          simp only [List.mem_cons] at hn
          rcases hn with rfl | hn
          · exact False.elim (ha hna)
          · exact ⟨n, hn, hna⟩
        obtain ⟨pre, n, post, hpath, hn, hpre⟩ := ih ht
        refine ⟨a :: pre, n, post, by simp [hpath], hn, ?_⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ha
        · exact hpre p hp

/-! ## Support constructed from local checks and all required predecessors -/

/-- Positive support is generated by the local conjunction recurrence, not
postulated global soundness. The recursive argument ranges over every predecessor. -/
inductive Supported (G : SupportGraph Node) (localPositive : Node → Prop) : Node → Prop
  | intro (n : Node) : localPositive n →
      (∀ p, G.edge p n → Supported G localPositive p) → Supported G localPositive n

variable {G} {localPositive : Node → Prop}

theorem supported_iff (n : Node) :
    Supported G localPositive n ↔
      localPositive n ∧ ∀ p, G.edge p n → Supported G localPositive p := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨hn, hp⟩
  · rintro ⟨hn, hp⟩
    exact Supported.intro n hn hp

theorem supported_ancestor {a b : Node} (hab : G.Ancestor a b)
    (hb : Supported G localPositive b) : Supported G localPositive a := by
  induction hab with
  | refl => exact hb
  | @tail p q hpath hpq ih =>
      exact ih (((supported_iff q).mp hb).2 p hpq)

/-- The manuscript's exact-support theorem: all and only the required ancestor
checks, including the endpoint's own check, determine positive support. -/
theorem supported_iff_all_ancestors [Finite Node] (n : Node) :
    Supported G localPositive n ↔ ∀ a, G.Ancestor a n → localPositive a := by
  constructor
  · intro hn a han
    exact ((supported_iff a).mp (supported_ancestor han hn)).1
  · intro hall
    induction n using G.edge_wellFounded.induction with
    | h n ih =>
        refine Supported.intro n (hall n .refl) ?_
        intro p hpn
        exact ih p hpn (fun a hap => hall a (hap.tail hpn))

/-- An actual failed required ancestor prevents positive support. -/
theorem failed_ancestor_blocks {a n : Node} (han : G.Ancestor a n)
    (ha : ¬ localPositive a) : ¬ Supported G localPositive n := by
  intro hn
  exact ha ((supported_iff a).mp (supported_ancestor han hn)).1

/-- Local verification rules imply global standing by induction on the
constructed support. There is no assumed global soundness field. -/
theorem local_soundness_global {Standing : Node → Prop}
    (localSound : ∀ n, localPositive n →
      (∀ p, G.edge p n → Standing p) → Standing n)
    {n : Node} (hn : Supported G localPositive n) : Standing n := by
  induction hn with
  | intro n hn hp ih => exact localSound n hn ih

/-- A retained extension keeps local checks and the entire incoming dependency
list of every old node. Extra new dependencies into an old node are excluded by
the backwards clause; outgoing old-to-new edges remain possible. -/
structure RetainedExtension {NewNode : Type v}
    (G : SupportGraph Node) (H : SupportGraph NewNode)
    (localPositive : Node → Prop) (newLocal : NewNode → Prop) where
  embed : Node → NewNode
  injective : Function.Injective embed
  local_iff : ∀ n, newLocal (embed n) ↔ localPositive n
  edge_forward : ∀ {p n}, G.edge p n → H.edge (embed p) (embed n)
  predecessors_complete : ∀ {q n}, H.edge q (embed n) →
    ∃ p, q = embed p ∧ G.edge p n

/-- Every old support value is preserved by an extension retaining all its
original checks and predecessor lists. -/
theorem retained_support_iff {NewNode : Type v} {H : SupportGraph NewNode}
    {newLocal : NewNode → Prop}
    (E : RetainedExtension G H localPositive newLocal) (n : Node) :
    Supported H newLocal (E.embed n) ↔ Supported G localPositive n := by
  constructor
  · intro hs
    generalize heq : E.embed n = q at hs
    induction hs generalizing n with
    | intro q hq hpred ih =>
        refine Supported.intro n ((E.local_iff n).mp (heq ▸ hq)) ?_
        intro p hpn
        exact ih (E.embed p) (heq ▸ E.edge_forward hpn) p rfl
  · intro hs
    induction hs with
    | intro n hn hpred ih =>
        refine Supported.intro (E.embed n) ((E.local_iff n).mpr hn) ?_
        intro q hqn
        obtain ⟨p, rfl, hpn⟩ := E.predecessors_complete hqn
        exact ih p hpn


/-- An old unsupported node remains unsupported and blocks every new required
 descendant that retains it. This is support conservation, not time asymmetry. -/
theorem retained_failure_blocks_descendant {NewNode : Type v} {H : SupportGraph NewNode}
    {newLocal : NewNode → Prop}
    (E : RetainedExtension G H localPositive newLocal) {n : Node} {v : NewNode}
    (hn : ¬ Supported G localPositive n) (hnv : H.Ancestor (E.embed n) v) :
    ¬ Supported H newLocal v := by
  intro hv
  exact hn ((retained_support_iff E n).mp (supported_ancestor hnv hv))
/-- A report checked against all required ancestors yields support and, from
verified local rules, standing. Coverage is for the original graph; a report
cannot silently select only convenient predecessors. -/
theorem report_from_local_evidence [Finite Node] {Standing : Node → Prop}
    (localSound : ∀ n, localPositive n →
      (∀ p, G.edge p n → Standing p) → Standing n)
    (reported : Finset Node) (n : Node)
    (coverage : ∀ a, G.Ancestor a n → a ∈ reported)
    (checks : ∀ a ∈ reported, localPositive a) :
    Supported G localPositive n ∧ Standing n := by
  have hs : Supported G localPositive n :=
    (supported_iff_all_ancestors n).mpr (fun a ha => checks a (coverage a ha))
  exact ⟨hs, local_soundness_global localSound hs⟩

/-- With an exact ancestor list, positive support supplies every local positive
check. Access to authentic evidence for those checks is a separate obligation. -/
theorem supported_report_checks (reported : Finset Node) (n : Node)
    (noSurplus : ∀ a ∈ reported, G.Ancestor a n)
    (hs : Supported G localPositive n) : ∀ a ∈ reported, localPositive a := by
  intro a ha
  exact ((supported_iff a).mp (supported_ancestor (noSurplus a ha) hs)).1

/-! ## Nonvacuous finite examples and the path/global distinction -/

namespace Examples

private theorem lt_of_transGen {k : Nat} {a b : Fin k}
    (h : Relation.TransGen (fun a b : Fin k => a < b) a b) : a < b := by
  induction h with
  | single h => exact h
  | tail h hbc ih => exact lt_trans ih hbc

/-- Three nodes, with dependencies 0 -> 1, 1 -> 2, and 0 -> 2. -/
def graph : SupportGraph (Fin 3) where
  edge a b := a < b
  acyclic n h := (lt_irrefl n) (lt_of_transGen h)

instance : DecidableRel graph.edge := fun a b => inferInstanceAs (Decidable (a < b))

/-- Nodes 1 and 2 genuinely supply a target-use warrant; node 0 is data only. -/
def interpretation : Interpretation (Fin 3) (Fin 3) Unit where
  statement := id
  suppliesWarrant n _ := n = 1 ∨ n = 2

theorem one_authoritative : interpretation.Authority 1 := ⟨(), Or.inl rfl⟩
theorem two_authoritative : interpretation.Authority 2 := ⟨(), Or.inr rfl⟩
theorem zero_not_authoritative : ¬ interpretation.Authority 0 := by
  rintro ⟨u, h⟩
  exact (by decide : ¬ ((0 : Fin 3) = 1 ∨ (0 : Fin 3) = 2)) h

/-- Authority first enters through a real inference with a non-authoritative
required predecessor, not through an already warranted source. -/
theorem one_introduces_authority : IntroducingRule graph interpretation 1 := by
  refine ⟨one_authoritative, ⟨0, by decide⟩, ?_⟩
  intro p hp ha
  obtain ⟨u, (rfl | rfl)⟩ := ha
  · exact (lt_irrefl (1 : Fin 3)) hp
  · exact (by decide : ¬ ((2 : Fin 3) < 1)) hp

/-- The finite cut theorem is applied to a warranted non-source endpoint. -/
theorem warranted_endpoint_has_cut :
    ∃ n, graph.Ancestor n 2 ∧ GloballyMinimalAuthority graph interpretation n ∧
      ((graph.Premise n ∧ interpretation.Authority n) ∨
        IntroducingRule graph interpretation n) :=
  finite_authorization_cut graph interpretation two_authoritative

/-- On the actual shortcut path 0 -> 2, 2 is first authority. But 1 is an
additional authoritative ancestor on the different path 0 -> 1 -> 2. -/
theorem path_first_need_not_be_global_minimal :
    graph.edge 0 2 ∧
    (∀ p ∈ ([0] : List (Fin 3)), ¬ interpretation.Authority p) ∧
    interpretation.Authority 2 ∧
    ¬ GloballyMinimalAuthority graph interpretation 2 := by
  refine ⟨by decide, ?_, two_authoritative, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact zero_not_authoritative
  · intro hmin
    exact hmin.2 1 (.single (by decide)) one_authoritative

/-- A failed required check at 1 blocks the later node 2. -/
theorem failed_required_check_blocks_endpoint :
    ¬ Supported graph (fun n => n ≠ 1) 2 :=
  failed_ancestor_blocks (.single (by decide : graph.edge 1 2)) (by simp)

/-- The same graph also has a positive grounded realization when all actual
local checks pass; the support predicate is not empty by construction. -/
theorem positive_grounded_endpoint : Supported graph (fun _ => True) 2 :=
  (supported_iff_all_ancestors 2).mpr (fun _ _ => trivial)

end Examples
end KernelReference.Authorization
