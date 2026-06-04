import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.APlusCurrentFocus

namespace MaleyLean
namespace Papers
namespace MinimalConditionsForAdmissibleConstruction
namespace Surface

/--
Human-facing kernel summary.

The manuscript is represented as the kernel paper for the AASC corpus: the
fixed-domain admissibility kernel is unique up to governance equivalence, and
no same-domain construction preserving the same governance work can be derived
below it.  The A+ audit surface records this at final strength: 31 theorem-spine
rows closed or audited, with no residual or hypothesis gates.
-/
theorem SummaryStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_binary : forall a : Act, R.admissible a \/ Not (R.admissible a))
    (h_no_selector : R.noSelectorImport)
    (h_standing :
      forall a : Act, R.standing a <-> ReuseStableStanding R a)
    (h_unique :
      forall P Q : Act -> Prop,
        (forall a : Act, P a <-> R.standing a) ->
        (forall a : Act, Q a <-> R.standing a) ->
        forall a : Act, P a <-> Q a)
    (h_conservation :
      forall a b : Act,
        Not (R.standing a) -> R.licensedContinuation a b -> Not (R.standing b)) :
    Verbatim.resultTitle
        Verbatim.ResultTag.fixedDomainClosurePacket =
      "Fixed-Domain Closure Packet" /\
    FixedDomainClosurePacket R := by
  refine And.intro Verbatim.manuscriptHasFixedDomainClosurePacketEntry ?_
  exact
    PaperFixedDomainClosurePacketStatement
      R
      h_binary
      h_no_selector
      h_standing
      h_unique
      h_conservation

/-- Human-facing statement of the final A+ strength of the kernel paper. -/
theorem APlusStrengthSummaryStatement :
    Verbatim.manuscriptTitle =
      "Non-Degenerate Construction and the Kernel of Admissibility" /\
    Verbatim.manuscriptAuditStrength =
      "A+ closed: 31 theorem-spine rows, 31 closed or audited, 0 residual gates, 0 hypothesis gates." /\
    kernelAPlusCurrentProgressTuple =
      ("Final A+ closure", 31, 31, 0, 7, 14, 10, 0, 0) /\
    kernelAPlusFinalAPlusCurrentlyClosedBool = true := by
  exact
    And.intro Verbatim.manuscriptHasRegisteredTitle
      (And.intro Verbatim.manuscriptAuditStrengthStatesFinalClosure
        (And.intro rfl kernelAPlusFinalAPlusCurrentlyClosedBool_eq_true))

/--
Summary bridge into the existing bivalence/AASC governance surface.

This records that the kernel-paper construction regime supplies the prior gate
used by the downstream bivalence surface rather than being derived from that
surface.
-/
theorem BivalenceBridgeSummaryStatement
    {Act Object : Type}
    (R : ConstructionRegime Act Object)
    (h_boundary : R.boundaryFixed)
    (h_target : R.targetIdentityFixed)
    (h_scope : R.noDomainShift)
    (h_failClosed : R.actTimeFailureStable) :
    BivalenceNonDegenerateReasoning.AASCClass (bivalenceGovernanceSystem R) := by
  exact PaperBivalenceBridgeStatement R h_boundary h_target h_scope h_failClosed

end Surface
end MinimalConditionsForAdmissibleConstruction
end Papers
end MaleyLean
