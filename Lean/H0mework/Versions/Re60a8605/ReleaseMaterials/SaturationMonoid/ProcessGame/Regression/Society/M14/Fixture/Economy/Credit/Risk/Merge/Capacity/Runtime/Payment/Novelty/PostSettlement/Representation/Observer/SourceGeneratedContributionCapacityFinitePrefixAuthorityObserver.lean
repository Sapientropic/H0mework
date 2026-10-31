import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Replay.Producer.SourceGeneratedContributionCapacityPostSettlementPaidReplay

/-!
# Finite-prefix authority observer

At boundary `n`, the boundary-fixed finite representation remembers exactly the
history slots `0 .. n` and one normalized singleton-pulse slot.  All later
replays enter the last finite slot.  The law is fixed by the already generated
prefix; it does not mention a future pair, failure, U7 branch or target.

This file deliberately exposes no canonical kernel pair or no-section
theorem.  Those require the downstream responsibility incidence that consumes
both Payments, channel returns, source ownership and the root consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver

noncomputable section

open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay

/-- Entirely finite visible carrier of the prefix law. -/
abbrev FinitePrefixReplayVisibleAt (boundary : Nat) :=
  Fin (boundary + 1) × Fin 1

def finitePrefixHistorySlotAt (boundary index : Nat) : Fin (boundary + 1) :=
  ⟨min index boundary, Nat.lt_succ_of_le (min_le_right index boundary)⟩

/-- The law-visible image is fixed before the later pair is generated. -/
def finitePrefixReplayAuthorityObserverAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AuthorityObserver
      (AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
      (FinitePrefixReplayVisibleAt boundary)
      AnyPeriodicActualServiceExit where
  forget := fun replay =>
    ⟨finitePrefixHistorySlotAt boundary replay.1, ⟨0, Nat.zero_lt_succ 0⟩⟩
  authorityK := fun replay => replay.2.authorityK

theorem finitePrefixHistorySlot_exact_of_le
    {boundary index : Nat} (index_le : index ≤ boundary) :
    (finitePrefixHistorySlotAt boundary index).val = index := by
  simp [finitePrefixHistorySlotAt, min_eq_left index_le]

theorem finitePrefixHistorySlot_afterBoundary
    (boundary extra : Nat) :
    finitePrefixHistorySlotAt boundary (boundary + 1 + extra) =
      finitePrefixHistorySlotAt boundary boundary := by
  apply Fin.ext
  change min (boundary + 1 + extra) boundary = min boundary boundary
  omega

end
end M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver.finitePrefixHistorySlot_afterBoundary
