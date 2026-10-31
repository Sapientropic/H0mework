import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.FiniteExchangeFixture
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.GeneratedSettlement
import H0mework.Foundation.Agency.OriginExit

/-!
# Native settlement disposition regression

Every review uses the same process that admitted the finite exchange.  The
process-generated disposition alone decides whether the stable exchange slot
is live or terminal.  Supersession and bearer release keep live residuals;
fulfillment closes; an exact later reopen restores the same debt lineage.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M3SettlementDispositionRegression

open ResponsibilityLifecycle
open Lifecycle Universal Exchange Settlement
open M3FiniteExchangeFixture

abbrev exchangeState : P.GeneratedState :=
  exactExchangeSeed.generatedState exchangeCompiler

def settlementOf (leg : Leg)
    (event : ReviewEvent
      (exactExchangeSeed.obligation exchangeCompiler leg)) :
    ExactSettlementEdge P exchangeState.current where
  slot := exactExchangeSeed.obligationSlot exchangeCompiler leg
  obligation := exactExchangeSeed.obligation exchangeCompiler leg
  present := exactExchangeSeed.generatedState_obligationSlot_get
    exchangeCompiler leg
  event := event

/-- Exhaustion is over every generated exchange leg and every installed
review event. -/
theorem every_review_is_live_or_closed
    (leg : Leg)
    (event : ReviewEvent
      (exactExchangeSeed.obligation exchangeCompiler leg)) :
    Nonempty (ExactSettlementEdge.LiveResidualAt
      (settlementOf leg event)) ∨
      Nonempty (ExactSettlementEdge.ClosedSettlementAt
        (settlementOf leg event)) :=
  ExactSettlementEdge.live_or_closed (settlementOf leg event)

@[simp] theorem maintain_classification (leg : Leg) :
    (settlementOf leg .maintain).classification =
      ExactSettlementEdge.Class.maintained :=
  rfl

def maintainOpen (leg : Leg) :
    ExactSettlementEdge.LiveResidualAt (settlementOf leg .maintain) :=
  ⟨exactExchangeSeed.obligation exchangeCompiler leg, rfl⟩

@[simp] theorem supersession_classification (leg : Leg) :
    (settlementOf leg .supersede).classification =
      ExactSettlementEdge.Class.supersededRollover :=
  rfl

def supersessionOpen (leg : Leg) :
    ExactSettlementEdge.LiveResidualAt (settlementOf leg .supersede) :=
  ⟨exactExchangeSeed.obligation exchangeCompiler leg, rfl⟩

@[simp] theorem bearer_release_classification (leg : Leg) :
    (settlementOf leg .bearerRelease).classification =
      ExactSettlementEdge.Class.capacityReleasedWithResidue :=
  rfl

def bearerReleaseOpen (leg : Leg) :
    ExactSettlementEdge.LiveResidualAt (settlementOf leg .bearerRelease) :=
  ⟨exactExchangeSeed.obligation exchangeCompiler leg, rfl⟩

@[simp] theorem fulfilled_classification (leg : Leg) :
    (settlementOf leg .fulfill).classification =
      ExactSettlementEdge.Class.fulfilled :=
  rfl

def fulfilledClosed (leg : Leg) :
    ExactSettlementEdge.ClosedSettlementAt (settlementOf leg .fulfill) :=
  ⟨⟨exactExchangeSeed.obligation exchangeCompiler leg, .after,
      .fulfilled ()⟩,
    rfl⟩

theorem fulfilled_is_not_open (leg : Leg) :
    ¬ Nonempty
      (ExactSettlementEdge.LiveResidualAt (settlementOf leg .fulfill)) := by
  intro live
  exact (ExactSettlementEdge.live_not_closed (settlementOf leg .fulfill)
    live) ⟨fulfilledClosed leg⟩

/-! ## Exact terminal-to-reopen continuation on one stable exchange slot -/

def fulfilledAEdge : P.Edge exchangeState.current :=
  (settlementOf .a .fulfill).edge

def fulfilledAArchive : TerminalArchive V :=
  ⟨exactExchangeSeed.obligation exchangeCompiler .a, .after,
    .fulfilled ()⟩

def fulfilledASlot : Fin fulfilledAEdge.target.slots.length :=
  ⟨exactExchangeSeed.obligationSlotIndex exchangeCompiler .a, by decide⟩

theorem fulfilledA_present :
    fulfilledAEdge.target.slots.get fulfilledASlot =
      .terminal fulfilledAArchive :=
  rfl

def reopenAEvent : P.ReopenEvent fulfilledAArchive :=
  ⟨rfl⟩

def reopenAEdge : P.Edge fulfilledAEdge.target :=
  .reopen fulfilledASlot fulfilledAArchive fulfilledA_present reopenAEvent

def reopenAAuthority : ReopenEdge P reopenAEdge :=
  ReopenEdge.ofEvent P fulfilledASlot fulfilledAArchive fulfilledA_present
    reopenAEvent

theorem exact_reopen_restores_live_same_lineage :
    reopenAEdge.target.slots[reopenAAuthority.slot P]? =
        some (.live (reopenAAuthority.targetObligation P)) ∧
      SameDebtLineage fulfilledAArchive.obligation
        (reopenAAuthority.targetObligation P) :=
  ⟨reopenAAuthority.target_slot P,
    reopenAAuthority.sameDebtLineage P⟩

theorem reopen_is_not_fresh_admission :
    FreshAdmissionEdge.compile P reopenAEdge = none :=
  rfl

end M3SettlementDispositionRegression
end Society
end ProcessGame
end SaturationMonoid
