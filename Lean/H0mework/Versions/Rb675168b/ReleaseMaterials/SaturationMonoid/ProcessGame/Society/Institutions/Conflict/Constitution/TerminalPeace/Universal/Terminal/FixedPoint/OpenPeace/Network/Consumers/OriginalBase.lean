import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Settlement
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.OriginalBase

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual
open Quantities.Execution (endAt next endAt_append)
open ExposureGuard
open NoFreeProbe (PaidReview)

open private current from
  H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original
open private rebased_world from
  H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Inherited

noncomputable section

local notation "Seed" => TerminalPeace.Original.seed
local notation "Community" => TerminalPeace.Original.community
local notation "History" => Reparation.Actual.Script Bool Bool Bool Unit Unit
local notation "Entry" => Reparation.Actual.Input Bool Bool Bool Unit Unit
local notation "At" => Reparation.Actual.State Seed Community

private theorem personal_positions_world (answers : OwnerAnswers Seed) (past : History) (input : Entry)
    (positions : List (Allocation.Position Seed past input))
    (state : StateAt Seed Community (next (endAt Seed past) input)) :
    (Receipts.consumePositions answers past input positions state).world = state.world := by
  induction positions generalizing state with
  | nil => rfl
  | cons position remaining earlier =>
    rw [Receipts.consumePositions, earlier]
    rfl

private def inheritedPersonalTick (answers : OwnerAnswers Seed) {past : History} (state : At past)
    (input : Entry) (prior : InheritedCalculus state.world) :
    InheritedCalculus (Receipts.writeTick answers state input).world := by
  let material := posted state input
  let positions := Allocation.itemPositions (seed := Seed) past input
  let written := Receipts.consumePositions answers past input positions material
  have same : (Receipts.writeTick answers state input).world = written.world :=
    rebased_world written (endAt_append Seed past [input]).symm
  exact (same.trans (personal_positions_world answers past input positions material)).symm ▸
    inheritedPosted state input prior

private theorem cast_world {past later : History} (same : past = later) (state : At past) :
    (same ▸ state : At later).world = state.world := by
  cases same
  rfl

private def inheritedPersonalHistory (answers : OwnerAnswers Seed) {past : History} (state : At past)
    (suffix : History) (prior : InheritedCalculus state.world) :
    InheritedCalculus (Receipts.writeAfter answers state suffix).world := by
  induction suffix using List.reverseRecOn with
  | nil =>
    rw [Receipts.writeAfter, List.reverseRecOn_nil, cast_world]
    exact prior
  | append_singleton previous input earlier =>
    rw [Receipts.writeAfter_snoc, cast_world]
    exact inheritedPersonalTick answers _ input earlier

private def inheritedProtected : InheritedCalculus protectedCut.state.world := by
  unfold protectedCut firstWrite Visit.step Visit.advance
  exact inheritedPersonalHistory _ TerminalPeace.Original.state _ (inheritedRun _ _ _)

private def inheritedPaidBody : InheritedCalculus Settlement.paidBody.world :=
  inheritedSettlementTick Settlement.replies protectedCut.state Settlement.payerInput inheritedProtected

/-- The settled original peace current inherits its full U7 compiler
from the literal material and financial replay and the actual discharge. -/
def inherited : InheritedCalculus current.ledger.world :=
  inheritedAdvance Settlement.paidBody none inheritedPaidBody

/-- Every actual fee receipt at this cut reads the same world index from
its canonical whole-ledger successor. -/
def inheritedAtReceipt {bid : ReviewBid Bool Bool Bool Unit Unit}
    (paid : PaidReview current bid) : InheritedCalculus paid.round.next.ledger.world := by
  have same : current.ledger.world = paid.round.next.ledger.world :=
    congrArg AnyAuthoritativeRootCurrent.N paid.round.wholeNext
  exact same ▸ inherited

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.OriginalBase
