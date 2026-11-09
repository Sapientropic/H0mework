import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Inherited
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Reparation.Actual
open Quantities.Execution (endAt next endAt_append)

open private rebased_world from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Inherited

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "History" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Entry" => Reparation.Actual.Input Party Good Port Technology Instrument

private theorem settlement_positions_world (answers : ReceiptAnswers seed) (past : History) (input : Entry)
    (positions : List (Allocation.Position seed past input))
    (state : StateAt seed community (next (endAt seed past) input)) :
    (TerminalPeace.Settlement.writePositions answers past input positions state).world = state.world := by
  induction positions generalizing state with
  | nil => rfl
  | cons position remaining earlier =>
    rw [TerminalPeace.Settlement.writePositions, earlier]
    rfl

/-- Settlement changes balances through its original motions. The total
U7 compiler of the posted world remains the compiler of its successor. -/
def inheritedSettlementTick (answers : ReceiptAnswers seed) {past : History}
    (state : State seed community past) (input : Entry) (prior : InheritedCalculus state.world) :
    InheritedCalculus (TerminalPeace.Settlement.writeTick answers state input).world := by
  let material := posted state input
  let positions := Allocation.itemPositions (seed := seed) past input
  let written := TerminalPeace.Settlement.writePositions answers past input positions material
  have same : (TerminalPeace.Settlement.writeTick answers state input).world = written.world :=
    rebased_world written (endAt_append seed past [input]).symm
  exact (same.trans (settlement_positions_world answers past input positions material)).symm ▸
    inheritedPosted state input prior

private theorem cast_world {past later : History} (same : past = later) (state : State seed community past) :
    (same ▸ state : State seed community later).world = state.world := by
  cases same
  rfl

def inheritedSettlementAfter (answers : ReceiptAnswers seed) {past : History}
    (state : State seed community past) (suffix : History) (prior : InheritedCalculus state.world) :
    InheritedCalculus (TerminalPeace.Universal.Occurrence.writeAfter answers state suffix).world := by
  induction suffix using List.reverseRecOn with
  | nil =>
    rw [TerminalPeace.Universal.Occurrence.writeAfter, List.reverseRecOn_nil, cast_world]
    exact prior
  | append_singleton previous input earlier =>
    rw [TerminalPeace.Universal.Occurrence.writeAfter_snoc, cast_world]
    exact inheritedSettlementTick answers _ input earlier

def inheritedReached (loss : Reparation.Actual.Occurrence seed community)
    (answers : ReceiptAnswers seed) (suffix : History) :
    InheritedCalculus (TerminalPeace.Universal.Occurrence.reached answers loss suffix).world :=
  inheritedSettlementAfter answers (TerminalPeace.Universal.Occurrence.originState loss) suffix
    (inheritedRun seed community (TerminalPeace.Universal.Occurrence.history loss))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
