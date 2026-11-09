import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open private selects_ordinary selects_revision from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance
open private Runtime.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance
open private OpenPeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private AdaptivePeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "StateAt" => Runtime.State (seed := seed) (cut := cut) (community := community)
  origin people quantum (reserveBase := reserveBase)

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (before : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase))
  (input : OpenPeace.Input Party Good Port Technology Instrument)

def stepReads :
    ReadPath before.current.ledger.resident (Runtime.advance home replies before input).next.current.ledger.resident := by
  classical
  let posted := Runtime.source home replies before input
  have carry := adaptiveReads posted
  by_cases novel : ¬ Runtime.scope home replies before input ⊆ before.base.language.covered
  · rw [selects_revision home replies before input novel]
    exact carry.trans (revisedReads posted.next.native.ledger before.base.language (Runtime.scope home replies before input)
      (Runtime.reviewLane home replies before input) novel)
  · rw [selects_ordinary home replies before input (not_not.mp novel)]
    exact carry

variable (policy : Policy Party Good Port Technology Instrument)

def historyReads : (n : Nat) → ReadPath before.current.ledger.resident
    (Runtime.history home replies before policy n).1.current.ledger.resident
  | 0 => ⟨id, fun _ => rfl⟩
  | n + 1 => by
    rw [Runtime.history_succ]
    exact (historyReads n).trans (stepReads home replies (Runtime.history home replies before policy n).1
      (Runtime.inputAt home replies before policy n))

variable {Payload : Type} (payload : Payload)

/-- Install a source-generated read at the actual live current. This
primitive is consumed by the paid deferred decision and menu diagnostics. -/
private def publishOn : StateAt :=
  let prior := before.current.ledger
  let write := Installation.Live.publish prior payload true
  let reads := ReadPath.write prior.ready payload true
  Runtime.State.mk
    (OpenPeace.State.mk (AdaptivePeace.State.mk { before.current with ledger := write.state }
      before.base.adaptive.amendment) before.base.expansion)
    (before.lanes.map reads.carry) before.u7

private def publishedRead : ReadOn (publishOn before payload).current.ledger.resident Payload :=
  ReadAt.ofWrite before.current.ledger.resident before.current.ledger.ready payload true

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
