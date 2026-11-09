import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.History
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Privacy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open private selects_ordinary from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "St" => State (seed := seed) (cut := cut) (community := community)
  origin people quantum (reserveBase := reserveBase)
local notation "RequestAt" => Input Party Good Port Technology Instrument

/-- The three publicly installed reads may be carried by different
residents of the same source. They are independent of private replies. -/
structure SameReads (left right : St) : Prop where
  tariff : left.lanes.tariff.read = right.lanes.tariff.read
  orders : left.lanes.payment.read = right.lanes.payment.read
  proposals : left.lanes.openPayment.read = right.lanes.openPayment.read

def publicAgenda (replies : Replies Party Good Port Technology Instrument) (before : St) (input : RequestAt) :
    Terms Party Good Port Technology Instrument × NoFreeProbe.Observation :=
  AdaptivePeace.publicAgenda before.lanes.tariff.read (input.replies replies) before.base.adaptive
    (fun _ _ => input.due)

variable (home : AnyAuthoritativeRootCurrent.{0})
  (replies otherReplies : Replies Party Good Port Technology Instrument)

theorem same_public_agenda_selects_the_same_payment (left right : St) (input : RequestAt)
    (reads : SameReads left right)
    (observed : publicAgenda replies left input = publicAgenda otherReplies right input) :
    (source home replies left input).source.paidWire = (source home otherReplies right input).source.paidWire := by
  change AdaptivePeace.paymentAt left.lanes.tariff.read home
    (input.orders left.lanes.payment.read left.lanes.openPayment.read) (input.replies replies)
    left.base.adaptive (fun _ _ => input.due) =
    AdaptivePeace.paymentAt right.lanes.tariff.read home
    (input.orders right.lanes.payment.read right.lanes.openPayment.read) (input.replies otherReplies)
    right.base.adaptive (fun _ _ => input.due)
  unfold publicAgenda at observed
  rw [reads.tariff] at observed
  rw [reads.tariff, reads.orders, reads.proposals]
  exact AdaptivePeace.same_public_agenda_selects_the_same_payment _ _ _ _ _ _ _ _ observed

theorem unpaid_observation_is_the_original_agenda (before : St) (input : RequestAt)
    (unpaid : (source home replies before input).source.paidWire = none) :
    let normal := (publicAgenda replies before input).2
    (source home replies before input).observe =
      ⟨normal.opensAt, normal.landsAt, .ordinary (.ordinary normal.reply)⟩ := by
  let agenda := fun (_ : ℚ) (_ : Terms Party Good Port Technology Instrument) => input.due
  let orders := input.orders before.lanes.payment.read before.lanes.openPayment.read
  let actual := AdaptivePeace.commandedStep before.lanes.tariff.read home orders (input.replies replies)
    before.base.adaptive agenda
  have quiet : AdaptivePeace.paymentAt before.lanes.tariff.read home orders (input.replies replies)
      before.base.adaptive agenda = none := unpaid
  change actual.observe = _
  dsimp only [actual]
  rw [AdaptivePeace.unpaid_command_is_the_exact_ordinary_write _ _ _ _ _ _ quiet]
  rfl

theorem unpaid_keeps_the_language (before : St) (input : RequestAt)
    (unpaid : (source home replies before input).source.paidWire = none) :
    (advance home replies before input).next.base.language = before.base.language := by
  have covered : scope home replies before input ⊆ before.base.language.covered := by
    unfold scope
    rw [OpenPeace.no_unpaid_scope _ _ _ _ _ _ _ unpaid]
    exact Set.empty_subset _
  rw [selects_ordinary home replies before input covered]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
