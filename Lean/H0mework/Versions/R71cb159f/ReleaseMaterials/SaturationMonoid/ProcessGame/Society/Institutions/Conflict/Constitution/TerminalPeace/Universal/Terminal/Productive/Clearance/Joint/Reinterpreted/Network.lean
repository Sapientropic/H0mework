import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Renewal
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Privacy.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Reparation.Actual (Script)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint.OpenPeace (OpenOrders)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeConditions)
open FixedPoint.NoFreeProbe (Tariff)
open FixedPoint.NoFreeProbe.Prepayment (PaymentOrders)
open FixedPoint.OpenPeace.Network.Runtime (ReadAt SignedLanes)
open private FixedPoint.OpenPeace.State.start from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private FixedPoint.AdaptivePeace.State.start from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

variable (settled : Current loss front)

local notation "Cut" => endAt seed (anchor loss front)
local notation "Origin" => originalRaw loss
local notation "People" => people loss front
local notation "Reserve" => Capitalism.Universal.Abolition.Root.Actual.Current.raw (Current.physical settled)
local notation "Quantum" => settled.programme.law.duration Reserve
local notation "Live" => FixedPoint.OpenPeace.Network.Runtime.State (seed := seed) (cut := Cut)
  (community := community) Origin People Quantum (reserveBase := Reserve)

variable (tariff : Tariff Party Good Port Technology Instrument)
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)

/-- The existing live network receives the same settled stack and the
physical state that its published material write actually produced. That
state fixes the common reserve of the dispatcher and its observation fibres. -/
structure NetworkOpening (word : RawEvent Party Good Port Technology Instrument) where
  private mk ::
  state : Live
  home : AnyAuthoritativeRootCurrent.{0}
  entireStack : HEq state.current.ledger.stack settled.ledger.stack
  rows : state.current.ledger.stack.balances = settled.ledger.stack.balances
  physical : state.current.physical = settled.physical
  programme : state.current.programme = settled.programme
  paid : ∀ row ∈ state.current.ledger.stack.balances, row.2.remaining = 0
  recipeWord : state.current.recipe.move.word = word
  initialLanguage : state.base.language.covered = ∅
  signatures : state.lanes.tariff.read = tariff ∧ state.lanes.payment.read = orders ∧
    state.lanes.openPayment.read = openOrders

private def installNetwork {word : RawEvent Party Good Port Technology Instrument}
    (cleared : ClearedOpening settled) (literal : cleared.recipe.move.word = word) :
    NetworkOpening settled tariff orders openOrders word := by
  let original := Installation.Live.Ledger.ofState settled.ledger
  let quote := Installation.Live.publish original tariff true
  let payment := Installation.Live.publish quote.state orders true
  let openPayment := Installation.Live.publish payment.state openOrders true
  let physical : FixedPoint.Current (seed := seed) (cut := Cut) (community := community) Origin People Quantum (reserveBase := Reserve) :=
    ⟨openPayment.state, settled.physical, settled.programme, cleared.recipe, ⟨fun _ _ => le_rfl, rfl, rfl⟩⟩
  let base := FixedPoint.OpenPeace.State.start (FixedPoint.AdaptivePeace.State.start physical)
  let quoteLane := ReadAt.ofWrite original.resident original.ready tariff true
  let paymentLane := ReadAt.ofWrite quote.state.resident quote.state.ready orders true
  let lanes : SignedLanes Party Good Port Technology Instrument base.adaptive.native.ledger.resident :=
    ⟨(quoteLane.afterWrite quote.state.ready orders true).afterWrite payment.state.ready openOrders true,
      paymentLane.afterWrite payment.state.ready openOrders true,
      ReadAt.ofWrite payment.state.resident payment.state.ready openOrders true⟩
  exact ⟨FixedPoint.OpenPeace.Network.Runtime.start base lanes settled.inherited, payment.state.resident.erase,
    HEq.rfl, rfl, rfl, rfl, cleared.allPaid, literal, FixedPoint.OpenPeace.Language.covered_initial, ⟨rfl, rfl, rfl⟩⟩

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (code : RepeatCode settled.programme settled.physical.raw)

/-- The funded recipe at the actual settlement cut opens the signed
U7/U8 dispatcher. A shortage is written at that same original resident. -/
def openNetwork : Refused settled (RenewalIssue settled code) ⊕
    NetworkOpening settled tariff orders openOrders code.production :=
  match inspectRenewal settled code with
  | .error issue => .inl (refuse settled issue)
  | .ok checked => .inr (installNetwork settled tariff orders openOrders checked.val checked.property)

theorem opens_network_at_the_original_resident
    (cleared : ∀ row ∈ settled.ledger.stack.balances, row.2.remaining = 0)
    (viable : RecipeConditions settled.programme Origin Reserve People code) :
    ∃ opened, openNetwork settled tariff orders openOrders code = .inr opened := by
  obtain ⟨checked, accepted⟩ := inspectRenewal_accepts_the_cleared_actual_recipe settled code cleared viable
  exact ⟨installNetwork settled tariff orders openOrders checked.val checked.property, by rw [openNetwork, accepted]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
