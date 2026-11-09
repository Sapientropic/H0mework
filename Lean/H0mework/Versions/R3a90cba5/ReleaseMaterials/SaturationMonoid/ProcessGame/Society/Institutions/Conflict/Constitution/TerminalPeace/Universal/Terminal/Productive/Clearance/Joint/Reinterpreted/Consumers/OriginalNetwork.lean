import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.RevisionOrders
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Network

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open FixedPoint.OpenPeace (Policy)
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open RevisedOrders (openPayment)
open Joint.OriginalExchange (claim)
open Supply.Consumers (refillWord)

noncomputable section

abbrev namedReplies := FixedPoint.OriginalReview.personalReplies false

def networkCode (paid : PaidWrite payerCut (signed true) claim 6) :=
  codeFor _ (paid.sameProgramme.trans actualTrial.revisedProgramme) paid.next.physical.raw

structure ReinterpretedNetwork where
  paid : PaidWrite payerCut (signed true) claim 6
  selected : pay payerCut (signed true) claim 6 cells allCells = .inr paid
  network : NetworkOpening paid.next quote Runtime.OriginalOrders.payment openPayment (networkCode paid).production
  opened : openNetwork paid.next quote Runtime.OriginalOrders.payment openPayment (networkCode paid) = .inr network
  originalRows : network.state.current.ledger.stack.balances.map Prod.fst = [loss]
  actualStock : network.state.current.physical.raw = afterClear

theorem the_new_interpreter_enters_the_existing_network : Nonempty ReinterpretedNetwork := by
  obtain ⟨paid, selected, _, _, addresses, cleared, _, _, _⟩ := the_new_interpreter_clears_the_original_six
  have stock := payment_lands_at_the_actual_stock paid
  obtain ⟨network, opened⟩ := opens_network_at_the_original_resident
    paid.next quote Runtime.OriginalOrders.payment openPayment (networkCode paid) cleared
    (the_cleared_actual_recipe_checks paid)
  exact ⟨⟨paid, selected, network, opened, (congrArg (List.map Prod.fst) network.rows).trans addresses,
    (congrArg (fun current => current.raw) network.physical).trans stock⟩⟩

def actualNetwork : ReinterpretedNetwork := Classical.choice the_new_interpreter_enters_the_existing_network

theorem the_network_opens_below_the_old_stock :
    actualNetwork.network.state.current.physical.raw.stock true false = 111 ∧
    actualNetwork.network.state.current.physical.raw.stock true false <
      (endAt Original.seed (anchor loss front)).raw.stock true false := by
  rw [actualNetwork.actualStock, original_native_cut, Original.cut_raw]
  decide +kernel

def liveHistory (policy : Policy Bool Bool Bool Unit Unit) :=
  Runtime.history actualNetwork.network.home namedReplies actualNetwork.network.state policy

theorem every_interleaving_keeps_the_original_paid_row_and_lives
    (policy : Policy Bool Bool Bool Unit Unit) (n : Nat) :
    let rows := (liveHistory policy n).1.current.ledger.stack.balances
    rows.map Prod.fst = [loss] ∧ (∀ row ∈ rows, row.2.remaining = 0) ∧
      HEq (liveHistory policy n).1.current.ledger.stack actualNetwork.paid.next.ledger.stack ∧
      FixedPoint.InReserve actualNetwork.paid.next.physical.raw (liveHistory policy n).1.current.physical.raw ∧
      Runtime.SameReads (liveHistory policy n).1 actualNetwork.network.state ∧
      Runtime.LivingVisitAt actualNetwork.network.home namedReplies actualNetwork.network.state policy n := by
  dsimp only
  have same := Runtime.history_keeps_rows actualNetwork.network.home namedReplies actualNetwork.network.state policy n
  rw [liveHistory, same]
  have stack := Runtime.history_keeps_the_stack actualNetwork.network.home namedReplies actualNetwork.network.state policy n
  have signed := Runtime.history_keeps_original_signatures
    actualNetwork.network.home namedReplies actualNetwork.network.state policy n
  exact ⟨actualNetwork.originalRows, actualNetwork.network.paid, stack.trans actualNetwork.network.entireStack,
    (liveHistory policy n).1.current.reserved, ⟨signed.1, signed.2.1, signed.2.2⟩,
    Runtime.history_is_living_and_peaceful actualNetwork.network.home namedReplies actualNetwork.network.state policy n⟩

theorem every_interleaving_is_cofinal (policy : Policy Bool Bool Bool Unit Unit) (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (liveHistory policy n).1.current.physical.raw.clock :=
  Runtime.history_clock_is_cofinal actualNetwork.network.home namedReplies actualNetwork.network.state policy start bound

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
