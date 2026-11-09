import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.History
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OpeningAuthority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Opening

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (ReceiptAnswers)
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {reserve : Party → Good → ℚ} {body : RawEvent Party Good Port Technology Instrument}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  {replies : Replies Party Good Port Technology Instrument}
  {tariff : Tariff Party Good Port Technology Instrument}
  {orders : PaymentOrders Party Good Port Technology Instrument}
  {openOrders : OpenOrders Party Good Port Technology Instrument}

variable (opening : Opening loss answers reserve body offers replies tariff orders openOrders)

def liveInitial := Network.Runtime.start opening.initial (Network.Runtime.openingLanes opening) opening.inherited

def liveRun (policy : Policy Party Good Port Technology Instrument) :=
  Network.Runtime.history opening.home replies opening.liveInitial policy

variable (policy : Policy Party Good Port Technology Instrument) (n : Nat)

def run :=
  let reached := opening.liveRun policy n
  (reached.1.base, reached.2)

def submitted :=
  Network.Runtime.inputAt opening.home replies opening.liveInitial policy n

local notation "Before" => Prod.fst (opening.liveRun policy n)
local notation "InputAt" => opening.submitted policy n

def visit := Network.Runtime.source opening.home replies Before InputAt

def observedEffects := Network.Runtime.scope opening.home replies Before InputAt

def languageAmendment := (Network.Runtime.advance opening.home replies Before InputAt).write

/-- The next material input is the resident of the selected whole-ledger write. -/
def networkNext : AnyAuthoritativeRootCurrent :=
  (opening.run policy (n + 1)).1.adaptive.native.ledger.resident.erase

def networkRevision (novel : ¬ opening.observedEffects policy n ⊆ (Before).base.language.covered) :=
  Network.Runtime.revision opening.home replies Before InputAt novel

def networkFailure (novel : ¬ opening.observedEffects policy n ⊆ (Before).base.language.covered) :=
  Network.Runtime.failure opening.home replies Before InputAt novel

theorem actual_paid_scope_generates_the_whole_network_first_write
    (novel : ¬ opening.observedEffects policy n ⊆ (Before).base.language.covered) :
    (∃ wire, (opening.visit policy n).source.paidWire = some wire) ∧
    let revision := (opening.networkRevision policy n novel).generate
    (⟨revision.NewN, revision.newLivingRoot.generatedNextCurrentAt
      (.finite revision.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      opening.networkNext policy n := by
  refine ⟨?_, Network.Runtime.history_enters_the_exact_revised_world
    opening.home replies opening.liveInitial policy n novel⟩
  cases paid : (opening.visit policy n).source.paidWire with
  | some wire => exact ⟨wire, rfl⟩
  | none =>
    have empty := no_unpaid_scope (Before).lanes.tariff.read opening.home (Before).lanes.payment.read
      (Before).lanes.openPayment.read replies (Before).base InputAt paid
    have observed : opening.observedEffects policy n = ∅ := empty
    exact (novel (observed.symm ▸ Set.empty_subset _)).elim

theorem an_unpaid_visit_keeps_its_original_successor
    (unpaid : (opening.visit policy n).source.paidWire = none) :
    opening.languageAmendment policy n = none ∧
      opening.networkNext policy n = (opening.visit policy n).next.native.ledger.resident.erase := by
  have same := Network.Runtime.unpaid_keeps_its_material_next opening.home replies Before InputAt unpaid
  exact ⟨same.1, congrArg (fun state => state.native.ledger.resident.erase) same.2⟩

set_option maxHeartbeats 480000 in
theorem every_epoch_keeps_the_exact_original_stack :
    HEq (opening.run policy n).1.adaptive.native.ledger.stack
      opening.source.source.source.source.entry.current.ledger.stack := by
  have current := Network.Runtime.history_keeps_the_stack opening.home replies opening.liveInitial policy n
  have original : opening.liveInitial.current.ledger.stack = opening.source.source.current.ledger.stack := rfl
  have inherited := original.trans opening.source.source.installation_keeps_the_original_stack
  exact current.trans (heq_of_eq inherited)

theorem every_epoch_keeps_the_original_paid_addresses :
    let rows := (opening.run policy n).1.adaptive.native.ledger.stack.balances
    rows.map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst ∧
      ∀ row ∈ rows, row.2.remaining = 0 := by
  let settled := opening.source.source.source.source
  have original := Network.Runtime.history_keeps_rows opening.home replies opening.liveInitial policy n
  exact ⟨(congrArg (List.map Prod.fst) original).trans settled.entry.every_old_address_is_retained,
    fun row listed => settled.fixed.oldPaid row (original ▸ listed)⟩

theorem every_expression_is_generated_by_its_original_paid_visit
    (effect : Effect Party Good Port Technology Instrument) :
    effect ∈ (opening.run policy n).1.language.covered ↔ ∃ i < n, effect ∈ opening.observedEffects policy i := by
  have generated := Network.Runtime.history_covers_exactly_the_observed_effects
    opening.home replies opening.liveInitial policy n effect
  change effect ∈ (opening.run policy n).1.language.covered ↔
    effect ∈ opening.initial.language.covered ∨ ∃ i < n, effect ∈ opening.observedEffects policy i at generated
  simpa only [opening.no_future_expressions_are_installed, Set.mem_empty_iff_false, false_or] using generated

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Opening
