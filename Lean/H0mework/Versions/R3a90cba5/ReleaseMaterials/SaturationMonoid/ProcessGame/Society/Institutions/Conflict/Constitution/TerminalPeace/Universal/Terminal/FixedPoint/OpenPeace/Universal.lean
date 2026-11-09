import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Compile

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open NoFreeProbe
open Reparation.Actual (ReceiptAnswers)
open NoFreeProbe.Prepayment (PaymentOrders)

universe u

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

local notation "Alphabet" => Language (RawEvent Party Good Port Technology Instrument)
  (Effect Party Good Port Technology Instrument)
local notation "Visible" => Terms Party Good Port Technology Instrument
local notation "Transcript" => List AdaptivePeace.Observation
local notation "Request" => Input Party Good Port Technology Instrument

/-- A rival can change its syntax with the actual public transcript,
clock, registered terms, and language epoch. Its only ingress is the
original dispatcher's request type. -/
def interpretedPolicy {Syntax : Nat → Transcript → ℚ → Visible → Alphabet → Type u}
    (interpret : ∀ n past clock terms grammar, Syntax n past clock terms grammar → Option Request)
    (rival : ∀ n past clock terms grammar, Syntax n past clock terms grammar) :
    Policy Party Good Port Technology Instrument :=
  fun n past clock terms grammar =>
    (interpret n past clock terms grammar (rival n past clock terms grammar)).getD (.native ⟨none, []⟩)

namespace Opening

variable (opening : Opening loss answers reserve body offers replies tariff orders openOrders)
  {Syntax : Nat → List AdaptivePeace.Observation → ℚ → Terms Party Good Port Technology Instrument →
    Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument) → Type u}
  (interpret : ∀ n past clock terms grammar,
    Syntax n past clock terms grammar → Option (Input Party Good Port Technology Instrument))
  (rival : ∀ n past clock terms grammar, Syntax n past clock terms grammar)

local notation "Strategy" => interpretedPolicy interpret rival
local notation "Run" => opening.liveRun (interpretedPolicy interpret rival)
local notation "At" n => (Prod.fst (Run n))
local notation "Base" n => Network.Runtime.State.base (At n)

/-- All source-generated language epochs use the original productive
and settlement executor. Exact paid expression failures are the only
entries that can grow the language. -/
theorem open_future_permanent_peace :
    (∀ n, Network.Runtime.LivingVisitAt opening.home replies opening.liveInitial Strategy n) ∧
    (∀ n,
      KeepsPublicTerms opening.initial.adaptive.native.programme (At n).current.programme ∧
      let rows := (At n).current.ledger.stack.balances
      rows.map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst ∧
        ∀ row ∈ rows, row.2.remaining = 0) ∧
    (∀ n,
      (opening.languageAmendment Strategy n).isSome = true ↔
        ∃ effect ∈ opening.observedEffects Strategy n,
          ∀ code : (Base n).language.Code, effect ∉ (Base n).language.denotes code) ∧
    (∀ i j, i < j → ∀ effect ∈ opening.observedEffects Strategy i,
      ∃ code : (Base j).language.Code, effect ∈ (Base j).language.denotes code) ∧
    (∀ n wire, (opening.visit Strategy n).source.paidWire = some wire →
      ∀ weight : Good → ℚ, (∀ good, 0 < weight good) →
        materialPayoff (bill (At n).lanes.tariff.read wire) (At (n + 1)).current.physical.raw
          (At n).current.move.next weight < 0) ∧
    ∀ (start : Nat) (bound : ℚ), ∃ n ≥ start, bound < (At n).current.physical.raw.clock := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Network.Runtime.history_is_living_and_peaceful opening.home replies opening.liveInitial Strategy
  · intro n
    exact ⟨Network.Runtime.history_keeps_public_terms opening.home replies opening.liveInitial Strategy n,
      opening.every_epoch_keeps_the_original_paid_addresses Strategy n⟩
  · intro n
    rw [languageAmendment, Network.Runtime.write_iff]
    constructor
    · intro novel
      obtain ⟨effect, found, missing, _⟩ :=
        (Base n).language.gap_not_denotable (opening.observedEffects Strategy n) novel
      exact ⟨effect, found, missing⟩
    · rintro ⟨effect, found, missing⟩ covered
      obtain ⟨code, names⟩ := covered found
      exact missing code names
  · intro i j later effect observed
    exact (opening.every_expression_is_generated_by_its_original_paid_visit Strategy j effect).mpr
      ⟨i, later, observed⟩
  · intro n wire charged weight valuable
    let old := At n
    let input := opening.submitted Strategy n
    let quote := old.lanes.tariff.read
    let pay := old.lanes.payment.read
    let openPay := old.lanes.openPayment.read
    have expense := every_paid_visit_charges_its_actual_payer quote opening.home pay openPay
      replies old.base input charged weight valuable
    rw [same_physical_successor] at expense
    change materialPayoff (bill quote wire) (At (n + 1)).current.physical.raw old.current.move.next weight < 0
    rw [liveRun, Network.Runtime.history_succ, Network.Runtime.same_physical]
    exact expense
  · exact Network.Runtime.history_clock_is_cofinal opening.home replies opening.liveInitial Strategy

end Opening

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
