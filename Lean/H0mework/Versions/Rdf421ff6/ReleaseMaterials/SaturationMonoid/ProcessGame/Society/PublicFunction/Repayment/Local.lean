import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

/-! Current liquidity is used first. Otherwise the local technique is
attempted once, and only its actual output can finance the generated payment.
A failed candidate retains its obstruction; it is not a universal no-go. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure Position (Party Instrument : Type) where
  instrument : Instrument
  debtor : Party
  creditor : Party

variable (law : RawLaw Party Good Port Technology Instrument)
  (position : Position Party Instrument) (current : RawCurrent Party Good Technology Instrument)

def balance : ℚ := current.claims position.instrument position.debtor position.creditor

def production : Request Party Good Port Technology Instrument :=
  ⟨position.debtor, [], law.stockPort current.technology position.debtor
    (law.settlementUnit position.instrument), [], .produce position.debtor⟩

def preparation : RawEvent Party Good Port Technology Instrument :=
  if 0 < current.stock position.debtor (law.settlementUnit position.instrument) then []
  else [production law position current]

def readyCurrent : RawCurrent Party Good Technology Instrument :=
  (law.execute current 0 (preparation law position current)).final

def quantity : ℚ := min (balance position current)
  ((readyCurrent law position current).stock position.debtor (law.settlementUnit position.instrument) /
    law.settlementRate position.instrument)

def payment : Request Party Good Port Technology Instrument :=
  ⟨position.debtor, [], law.issuerPort position.instrument, [],
    .settle position.instrument position.debtor position.creditor (quantity law position current)⟩

def candidate : RawEvent Party Good Port Technology Instrument :=
  preparation law position current ++ [payment law position current]

def Ready : Prop :=
  0 < quantity law position current ∧
    ∀ item ∈ law.rawItems current (candidate law position current), law.Valid item.before item.request

instance : Decidable (Ready law position current) := by unfold Ready; infer_instance

inductive Response
  | noPositiveDebt (clear : ¬ 0 < balance position current)
  | paid (ready : Ready law position current)
  | blocked (positive : 0 < balance position current) (failed : ¬ Ready law position current)

def respond : Response law position current :=
  if positive : 0 < balance position current then
    if ready : Ready law position current then .paid ready else .blocked positive ready
  else .noPositiveDebt positive

def Response.word : Response law position current → RawEvent Party Good Port Technology Instrument
  | .paid _ => candidate law position current
  | .noPositiveDebt _ | .blocked .. => []

theorem payment_is_an_actual_item (ready : Ready law position current) :
    ∃ item ∈ law.rawItems current (candidate law position current),
      item.before = readyCurrent law position current ∧ item.request = payment law position current ∧
        law.Valid item.before item.request := by
  have present : ⟨(preparation law position current).length, readyCurrent law position current,
      payment law position current⟩ ∈ law.rawItems current (candidate law position current) := by
    by_cases cash : 0 < current.stock position.debtor (law.settlementUnit position.instrument) <;>
      simp [candidate, preparation, readyCurrent, cash, RawLaw.rawItems, RawLaw.execute]
  exact ⟨_, present, rfl, rfl, ready.2 _ present⟩

theorem paid_principal_balance (ready : Ready law position current) :
    (law.next current (candidate law position current)).claims
        position.instrument position.debtor position.creditor =
      balance position current - quantity law position current := by
  have actual := law.accepted_next_financial_balance current (candidate law position current)
    ready.2 position.instrument position.debtor position.creditor
  have delta : ((candidate law position current).map (fun request =>
      RawLaw.claimDelta request position.instrument position.debtor position.creditor)).sum =
        -quantity law position current := by
    unfold candidate preparation
    split <;> simp [payment, production, RawLaw.claimDelta]
  rw [delta] at actual
  simpa only [balance, sub_eq_add_neg] using actual

theorem paid_strictly_reduces_principal (ready : Ready law position current) :
    (law.next current (candidate law position current)).claims
        position.instrument position.debtor position.creditor < balance position current := by
  rw [paid_principal_balance law position current ready]
  exact sub_lt_self _ ready.1

theorem other_positions_are_preserved (ready : Ready law position current)
    (code : Instrument) (debtor creditor : Party)
    (other : (code, debtor, creditor) ≠ (position.instrument, position.debtor, position.creditor)) :
    (law.next current (candidate law position current)).claims code debtor creditor =
      current.claims code debtor creditor := by
  have actual := law.accepted_next_financial_balance current (candidate law position current)
    ready.2 code debtor creditor
  have delta : ((candidate law position current).map (fun request =>
      RawLaw.claimDelta request code debtor creditor)).sum = 0 := by
    have paymentDelta : RawLaw.claimDelta (payment law position current) code debtor creditor = 0 := by
      change -(if (code, debtor, creditor) = (position.instrument, position.debtor, position.creditor)
        then quantity law position current else 0) = 0
      rw [if_neg other, neg_zero]
    have productionDelta : RawLaw.claimDelta (production law position current) code debtor creditor = 0 := rfl
    unfold candidate preparation
    split <;> simp [paymentDelta, productionDelta]
  simpa only [delta, add_zero] using actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment
