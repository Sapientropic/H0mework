import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

/-!
# Source-bounded market readout

This is deliberately a readout, not a market producer.  It can observe only
an accepted item already present in the source execution inventory.  A quote
exists only for an actual `settle` operation and is computed from the source
quantity and settlement rate.  No owner, demand, permission, or future state
is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure MarketReadout
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument) where
  private mk ::
  item : ExecutionItem Party Good Port Technology Instrument
  inside : item ∈ law.rawItems current original
  accepted : law.Valid item.before item.request

namespace MarketReadout

variable {law : RawLaw Party Good Port Technology Instrument}
variable {current : RawCurrent Party Good Technology Instrument}
variable {original : RawEvent Party Good Port Technology Instrument}

def ofAccepted
    (item : ExecutionItem Party Good Port Technology Instrument)
    (inside : item ∈ law.rawItems current original)
    (accepted : law.Valid item.before item.request) :
    MarketReadout law current original :=
  ⟨item, inside, accepted⟩

def settlementQuote
    (readout : MarketReadout law current original) : Option ℚ :=
  match readout.item.request.operation with
  | .settle instrument _ _ quantity =>
      some (quantity * law.settlementRate instrument)
  | _ => none

theorem quote_zero_for_nonsettlement
    (readout : MarketReadout law current original)
    (notSettlement : ∀ instrument debtor creditor quantity,
      readout.item.request.operation ≠
        .settle instrument debtor creditor quantity) :
    readout.settlementQuote = none := by
  cases operation : readout.item.request.operation with
  | produce operator => simp [settlementQuote, operation]
  | transfer sender recipient goods => simp [settlementQuote, operation]
  | use bearer goods purpose => simp [settlementQuote, operation]
  | issue instrument issuer beneficiary quantity => simp [settlementQuote, operation]
  | assign instrument issuer sender recipient quantity =>
      simp [settlementQuote, operation]
  | settle instrument debtor creditor quantity =>
      exact (notSettlement instrument debtor creditor quantity operation).elim
  | revise operator technology => simp [settlementQuote, operation]
  | present => simp [settlementQuote, operation]

theorem quote_sound
    (readout : MarketReadout law current original)
    (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)
    (operation : readout.item.request.operation =
      .settle instrument debtor creditor quantity) :
    readout.settlementQuote = some (quantity * law.settlementRate instrument) := by
  simp [settlementQuote, operation]

theorem quote_eq_actual_debit
    (readout : MarketReadout law current original)
    (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)
    (operation : readout.item.request.operation =
      .settle instrument debtor creditor quantity) :
    flowAt (law.actualDebit readout.item.before readout.item.request)
        debtor (law.settlementUnit instrument) =
      quantity * law.settlementRate instrument := by
  have accepted := readout.accepted
  simp only [RawLaw.actualDebit, if_pos accepted]
  simp [RawLaw.debit, operation, flowAt, amount, locate]

theorem quote_eq_actual_credit
    (readout : MarketReadout law current original)
    (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)
    (operation : readout.item.request.operation =
      .settle instrument debtor creditor quantity) :
    flowAt (law.actualCredit readout.item.before readout.item.request)
        creditor (law.settlementUnit instrument) =
      quantity * law.settlementRate instrument := by
  have accepted := readout.accepted
  simp only [RawLaw.actualCredit, if_pos accepted]
  simp [RawLaw.credit, operation, flowAt, amount, locate]

end MarketReadout

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
