import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Decomposition
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit

open Source.Program ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- Read all remaining native assets and liabilities in the original instrument's unit.
The archive is retained as an original slot; its remaining balance is zero. -/
def nativeSlotPosition (slot : ObligationSlot (Epoch.Finance.vocabulary input depth count))
    (person : Party) (good : Good) : ℚ :=
  let claim := Epoch.Finance.slotClaim input depth count slot
  let balance := Epoch.Finance.slotBalance input depth count slot
  if input.law.settlementUnit (claim.instrument input depth count) = good then
    (balance person - if claim.debtor input depth count = person then balance.sum (fun _ value => value) else 0) *
      input.law.settlementRate (claim.instrument input depth count)
  else 0

def nativePosition (account : (Epoch.Finance.process input depth count).GeneratedState)
    (person : Party) (good : Good) : ℚ :=
  (account.current.slots.map fun slot => nativeSlotPosition input depth count slot person good).sum

theorem an_original_archive_has_zero_remaining_valued_principal
    (archive : TerminalArchive (Epoch.Finance.vocabulary input depth count)) (person : Party) (good : Good) :
    nativeSlotPosition input depth count (.terminal archive) person good = 0 := by
  simp [nativeSlotPosition,Epoch.Finance.slotBalance]

/-- A quotation reads source states; it is never an execution permission or a production input. -/
structure Quotation where
  unitPrice : Party → Good → ℚ
  rightsValue : RawCurrent Party Good Technology Instrument → Party → Good → ℚ

variable (interpreter : RawLaw Party Good Port Technology Instrument)
  (initial : RawCurrent Party Good Technology Instrument)
  (account : (Epoch.Finance.process input depth count).GeneratedState)
  (word : RawEvent Party Good Port Technology Instrument)

def openingPosition (person : Party) (good : Good) : ℚ :=
  initial.stock person good + nativePosition input depth count account person good

/-- This is the original finite effect added to the entire inherited native position,
not a supplied closing balance or a replacement account. -/
def closingPosition (person : Party) (good : Good) : ℚ :=
  openingPosition input depth count initial account person good +
    fullIncome interpreter (interpreter.rawItems initial word) (person,good)

theorem the_closing_read_uses_actual_stock_and_the_same_original_financial_delta
    (person : Party) (good : Good) :
    closingPosition input depth count interpreter initial account word person good =
      (interpreter.next initial word).stock person good + nativePosition input depth count account person good +
        Financial.value interpreter (Financial.inventoryClaims interpreter (interpreter.rawItems initial word)) (person,good) := by
  unfold closingPosition openingPosition
  rw [the_original_full_account_uses_its_actual_stock_and_financial_changes]
  ring

def bookIncome (before after : Quotation (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))
    (person : Party) (good : Good) : ℚ :=
  after.unitPrice person good * closingPosition input depth count interpreter initial account word person good +
    after.rightsValue (interpreter.next initial word) person good -
    (before.unitPrice person good * openingPosition input depth count initial account person good +
      before.rightsValue initial person good)

def revaluation (before after : Quotation (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))
    (person : Party) (good : Good) : ℚ :=
  (after.unitPrice person good - before.unitPrice person good) * closingPosition input depth count interpreter initial account word person good +
    after.rightsValue (interpreter.next initial word) person good - before.rightsValue initial person good

theorem the_original_book_return_has_its_complete_four_component_decomposition
    (before after : Quotation (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))
    (person : Party) (good : Good) :
    bookIncome input depth count interpreter initial account word before after person good =
      before.unitPrice person good * production interpreter (interpreter.rawItems initial word) (person,good) +
      before.unitPrice person good * otherTransfers interpreter initial word (person,good) +
      before.unitPrice person good * controlIncome interpreter initial word (person,good) +
      revaluation input depth count interpreter initial account word before after person good := by
  have original := congrArg (fun vector : Vector (Party := Party) (Good := Good) => vector (person,good))
    (the_original_full_account_separates_production_transfer_and_control interpreter initial word)
  simp only [Finsupp.add_apply] at original
  unfold bookIncome revaluation closingPosition
  rw [original]
  ring

theorem holding_without_any_new_request_has_only_valuation_income
    (before after : Quotation (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))
    (person : Party) (good : Good) :
    bookIncome input depth count interpreter initial account [] before after person good =
        revaluation input depth count interpreter initial account [] before after person good ∧
      production interpreter (interpreter.rawItems initial []) = 0 := by
  constructor
  · simp only [bookIncome,revaluation,closingPosition,fullIncome,Financial.inventoryMaterial,
      Financial.inventoryClaims,RawLaw.rawItems,RawLaw.execute,List.map_nil,List.sum_nil,map_zero,Finsupp.zero_apply,add_zero]
    ring
  · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit
