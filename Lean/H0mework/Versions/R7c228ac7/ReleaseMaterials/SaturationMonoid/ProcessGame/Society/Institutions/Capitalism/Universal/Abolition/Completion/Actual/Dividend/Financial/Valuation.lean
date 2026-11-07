import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Source
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

abbrev ClaimKey := Instrument × Party × Party
abbrev ClaimChange := ClaimKey (Party := Party) (Instrument := Instrument) →₀ ℚ
abbrev MaterialChange := Party × Good →₀ ℚ

/-- A finite change of the original matrix, never a replacement debt ledger. -/
def rawClaimChange (request : Request Party Good Port Technology Instrument) :
    ClaimChange (Party := Party) (Instrument := Instrument) :=
  match request.operation with
  | .issue instrument debtor creditor quantity => Finsupp.single (instrument, debtor, creditor) quantity
  | .assign instrument debtor sender recipient quantity =>
      -Finsupp.single (instrument, debtor, sender) quantity + Finsupp.single (instrument, debtor, recipient) quantity
  | .settle instrument debtor creditor quantity => -Finsupp.single (instrument, debtor, creditor) quantity
  | _ => 0

variable (law : RawLaw Party Good Port Technology Instrument)

def claimChange (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : ClaimChange (Party := Party) (Instrument := Instrument) :=
  if law.Valid before request then rawClaimChange request else 0

theorem claim_change_is_the_original_actual_matrix_delta
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (instrument : Instrument) (debtor creditor : Party) :
    claimChange law before request (instrument, debtor, creditor) =
      law.actualClaimDelta before request instrument debtor creditor := by
  unfold claimChange RawLaw.actualClaimDelta
  split
  · cases operation : request.operation <;>
      simp [rawClaimChange, RawLaw.claimDelta, operation, Finsupp.single_apply, eq_comm]
  · rfl

def value : ClaimChange (Party := Party) (Instrument := Instrument) →+
    MaterialChange (Party := Party) (Good := Good) :=
  Finsupp.liftAddHom fun key => {
    toFun := fun quantity =>
      Finsupp.single (key.2.2, law.settlementUnit key.1) (quantity * law.settlementRate key.1) -
        Finsupp.single (key.2.1, law.settlementUnit key.1) (quantity * law.settlementRate key.1)
    map_zero' := by simp
    map_add' := by
      intro first second
      simp only [add_mul, Finsupp.single_add]
      abel }

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem value_single (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ) :
    value law (Finsupp.single (instrument, debtor, creditor) quantity) =
      Finsupp.single (creditor, law.settlementUnit instrument) (quantity * law.settlementRate instrument) -
        Finsupp.single (debtor, law.settlementUnit instrument) (quantity * law.settlementRate instrument) :=
  Finsupp.liftAddHom_apply_single _ _ _

def flowVector (flow : Flow Party Good) : MaterialChange (Party := Party) (Good := Good) :=
  (flow.map fun lot => Finsupp.single lot.1 lot.2).sum

theorem flowVector_apply (flow : Flow Party Good) (person : Party) (good : Good) :
    flowVector flow (person, good) = flowAt flow person good := by
  induction flow with
  | nil => rfl
  | cons lot later inherited =>
      simp only [flowVector, List.map_cons, List.sum_cons, Finsupp.add_apply] at *
      rw [inherited]
      simp [flowAt, amount, Finsupp.single_apply]

def materialChange (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : MaterialChange (Party := Party) (Good := Good) :=
  flowVector (law.actualCredit before request) - flowVector (law.actualDebit before request)

def fullChange (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : MaterialChange (Party := Party) (Good := Good) :=
  materialChange law before request + value law (claimChange law before request)

omit [DecidableEq Instrument] in
theorem material_change_is_the_original_net_flow
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (person : Party) (good : Good) :
    materialChange law before request (person, good) =
      flowAt (law.actualCredit before request) person good - flowAt (law.actualDebit before request) person good := by
  simp only [materialChange, Finsupp.sub_apply, flowVector_apply]

omit [DecidableEq Instrument] in
/-- Physical repayment and the decline of both original financial positions
cancel separately for every bearer and the instrument's own material unit. -/
theorem settlement_is_neutral_for_every_original_bearer
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)
    (operation : request.operation = .settle instrument debtor creditor quantity) :
    fullChange law before request = 0 := by
  by_cases paid : law.Valid before request
  · simp only [fullChange, materialChange, claimChange, RawLaw.actualCredit, RawLaw.actualDebit,
      if_pos paid, rawClaimChange, RawLaw.credit, RawLaw.debit, operation, flowVector, locate,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_neg, value_single]
    abel
  · simp [fullChange, materialChange, claimChange, RawLaw.actualCredit, RawLaw.actualDebit, paid, flowVector]

omit [DecidableEq Instrument] in
theorem issue_creates_the_original_creditor_asset_and_debtor_liability
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)
    (operation : request.operation = .issue instrument debtor creditor quantity)
    (paid : law.Valid before request) :
    fullChange law before request =
      Finsupp.single (creditor, law.settlementUnit instrument) (quantity * law.settlementRate instrument) -
        Finsupp.single (debtor, law.settlementUnit instrument) (quantity * law.settlementRate instrument) := by
  simp [fullChange, materialChange, claimChange, RawLaw.actualCredit, RawLaw.actualDebit,
    rawClaimChange, RawLaw.credit, RawLaw.debit, operation, paid, flowVector, value_single]

omit [DecidableEq Instrument] in
theorem assignment_moves_the_claim_between_its_actual_holders
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor sender recipient : Party) (quantity : ℚ)
    (operation : request.operation = .assign instrument debtor sender recipient quantity)
    (paid : law.Valid before request) :
    fullChange law before request =
      Finsupp.single (recipient, law.settlementUnit instrument) (quantity * law.settlementRate instrument) -
        Finsupp.single (sender, law.settlementUnit instrument) (quantity * law.settlementRate instrument) := by
  simp only [fullChange, materialChange, claimChange, RawLaw.actualCredit, RawLaw.actualDebit,
    if_pos paid, rawClaimChange, RawLaw.credit, RawLaw.debit, operation, flowVector, List.map_nil,
    List.sum_nil, sub_self, zero_add, map_add, map_neg, value_single]
  abel

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem public_interpretation_uses_the_literal_original_instrument_quote
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) :
    value (Physical.Public.interpreter input) = value input.law := rfl

#print axioms claim_change_is_the_original_actual_matrix_delta
#print axioms value
#print axioms settlement_is_neutral_for_every_original_bearer
#print axioms issue_creates_the_original_creditor_asset_and_debtor_liability
#print axioms assignment_moves_the_claim_between_its_actual_holders

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial
