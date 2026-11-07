import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace
import Mathlib.Algebra.Order.Field.Rat

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (payer provider : Party) (instrument : Instrument) (purpose : Port) (net : ℚ)

/-- The sign changes the actual debtor; it does not negate a claim quantity. -/
def debtor : Party := if 0 ≤ net then payer else provider
def creditor : Party := if 0 ≤ net then provider else payer
def units : ℚ := |net| / law.settlementRate instrument

def issue : Request Party Good Port Technology Instrument :=
  ⟨debtor payer provider net, [], purpose, [],
    .issue instrument (debtor payer provider net) (creditor payer provider net) (units law instrument net)⟩

def settle : Request Party Good Port Technology Instrument :=
  ⟨debtor payer provider net, [], purpose, [],
    .settle instrument (debtor payer provider net) (creditor payer provider net) (units law instrument net)⟩

def afterIssue (before : RawCurrent Party Good Technology Instrument) :=
  law.step before (issue law payer provider instrument purpose net)

def afterPayment (before : RawCurrent Party Good Technology Instrument) :=
  law.step (afterIssue law payer provider instrument purpose net before)
    (settle law payer provider instrument purpose net)

def requests : RawEvent Party Good Port Technology Instrument :=
  if net = 0 then [] else [issue law payer provider instrument purpose net,
    settle law payer provider instrument purpose net]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem actual_debtor_signs_both_original_requests :
    (issue law payer provider instrument purpose net).signer = debtor payer provider net ∧
      (settle law payer provider instrument purpose net).signer = debtor payer provider net := ⟨rfl,rfl⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem quantities_are_nonnegative (positive : 0 < law.settlementRate instrument) :
    0 ≤ units law instrument net := div_nonneg (abs_nonneg _) positive.le

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem the_claim_units_pay_the_exact_material_amount
    (positive : 0 < law.settlementRate instrument) :
    units law instrument net * law.settlementRate instrument = |net| := by
  exact div_mul_cancel₀ _ (ne_of_gt positive)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement
