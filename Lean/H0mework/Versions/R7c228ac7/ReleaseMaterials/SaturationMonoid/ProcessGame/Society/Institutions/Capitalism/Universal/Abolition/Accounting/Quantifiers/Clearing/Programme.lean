import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing

open Source.Program

variable {Party Good Port Technology Instrument : Type}

/-- Return the original material first. The second leg really retires the
old claim; the first transfer is never retroactively called a repayment. -/
def refund (law : RawLaw Party Good Port Technology Instrument)
    (controller victim : Party) (good : Good) (quantity : ℚ) (instrument : Instrument) :
    Request Party Good Port Technology Instrument :=
  ⟨victim,[],law.issuerPort instrument,[],.transfer controller victim [(good,quantity)]⟩

def payment (law : RawLaw Party Good Port Technology Instrument)
    (controller victim : Party) (instrument : Instrument) (principal : ℚ) :
    Request Party Good Port Technology Instrument :=
  ⟨victim,[],law.issuerPort instrument,[],.settle instrument victim controller principal⟩

def word (law : RawLaw Party Good Port Technology Instrument)
    (controller victim : Party) (good : Good) (quantity : ℚ) (instrument : Instrument) (principal : ℚ) :
    RawEvent Party Good Port Technology Instrument :=
  [refund law controller victim good quantity instrument,payment law controller victim instrument principal]

variable [DecidableEq Good]

/-- Only original stock, the old claim and its own settlement quote enter.
Neither execution validity nor a successful closing balance is a premise. -/
structure Resources (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (controller victim : Party)
    (good : Good) (quantity : ℚ) (instrument : Instrument) (principal : ℚ) : Prop where
  distinct : controller ≠ victim
  refund_nonnegative : 0 ≤ quantity
  principal_nonnegative : 0 ≤ principal
  rate_positive : 0 < law.settlementRate instrument
  old_claim : principal ≤ before.claims instrument victim controller
  refund_stock : quantity ≤ before.stock controller good
  repayment_stock : principal * law.settlementRate instrument ≤
    before.stock victim (law.settlementUnit instrument) +
      if good = law.settlementUnit instrument then quantity else 0

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing
