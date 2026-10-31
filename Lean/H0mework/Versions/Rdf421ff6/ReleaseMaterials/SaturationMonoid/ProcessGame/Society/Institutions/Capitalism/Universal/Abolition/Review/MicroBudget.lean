import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Budget

/-! Actual fee microsteps retain the original period clock. They consume
physical stock, so a period cannot hide infinitely many unpaid reviews.
The enclosing migration must settle life and maintenance before its period
clock advances; this file creates no period or terminal authority. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (request : Request Party Good Port Technology Instrument) (fee : FeeScope request)

namespace PaymentAt
variable {law request} {current : RawCurrent Party Good Technology Instrument}
  (payment : PaymentAt law request current)

def microNext (_payment : PaymentAt law request current) := law.step current request

theorem micro_stock_balance :
    payment.microNext.stock fee.payer fee.good + fee.amount = current.stock fee.payer fee.good :=
  payment.stock_balance fee

theorem micro_budget_debits_one :
    physicalBudget request fee current = physicalBudget request fee payment.microNext + 1 :=
  payment.physical_budget_debits_one fee

include fee in
theorem micro_claims_unchanged : payment.microNext.claims = current.claims :=
  payment.original_claims_unchanged fee

theorem micro_clock_and_round :
    payment.microNext.clock = current.clock ∧ payment.microNext.round = current.round := by
  simp [microNext, RawLaw.step, payment.accepted, RawLaw.paidStep]

end PaymentAt

inductive PaidMicroRun : RawCurrent Party Good Technology Instrument →
    RawCurrent Party Good Technology Instrument → Nat → Type u
  | nil (current) : PaidMicroRun current current 0
  | snoc {start middle count} (prior : PaidMicroRun start middle count)
      (payment : PaymentAt law request middle) :
      PaidMicroRun start payment.microNext (count + 1)

namespace PaidMicroRun
variable {law request} {start target : RawCurrent Party Good Technology Instrument} {count : Nat}
  (run : PaidMicroRun law request start target count)

include run fee

theorem material_balance :
    target.stock fee.payer fee.good + (count : ℚ) * fee.amount = start.stock fee.payer fee.good := by
  induction run with
  | nil => simp
  | snoc prior payment previous =>
      have paid := payment.micro_stock_balance fee
      push_cast
      nlinarith

theorem count_add_remaining_budget :
    count + physicalBudget request fee target = physicalBudget request fee start := by
  induction run with
  | nil => simp
  | snoc prior payment previous =>
      have paid := payment.micro_budget_debits_one fee
      omega

theorem count_le_original_budget : count ≤ physicalBudget request fee start := by
  have budget := run.count_add_remaining_budget fee
  omega

theorem original_claims_unchanged : target.claims = start.claims := by
  induction run with
  | nil => rfl
  | snoc prior payment previous => exact (payment.micro_claims_unchanged fee).trans previous

omit fee in
theorem same_period : target.clock = start.clock ∧ target.round = start.round := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | snoc prior payment previous =>
      exact ⟨payment.micro_clock_and_round.1.trans previous.1,
        payment.micro_clock_and_round.2.trans previous.2⟩

theorem no_unpaid_extension (spent : count = physicalBudget request fee start) :
    IsEmpty (PaymentAt law request target) := by
  refine ⟨fun payment => ?_⟩
  have budget := run.count_add_remaining_budget fee
  have next := payment.micro_budget_debits_one fee
  omega

end PaidMicroRun

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.PaidMicroRun.count_le_original_budget
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.PaidMicroRun.same_period
