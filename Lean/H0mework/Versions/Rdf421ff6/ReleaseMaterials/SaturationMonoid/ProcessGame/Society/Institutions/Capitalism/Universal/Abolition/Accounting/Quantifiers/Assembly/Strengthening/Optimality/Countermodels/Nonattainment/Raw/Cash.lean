import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Raw.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

theorem no_other_original_operation_can_produce_cash
    (current : RawCurrent Bool Bool Nat Unit) (instruction : Request Bool Bool Unit Nat Unit)
    (nonnegative : StockNonnegative current) (empty : CashZero current)
    (accepted : law.Valid current instruction) (notProduction : instruction.operation ≠ .produce false)
    (actor : Bool) : flowAt (law.credit current instruction) actor false = 0 := by
  cases operation : instruction.operation with
  | produce operator =>
      cases operator with
      | false => exact (notProduction operation).elim
      | true => simp [RawLaw.credit,operation,law,flowAt,locate,amount]
  | transfer sender receiver goods =>
      have debit := no_cash_means_no_accepted_cash_debit current instruction nonnegative empty accepted sender
      have absent : amount Bool goods false = 0 := by
        simpa [RawLaw.debit,operation,flow_at_located_bundle] using debit
      simp [RawLaw.credit,operation,flow_at_located_bundle,absent]
  | settle instrument debtor holder quantity =>
      cases instrument
      have zero := no_cash_cannot_pay_positive_original_debt current instruction nonnegative empty accepted debtor holder quantity operation
      simp [RawLaw.credit,operation,zero,flowAt,locate,amount]
  | use bearer goods purpose => simp [RawLaw.credit,operation,flowAt,amount]
  | issue instrument issuer holder quantity => simp [RawLaw.credit,operation,flowAt,amount]
  | assign instrument issuer sender holder quantity => simp [RawLaw.credit,operation,flowAt,amount]
  | revise operator technology => simp [RawLaw.credit,operation,flowAt,amount]
  | present => simp [RawLaw.credit,operation,flowAt,amount]

theorem cash_zero_is_preserved_without_real_production
    (current : RawCurrent Bool Bool Nat Unit) (instruction : Request Bool Bool Unit Nat Unit)
    (nonnegative : StockNonnegative current) (empty : CashZero current)
    (notProduction : instruction.operation ≠ .produce false) : CashZero (law.step current instruction) := by
  by_cases accepted : law.Valid current instruction
  · intro actor
    simp only [RawLaw.step,if_pos accepted,RawLaw.paidStep]
    rw [empty actor,no_cash_means_no_accepted_cash_debit current instruction nonnegative empty accepted actor,
      no_other_original_operation_can_produce_cash current instruction nonnegative empty accepted notProduction actor]
    ring
  · rw [law.rejected_preserves_current current instruction accepted]
    exact empty

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
