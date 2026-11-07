import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Raw.Cash
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

def Obstruction (current : RawCurrent Bool Bool Nat Unit) : Prop :=
  StockNonnegative current ∧ CashZero current ∧ 1 ≤ claimTotal current

theorem a_source_microstep_preserves_the_obstruction
    (current : RawCurrent Bool Bool Nat Unit) (instruction : Request Bool Bool Unit Nat Unit)
    (prior : Obstruction current) (notProduction : instruction.operation ≠ .produce false) :
    Obstruction (law.step current instruction) :=
  ⟨law.step_stock_nonnegative current instruction prior.1,
    cash_zero_is_preserved_without_real_production current instruction prior.1 prior.2.1 notProduction,
    prior.2.2.trans (cash_zero_prevents_any_reduction_of_complete_debt current instruction prior.1 prior.2.1)⟩

theorem the_original_execution_cannot_remove_the_obstruction_without_production
    (current : RawCurrent Bool Bool Nat Unit) (index : Nat) (word : RawEvent Bool Bool Unit Nat Unit)
    (prior : Obstruction current)
    (notProduction : ∀ item ∈ (law.execute current index word).items,item.request.operation ≠ .produce false) :
    Obstruction (law.execute current index word).final := by
  induction word generalizing current index with
  | nil => exact prior
  | cons instruction tail inherited =>
      have first := a_source_microstep_preserves_the_obstruction current instruction prior
        (notProduction ⟨index,current,instruction⟩ List.mem_cons_self)
      exact inherited (law.step current instruction) (index+1) first
        (fun item listed => notProduction item (List.mem_cons_of_mem _ listed))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
