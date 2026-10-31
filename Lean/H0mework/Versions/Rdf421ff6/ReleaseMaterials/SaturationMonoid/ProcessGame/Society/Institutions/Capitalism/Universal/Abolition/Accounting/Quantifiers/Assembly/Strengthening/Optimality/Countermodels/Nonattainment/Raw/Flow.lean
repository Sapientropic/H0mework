import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

def CashZero (current : RawCurrent Bool Bool Nat Unit) : Prop := ∀ actor,current.stock actor false = 0
def StockNonnegative (current : RawCurrent Bool Bool Nat Unit) : Prop := ∀ actor good,0 ≤ current.stock actor good

theorem flow_at_located_bundle (actor person : Bool) (goods : Bundle Bool) (good : Bool) :
    flowAt (locate actor goods) person good = if person = actor then amount Bool goods good else 0 := by
  by_cases same : person = actor
  · subst person
    simp [flowAt,locate,amount,List.map_map,Function.comp_def]
  · simp [flowAt,locate,amount,List.map_map,Function.comp_def,same,Ne.symm same]

theorem no_cash_means_no_accepted_cash_debit
    (current : RawCurrent Bool Bool Nat Unit) (instruction : Request Bool Bool Unit Nat Unit)
    (nonnegative : StockNonnegative current) (empty : CashZero current)
    (accepted : law.Valid current instruction) (actor : Bool) :
    flowAt (law.debit current instruction) actor false = 0 := by
  have upper := law.debit_affordable current instruction nonnegative accepted actor false
  rw [empty actor] at upper
  have lower := amount_nonnegative (law.debit current instruction) accepted.2.2.2.1 (actor,false)
  exact le_antisymm upper lower

theorem no_cash_cannot_pay_positive_original_debt
    (current : RawCurrent Bool Bool Nat Unit) (instruction : Request Bool Bool Unit Nat Unit)
    (nonnegative : StockNonnegative current) (empty : CashZero current)
    (accepted : law.Valid current instruction) (debtor holder : Bool) (quantity : ℚ)
    (operation : instruction.operation = .settle () debtor holder quantity) : quantity = 0 := by
  have debit := no_cash_means_no_accepted_cash_debit current instruction nonnegative empty accepted debtor
  simpa [RawLaw.debit,operation,law,flow_at_located_bundle,amount] using debit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
