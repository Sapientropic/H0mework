import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Raw.Claims

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

def cutRaw : RawCurrent Bool Bool Nat Unit where
  stock := fun actor good => if good then if actor then 0 else 5 else 0
  claims := fun _ debtor holder => if debtor = false ∧ holder = true then 1 else 0
  technology := 0
  clock := genesis.raw.clock
  round := genesis.raw.round

theorem the_unpaid_cut_is_generated_by_the_original_actual_prefix : before.raw = cutRaw := by
  apply RawCurrent.ext
  · funext actor good
    cases actor <;> cases good <;> decide +kernel
  · funext instrument debtor holder
    cases instrument
    cases debtor <;> cases holder <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem the_cash_was_really_advanced_and_then_used_for_living :
    (Programme.run input genesis ([issued,advance].map Compile.RawInput.primitive)).raw.stock false false = 1 ∧
      (Programme.run input genesis ([issued,advance,living].map Compile.RawInput.primitive)).raw.stock false false = 0 ∧
      before.raw.claims () false true = 1 := by decide +kernel

theorem necessary_living_and_maintenance_were_both_actually_paid :
    Cost.resource input genesis initialHistory (.use .necessity) false false = 1 ∧
      Cost.resource input genesis initialHistory (.use .maintenance) false true = 1 ∧
      Programme.clockCost input genesis initialHistory = 0 := by decide +kernel

theorem the_original_cut_has_no_cash_and_retains_its_complete_debt :
    StockNonnegative before.raw ∧ CashZero before.raw ∧ 1 ≤ claimTotal before.raw := by
  rw [the_unpaid_cut_is_generated_by_the_original_actual_prefix]
  refine ⟨?_,?_,?_⟩
  · intro actor good; cases actor <;> cases good <;> norm_num [cutRaw]
  · intro actor; rfl
  · norm_num [claimTotal,cutRaw]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
