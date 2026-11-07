import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native.Inventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Word

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

omit [DecidableEq Port] in
/-- Cash and the very same original claim's retirement cancel at every
prefix, with no paid-state or successful-final-account premise. -/
theorem every_retirement_program_has_zero_full_income
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (retirement : ∀ request ∈ word, RetirementRequest request) :
    Profit.fullIncome law (law.rawItems before word) = 0 := by
  apply an_arbitrary_original_retirement_inventory_has_zero_full_income
  intro item original
  have listed : item.request ∈ (law.rawItems before word).map ExecutionItem.request := List.mem_map.mpr ⟨item,original,rfl⟩
  rw [RawLaw.rawItems,law.inventory_requests_exact] at listed
  exact retirement item.request listed

theorem every_source_complete_word_is_a_retirement_program
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (law : RawLaw Party Good Port Technology Instrument)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    ∀ request ∈ completeWord input depth count law before, RetirementRequest request := by
  intro request original
  obtain ⟨instrument,debtor,holder,quantity,operation,_⟩ :=
    the_complete_source_word_is_a_nonnegative_payment_inventory input depth count law before request original
  simp only [RetirementRequest,operation]

theorem the_source_complete_word_has_no_financial_timing_income
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (law : RawLaw Party Good Port Technology Instrument)
    (account : (Epoch.Finance.process input depth count).GeneratedState)
    (before : RawCurrent Party Good Technology Instrument) :
    ∀ (members : Party → Bool) good,
      Coalition.read members good (Profit.fullIncome law (law.rawItems before (completeWord input depth count law account))) = 0 := by
  intro members good
  rw [every_retirement_program_has_zero_full_income law before _
    (every_source_complete_word_is_a_retirement_program input depth count law account),map_zero]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native
