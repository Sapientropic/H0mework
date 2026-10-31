import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Read

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native

open Source.Program
open Abolition.Completion.Actual.Dividend
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

/-- This is an operation class, not a profitability or paid-endpoint predicate. -/
def RetirementRequest (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .settle .. | .present => True
  | _ => False

instance (request : Request Party Good Port Technology Instrument) : Decidable (RetirementRequest request) := by
  unfold RetirementRequest
  cases request.operation <;> infer_instance

theorem each_original_retirement_has_zero_full_income
    (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (retirement : RetirementRequest item.request) :
    Profit.productionAt law item = 0 ∧ Profit.transferAt law item = 0 := by
  cases operation : item.request.operation <;> simp only [RetirementRequest,operation] at retirement
  all_goals first | exact False.elim retirement | exact ⟨by simp [Profit.productionAt,operation],by simp [Profit.transferAt,operation]⟩

theorem an_arbitrary_original_retirement_inventory_has_zero_full_income
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (retirement : ∀ item ∈ items, RetirementRequest item.request) : Profit.fullIncome law items = 0 := by
  rw [Profit.every_original_inventory_separates_production_and_existing_positions]
  have production : Profit.production law items = 0 := by
    unfold Profit.production
    apply List.sum_eq_zero
    intro value listed
    obtain ⟨item,original,rfl⟩ := List.mem_map.mp listed
    exact (each_original_retirement_has_zero_full_income law item (retirement item original)).1
  have transfers : Profit.transfers law items = 0 := by
    unfold Profit.transfers
    apply List.sum_eq_zero
    intro value listed
    obtain ⟨item,original,rfl⟩ := List.mem_map.mp listed
    exact (each_original_retirement_has_zero_full_income law item (retirement item original)).2
  rw [production,transfers,add_zero]

private theorem income_cons
    (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (rest : List (ExecutionItem Party Good Port Technology Instrument)) :
    Profit.fullIncome law (item :: rest) = Profit.productionAt law item + Profit.transferAt law item + Profit.fullIncome law rest := by
  rw [Profit.every_original_inventory_separates_production_and_existing_positions,
    Profit.every_original_inventory_separates_production_and_existing_positions]
  simp only [Profit.production,Profit.transfers,List.map_cons,List.sum_cons]
  abel

/-- Filtering only reads original effects at their original before-states;
it does not replay the remaining requests without the settlements. -/
theorem every_program_keeps_all_other_effects_separate_from_retirement
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    Profit.fullIncome law items = Profit.fullIncome law (items.filter fun item => ¬ RetirementRequest item.request) := by
  induction items with
  | nil => rfl
  | cons item rest inherited =>
      by_cases retirement : RetirementRequest item.request
      · have zero := each_original_retirement_has_zero_full_income law item retirement
        have filtered : ((item :: rest).filter fun item => ¬ RetirementRequest item.request) =
            (rest.filter fun item => ¬ RetirementRequest item.request) := by simp [retirement]
        rw [filtered,income_cons,zero.1,zero.2,zero_add,zero_add]
        exact inherited
      · have filtered : ((item :: rest).filter fun item => ¬ RetirementRequest item.request) =
            item :: (rest.filter fun item => ¬ RetirementRequest item.request) := by simp [retirement]
        rw [filtered,income_cons,income_cons,inherited]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native
