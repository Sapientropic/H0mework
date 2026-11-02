import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Decomposition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.NoControl

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (initial : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

theorem the_open_interpretation_has_no_source_control_income :
    controlIncome (PublicFunction.physicalLaw law) initial word = 0 := by
  have unavailable := Functions.open_permissions_have_no_capital_kernel (PublicFunction.physicalLaw law)
    (fun _ _ _ => rfl) initial word
  have empty : originalControlImage (PublicFunction.physicalLaw law) initial word = [] := by
    cases image : originalControlImage (PublicFunction.physicalLaw law) initial word with
    | nil => rfl
    | cons kernel rest => exact (unavailable ⟨kernel⟩).elim
  have zero : controlAt (PublicFunction.physicalLaw law) initial word = fun _ => 0 := by
    funext item
    ext cell
    simp [controlAt,sourceOwnerMarked,empty]
  simp [controlIncome,zero]

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem the_original_full_step_is_preserved
    (item : ExecutionItem Party Good Port Technology Instrument) (accepted : law.Valid item.before item.request) :
    Financial.fullChange (PublicFunction.physicalLaw law) item.before item.request =
      Financial.fullChange law item.before item.request := by
  have opened := PublicFunction.valid_physical law item.before item.request accepted
  simp only [Financial.fullChange,Financial.materialChange,Financial.claimChange,RawLaw.actualCredit,
    RawLaw.actualDebit,if_pos accepted,if_pos opened]
  rfl

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem the_original_productive_step_is_preserved
    (item : ExecutionItem Party Good Port Technology Instrument) (accepted : law.Valid item.before item.request) :
    productionAt (PublicFunction.physicalLaw law) item = productionAt law item := by
  have opened := PublicFunction.valid_physical law item.before item.request accepted
  cases operation : item.request.operation <;> simp only [productionAt,operation]
  all_goals
    simp only [Financial.materialChange,RawLaw.actualCredit,RawLaw.actualDebit,if_pos accepted,if_pos opened]
    rfl

/-- Functional regeneration consumes the original lawful trace. It does not
claim a new institutional root has been enacted outside the existing migration. -/
theorem every_original_lawful_contribution_keeps_its_effect_and_full_account_without_control
    (legal : ∀ item ∈ law.rawItems initial word, law.Valid item.before item.request) :
    (PublicFunction.physicalLaw law).next initial word = law.next initial word ∧
      (PublicFunction.physicalLaw law).rawItems initial word = law.rawItems initial word ∧
      production (PublicFunction.physicalLaw law) ((PublicFunction.physicalLaw law).rawItems initial word) =
        production law (law.rawItems initial word) ∧
      fullIncome (PublicFunction.physicalLaw law) ((PublicFunction.physicalLaw law).rawItems initial word) =
        fullIncome law (law.rawItems initial word) ∧
      controlIncome (PublicFunction.physicalLaw law) initial word = 0 := by
  have inventory := Functions.original_items_and_before_states_are_preserved law initial word legal
  refine ⟨Functions.original_full_next_is_preserved law initial word legal,inventory,?_,?_,
    the_open_interpretation_has_no_source_control_income law initial word⟩
  · rw [inventory]
    apply congrArg List.sum
    apply List.map_congr_left
    exact fun item member => the_original_productive_step_is_preserved law item (legal item member)
  · have asSum (reader : RawLaw Party Good Port Technology Instrument)
        (items : List (ExecutionItem Party Good Port Technology Instrument)) :
        fullIncome reader items = (items.map fun item => Financial.fullChange reader item.before item.request).sum := by
      simp only [fullIncome,Financial.inventoryMaterial,Financial.inventoryClaims,Financial.fullChange,map_list_sum]
      simp only [List.map_map,Function.comp_def]
      rw [← List.sum_map_add]
    rw [asSum,asSum,inventory]
    apply congrArg List.sum
    apply List.map_congr_left
    exact fun item member => the_original_full_step_is_preserved law item (legal item member)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit
