import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Programme

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

theorem each_actual_item_cost_is_nonnegative (price : Cost.LinearReadout Bool Bool)
    (item : ExecutionItem Bool Bool Unit Nat Unit) : 0 ≤ Cost.itemValue price law item := by
  unfold Cost.itemValue
  apply List.sum_nonneg
  intro amount member
  obtain ⟨channel,listed,rfl⟩ := List.mem_map.mp member
  unfold Cost.weightedFlow
  apply List.sum_nonneg
  intro amount member
  obtain ⟨entry,listed,rfl⟩ := List.mem_map.mp member
  exact mul_nonneg (price.resource_nonnegative channel entry.1.1 entry.1.2)
    (Cost.actualPart_is_the_original_nonnegative_flow law item.before item.request channel entry listed)

theorem the_productive_item_pays_its_actual_input_and_positive_maintenance
    (item : ExecutionItem Bool Bool Unit Nat Unit) (operation : item.request.operation = .produce false)
    (accepted : law.Valid item.before item.request) :
    Cost.itemValue reading law item = 1 + epsilon item.before.technology ∧
      Cost.itemValue fullReading law item = 1 + epsilon item.before.technology := by
  constructor <;> unfold Cost.itemValue <;> simp only [Cost.actualPart,if_pos accepted]
  all_goals (simp [Cost.channels,Cost.weightedFlow,Cost.part,operation,law,reading,fullReading,locate]; ring)

theorem an_original_nonnegative_member_is_bounded_by_the_whole_sum
    (items : List (ExecutionItem Bool Bool Unit Nat Unit)) (item : ExecutionItem Bool Bool Unit Nat Unit)
    (listed : item ∈ items) :
    Cost.itemValue reading law item ≤ (items.map (Cost.itemValue reading law)).sum := by
  induction items with
  | nil => cases listed
  | cons first tail inherited =>
      rcases List.mem_cons.mp listed with same | later
      · cases same
        apply le_add_of_nonneg_right
        exact List.sum_nonneg (fun amount member => by
          obtain ⟨actual,_,rfl⟩ := List.mem_map.mp member
          exact each_actual_item_cost_is_nonnegative reading actual)
      · exact (inherited later).trans (le_add_of_nonneg_left (each_actual_item_cost_is_nonnegative reading first))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
