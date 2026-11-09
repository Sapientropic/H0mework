import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers

open Source.Program Quantifiers.Joint

noncomputable section

theorem the_actual_menu_has_exactly_its_original_source_plan :
    Planning.Menu.plans Fixture.seed Fixture.grossClaim (Material.shared Fixture.seed Fixture.grossClaim) =
      [Quantifiers.Joint.Consumers.Compact.defaultWord] := by
  change Planning.Menu.plans Fixture.seed Fixture.grossClaim Consumers.Compact.shared = _
  have unpaid := Consumers.Compact.the_original_productive_row_is_still_active
  rw [Planning.Menu.plans,if_neg (fun paid => unpaid paid.1),Planning.Menu.operators,if_neg unpaid,
    Consumers.Compact.the_productive_gap_is_the_same_sources_real_eighteen.2]
  have technologies : Planning.Menu.technologies Fixture.seed Fixture.grossClaim Consumers.Compact.shared = [()] := by
    unfold Planning.Menu.technologies
    rw [show Consumers.Compact.shared.raw.technology = () from Subsingleton.elim _ _]
    decide +kernel
  rw [List.flatMap_cons,List.flatMap_nil,List.append_nil,technologies]
  rfl

theorem the_selected_source_word_is_the_original_funded_plan :
    Selected.word Fixture.seed Fixture.grossClaim = Consumers.Compact.defaultWord := by
  change Planning.selected Fixture.seed Fixture.grossClaim Consumers.Compact.shared = _
  rw [Planning.sufficient_source_resources_execute_the_whole_selected_programme _ _ _
    Consumers.Compact.the_source_generates_its_own_sufficient_plan]
  have menu : Planning.Menu.plans Fixture.seed Fixture.grossClaim Consumers.Compact.shared =
      [Consumers.Compact.defaultWord] := the_actual_menu_has_exactly_its_original_source_plan
  unfold Planning.chosen
  cases chosen : Planning.selection Fixture.seed Fixture.grossClaim Consumers.Compact.shared with
  | ready programme original resources =>
      rw [menu] at original
      exact List.mem_singleton.mp original
  | blocked issues =>
      exact (Planning.failure_inventory_retains_each_original_plan _ _ _ issues _
        (by rw [menu]; exact List.mem_singleton_self _)
        Consumers.Compact.the_default_source_plan_has_all_primitive_resources).elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers
