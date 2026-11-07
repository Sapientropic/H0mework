import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualBase

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
open Abolition.Accounting.Quantifiers
open Abolition.Accounting.Quantifiers.Joint
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material

noncomputable section

namespace Original
export Joint.Consumers.Compact
  (shared defaultWord the_original_productive_row_is_still_active the_productive_gap_is_the_same_sources_real_eighteen
   the_live_interpreter_is_the_same_public_physical_law shared_raw_readout shared_productive_scope
   shared_gross_scope shared_productive_remaining shared_gross_remaining shared_productive_declared shared_gross_declared
   live_roster original_financial_tail)
end Original

theorem the_actual_original_choice_is_the_existing_default_word :
    Planning.chosen Original.seed Original.grossClaim Original.shared = Original.defaultWord := by
  have member : Planning.chosen Original.seed Original.grossClaim Original.shared ∈
      Planning.Menu.plans Original.seed Original.grossClaim Original.shared := by
    unfold Planning.chosen
    cases selected : Planning.selection Original.seed Original.grossClaim Original.shared with
    | ready word original resources => exact original
    | blocked issues =>
        obtain ⟨word,original,resources⟩ := Original.the_source_generates_its_own_sufficient_plan
        exact (Planning.failure_inventory_retains_each_original_plan _ _ _ issues word original resources).elim
  rcases Planning.Menu.every_plan_keeps_the_original_actor_technology_and_financial_tail
    Original.seed Original.grossClaim Original.shared _ member with paid | ⟨operator,original,technology,_parameter,same⟩
  · exact (Original.the_original_productive_row_is_still_active paid.1).elim
  · rw [Planning.Menu.operators,if_neg Original.the_original_productive_row_is_still_active,
      Original.the_productive_gap_is_the_same_sources_real_eighteen.2] at original
    have operatorIsTrue : operator = true := List.mem_singleton.mp original
    subst operator
    cases technology
    exact same

theorem the_actual_original_selected_word_is_not_recomputed :
    Planning.selected Original.seed Original.grossClaim Original.shared = Original.defaultWord := by
  rw [Planning.sufficient_source_resources_execute_the_whole_selected_programme
    Original.seed Original.grossClaim Original.shared Original.the_source_generates_its_own_sufficient_plan]
  exact the_actual_original_choice_is_the_existing_default_word

theorem base_raw_is_the_original_default_execution :
    base.raw = (PublicFunction.physicalLaw Joint.Consumers.Compact.law).next
      Joint.Consumers.Compact.physicalSnapshot Original.defaultWord := by
  rw [base_has_the_same_original_raw_cut]
  change (Planning.actualNext Original.seed Original.grossClaim Original.shared).raw = _
  rw [Planning.the_selected_next_is_the_one_original_live_material_next,
    the_actual_original_selected_word_is_not_recomputed,
    Original.the_live_interpreter_is_the_same_public_physical_law,Original.shared_raw_readout]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
