import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Service
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.PaidUse

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual (life lifeWord task source_input_is_the_original_registered_input)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open Redemption (sourceLaw)

noncomputable section

private theorem the_script_is_the_original_two_paid_phases (quantity : ℚ) :
    Execution.primitiveScript (word (sourceLaw lifeSource) position quantity ++ lifeWord) =
      compile lifeSource position (proposal quantity) := by
  rw [Execution.primitiveScript_append]
  rfl

private theorem all_original_needs_remain_actually_paid (quantity : ℚ) (paid : PaidAt lifeSource position quantity) :
    Demand.Covers lifeSource (compile lifeSource position (proposal quantity)) := by
  have whole := Execution.append_primitive_traces paid.actual (actual_continuation quantity paid).1
  intro cell required
  unfold Demand.requirements Material.originalRequirements at required
  obtain ⟨bearer, _, sourceCell⟩ := List.mem_flatMap.mp required
  rw [source_input_is_the_original_registered_input] at sourceCell
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] ++ [] at sourceCell
  have exactCell : cell = (bearer, .necessity, true, 1) := by
    simpa [amount] using sourceCell
  have listed : life bearer ∈ word (sourceLaw lifeSource) position quantity ++ lifeWord := by
    apply List.mem_append_right
    cases bearer <;> simp [lifeWord]
  obtain ⟨item, original, same, accepted⟩ := Execution.every_original_request_has_its_paid_native_inventory_item
    whole (life bearer) listed
  rw [the_script_is_the_original_two_paid_phases] at original
  have kind : item.request.operation = .use bearer [(true, 1)] .necessity := by rw [same]; rfl
  have delivered := Demand.an_original_paid_use_is_counted lifeSource _ item original bearer [(true, 1)]
    .necessity true kind accepted
  rw [exactCell]
  simpa [amount] using delivered

theorem every_positive_small_grant_executes_and_leaves_an_actual_exit_service
    (quantity : ℚ) (positive : 0 < quantity) (bounded : quantity ≤ 1) :
    Completed lifeSource position [] task (proposal quantity) := by
  have paid := pay_from_the_existing_source quantity positive bounded
  have target := the_grant_and_its_continuation_share_the_actual_next lifeSource position (proposal quantity)
  refine ⟨settle lifeSource _ ⟨all_original_needs_remain_actually_paid quantity paid, ?_⟩,
    actual_eligibility quantity positive paid, paid, target⟩
  rw [target]
  exact (actual_continuation quantity paid).2

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
