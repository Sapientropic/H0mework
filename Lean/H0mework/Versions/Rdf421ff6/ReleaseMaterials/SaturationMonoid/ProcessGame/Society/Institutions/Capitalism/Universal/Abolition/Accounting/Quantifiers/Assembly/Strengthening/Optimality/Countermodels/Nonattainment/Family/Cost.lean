import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Family.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Cost.Pricing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (one_checked_original_primitive_has_one_actual_material_step)
noncomputable section

private theorem empty_parts_have_zero_item_value (price : Cost.LinearReadout Bool Bool)
    (item : ExecutionItem Bool Bool Unit Nat Unit)
    (empty : ∀ channel,Cost.actualPart law item.before item.request channel = []) : Cost.itemValue price law item = 0 := by
  simp [Cost.itemValue,empty,Cost.weightedFlow]

private theorem upgrade_value_is_zero (price : Cost.LinearReadout Bool Bool) (n : Nat) :
    Cost.itemValue price law ⟨0,before.raw,upgrade n⟩ = 0 := by
  apply empty_parts_have_zero_item_value
  intro channel
  unfold Cost.actualPart
  split
  · simp [Cost.part,upgrade,request,RawLaw.debit,law,locate]
  · rfl

private theorem original_payment_value_is_zero (price : Cost.LinearReadout Bool Bool) (n : Nat) :
    Cost.itemValue price law ⟨0,produced n,repay⟩ = 0 := by
  apply empty_parts_have_zero_item_value
  intro channel
  exact Cost.a_settlement_does_not_destroy_real_resources law (produced n) repay channel () false true 1 rfl

theorem the_candidates_pay_the_same_actual_positive_maintenance_and_efficient_input (n : Nat) :
    Cost.value reading input before (programme n) = 1 + epsilon n ∧
      Cost.value fullReading input before (programme n) = 1 + epsilon n := by
  have physical := (the_productive_item_pays_its_actual_input_and_positive_maintenance
    ⟨0,upgraded n,produce⟩ rfl (source_production_is_affordable n))
  have clock : Programme.clockCost input before (programme n) = 0 :=
    Programme.pure_microsteps_have_zero_elapsed_cost input before (word n)
  constructor <;> simp only [Cost.value,the_active_physical_interpreter_is_the_same_source_law,
    each_candidate_owns_exactly_its_actual_primitive_inventory,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    clock,mul_zero,add_zero,upgrade_value_is_zero,original_payment_value_is_zero,zero_add]
  · exact physical.1
  · exact physical.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
