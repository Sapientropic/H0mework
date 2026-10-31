import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Family.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Programme

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (one_checked_original_primitive_has_one_actual_material_step)
noncomputable section

def stage1 (n : Nat) := {before with raw := upgraded n}
def stage2 (n : Nat) := {before with raw := produced n}
def stage3 (n : Nat) := {before with raw := paid n}

theorem the_actual_upgrade_reaches_its_source_state (n : Nat) :
    (Physical.Public.compile input before (.primitive (upgrade n))).next = stage1 n := by
  have actual := (one_checked_original_primitive_has_one_actual_material_step input before (upgrade n) rfl
    (source_revision_is_available before.raw n)).2.2
  simpa only [the_active_physical_interpreter_is_the_same_source_law,source_revision_has_its_exact_actual_effect,stage1] using actual

theorem the_actual_production_reaches_its_source_state (n : Nat) :
    (Physical.Public.compile input (stage1 n) (.primitive produce)).next = stage2 n := by
  have actual := (one_checked_original_primitive_has_one_actual_material_step input (stage1 n) produce rfl
    (source_production_is_affordable n)).2.2
  simpa only [stage1,stage2,the_active_physical_interpreter_is_the_same_source_law,source_production_is_a_real_step] using actual

theorem the_actual_payment_reaches_its_source_state (n : Nat) :
    (Physical.Public.compile input (stage2 n) (.primitive repay)).next = stage3 n := by
  have actual := (one_checked_original_primitive_has_one_actual_material_step input (stage2 n) repay rfl
    (original_debt_is_payable_after_production n)).2.2
  simpa only [stage2,stage3,the_active_physical_interpreter_is_the_same_source_law,source_payment_is_a_real_step] using actual

theorem each_candidate_is_its_actual_original_programme_run (n : Nat) :
    Programme.run input before (programme n) = stage3 n := by
  simp only [programme,word,List.map_cons,List.map_nil,Programme.run]
  rw [the_actual_upgrade_reaches_its_source_state,the_actual_production_reaches_its_source_state,
    the_actual_payment_reaches_its_source_state]

theorem each_candidate_owns_exactly_its_actual_primitive_inventory (n : Nat) :
    Programme.items input before (programme n) =
      [⟨0,before.raw,upgrade n⟩,⟨0,upgraded n,produce⟩,⟨0,produced n,repay⟩] := by
  have first := (one_checked_original_primitive_has_one_actual_material_step input before (upgrade n) rfl
    (source_revision_is_available before.raw n)).2.1
  have second := (one_checked_original_primitive_has_one_actual_material_step input (stage1 n) produce rfl
    (source_production_is_affordable n)).2.1
  have third := (one_checked_original_primitive_has_one_actual_material_step input (stage2 n) repay rfl
    (original_debt_is_payable_after_production n)).2.1
  simp only [programme,word,List.map_cons,List.map_nil,Programme.items]
  rw [first,the_actual_upgrade_reaches_its_source_state,second,the_actual_production_reaches_its_source_state,third]
  rfl

theorem each_candidate_actually_clears_the_complete_original_debt (n : Nat) : RawCleared (programme n) := by
  intro debtor holder
  rw [each_candidate_is_its_actual_original_programme_run]
  cases debtor <;> cases holder <;>
    simp [stage3,paid,produced,upgraded,cutRaw,RawLaw.paidStep,RawLaw.nextClaims,repay,produce,request]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
