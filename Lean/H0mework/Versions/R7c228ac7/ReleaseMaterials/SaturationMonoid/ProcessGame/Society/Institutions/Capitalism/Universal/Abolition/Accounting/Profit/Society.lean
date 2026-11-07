import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Decomposition
import Mathlib.Data.Finsupp.Ext

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

/-- Sum an original material unit across all its finite affected support,
without an external population roster or a cross-good price. -/
def societyRead (good : Good) : Vector (Party := Party) (Good := Good) →+ ℚ :=
  Finsupp.liftAddHom fun cell => if cell.2 = good then AddMonoidHom.id ℚ else 0

omit [DecidableEq Party] in
theorem society_read_single (good : Good) (cell : Party × Good) (quantity : ℚ) :
    societyRead good (Finsupp.single cell quantity) = if cell.2 = good then quantity else 0 := by
  simp only [societyRead,Finsupp.liftAddHom_apply_single]
  split <;> rfl

omit [DecidableEq Party] in
theorem society_read_original_flow (good : Good) (flow : Flow Party Good) :
    societyRead good (Financial.flowVector flow) = Innovation.Control.physicalQuantity flow good := by
  induction flow with
  | nil => simp [Financial.flowVector,Innovation.Control.physicalQuantity]
  | cons lot rest inherited =>
      simp only [Financial.flowVector,List.map_cons,List.sum_cons,map_add] at inherited ⊢
      rw [society_read_single,inherited]
      rfl

variable (law : RawLaw Party Good Port Technology Instrument)

omit [DecidableEq Party] in
theorem original_financial_positions_sum_to_zero_in_every_material_unit
    (good : Good) (changes : Financial.ClaimChange (Party := Party) (Instrument := Instrument)) :
    societyRead good (Financial.value law changes) = 0 := by
  have neutral : (societyRead good).comp (Financial.value law) = 0 := by
    apply Finsupp.addHom_ext
    intro key quantity
    rcases key with ⟨instrument,debtor,holder⟩
    simp only [AddMonoidHom.comp_apply,Financial.value_single,map_sub,society_read_single,
      AddMonoidHom.zero_apply,sub_self]
  simpa only [AddMonoidHom.comp_apply,AddMonoidHom.zero_apply] using
    congrArg (fun read : Financial.ClaimChange (Party := Party) (Instrument := Instrument) →+ ℚ => read changes) neutral

theorem society_read_material_change
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) :
    societyRead good (Financial.materialChange law item.before item.request) =
      Innovation.Control.stepNet law item good := by
  simp only [Financial.materialChange,map_sub,society_read_original_flow]
  rfl

theorem society_read_production_is_the_actual_output_minus_all_original_costs
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) :
    societyRead good (productionAt law item) =
      Innovation.Control.stepOutput law item good - Innovation.Control.stepCost law item good := by
  have actual := Innovation.Control.each_real_step_separates_production_cost_and_internal_transfers law item good
  cases operation : item.request.operation <;>
    simp only [productionAt,Innovation.Control.stepOutput,Innovation.Control.stepCost,operation,map_zero,sub_zero]
  all_goals
    rw [society_read_material_change]
    simpa only [Innovation.Control.stepOutput,Innovation.Control.stepCost,operation] using actual

theorem original_claims_and_transfers_cannot_add_social_production
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) :
    societyRead good (transferAt law item) = 0 := by
  have split := congrArg (fun vector : Vector (Party := Party) (Good := Good) => societyRead good vector)
    (every_original_operation_separates_production_and_existing_positions law item)
  simp only [Financial.fullChange,map_add,original_financial_positions_sum_to_zero_in_every_material_unit,
    add_zero,society_read_material_change,society_read_production_is_the_actual_output_minus_all_original_costs] at split
  have actual := Innovation.Control.each_real_step_separates_production_cost_and_internal_transfers law item good
  linarith

theorem all_original_claims_and_transfers_have_zero_social_production
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) :
    societyRead good (transfers law items) = 0 := by
  induction items with
  | nil => simp [transfers]
  | cons item rest inherited =>
      simp only [transfers,List.map_cons,List.sum_cons,map_add] at inherited ⊢
      rw [original_claims_and_transfers_cannot_add_social_production, inherited,add_zero]

variable [DecidableEq Port] [DecidableEq Instrument]

theorem original_control_income_and_its_transfer_complement_create_no_social_output
    (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (good : Good) :
    societyRead good (controlIncome law initial word) + societyRead good (otherTransfers law initial word) = 0 := by
  rw [← map_add,all_original_transfers_are_exhausted_without_double_counting,
    all_original_claims_and_transfers_have_zero_social_production]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit
