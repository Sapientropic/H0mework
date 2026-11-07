import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Index
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion SourceNativeInquiryRuntime
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

attribute [local irreducible] Execution.Selected.items Planning.selected

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def financialFace (n : Nat) : SourceNativeRootSemanticFaceAt (Inquiry.root seed claim) (temporalAt seed claim n) :=
  { projection := .component Inquiry.Projection.financial,active := PUnit.unit,classifier_eq := rfl }

theorem the_financial_face_is_the_actual_native_cursor_account (n : Nat) :
    (financialFace seed claim n).rootRead = (visitAt seed claim n).current.account := rfl

theorem all_original_financial_rows_read_this_one_actual_root_account (n : Nat) :
    (Background.shape seed).AllRead seed.input seed.depth seed.count (financialFace seed claim n).rootRead
      (support seed claim (visitAt seed claim n).current).1.1 :=
  (Background.shape seed).ready_support_reads_one_whole_account seed.input seed.depth seed.count
    (Background.visit seed).current (Background.all_existing_native_rows_are_registered_at_this_actual_visit seed)
    (visitAt seed claim n).current.account (visitAt seed claim n).current.native

theorem the_source_budget_reaches_the_same_named_native_root :
    ((runtime seed claim).stateAt (Drain.budget seed claim)).engine.node =
      .active (answerPresentation seed claim (Execution.Selected.items seed claim).length) := by
  unfold Drain.budget
  rw [Nat.add_comm 1 _]
  exact every_actual_runtime_stage_is_the_original_native_visit seed claim _

theorem the_final_actual_native_coordinate_is_the_source_completed_cursor :
    (visitAt seed claim (Execution.Selected.items seed claim).length).current = Drain.completed seed claim := by
  rw [the_native_root_coordinate_is_the_original_source_iteration]
  unfold Drain.completed Drain.budget
  rw [Nat.add_comm 1 _]

theorem the_named_runtime_completes_the_original_financial_consumption_within_its_source_budget :
    (financialFace seed claim (Execution.Selected.items seed claim).length).rootRead = Execution.Selected.after seed claim := by
  rw [the_financial_face_is_the_actual_native_cursor_account]
  rw [the_final_actual_native_coordinate_is_the_source_completed_cursor]
  exact (Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).1

theorem the_named_final_root_keeps_the_one_executed_material_result :
    sharedAt seed claim (visitAt seed claim (Execution.Selected.items seed claim).length).current =
      Planning.actualNext seed claim (Material.shared seed claim) :=
  the_single_executed_body_is_retained_at_every_native_visit seed claim _

theorem the_actual_final_account_retains_the_entire_original_ordered_lifecycle :
    (Execution.Selected.before seed).current.history <+:
      (financialFace seed claim (Execution.Selected.items seed claim).length).rootRead.current.history := by
  rw [the_named_runtime_completes_the_original_financial_consumption_within_its_source_budget]
  exact Execution.Selected.the_entire_original_ordered_lifecycle_history_is_retained seed claim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
