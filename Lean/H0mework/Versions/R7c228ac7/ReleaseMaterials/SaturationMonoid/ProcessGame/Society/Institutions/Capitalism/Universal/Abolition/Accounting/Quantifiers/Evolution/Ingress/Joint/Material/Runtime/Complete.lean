import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Endpoint
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Economy
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Actors

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion SourceNativeInquiryRuntime
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

structure RootedJointPaymentAt : Prop where
  selected_by_original_root : (state seed claim).compileInquiry PUnit.unit = .actualAction (generated seed claim)
  activated_by_named_runtime : type_of% (the_source_programme_is_consumed_by_the_named_canonical_runtime seed claim)
  actual_root_next : type_of% (the_actual_whole_root_returns_this_current seed claim)
  actual_physical_next : type_of% (the_actual_next_material_face_is_the_real_physical_next seed claim)
  same_actual_inventory : type_of% (Execution.Selected.the_native_items_are_the_literal_original_source_inventory seed claim)
  same_original_actor : type_of% (Execution.Prefix.the_public_financial_source_inherits_every_original_generated_actor
    seed (Material.word seed claim))
  shared_root_rows : type_of% (the_actual_root_debt_rows_read_the_same_shared_face seed claim)
  funded_original_payment : Planning.Enough seed claim (Material.shared seed claim) →
    Current.productivePaid seed claim (sharedAt seed claim (nextVisit seed claim).current) ∧
      Current.grossPaid seed claim (sharedAt seed claim (nextVisit seed claim).current) ∧
      Exit.Necessity.AllNeedsPaid (actualLaw seed) (Material.shared seed claim).raw
        seed.current.members (Material.word seed claim)
  actual_coalition_account : ∀ members good,
    type_of% (no_coalition_keeps_unaccounted_control_income_in_the_actual_root seed claim members good)
  actual_refusal_disposition : type_of% (the_actual_root_reply_has_its_source_authority_disposition seed claim)
  actual_refusal_next : type_of% (the_actual_boundary_and_root_read_the_same_after seed claim)
  complete_financial_root : ∀ n, type_of% (all_original_financial_rows_read_this_one_actual_root_account seed claim n)
  finite_source_budget : type_of% (the_source_budget_reaches_the_same_named_native_root seed claim)
  finite_actual_completion : type_of% (the_named_runtime_completes_the_original_financial_consumption_within_its_source_budget seed claim)
  no_material_replay : type_of% (the_named_final_root_keeps_the_one_executed_material_result seed claim)
  complete_original_lifecycle : type_of% (the_actual_final_account_retains_the_entire_original_ordered_lifecycle seed claim)
  generated_whole_next : ∀ n, type_of% (next_is_the_same_complete_root seed claim n)

theorem the_original_root_executes_its_joint_payment_and_complete_native_account : RootedJointPaymentAt seed claim where
  selected_by_original_root := the_original_root_actually_executes_the_shared_material_programme seed claim
  activated_by_named_runtime := the_source_programme_is_consumed_by_the_named_canonical_runtime seed claim
  actual_root_next := the_actual_whole_root_returns_this_current seed claim
  actual_physical_next := the_actual_next_material_face_is_the_real_physical_next seed claim
  same_actual_inventory := Execution.Selected.the_native_items_are_the_literal_original_source_inventory seed claim
  same_original_actor := Execution.Prefix.the_public_financial_source_inherits_every_original_generated_actor seed (Material.word seed claim)
  shared_root_rows := the_actual_root_debt_rows_read_the_same_shared_face seed claim
  funded_original_payment := by
    intro enough
    have paid := primitive_resources_force_both_actual_root_rows_to_be_paid seed claim enough
    have source := Planning.sufficient_source_resources_force_the_actual_shared_payment seed claim (Material.shared seed claim) enough
    exact ⟨paid.1,paid.2,source.needsPaid⟩
  actual_coalition_account := no_coalition_keeps_unaccounted_control_income_in_the_actual_root seed claim
  actual_refusal_disposition := the_actual_root_reply_has_its_source_authority_disposition seed claim
  actual_refusal_next := the_actual_boundary_and_root_read_the_same_after seed claim
  complete_financial_root := all_original_financial_rows_read_this_one_actual_root_account seed claim
  finite_source_budget := the_source_budget_reaches_the_same_named_native_root seed claim
  finite_actual_completion := the_named_runtime_completes_the_original_financial_consumption_within_its_source_budget seed claim
  no_material_replay := the_named_final_root_keeps_the_one_executed_material_result seed claim
  complete_original_lifecycle := the_actual_final_account_retains_the_entire_original_ordered_lifecycle seed claim
  generated_whole_next := next_is_the_same_complete_root seed claim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
