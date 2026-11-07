import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

theorem all_native_stages_retain_the_one_material_result (stages : Nat) :
    Runtime.sharedAt seed claim (stateAt seed claim (stages + 1)) =
      Planning.actualNext seed claim (Material.shared seed claim) := by
  unfold Runtime.sharedAt
  rw [every_positive_native_stage_has_already_paid_the_single_body]
  exact if_pos rfl

theorem completion_retains_the_one_paid_material_result :
    Runtime.sharedAt seed claim (completed seed claim) = Planning.actualNext seed claim (Material.shared seed claim) := by
  unfold Runtime.sharedAt
  rw [(the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.2]
  exact if_pos rfl

theorem the_full_original_pending_suffix_is_empty :
    (Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)).drop
      (completed seed claim).position = [] := by
  rw [the_source_inventory_is_the_same_selected_occurrence,
    (the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.1]
  exact List.drop_length

theorem native_accounting_never_reexecutes_the_material_body (stages : Nat) :
    Public.Accounting.physical seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
      (stateAt seed claim (stages + 1)) =
    Public.Accounting.physical seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
      (stateAt seed claim 1) := by
  unfold Public.Accounting.physical
  rw [every_positive_native_stage_has_already_paid_the_single_body seed claim stages,
    every_positive_native_stage_has_already_paid_the_single_body seed claim 0]

theorem completed_claims_are_the_same_original_ordered_claims :
    (completed seed claim).account.current.slots.map (Epoch.Finance.slotClaim seed.input seed.depth seed.count) =
      (Execution.Selected.before seed).current.slots.map (Epoch.Finance.slotClaim seed.input seed.depth seed.count) := by
  rw [(the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).1]
  exact Execution.Selected.the_same_repair_neither_reissues_nor_deletes_any_original_claim seed claim

theorem completion_is_the_same_original_financial_run_endpoint :
    Nonempty ((Epoch.Finance.process seed.input seed.depth seed.count).Run
      (Execution.Selected.before seed).current (completed seed claim).account.current) := by
  rw [(the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).1]
  exact ⟨Execution.Selected.nativeRun seed claim⟩

theorem completion_retains_the_entire_original_ordered_lifecycle :
    (Execution.Selected.before seed).current.history <+: (completed seed claim).account.current.history := by
  rw [(the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).1]
  exact Execution.Selected.the_entire_original_ordered_lifecycle_history_is_retained seed claim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain
