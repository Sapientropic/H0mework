import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def result := Physical.Public.compile seed.input (Prefix.sharedState seed) (.execute (word seed claim))

theorem the_original_inventory_is_the_same_actual_public_query :
    execution seed claim = (result seed claim).execution := by
  change (Physical.Public.compile seed.input
    (Physical.Public.stateAt seed.input seed.depth seed.count 0 0 [] (Prefix.sharedCursor seed).past)
    (.execute (word seed claim))).execution = _
  unfold Prefix.sharedCursor
  rw [Physical.Prefix.past_readback]
  rfl

theorem the_source_compiler_executes_the_complete_selected_original_inventory :
    (result seed claim).execution = (Physical.Public.interpreter seed.input).execute
      (Prefix.sharedState seed).raw 0 (word seed claim) := by
  have literal : (word seed claim).map (fun request => request.resign request.signer) = word seed claim :=
    Planning.selected_is_literal_under_original_signer_resigning seed claim (Material.shared seed claim)
  unfold result Physical.Public.compile
  simp only [Physical.Public.wordAt,literal]
  split
  · rfl
  · rename_i item member failed scanned
    have sameMember : item ∈ (Physical.Public.interpreter seed.input).rawItems
        (Prefix.sharedState seed).raw (word seed claim) := by simpa only [literal] using member
    exact (failed (every_selected_original_item_is_actual seed claim item sameMember)).elim

theorem the_native_items_are_the_literal_original_source_inventory :
    (items seed claim).map (Epoch.Finance.ActualItem.instruction seed.input seed.depth seed.count) =
      (actualLaw seed).rawItems (Material.shared seed claim).raw (word seed claim) := by
  have original := Epoch.Finance.inventory_is_exact seed.input seed.depth seed.count
    (tag seed claim) (visit seed claim)
  have actual := congrArg ExecutionResult.items
    ((the_original_inventory_is_the_same_actual_public_query seed claim).trans
      (the_source_compiler_executes_the_complete_selected_original_inventory seed claim))
  have rawEq : (Prefix.sharedState seed).raw = (Material.shared seed claim).raw :=
    Prefix.the_complete_actual_source_history_reads_the_single_shared_raw seed
  have lawEq : Physical.Public.interpreter seed.input = actualLaw seed :=
    (Prefix.the_source_current_reads_the_original_public_interpreter seed).symm
  exact original.trans (actual.trans (congrArg₂
    (fun law raw => law.rawItems raw (word seed claim)) lawEq rawEq))

theorem physical_and_financial_execution_have_the_same_material_next :
    (result seed claim).next.raw = (Planning.actualNext seed claim (Material.shared seed claim)).raw := by
  have actual := Prefix.the_original_public_compiler_accepts_its_checked_word seed.input
    (Prefix.sharedState seed) (word seed claim)
    (every_selected_request_has_no_controller_consent seed claim)
    (every_selected_original_item_is_actual seed claim)
  have rawEq : (Prefix.sharedState seed).raw = (Material.shared seed claim).raw :=
    Prefix.the_complete_actual_source_history_reads_the_single_shared_raw seed
  have lawEq : Physical.Public.interpreter seed.input = actualLaw seed :=
    (Prefix.the_source_current_reads_the_original_public_interpreter seed).symm
  exact actual.2.trans ((congrArg₂
    (fun law raw => law.next raw (word seed claim)) lawEq rawEq).trans
      (Planning.the_selected_next_is_the_one_original_live_material_next seed claim (Material.shared seed claim)).symm)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected
