import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Native.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Replay
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Realization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open Abolition.Root.Registered Source.Program

variable (history : List (Compile.RawInput Party Good Port Technology Instrument))
  (before : (process input depth count).GeneratedState)

theorem the_actual_public_execution_reads_the_same_original_source :
    Abolition.Root.Epoch.Interface.execution input depth count (tag input depth count history before)
        (visit input depth count history before).current = (result input depth count history before).execution := by
  change (Physical.Public.compile input
    (Physical.Public.stateAt input depth count 0 0 [] (Physical.Prefix.cursor history).past)
    (.execute (word input depth count before))).execution = _
  rw [Physical.Prefix.past_readback]
  rfl

theorem primitive_resources_execute_the_complete_original_source_word
    (resources : Conditions input depth count history before) :
    (result input depth count history before).execution = (Physical.Public.interpreter input).execute
      (sourceState input depth count history).raw 0 (word input depth count before) := by
  have literal := the_source_word_is_literal_under_its_original_signer_resigning input depth count before
  unfold result Physical.Public.compile
  simp only [Physical.Public.wordAt,literal]
  split
  · rfl
  · rename_i item member failed scanned
    exact (failed (primitive_source_resources_generate_all_actual_items input depth count history before resources item
      (by simpa only [literal] using member))).elim

theorem the_native_financial_inventory_is_the_literal_source_execution
    (resources : Conditions input depth count history before) :
    (items input depth count history before).map (ActualItem.instruction input depth count) =
      (Physical.Public.interpreter input).rawItems (sourceState input depth count history).raw (word input depth count before) := by
  exact (inventory_is_exact input depth count (tag input depth count history before) (visit input depth count history before)).trans
    (congrArg ExecutionResult.items ((the_actual_public_execution_reads_the_same_original_source input depth count history before).trans
      (primitive_resources_execute_the_complete_original_source_word input depth count history before resources)))

theorem every_original_native_financial_item_is_actually_accepted
    (resources : Conditions input depth count history before) :
    ∀ item ∈ items input depth count history before,
      (item.interpreter input depth count).Valid (item.instruction input depth count).before
        (item.instruction input depth count).request := by
  intro item member
  have actual : item.instruction input depth count ∈ (Physical.Public.interpreter input).rawItems
      (sourceState input depth count history).raw (word input depth count before) := by
    rw [← the_native_financial_inventory_is_the_literal_source_execution input depth count history before resources]
    exact List.mem_map.mpr ⟨item,member,rfl⟩
  have law : item.interpreter input depth count = Physical.Public.interpreter input := by
    change item ∈ inventory input depth count (tag input depth count history before) (visit input depth count history before) at member
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp member
    rfl
  rw [law]
  exact primitive_source_resources_generate_all_actual_items input depth count history before resources _ actual

theorem the_native_inventory_requests_exactly_the_original_source_word
    (resources : Conditions input depth count history before) :
    (items input depth count history before).map (fun item => (item.instruction input depth count).request) =
      word input depth count before := by
  have same := congrArg (List.map ExecutionItem.request)
    (the_native_financial_inventory_is_the_literal_source_execution input depth count history before resources)
  calc
    _ = ((Physical.Public.interpreter input).rawItems (sourceState input depth count history).raw
        (word input depth count before)).map ExecutionItem.request := by
      simpa only [List.map_map,Function.comp_def] using same
    _ = _ := RawLaw.inventory_requests_exact _ _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative
