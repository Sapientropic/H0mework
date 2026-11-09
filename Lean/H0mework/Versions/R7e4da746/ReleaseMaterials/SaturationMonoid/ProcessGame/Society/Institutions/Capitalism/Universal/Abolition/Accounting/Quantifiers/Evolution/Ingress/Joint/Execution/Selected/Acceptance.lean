import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Actual

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

theorem each_actual_item_reads_the_same_source_interpreter
    (item : Epoch.Finance.ActualItem seed.input seed.depth seed.count) (original : item ∈ items seed claim) :
    item.interpreter seed.input seed.depth seed.count = actualLaw seed := by
  change item ∈ Epoch.Finance.inventory seed.input seed.depth seed.count (tag seed claim) (visit seed claim) at original
  obtain ⟨position,rfl⟩ := List.mem_ofFn.mp original
  change Physical.Public.interpreter seed.input = actualLaw seed
  exact (Prefix.the_source_current_reads_the_original_public_interpreter seed).symm

theorem no_actual_item_is_rejected_by_its_native_financial_interpreter
    (item : Epoch.Finance.ActualItem seed.input seed.depth seed.count) (original : item ∈ items seed claim) :
    (item.interpreter seed.input seed.depth seed.count).Valid
      (item.instruction seed.input seed.depth seed.count).before (item.instruction seed.input seed.depth seed.count).request := by
  rw [each_actual_item_reads_the_same_source_interpreter seed claim item original]
  apply Planning.every_selected_original_inventory_item_is_actual seed claim (Material.shared seed claim)
  change item.instruction seed.input seed.depth seed.count ∈
    (actualLaw seed).rawItems (Material.shared seed claim).raw (word seed claim)
  rw [← the_native_items_are_the_literal_original_source_inventory seed claim]
  exact List.mem_map.mpr ⟨item,original,rfl⟩

theorem every_actual_requested_instruction_is_the_same_selected_instruction :
    (items seed claim).map (fun item => (item.instruction seed.input seed.depth seed.count).request) = word seed claim := by
  have same := congrArg (List.map ExecutionItem.request)
    (the_native_items_are_the_literal_original_source_inventory seed claim)
  calc
    _ = ((actualLaw seed).rawItems (Material.shared seed claim).raw (word seed claim)).map ExecutionItem.request := by
      simpa only [List.map_map,Function.comp_def] using same
    _ = _ := (actualLaw seed).inventory_requests_exact (Material.shared seed claim).raw 0 (word seed claim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected
