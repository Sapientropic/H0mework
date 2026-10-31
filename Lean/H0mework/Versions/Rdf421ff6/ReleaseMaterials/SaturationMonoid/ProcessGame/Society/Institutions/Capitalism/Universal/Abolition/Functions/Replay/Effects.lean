import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (original : RawEvent Party Good Port Technology Instrument)

theorem each_original_item_has_the_same_before_and_actual_after
    (item : ExecutionItem Party Good Port Technology Instrument)
    (present : item ∈ law.rawItems current original) :
    itemAt law item ∈ (PublicFunction.physicalLaw law).rawItems current (wordAt law current original) ∧
    (itemAt law item).before = item.before ∧
    (PublicFunction.physicalLaw law).step (itemAt law item).before (itemAt law item).request =
      law.step item.before item.request := by
  refine ⟨?_, rfl, the_computed_request_preserves_the_original_actual_step law item.before item.request⟩
  change itemAt law item ∈ ((PublicFunction.physicalLaw law).execute current 0 (wordAt law current original)).items
  rw [(replay_execution_has_the_same_actual_currents law current 0 original).2]
  exact List.mem_map.mpr ⟨item, present, rfl⟩

theorem the_full_original_material_and_financial_trajectory_is_preserved :
    ((PublicFunction.physicalLaw law).rawItems current (wordAt law current original)).map
      (fun item => (item.index, item.before, (PublicFunction.physicalLaw law).step item.before item.request)) =
    (law.rawItems current original).map (fun item => (item.index, item.before, law.step item.before item.request)) := by
  change (((PublicFunction.physicalLaw law).execute current 0 (wordAt law current original)).items.map _) = _
  rw [(replay_execution_has_the_same_actual_currents law current 0 original).2, List.map_map]
  apply List.map_congr_left
  intro item present
  exact congrArg (fun after => (item.index, item.before, after))
    (the_computed_request_preserves_the_original_actual_step law item.before item.request)

theorem both_gross_flow_traces_are_exact :
    ((PublicFunction.physicalLaw law).rawItems current (wordAt law current original)).map
      (fun item => (PublicFunction.physicalLaw law).actualDebit item.before item.request) =
      (law.rawItems current original).map (fun item => law.actualDebit item.before item.request) ∧
    ((PublicFunction.physicalLaw law).rawItems current (wordAt law current original)).map
      (fun item => (PublicFunction.physicalLaw law).actualCredit item.before item.request) =
      (law.rawItems current original).map (fun item => law.actualCredit item.before item.request) := by
  have items := (replay_execution_has_the_same_actual_currents law current 0 original).2
  change (PublicFunction.physicalLaw law).rawItems current (wordAt law current original) =
    (law.rawItems current original).map (itemAt law) at items
  rw [items, List.map_map, List.map_map]
  constructor
  · apply List.map_congr_left
    intro item present
    exact (the_computed_request_preserves_both_original_gross_flows law item.before item.request).1
  · apply List.map_congr_left
    intro item present
    exact (the_computed_request_preserves_both_original_gross_flows law item.before item.request).2

theorem original_total_debit_and_credit_are_preserved (person : Party) (good : Good) :
    (PublicFunction.physicalLaw law).totalDebit
        ((PublicFunction.physicalLaw law).rawItems current (wordAt law current original)) person good =
      law.totalDebit (law.rawItems current original) person good ∧
    (PublicFunction.physicalLaw law).totalCredit
        ((PublicFunction.physicalLaw law).rawItems current (wordAt law current original)) person good =
      law.totalCredit (law.rawItems current original) person good := by
  have flows := both_gross_flow_traces_are_exact law current original
  constructor
  · simpa only [RawLaw.totalDebit, List.map_map, Function.comp_def] using
      congrArg (fun flows => (flows.map (fun flow => flowAt flow person good)).sum) flows.1
  · simpa only [RawLaw.totalCredit, List.map_map, Function.comp_def] using
      congrArg (fun flows => (flows.map (fun flow => flowAt flow person good)).sum) flows.2

theorem original_production_recipes_and_capacities_are_retained (person : Party) :
    (PublicFunction.physicalLaw law).technique current.technology person = law.technique current.technology person ∧
    (PublicFunction.physicalLaw law).technique
      ((PublicFunction.physicalLaw law).next current (wordAt law current original)).technology person =
      law.technique (law.next current original).technology person := by
  rw [replay_preserves_the_original_full_next]
  exact ⟨rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.the_full_original_material_and_financial_trajectory_is_preserved
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.both_gross_flow_traces_are_exact
