import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Source

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Export
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Protocol.SymbolicAuthentication Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
noncomputable section

def parent := ProviderMaterialSource.model
def saved := (ProviderMaterialSource.trace 3 true true).cursor
def retained := (ProviderMaterialSource.trace 3 true true).before

def catalogue (quantity : ℚ) : CatalogueHandoffSource.Catalogue parent.source.code :=
  ⟨if 0<quantity ∧ parent.source.code.law.Valid Upstream.current (Upstream.contribute quantity)
    then [Upstream.contribute quantity] else [],1,[],0,
    (List.finRange parent.source.code.sites).map Event.activate⟩
def point (quantity : ℚ) := CatalogueHandoffSource.cursor parent.source.code (catalogue quantity) saved
def model (quantity : ℚ) : CompletionReviewHandoff.Model :=
  ⟨parent.base,parent.scope,(point quantity).source,parent.law_exact,parent.task_exact⟩
def initialRaw (quantity : ℚ) : Feedback.State (model quantity).source.code :=
  Extension.state parent.source.code (CatalogueHandoffSource.supply parent.source.code (catalogue quantity)) retained

-- Cache the already checked current inside the entire retained state, preserving all other fields.
def initial (quantity : ℚ) : Feedback.State (model quantity).source.code :=
  {initialRaw quantity with current:=Upstream.current}
theorem initial_cache_is_the_entire_same_state (quantity : ℚ) : initial quantity=initialRaw quantity := by
  have same : Upstream.current=(initialRaw quantity).current := Upstream.exact_occurrence
  unfold initial
  rw [same]


def control (quantity : ℚ) (state : SourceContinuationTrace.Trace (model quantity)) : LocalCommandSource.Input :=
  if 0<quantity ∧ (model quantity).source.code.law.Valid state.before.current (Upstream.contribute quantity) then
    match (List.range (model quantity).source.code.actions.length).find?
        (fun index => decide ((model quantity).source.code.actions[index]?=some (Upstream.contribute quantity))) with
    | some index => .command index
    | none => .idle
  else .idle
def trace (quantity : ℚ) :=
  SourceOpportunityHandoff.controlled (model quantity) (point quantity) (initial quantity) (control quantity) 6

theorem retained_is_the_complete_original_seed : retained=EventStep.seed saved :=
  (ProviderMaterialConsumer.every_material_request_replays_only_its_actual_source_inputs 3 true true).2.1
theorem original_side : saved.side=.original := by source_refl

theorem registration_keeps_the_entire_actual_seed (quantity : ℚ) :
    initial quantity=EventStep.seed (point quantity) :=
  (initial_cache_is_the_entire_same_state quantity).trans ((congrArg (Extension.state parent.source.code
    (CatalogueHandoffSource.supply parent.source.code (catalogue quantity))) retained_is_the_complete_original_seed).trans
    (CatalogueHandoffSource.seed parent.source.code (catalogue quantity) saved original_side).symm)

theorem every_export_replays_the_actual_source_inputs (quantity : ℚ) :
    SourceContinuationTrace.Sound (model quantity) (point quantity) (trace quantity)
      (LocalCommandRun.run (model quantity) (point quantity) (trace quantity).inputs) :=
  SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs
    (model quantity) (point quantity) (initial quantity) (registration_keeps_the_entire_actual_seed quantity)
    (control quantity) 6

theorem every_export_keeps_the_complete_original_financial_prefix (quantity : ℚ)
    (ordinal : Nat) (bounded : ordinal≤EventStep.boundary saved) :
    Native.Coupling.Match parent.source.code saved.source.input
      (EventHistory.execute (point quantity) (trace quantity).stages).source.input
      (Financial.accountAt saved.source.input ordinal)
      (Financial.accountAt (EventHistory.execute (point quantity) (trace quantity).stages).source.input ordinal) :=
  CatalogueHandoffSource.completeFinancialPrefix parent.source.code (catalogue quantity) saved original_side
    (trace quantity).stages ordinal bounded

theorem every_export_row_has_its_original_native_inventory (quantity : ℚ)
    (row : StageTrace.Record (code := (model quantity).source.code)) (inside : row∈(trace quantity).rows) :
    let final:=EventHistory.execute (point quantity) (trace quantity).stages
    (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? final.source.input)=StageTrace.items row := by
  have same : (trace quantity).rows=StageTrace.records (point quantity) (trace quantity).stages :=
    (every_export_replays_the_actual_source_inputs quantity).2.2.1.trans
      (congrArg (StageTrace.records (point quantity)) (every_export_replays_the_actual_source_inputs quantity).2.2.2.2.symm)
  exact StageTrace.final_financial_inventory_is_the_original_record_items (point quantity) (trace quantity).stages row
    (Eq.mp (congrArg (fun records => row∈records) same) inside)

theorem the_three_real_units_are_exported_by_the_original_source :
    (trace 3).before.current.stock 1 .feedstock=0 ∧
    (trace 3).before.current.claims=retained.current.claims ∧
    (trace 3).before.remaining=retained.remaining-6 ∧
    (trace 3).rows.any (fun row => decide (row.submitted=[Upstream.contribute 3]))=true := by
  and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Export
