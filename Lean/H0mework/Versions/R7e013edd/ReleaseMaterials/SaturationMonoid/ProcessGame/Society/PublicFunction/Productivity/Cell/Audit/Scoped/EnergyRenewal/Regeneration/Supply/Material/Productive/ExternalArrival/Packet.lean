import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Root

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Packet
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Protocol.SymbolicAuthentication Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

structure View where
  available : ℚ
  clock : ℚ
  round : Nat
def view (current : ProviderCurrent) : View := ⟨current.stock 1 .feedstock,current.clock,current.round⟩
structure Item where
  index : Nat
  request : ProviderAction
  accepted : Bool
  debit : Flow ProviderParty ProviderGood
  credit : Flow ProviderParty ProviderGood
structure Row where
  cut : Nat
  before : View
  after : View
  remainingBefore : Nat
  remainingAfter : Nat
  submitted : List ProviderAction
  items : List Item

def project (row : StageTrace.Record (code := (Export.model 3).source.code)) : Row :=
  ⟨row.cursor.cut,view row.before.current,view row.after.current,row.before.remaining,row.after.remaining,row.submitted,
   (Upstream.law.rawItems row.before.current row.submitted).map fun item =>
     ⟨item.index,item.request,decide (Upstream.law.Valid item.before item.request),
       Upstream.law.actualDebit item.before item.request,Upstream.law.actualCredit item.before item.request⟩⟩
-- Execute the existing computable source directly; no new balance or quota is reconstructed.
def rows : List Row := (Export.trace 3).rows.map project
theorem rows_are_the_original_actual_export_rows : rows=(Export.trace 3).rows.map project := rfl

def before : ProviderCurrent := Upstream.current
def after : ProviderCurrent := (Export.trace 3).before.current
def remainingBefore : Nat := Export.retained.remaining
def remainingAfter : Nat := (Export.trace 3).before.remaining
def inputs : List LocalCommandSource.Input := (Export.trace 3).inputs
def oldCut : Nat := Export.saved.cut
def nextCut : Nat := (Export.trace 3).cursor.cut

theorem before_exact : before=Export.retained.current := Upstream.exact_occurrence
theorem after_exact : after=(Export.trace 3).before.current := rfl
theorem inputs_exact : inputs=(Export.trace 3).inputs := rfl
theorem real_source_is_exhausted_without_refilling_its_execution_budget :
    before.stock 1 .feedstock=3 ∧ after.stock 1 .feedstock=0 ∧
    remainingBefore=26 ∧ remainingAfter=20 ∧ nextCut=oldCut+6 := by
  refine ⟨Upstream.actually_produced.1,Export.the_three_real_units_are_exported_by_the_original_source.1,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · source_refl

/-- The phase selects a full actual source state, including archives, windows and lineage rows. -/
noncomputable def full (spent : Bool) := if spent then Root.after else Root.initial
noncomputable def physical (spent : Bool) := FreshSigningReplay.physical (full spent).actual

theorem physical_is_the_complete_actual_source (spent : Bool) : physical spent=
    if spent then ⟨Export.model 3,(Export.trace 3).cursor⟩ else ⟨Export.parent,Export.saved⟩ := by
  cases spent
  · exact Root.initial_is_the_complete_original_occurrence
  · exact Root.after_is_the_complete_actual_export_occurrence

def current (spent : Bool) : ProviderCurrent := if spent then after else before

theorem current_is_its_complete_source_occurrence (spent : Bool) :
    current spent=(EventStep.seed (physical spent).2).current := by
  cases spent
  · exact before_exact.trans (SourceContinuationTrace.current_from_the_same_complete_occurrence
      Export.parent Export.saved Root.initial.actual Export.retained
      Root.initial_is_the_complete_original_occurrence Export.retained_is_the_complete_original_seed).symm
  · exact after_exact.trans (SourceContinuationTrace.current_from_the_same_complete_occurrence
      (Export.model 3) (Export.trace 3).cursor Root.after.actual (Export.trace 3).before
      Root.after_is_the_complete_actual_export_occurrence (Export.every_export_replays_the_actual_source_inputs 3).2.1).symm

theorem original_financial_inventory_is_retained (ordinal : Nat) (bounded : ordinal≤EventStep.boundary Export.saved) :
    Native.Coupling.Match Export.parent.source.code Export.saved.source.input
      (EventHistory.execute (Export.point 3) (Export.trace 3).stages).source.input
      (Financial.accountAt Export.saved.source.input ordinal)
      (Financial.accountAt (EventHistory.execute (Export.point 3) (Export.trace 3).stages).source.input ordinal) :=
  Export.every_export_keeps_the_complete_original_financial_prefix 3 ordinal bounded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Packet
