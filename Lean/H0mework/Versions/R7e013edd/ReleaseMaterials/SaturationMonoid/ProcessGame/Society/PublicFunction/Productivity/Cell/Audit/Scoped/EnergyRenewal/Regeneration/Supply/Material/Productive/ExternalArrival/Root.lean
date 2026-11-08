import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Original
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Export

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Root
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Protocol.SymbolicAuthentication Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
open SourceCreditSource (exchange)
open private RenewableArchiveSource.State.mk in RenewableArchiveSource.initial
open private JointReceptionSource.State.mk in JointReceptionSource.initial
noncomputable section

noncomputable abbrev initial := Original.initial

theorem initial_is_the_complete_original_occurrence :
    FreshSigningReplay.physical initial.actual=⟨Export.parent,Export.saved⟩ :=
  ProviderMaterialConsumer.every_material_request_keeps_the_complete_actual_joint_occurrence 3 true true

variable (model : CompletionReviewHandoff.Model) (saved : Cursor model.source.code)
def catalogue (quantity : ℚ) : CatalogueHandoffSource.Catalogue model.source.code :=
  ⟨if 0<quantity ∧ model.source.code.law.Valid (EventStep.seed saved).current (Upstream.contribute quantity)
    then [Upstream.contribute quantity] else [],1,[],0,
    (List.finRange model.source.code.sites).map Event.activate⟩
def point (quantity : ℚ) := CatalogueHandoffSource.cursor model.source.code (catalogue model saved quantity) saved
def modelAfter (quantity : ℚ) : CompletionReviewHandoff.Model :=
  ⟨model.base,model.scope,(point model saved quantity).source,model.law_exact,model.task_exact⟩
def output (quantity : ℚ) : FreshSigningReplay.Physical
    (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
    (Technology := Bool) (Instrument := Unit) := ⟨modelAfter model saved quantity,point model saved quantity⟩

variable {root : RenewableCodeLineage.Emitter (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
  (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)}
def register (state : JointReceptionSource.State root) (quantity : ℚ) : JointReceptionSource.State root :=
  let extra:=catalogue state.actual.model state.actual.point quantity
  JointReceptionSource.State.mk
    (RenewableArchiveSource.State.mk (modelAfter state.actual.model state.actual.point quantity)
      (point state.actual.model state.actual.point quantity) state.actual.archive state.actual.windows)
    (.extended state.lineage extra) state.rows

theorem registration_keeps_the_actual_physical_source (state : JointReceptionSource.State root)
    (physical : FreshSigningReplay.physical state.actual=⟨model,saved⟩) (quantity : ℚ) :
    FreshSigningReplay.physical (register state quantity).actual=output model saved quantity := by
  cases state
  rename_i actual lineage rows
  cases actual
  cases physical
  rfl

theorem registration_keeps_all_archives_windows_and_rows (state : JointReceptionSource.State root) (quantity : ℚ) :
    (register state quantity).actual.archive=state.actual.archive ∧
    (register state quantity).actual.windows=state.actual.windows ∧ (register state quantity).rows=state.rows := ⟨rfl,rfl,rfl⟩

theorem original_catalogue : catalogue Export.parent Export.saved 3=Export.catalogue 3 := by
  have same : (EventStep.seed Export.saved).current=Upstream.current :=
    (congrArg Feedback.State.current Export.retained_is_the_complete_original_seed).symm.trans Upstream.exact_occurrence.symm
  unfold catalogue Export.catalogue
  congr 1
  exact congrArg (fun current : ProviderCurrent =>
    if (0:ℚ)<3 ∧ Export.parent.source.code.law.Valid current (Upstream.contribute 3) then [Upstream.contribute 3] else []) same

theorem registered_is_the_same_export_source :
    FreshSigningReplay.physical (register initial 3).actual=⟨Export.model 3,Export.point 3⟩ :=
  (registration_keeps_the_actual_physical_source Export.parent Export.saved initial
    initial_is_the_complete_original_occurrence 3).trans (by
      unfold output modelAfter point Export.model Export.point
      rw [original_catalogue])

noncomputable def after : JointReceptionSource.State ConcreteProductiveSource.bound.source.code := JointReceptionSource.advance contract (register initial 3) (RenewableArchiveSource.Command.execute (Export.trace 3).inputs)
set_option backward.isDefEq.respectTransparency true in
theorem after_is_the_complete_actual_export_occurrence :
    FreshSigningReplay.physical after.actual=⟨Export.model 3,(Export.trace 3).cursor⟩ := by
  unfold after
  exact SourceCreditHandoff.controlled_execution_keeps_the_entire_actual_occurrence
    (Export.model 3) (Export.point 3) (Export.initial 3) contract (register initial 3)
    registered_is_the_same_export_source (Export.registration_keeps_the_entire_actual_seed 3) (Export.control 3) 6

-- Archive/window/row preservation and native continuation are consumed from
-- SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows and
-- JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next.

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Root
