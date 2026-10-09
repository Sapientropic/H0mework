import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.PaidPositiveHead
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.RepairCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedCursor
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Next

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1MaterialIncidence.NativePaidPositive
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent

variable {frame : CPS1Recycling.Frame}

def pendingTail : List CPS1Deformation.Source.RawAction :=
  [.old (.old (.old (.old .prepare))),.old .adopt,.adopt]

def SourceReady (point : SourcePoint) : Prop :=
  ∃ tail, point.2.native.current.old.current.stock = wrappedJoint (sourceJoint point.1) :: tail ∧
    point.2.native.current.old.current.pending = deformedAttach :: pendingTail ∧
    point.2.native.current.old.current.cut = some (deformedCP point.1) ∧
    point.2.native.current.old.current.stock.filterMap Classical.ownedDeformed? = [initialOwner point.1] ∧
    LiveStock point.2 = point.2.native.current.old.current.stock.map CPS1ReactiveField.LiveMaterial.old

theorem returned_source_ready {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (complete : event.physicalEvent.seed.translation.native.missing = none) :
    SourceReady ⟨event.physicalEvent.seed.translation.generatedFrame,event.reached⟩ := by
  obtain ⟨tail,head,pending,cut,_absent⟩ := physical_deformed_source event.physicalEvent complete
  have owned := physical_deformed_owned event.physicalEvent complete
  have oldEntry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    (CPS1BiologicalUpdate.entryCursor value).native.current.old) event.physicalEvent.actualEntry
  have initial := congrArg (fun value => value.old)
    (initial_entry_current event.physicalEvent.deformation noPhysicalSupply.actions noPhysicalSupply.feed noPhysicalSupply.rows)
  have actualOld : event.reached.native.current.old = event.physicalEvent.deformation :=
    (reached_old_source event.outcome).trans (oldEntry.trans initial)
  have entry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    CPS1ReactiveField.liveStock (CPS1BiologicalUpdate.entryCursor value).native.current) event.physicalEvent.actualEntry
  dsimp only [noPhysicalSupply] at entry
  rw [initial_entry_current,current_stock_of_no_deformed event.physicalEvent.deformation owned.2] at entry
  have reached := reached_live_stock event.outcome
  rw [entry] at reached
  refine ⟨tail,?_,?_,?_,?_,?_⟩
  · rw [actualOld]
    exact head
  · rw [actualOld]
    exact pending
  · rw [actualOld]
    exact cut
  · rw [actualOld]
    exact owned.1
  · rw [actualOld]
    exact reached

variable {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def CPConsumed {source : Common before step raw} {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) : Prop :=
  match paid.pending with | .cpConsumed .. => True | .otherPending .. => False

def afterCPExecution {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (joint : CPS1EnzymeBath.Joint.State frame) : CPS1Deformation.Execution frame :=
  CPS1Deformation.execute frame
    (CPS1Deformation.Source.program frame
      (some (.molecular (.following (.reference (.joint (CPS1EnzymeBath.Joint.attach frame joint .carbamoylPhosphate)))))) pendingTail)
    (attachmentAfter parent joint)

end
end CPS1MaterialIncidence.NativePaidPositive
