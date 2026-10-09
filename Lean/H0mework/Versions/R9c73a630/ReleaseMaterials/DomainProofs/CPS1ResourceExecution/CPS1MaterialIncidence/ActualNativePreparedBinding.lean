import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePreparedOriginGerm
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativePrepareNext

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePrepareBinding
noncomputable section
open CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open NativePaidEvent NativeCPContinuationProbe NativePrepareNextProbe

variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}

theorem source_generated_prepared_binding
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) (continuation : CPNativeContinuation paid) :
    Nonempty (Σ returned : NativePrepareNext paid continuation, NativeOriginGerm returned.occurrence) := by
  obtain ⟨returned⟩ := source_generated_native_prepare_next whole supply profile receipt repaired source paid continuation
  exact ⟨⟨returned,native_origin_germ returned.occurrence⟩⟩

end
end CPS1MaterialIncidence.NativePrepareBinding
