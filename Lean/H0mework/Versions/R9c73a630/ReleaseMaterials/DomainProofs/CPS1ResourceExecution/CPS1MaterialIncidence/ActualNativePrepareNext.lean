import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePrepareExecution
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePrepareSourceCut

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePrepareNextProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open CPS1BiologicalUpdate CPS1LiveEditing NativePaidEvent NativePaidPositive NativeAmmoniaDynamics
open NativeCPContinuationProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}

structure NativePrepareNext (paid : SourceGeneratedPaidReturn source current)
    (continuation : CPNativeContinuation paid) where
  occurrence : NativeOccurrence paid continuation
  requested : (NativePaidEvent.nextCursor paid.parent).pending = pendingTail
  execution : Execution occurrence
  executionActual : execution = runPrepare (startCursor occurrence (NativePaidEvent.nextCursor paid.parent))
  next : Cursor occurrence
  nextActual : next = advancePrepare (startCursor occurrence (NativePaidEvent.nextCursor paid.parent))

namespace NativePrepareNext
variable (returned : NativePrepareNext paid continuation)

/-- The old germ/source remains the exact provenance restriction. Native
preparation is recorded in `next`, without mutating that germ's old centres. -/
def sourceRestriction (_returned : NativePrepareNext paid continuation) : CPS1ReactiveNuclear.SourceCursor frame := cursor

def prepared : NativePrepared returned.occurrence := native_prepared returned.occurrence

theorem execution_exact : returned.execution =
    ⟨[.prepare],[],preparedStock returned.occurrence,none⟩ := by
  rw [returned.executionActual]
  apply execution_requested
  rw [returned.requested]
  rfl

theorem next_exact : returned.next =
    ⟨preparedStock returned.occurrence,[.old .adopt,.adopt],
      (NativePaidEvent.nextCursor paid.parent).stages.map LedgerStage.retained ++ [.native returned.execution],none⟩ := by
  rw [returned.nextActual,advance_requested]
  · rw [returned.requested,returned.execution_exact]
    rfl
  · rw [returned.requested]
    rfl

theorem prepared_present : (Species.prepared : Species returned.occurrence) ∈ returned.next.stock := by
  rw [returned.next_exact]
  exact List.mem_cons_self

theorem prepared_face : Species.preparedFace (Species.prepared : Species returned.occurrence) = some returned.prepared := rfl

theorem remaining_exact : returned.next.stock.filterMap Species.live? = current.remaining := by
  rw [returned.next_exact]
  exact prepared_remaining _

theorem single_mother : (returned.next.stock.filter Species.mother?).length = 1 := by
  rw [returned.next_exact]
  exact prepared_single_mother _

theorem physical_exact : returned.next.stock.filterMap Species.physical = [continuation.after] := by
  rw [returned.next_exact]
  exact prepared_physical _

theorem no_replay : Inventory.fire reactants products (Event.prepare : Event returned.occurrence) returned.next.stock =
    .error Species.evolved := by
  rw [returned.next_exact]
  exact prepare_no_repeat _

theorem full_fields : returned.occurrence.physical = continuation.after ∧
    returned.occurrence.physical.rawC = continuation.after.rawC ∧
    returned.occurrence.physical.pose = continuation.after.pose ∧
    returned.occurrence.physical.occupied = continuation.after.occupied ∧
    returned.occurrence.physical.reserve = continuation.after.reserve ∧
    returned.occurrence.physical.elapsed = continuation.after.elapsed ∧
    returned.occurrence.physical.index = continuation.after.index :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem full_whole : returned.occurrence.charged = paid.parent.products.serial.after ∧
    returned.occurrence.charged.spent = paid.parent.products.serial.after.spent ∧
    returned.occurrence.remaining = current.remaining := returned.occurrence.full_inventory

theorem account : returned.occurrence.physical.energy + returned.occurrence.physical.reserve =
    paid.physical.energy + paid.physical.reserve := returned.occurrence.full_account

theorem electron_number : Matrix.trace (returned.occurrence.physical.occupied *
    returned.occurrence.physical.occupied.conjTranspose) = (electronCount source.nodes : ℂ) :=
  returned.occurrence.full_electrons

end NativePrepareNext

section Source
variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}

theorem source_generated_native_prepare_next
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) (continuation : CPNativeContinuation paid) :
    Nonempty (NativePrepareNext paid continuation) := by
  let occurrence := source_native_occurrence whole supply profile receipt repaired source paid continuation
  have actual := NativeFunctionalNextProbe.next_cp_only_exact whole supply profile receipt repaired paid.parent
  have requested : (NativePaidEvent.nextCursor paid.parent).pending = pendingTail :=
    congrArg CPS1Deformation.Source.Cursor.pending actual
  exact ⟨⟨occurrence,requested,runPrepare (startCursor occurrence (NativePaidEvent.nextCursor paid.parent)),rfl,
    advancePrepare (startCursor occurrence (NativePaidEvent.nextCursor paid.parent)),rfl⟩⟩

end Source
end
end CPS1MaterialIncidence.NativePrepareNextProbe
