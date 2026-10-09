import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePrepareSourceStock

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeFunctionalNextProbe
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativePaidPositive

variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}

theorem attachment_guard_absent_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    prepareGuard receipt.nextBody.current.1 ∉ attachmentAfter parent (sourceJoint receipt.nextBody.current.1) := by
  have absent := paid_guard_absent_of_profile whole supply profile receipt repaired parent
  intro held
  rcases List.mem_append.mp held with produced | retained
  · change prepareGuard receipt.nextBody.current.1 ∈ [wrappedJoint (attachedJoint receipt.nextBody.current.1)] at produced
    simp [prepareGuard,wrappedJoint] at produced
  · have canonical : prepareGuard receipt.nextBody.current.1 ∈ NativePaidEvent.canonicalStock parent :=
      List.mem_of_mem_erase (List.mem_of_mem_erase retained)
    exact absent ((canonical_paid_stock parent).mem_iff.mpr canonical)

def afterCPProgram (frame : CPS1Recycling.Frame) : List (CPS1Deformation.Reaction frame) :=
  CPS1Deformation.Source.program frame
    (some (.molecular (.following (.reference (.joint (attachedJoint frame)))))) pendingTail

theorem after_cp_cut_exact
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    afterCPExecution parent (sourceJoint receipt.nextBody.current.1) =
      ⟨[],afterCPProgram receipt.nextBody.current.1,attachmentAfter parent (sourceJoint receipt.nextBody.current.1),
        some (prepareGuard receipt.nextBody.current.1)⟩ := by
  have present : wrappedJoint (attachedJoint receipt.nextBody.current.1) ∈
      attachmentAfter parent (sourceJoint receipt.nextBody.current.1) := by
    change wrappedJoint (attachedJoint receipt.nextBody.current.1) ∈
      wrappedJoint (attachedJoint receipt.nextBody.current.1) :: _
    exact List.mem_cons_self
  have cut := fire_two_cut (CPS1Deformation.Reaction.reactants receipt.nextBody.current.1)
    (CPS1Deformation.Reaction.products receipt.nextBody.current.1) (prepareReaction receipt.nextBody.current.1)
    (attachmentAfter parent (sourceJoint receipt.nextBody.current.1)) (wrappedJoint (attachedJoint receipt.nextBody.current.1))
    (prepareGuard receipt.nextBody.current.1) (prepare_reactants _)
    present (attachment_guard_absent_of_profile whole supply profile receipt repaired parent)
  change CPS1Deformation.execute receipt.nextBody.current.1
      (prepareReaction receipt.nextBody.current.1 :: (afterCPProgram receipt.nextBody.current.1).tail)
      (attachmentAfter parent (sourceJoint receipt.nextBody.current.1)) =
    ⟨[],prepareReaction receipt.nextBody.current.1 :: (afterCPProgram receipt.nextBody.current.1).tail,
      attachmentAfter parent (sourceJoint receipt.nextBody.current.1),some (prepareGuard receipt.nextBody.current.1)⟩
  rw [CPS1Deformation.execute,Inventory.execute_cons,cut]

theorem pending_cp_only_exact
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    pendingExecution parent =
      ⟨[jointAttach (sourceJoint receipt.nextBody.current.1)],afterCPProgram receipt.nextBody.current.1,
        attachmentAfter parent (sourceJoint receipt.nextBody.current.1),some (prepareGuard receipt.nextBody.current.1)⟩ := by
  rw [repaired_pending_execution_of_profile whole supply profile receipt repaired parent,
    after_cp_cut_exact whole supply profile receipt repaired parent]

theorem next_cp_only_exact
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    nextCursor parent =
      ⟨attachmentAfter parent (sourceJoint receipt.nextBody.current.1),pendingTail,
        (oldCurrent source).stages ++
          [⟨[jointAttach (sourceJoint receipt.nextBody.current.1)],afterCPProgram receipt.nextBody.current.1,
            attachmentAfter parent (sourceJoint receipt.nextBody.current.1),some (prepareGuard receipt.nextBody.current.1)⟩],
        some (prepareGuard receipt.nextBody.current.1)⟩ := by
  rw [next_cursor_exact,pending_cp_only_exact whole supply profile receipt repaired parent,
    (repaired_native_source_of_profile whole supply profile receipt repaired current).2.1]
  rfl

end
end CPS1MaterialIncidence.NativeFunctionalNextProbe
