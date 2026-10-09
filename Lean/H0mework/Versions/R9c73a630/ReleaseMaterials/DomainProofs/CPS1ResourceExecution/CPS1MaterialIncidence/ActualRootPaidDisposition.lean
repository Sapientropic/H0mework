import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.PaidPositiveGenericSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1MaterialIncidence.NativePaidPositive
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent

variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}

theorem repaired_source_ready_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt) : SourceReady receipt.nextBody.current := by
  rcases supply with ⟨nextWater,translation,nextPath,recycling,recycleFeed,nextPhysical,nextDepth⟩
  rcases profile with ⟨rfl,rfl,rfl⟩
  obtain ⟨first,update,current⟩ := repair_return_current whole _ receipt repaired
  rw [current]
  exact returned_source_ready update.returned update.nextNative

theorem repaired_native_source_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} (current : NativeCurrent source) :
    chainSpecies current = wrappedJoint (sourceJoint receipt.nextBody.current.1) ∧
      (oldCurrent source).pending = deformedAttach :: pendingTail ∧
      (oldCurrent source).cut = some (deformedCP receipt.nextBody.current.1) := by
  obtain ⟨tail,head,pending,cut,unique,live⟩ := repaired_source_ready_of_profile whole supply profile receipt repaired
  let material := (LiveStock receipt.nextBody.current.2).get current.chainSlot
  have held : material ∈ receipt.nextBody.current.2.native.current.old.current.stock.map CPS1ReactiveField.LiveMaterial.old :=
    live ▸ List.get_mem _ _
  obtain ⟨species,speciesHeld,identity⟩ := List.mem_map.mp held
  have paid := current.chainSlotActual
  change Classical.ownedLive? material = some before.packet.source.owned at paid
  rw [← identity] at paid
  have tailEmpty : tail.filterMap Classical.ownedDeformed? = [] := by
    rw [head,List.filterMap_cons] at unique
    change initialOwner receipt.nextBody.current.1 :: tail.filterMap Classical.ownedDeformed? = [initialOwner receipt.nextBody.current.1] at unique
    exact (List.cons.inj unique).2
  have sourceHead : species = wrappedJoint (sourceJoint receipt.nextBody.current.1) := by
    have member : species ∈ wrappedJoint (sourceJoint receipt.nextBody.current.1) :: tail := head ▸ speciesHeld
    rcases List.mem_cons.mp member with atHead | retained
    · exact atHead
    · have impossible : before.packet.source.owned ∈ tail.filterMap Classical.ownedDeformed? :=
        List.mem_filterMap.mpr ⟨species,retained,paid⟩
      rw [tailEmpty] at impossible
      cases impossible
  refine ⟨?_,pending,cut⟩
  change liveSpecies material = _
  rw [← identity,sourceHead]
  rfl


theorem repaired_pending_execution_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    pendingExecution parent =
      {afterCPExecution parent (sourceJoint receipt.nextBody.current.1) with
        fired := jointAttach (sourceJoint receipt.nextBody.current.1) ::
          (afterCPExecution parent (sourceJoint receipt.nextBody.current.1)).fired} := by
  obtain ⟨selected,requested,_cut⟩ := repaired_native_source_of_profile whole supply profile receipt repaired current
  have held : CPS1Deformation.Source.heldCarrier receipt.nextBody.current.1 (NativePaidEvent.canonicalStock parent) =
      some (.molecular (.following (.reference (.joint (sourceJoint receipt.nextBody.current.1))))) := by
    rw [NativePaidEvent.canonicalStock,selected]
    rfl
  have program : CPS1Deformation.Source.program receipt.nextBody.current.1
      (CPS1Deformation.Source.heldCarrier receipt.nextBody.current.1 (NativePaidEvent.canonicalStock parent)) (oldCurrent source).pending =
      jointAttach (sourceJoint receipt.nextBody.current.1) :: CPS1Deformation.Source.program receipt.nextBody.current.1
        (some (.molecular (.following (.reference (.joint (CPS1EnzymeBath.Joint.attach receipt.nextBody.current.1
          (sourceJoint receipt.nextBody.current.1) .carbamoylPhosphate)))))) pendingTail := by
    rw [requested,held]
    rfl
  rw [pendingExecution,program,CPS1Deformation.execute,CPS1ResourceExecution.Inventory.execute_cons,
    attachment_actual parent _ selected]
  rfl

theorem repaired_next_cursor_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    nextCursor parent =
      ⟨(afterCPExecution parent (sourceJoint receipt.nextBody.current.1)).stock,
        pendingTail.drop (afterCPExecution parent (sourceJoint receipt.nextBody.current.1)).fired.length,
        (oldCurrent source).stages ++
          [{afterCPExecution parent (sourceJoint receipt.nextBody.current.1) with
            fired := jointAttach (sourceJoint receipt.nextBody.current.1) ::
              (afterCPExecution parent (sourceJoint receipt.nextBody.current.1)).fired}],
        (afterCPExecution parent (sourceJoint receipt.nextBody.current.1)).missing⟩ := by
  rw [next_cursor_exact,repaired_pending_execution_of_profile whole supply profile receipt repaired parent,
    (repaired_native_source_of_profile whole supply profile receipt repaired current).2.1]
  simp only [List.length_cons,List.drop_succ_cons]

theorem source_generated_paid_positive_of_repair
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) (current : NativeCurrent source) :
    ∃ paid : SourceGeneratedPaidReturn source current, CPConsumed paid ∧
      pendingExecution paid.parent =
        {afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1) with
          fired := jointAttach (sourceJoint receipt.nextBody.current.1) ::
            (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).fired} ∧
      nextCursor paid.parent =
        ⟨(afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).stock,
          pendingTail.drop (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).fired.length,
          (oldCurrent source).stages ++
            [{afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1) with
              fired := jointAttach (sourceJoint receipt.nextBody.current.1) ::
                (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).fired}],
          (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).missing⟩ := by
  obtain ⟨paid⟩ := source_generated_paid_return source current
  refine ⟨paid,?_,repaired_pending_execution_of_profile whole supply profile receipt repaired paid.parent,
    repaired_next_cursor_of_profile whole supply profile receipt repaired paid.parent⟩
  unfold CPConsumed
  cases pending : paid.pending with
  | cpConsumed joint rest selected requested actual fired => exact True.intro
  | otherPending failed =>
    apply failed
    obtain ⟨selected,requested,_cut⟩ := repaired_native_source_of_profile whole supply profile receipt repaired current
    exact ⟨sourceJoint receipt.nextBody.current.1,pendingTail,selected,requested⟩

theorem returned_cp_absent {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (complete : event.physicalEvent.seed.translation.native.missing = none) :
    deformedCP event.physicalEvent.seed.translation.generatedFrame ∉ event.reached.native.current.old.current.stock := by
  obtain ⟨_tail,_head,_pending,_cut,absent⟩ := physical_deformed_source event.physicalEvent complete
  have oldEntry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    (CPS1BiologicalUpdate.entryCursor value).native.current.old) event.physicalEvent.actualEntry
  have initial := congrArg (fun value => value.old)
    (initial_entry_current event.physicalEvent.deformation noPhysicalSupply.actions noPhysicalSupply.feed noPhysicalSupply.rows)
  have actualOld : event.reached.native.current.old = event.physicalEvent.deformation :=
    (reached_old_source event.outcome).trans (oldEntry.trans initial)
  rw [actualOld]
  exact absent

theorem repaired_cp_absent_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt) :
    deformedCP receipt.nextBody.current.1 ∉ receipt.nextBody.current.2.native.current.old.current.stock := by
  rcases supply with ⟨nextWater,translation,nextPath,recycling,recycleFeed,nextPhysical,nextDepth⟩
  rcases profile with ⟨rfl,rfl,rfl⟩
  obtain ⟨first,update,current⟩ := repair_return_current whole _ receipt repaired
  rw [current]
  exact returned_cp_absent update.returned update.nextNative

inductive RootPaidDisposition
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) (current : NativeCurrent source) where
  | positive
      (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
      (absent : deformedCP receipt.nextBody.current.1 ∉ (oldCurrent source).stock)
      (paid : SourceGeneratedPaidReturn source current) (consumed : CPConsumed paid)
      (execution : pendingExecution paid.parent =
        {afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1) with
          fired := jointAttach (sourceJoint receipt.nextBody.current.1) ::
            (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).fired})
      (next : nextCursor paid.parent =
        ⟨(afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).stock,
          pendingTail.drop (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).fired.length,
          (oldCurrent source).stages ++
            [{afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1) with
              fired := jointAttach (sourceJoint receipt.nextBody.current.1) ::
                (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).fired}],
          (afterCPExecution paid.parent (sourceJoint receipt.nextBody.current.1)).missing⟩)
  | otherProfile
      (actual : ¬ (supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply))
      (paid : SourceGeneratedPaidReturn source current)

theorem source_generated_paid_disposition_of_repair
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) (current : NativeCurrent source) : Nonempty (RootPaidDisposition whole supply receipt repaired source current) := by
  classical
  by_cases profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply
  · obtain ⟨paid,consumed,execution,next⟩ :=
      source_generated_paid_positive_of_repair whole supply profile receipt repaired source current
    exact ⟨.positive profile (repaired_cp_absent_of_profile whole supply profile receipt repaired) paid consumed execution next⟩
  · obtain ⟨paid⟩ := source_generated_paid_return source current
    exact ⟨.otherProfile profile paid⟩

end
end CPS1MaterialIncidence.NativePaidPositive
