import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePrepareSourceGuard

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1MaterialIncidence.NativeFunctionalNextProbe
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativePaidPositive
variable {frame : CPS1Recycling.Frame}

theorem physical_guard_absent {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (event : PhysicalEvent before water raw path [] [] noPhysicalSupply)
    (complete : event.seed.translation.native.missing = none) :
    prepareGuard event.seed.translation.generatedFrame ∉ event.deformation.current.stock := by
  obtain ⟨bathTail,bathHead,bathPending,bathAbsent,_⟩ := physical_bath_head event complete
  let joint := sourceJoint event.seed.translation.generatedFrame
  have electronicSource := event.electronicSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at electronicSource
  have electronicFacts := electronic_source_stalls event.bath joint bathTail [] bathHead bathPending bathAbsent
  have electronicStock : event.electronic.current.stock = event.bath.current.stock.map
      (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame) := by
    rw [electronicSource]
    exact electronicFacts.1
  have electronicHead : event.electronic.current.stock = .retained (.joint joint) ::
      bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame) := by
    rw [electronicStock,bathHead,List.map_cons]
    rfl
  have electronicPending : event.electronic.current.pending = electronicAttach :: [.prepare] := by
    rw [electronicSource,electronicFacts.2.1,bathPending]
    rfl
  have electronicAbsent : electronicCP event.seed.translation.generatedFrame ∉ event.electronic.current.stock := by
    rw [electronicStock]
    exact electronic_lift_cp_absent _ bathAbsent
  have nuclearSource := event.nuclearSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at nuclearSource
  have nuclearFacts := nuclear_source_stalls event.electronic joint (bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)) ([.prepare])
    electronicHead electronicPending electronicAbsent
  have nuclearStock : event.nuclear.current.stock = event.electronic.current.stock.map CPS1QuantumNuclear.Species.retained := by
    rw [nuclearSource]
    exact nuclearFacts.1
  have nuclearHead : event.nuclear.current.stock = (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species event.seed.translation.generatedFrame) ::
      (bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained := by
    rw [nuclearStock,electronicHead,List.map_cons]
  have nuclearPending : event.nuclear.current.pending = nuclearAttach :: [.old .prepare] := by
    rw [nuclearSource,nuclearFacts.2.1,electronicPending]
    rfl
  have nuclearAbsent : nuclearCP event.seed.translation.generatedFrame ∉ event.nuclear.current.stock := by
    rw [nuclearStock]
    exact mapped_absent CPS1QuantumNuclear.Species.retained (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same) _ _ electronicAbsent
  have followingSource := event.followingSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at followingSource
  have followingFacts := following_source_stalls event.nuclear joint ((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained) ([.old .prepare])
    nuclearHead nuclearPending nuclearAbsent
  have followingStock : event.following.current.stock = event.nuclear.current.stock.map CPS1Following.Species.retained := by
    rw [followingSource]
    exact followingFacts.1
  have followingHead : event.following.current.stock = (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species event.seed.translation.generatedFrame) ::
      ((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained := by
    rw [followingStock,nuclearHead,List.map_cons]
  have followingPending : event.following.current.pending = followingAttach :: [.old (.old .prepare)] := by
    rw [followingSource,followingFacts.2.1,nuclearPending]
    rfl
  have followingAbsent : followingCP event.seed.translation.generatedFrame ∉ event.following.current.stock := by
    rw [followingStock]
    exact mapped_absent CPS1Following.Species.retained (fun _ _ same => CPS1Following.Species.retained.inj same) _ _ nuclearAbsent
  have molecularSource := event.molecularSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at molecularSource
  have molecularFacts := molecular_source_stalls event.following joint (((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained) ([.old (.old .prepare)])
    followingHead followingPending followingAbsent
  have molecularStock : event.molecular.current.stock = event.following.current.stock.map CPS1MolecularFrame.Species.retained := by
    rw [molecularSource]
    exact molecularFacts.1
  have molecularHead : event.molecular.current.stock = (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species event.seed.translation.generatedFrame) ::
      (((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained).map CPS1MolecularFrame.Species.retained := by
    rw [molecularStock,followingHead,List.map_cons]
  have molecularPending : event.molecular.current.pending = molecularAttach :: [.old (.old (.old .prepare)),.adopt] := by
    rw [molecularSource,molecularFacts.2.1,followingPending]
    rfl
  have molecularAbsent : molecularCP event.seed.translation.generatedFrame ∉ event.molecular.current.stock := by
    rw [molecularStock]
    exact mapped_absent CPS1MolecularFrame.Species.retained (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same) _ _ followingAbsent
  have deformedSource := event.deformationSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at deformedSource
  have deformedFacts := deformed_source_stalls event.molecular joint ((((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained).map CPS1MolecularFrame.Species.retained) ([.old (.old (.old .prepare)),.adopt])
    molecularHead molecularPending molecularAbsent
  have deformedStock : event.deformation.current.stock = event.molecular.current.stock.map CPS1Deformation.Species.retained := by
    rw [deformedSource]
    exact deformedFacts.1
  rw [deformedStock,molecularStock,followingStock,nuclearStock,electronicStock]
  unfold prepareGuard
  apply mapped_absent CPS1Deformation.Species.retained (fun _ _ same => CPS1Deformation.Species.retained.inj same)
  apply mapped_absent CPS1MolecularFrame.Species.retained (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same)
  apply mapped_absent CPS1Following.Species.retained (fun _ _ same => CPS1Following.Species.retained.inj same)
  apply mapped_absent CPS1QuantumNuclear.Species.retained (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same)
  intro held
  obtain ⟨item,_member,same⟩ := List.mem_map.mp held
  cases item <;> simp [CPS1ElectronicSource.Source.liftMaterial] at same

theorem returned_guard_absent {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (complete : event.physicalEvent.seed.translation.native.missing = none) :
    prepareGuard event.physicalEvent.seed.translation.generatedFrame ∉ event.reached.native.current.old.current.stock := by
  have oldEntry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    (CPS1BiologicalUpdate.entryCursor value).native.current.old) event.physicalEvent.actualEntry
  have initial := congrArg (fun value => value.old)
    (initial_entry_current event.physicalEvent.deformation noPhysicalSupply.actions noPhysicalSupply.feed noPhysicalSupply.rows)
  have actualOld : event.reached.native.current.old = event.physicalEvent.deformation :=
    (reached_old_source event.outcome).trans (oldEntry.trans initial)
  rw [actualOld]
  exact physical_guard_absent event.physicalEvent complete

variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}

theorem repaired_guard_absent_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt) :
    prepareGuard receipt.nextBody.current.1 ∉ receipt.nextBody.current.2.native.current.old.current.stock := by
  rcases supply with ⟨nextWater,translation,nextPath,recycling,recycleFeed,nextPhysical,nextDepth⟩
  rcases profile with ⟨rfl,rfl,rfl⟩
  obtain ⟨first,update,current⟩ := repair_return_current whole _ receipt repaired
  rw [current]
  exact returned_guard_absent update.returned update.nextNative

theorem lift_no_prepare_guard {frame : CPS1Recycling.Frame} (species : CPS1LocalChemicalExecution.Species frame) :
    liftLocalSpecies species ≠ prepareGuard frame := by
  intro same
  cases same

theorem paid_guard_absent_of_profile
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    {source : Common before step raw} {current : NativeCurrent source} (parent : ParentSource source current) :
    prepareGuard receipt.nextBody.current.1 ∉ paidStock parent := by
  classical
  have oldAbsent := repaired_guard_absent_of_profile whole supply profile receipt repaired
  have sourceAbsent : prepareGuard receipt.nextBody.current.1 ∉ sourceStock source current := by
    intro held
    rcases List.mem_append.mp held with inherited | fuel
    · rcases List.mem_append.mp inherited with old | reactive
      · exact oldAbsent old
      · obtain ⟨item,_member,same⟩ := List.mem_map.mp reactive
        exact lift_no_prepare_guard _ same
    · obtain ⟨entry,_member,same⟩ := List.mem_map.mp fuel
      exact lift_no_prepare_guard _ same
  have parentAbsent : prepareGuard receipt.nextBody.current.1 ∉
      (parentStock parent).map (fun item => readSpecies item.species) := by
    intro held
    have paid := parent_stock_source parent
    rw [forget_read] at paid
    exact sourceAbsent (paid.mem_iff.mp held)
  have remainingAbsent : prepareGuard receipt.nextBody.current.1 ∉
      (remainingParents parent).map (fun item => readSpecies item.species) := by
    intro held
    obtain ⟨item,held,same⟩ := List.mem_map.mp held
    have prior : item ∈ parentStock parent :=
      List.mem_of_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase held)))
    exact parentAbsent (List.mem_map.mpr ⟨item,prior,same⟩)
  rw [paidStock,read_execution_stock,forget_read,paid_execution_exact,third_after]
  simpa [secondADP,carbamoylPhosphate,phosphate,proton,firstADP,
    CPS1AddressedChemicalReaction.Material.species,readSpecies,liftLocalSpecies,prepareGuard] using remainingAbsent

end
end CPS1MaterialIncidence.NativeFunctionalNextProbe
