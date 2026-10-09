import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaTransport
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.CurrentGenome

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1EnzymeBath.BathAccounting
variable {frame : CPS1Recycling.Frame}

theorem inventory_count_preserved_at {S R : Type} [DecidableEq S]
    (reactants products : R → List S) (program : List R) (stock : List S) (species : S)
    (untouched : ∀ reaction ∈ program, (reactants reaction).count species = 0 ∧
      (products reaction).count species = 0) :
    (Inventory.execute reactants products program stock).stock.count species = stock.count species := by
  induction program generalizing stock with
  | nil => rfl
  | cons reaction rest ih =>
    rw [Inventory.execute_cons]
    cases action : Inventory.fire reactants products reaction stock with
    | error missing => rfl
    | ok next =>
      have balance := Inventory.fire_balance reactants products reaction stock next action species
      rw [(untouched reaction List.mem_cons_self).1,(untouched reaction List.mem_cons_self).2,Nat.add_zero,Nat.add_zero] at balance
      exact (ih next (fun other held => untouched other (List.mem_cons_of_mem _ held))).trans balance.symm

theorem count_map_only {S T : Type} [DecidableEq S] [DecidableEq T]
    (lift : S → T) (old : S) (new : T) (same : ∀ item, lift item = new ↔ item = old) (stock : List S) :
    (stock.map lift).count new = stock.count old := by
  induction stock with
  | nil => rfl
  | cons item rest ih => simp [List.count_cons,same,ih]

def reinitiatedNH3 (f : CPS1Recycling.Frame) := CPS1StockRecursion.Dictionary.old f .ammonia

theorem captured_source_ammonia (previous : CPS1StockRecursion.Source.Observation frame) :
    (CPS1LocalChemicalExecution.Source.fromCurrent frame previous).current.stock.count (localNH3 frame) =
      previous.current.stock.count (reinitiatedNH3 frame) := by
  have preserved := inventory_count_preserved_at
    (CPS1LocalChemicalExecution.Reaction.reactants frame) (CPS1LocalChemicalExecution.Reaction.products frame)
    [.capture] (previous.current.stock.map CPS1LocalChemicalExecution.Species.retained) (localNH3 frame)
    (by intro reaction held; simp only [List.mem_singleton] at held; subst reaction
        simp [CPS1LocalChemicalExecution.Reaction.reactants,CPS1LocalChemicalExecution.Reaction.products,
          localNH3,CPS1LocalChemicalExecution.molecule,CPS1LocalChemicalExecution.Actual.species,CPS1StockRecursion.Dictionary.old])
  change (CPS1LocalChemicalExecution.Source.fromCurrent frame previous).current.stock.count (localNH3 frame) = _ at preserved
  rw [preserved]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1LocalChemicalExecution.Species.retained.inj same) _

theorem seed_source_ammonia {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] []) :
    seed.atomic.current.stock.count (atomizedNH3 seed.translation.generatedFrame) = seed.translation.native.stock.count .ammonia := by
  have observed := congrArg (fun value : CPS1StockRecursion.Source.Observation seed.translation.generatedFrame =>
    value.current.stock.count (reinitiatedNH3 seed.translation.generatedFrame)) seed.observedSource
  change seed.observed.current.stock.count (reinitiatedNH3 seed.translation.generatedFrame) =
    (seed.recycled.stock.map CPS1Reinitiation.Species.retained).count (reinitiatedNH3 seed.translation.generatedFrame) at observed
  dsimp only [reinitiatedNH3,CPS1StockRecursion.Dictionary.old] at observed
  rw [List.count_map_of_injective _ _ (fun _ _ same => CPS1Reinitiation.Species.retained.inj same)] at observed
  have captured := congrArg (fun value : CPS1LocalChemicalExecution.Source.Occurrence seed.translation.generatedFrame =>
    value.current.stock.count (localNH3 seed.translation.generatedFrame)) seed.actualCapture
  rw [captured_source_ammonia] at captured
  have joined := congrArg (fun value : CPS1LocalChemicalExecution.Source.Cursor seed.translation.generatedFrame =>
    value.stock.count (localNH3 seed.translation.generatedFrame)) seed.noReload
  have atomized := congrArg (fun value : CPS1AtomicSource.Current.Occurrence seed.translation.generatedFrame =>
    value.current.stock.count (atomizedNH3 seed.translation.generatedFrame)) seed.actualAtomic
  rw [atomization_ammonia_count] at atomized
  have recycled := congrArg (fun value : CPS1Recycling.ExecutionAt seed.translation.generatedFrame =>
    value.stock.count (CPS1Recycling.Species.old .ammonia)) seed.actualRecycling
  simp only [CPS1Recycling.run,CPS1Recycling.compile,CPS1Recycling.currentStock,
    List.map_nil,List.append_nil,Inventory.execute] at recycled
  rw [List.count_map_of_injective _ _ (fun _ _ same => CPS1Recycling.Species.old.inj same)] at recycled
  have native := congrArg (fun value : CPS1Recycling.Frame => value.native.stock.count .ammonia) seed.translation.frameSource
  exact atomized.trans (joined.trans (captured.trans (observed.trans (recycled.trans native))))

theorem atomic_ammonia_preserved (program : List (CPS1AtomicDynamics.Reaction frame)) (stock : CPS1AtomicDynamics.Stock frame) :
    (CPS1AtomicDynamics.execute frame program stock).stock.count (atomicNH3 frame) = stock.count (atomicNH3 frame) :=
  execute_retained_count frame (atomizedNH3 frame) (fun _ same => by cases same) program stock

theorem atomic_source_ammonia (previous : CPS1AtomicSource.Current.Occurrence frame) :
    (CPS1AtomicDynamics.Source.resume frame (CPS1AtomicDynamics.Source.fromActual frame previous) []).current.stock.count (atomicNH3 frame) =
      previous.current.stock.count (atomizedNH3 frame) := by
  unfold CPS1AtomicDynamics.Source.resume CPS1AtomicDynamics.Source.advance CPS1AtomicDynamics.Source.fromActual CPS1AtomicDynamics.Source.start
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [atomic_ammonia_preserved,List.flatMap_nil,List.append_nil]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1AtomicDynamics.Species.retained.inj same) _

theorem bath_source_ammonia (previous : CPS1AtomicDynamics.Source.Occurrence frame) :
    (CPS1EnzymeBath.Source.resume frame (CPS1EnzymeBath.Source.fromActual frame previous) CPS1EnzymeBath.Source.generatedPartnerProgram []).current.stock.count (bathNH3 frame) =
      previous.current.stock.count (atomicNH3 frame) := by
  unfold CPS1EnzymeBath.Source.resume CPS1EnzymeBath.Source.advance CPS1EnzymeBath.Source.fromActual CPS1EnzymeBath.Source.start CPS1EnzymeBath.Source.generatedPartnerProgram CPS1EnzymeBath.Source.RawAction.material
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [bath_ammonia_preserved,List.map_nil,List.append_nil,List.flatMap_cons,List.flatMap_nil]
  exact count_map_only _ _ _ (by
    intro item
    dsimp only [bathNH3,atomicNH3,atomizedNH3]
    cases item <;> simp [CPS1EnzymeBath.Source.liftMaterial]) _

theorem electronic_source_ammonia (previous : CPS1EnzymeBath.Source.Occurrence frame) :
    (CPS1ElectronicSource.Source.resume frame (CPS1ElectronicSource.Source.fromActual frame previous) [] []).current.stock.count (electronicNH3 frame) =
      previous.current.stock.count (bathNH3 frame) := by
  unfold CPS1ElectronicSource.Source.resume CPS1ElectronicSource.Source.advance CPS1ElectronicSource.Source.fromActual CPS1ElectronicSource.Source.start
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [electronic_ammonia_preserved,List.map_nil,List.append_nil,List.flatMap_nil]
  exact count_map_only _ _ _ (by
    intro item
    dsimp only [electronicNH3,bathNH3,atomicNH3,atomizedNH3]
    cases item <;> simp [CPS1ElectronicSource.Source.liftMaterial]) _

theorem nuclear_source_ammonia (previous : CPS1ElectronicSource.Source.Occurrence frame) :
    (CPS1QuantumNuclear.Source.resume frame (CPS1QuantumNuclear.Source.fromActual frame previous) [] []).current.stock.count (nuclearNH3 frame) =
      previous.current.stock.count (electronicNH3 frame) := by
  unfold CPS1QuantumNuclear.Source.resume CPS1QuantumNuclear.Source.advance CPS1QuantumNuclear.Source.fromActual
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [nuclear_ammonia_preserved,List.map_nil,List.flatMap_nil,List.append_nil]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same) _

theorem following_source_ammonia (previous : CPS1QuantumNuclear.Source.Occurrence frame) :
    (CPS1Following.Source.resume frame (CPS1Following.Source.fromActual frame previous) [] []).current.stock.count (followingNH3 frame) =
      previous.current.stock.count (nuclearNH3 frame) := by
  unfold CPS1Following.Source.resume CPS1Following.Source.advance CPS1Following.Source.fromActual
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [following_ammonia_preserved,List.map_nil,List.flatMap_nil,List.append_nil]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1Following.Species.retained.inj same) _

theorem molecular_source_ammonia (previous : CPS1Following.Source.Occurrence frame) :
    (CPS1MolecularFrame.Source.resume frame (CPS1MolecularFrame.Source.fromActual frame previous) [] []).current.stock.count (molecularNH3 frame) =
      previous.current.stock.count (followingNH3 frame) := by
  unfold CPS1MolecularFrame.Source.resume CPS1MolecularFrame.Source.advance CPS1MolecularFrame.Source.fromActual
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [molecular_ammonia_preserved,List.map_nil,List.flatMap_nil,List.append_nil]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same) _

theorem deformed_source_ammonia (previous : CPS1MolecularFrame.Source.Occurrence frame) :
    (CPS1Deformation.Source.resume frame (CPS1Deformation.Source.fromActual frame previous) [] []).current.stock.count (deformedNH3 frame) =
      previous.current.stock.count (molecularNH3 frame) := by
  unfold CPS1Deformation.Source.resume CPS1Deformation.Source.advance CPS1Deformation.Source.fromActual
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [deformed_ammonia_preserved,List.map_nil,List.flatMap_nil,List.append_nil]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1Deformation.Species.retained.inj same) _

theorem physical_event_ammonia {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    (event : PhysicalEvent before water raw path [] [] CPS1BiologicalUpdate.noPhysicalSupply) :
    event.deformation.current.stock.count (deformedNH3 event.seed.translation.generatedFrame) = event.seed.translation.native.stock.count .ammonia := by
  have deformation := congrArg (fun value : CPS1Deformation.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (deformedNH3 event.seed.translation.generatedFrame)) event.deformationSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at deformation
  rw [deformed_source_ammonia] at deformation
  have molecular := congrArg (fun value : CPS1MolecularFrame.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (molecularNH3 event.seed.translation.generatedFrame)) event.molecularSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at molecular
  rw [molecular_source_ammonia] at molecular
  have following := congrArg (fun value : CPS1Following.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (followingNH3 event.seed.translation.generatedFrame)) event.followingSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at following
  rw [following_source_ammonia] at following
  have nuclear := congrArg (fun value : CPS1QuantumNuclear.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (nuclearNH3 event.seed.translation.generatedFrame)) event.nuclearSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at nuclear
  rw [nuclear_source_ammonia] at nuclear
  have electronic := congrArg (fun value : CPS1ElectronicSource.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (electronicNH3 event.seed.translation.generatedFrame)) event.electronicSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at electronic
  rw [electronic_source_ammonia] at electronic
  have bath := congrArg (fun value : CPS1EnzymeBath.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (bathNH3 event.seed.translation.generatedFrame)) event.bathSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at bath
  simp only [List.append_nil] at bath
  rw [bath_source_ammonia] at bath
  have atomic := congrArg (fun value : CPS1AtomicDynamics.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.count (atomicNH3 event.seed.translation.generatedFrame)) event.atomicSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at atomic
  rw [atomic_source_ammonia] at atomic
  exact deformation.trans (molecular.trans (following.trans (nuclear.trans
    (electronic.trans (bath.trans (atomic.trans (seed_source_ammonia event.seed)))))))

end
end CPS1SameEventFunction
