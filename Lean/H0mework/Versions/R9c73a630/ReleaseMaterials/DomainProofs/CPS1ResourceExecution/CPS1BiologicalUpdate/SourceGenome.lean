import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Transport

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

def noPhysicalSupply : PhysicalRaw := ⟨[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]⟩

private theorem mapped_dna {S T : Type} (read : S → Option DNA) (lift : S → T)
    (readLift : T → Option DNA) (same : ∀ item, readLift (lift item) = read item) (stock : List S) :
    (stock.map lift).filterMap readLift = stock.filterMap read := by
  induction stock with
  | nil => rfl
  | cons item rest ih => simp only [List.map_cons,List.filterMap_cons,same,ih]

theorem captured_source_genome (previous : CPS1StockRecursion.Source.Observation frame) :
    (CPS1LocalChemicalExecution.Source.fromCurrent frame previous).current.stock.filterMap localDNA? =
      previous.current.stock.filterMap reinitiatedDNA? := by
  unfold CPS1LocalChemicalExecution.Source.fromCurrent CPS1LocalChemicalExecution.Source.start
    CPS1LocalChemicalExecution.execute
  dsimp only
  rw [local_stock_genome]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem atomized_source_genome (previous : CPS1EditingChemicalJoin.Source.Occurrence frame) :
    (CPS1AtomicSource.Current.fromActual frame previous).current.stock.filterMap atomizedDNA? =
      previous.current.stock.filterMap localDNA? := by
  unfold CPS1AtomicSource.Current.fromActual CPS1AtomicSource.Current.execute
  dsimp only
  rw [atomized_stock_genome]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem seed_source_genome {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] []) :
    seed.atomic.current.stock.filterMap atomizedDNA? = seed.translation.native.stock.filterMap nativeDNA? := by
  have observed := congrArg (fun value : CPS1StockRecursion.Source.Observation seed.translation.generatedFrame =>
    value.current.stock.filterMap reinitiatedDNA?) seed.observedSource
  change seed.observed.current.stock.filterMap reinitiatedDNA? =
    (seed.recycled.stock.map CPS1Reinitiation.Species.retained).filterMap reinitiatedDNA? at observed
  rw [mapped_dna recycledDNA? _ reinitiatedDNA? (fun _ => rfl)] at observed
  have captured := congrArg (fun value : CPS1LocalChemicalExecution.Source.Occurrence seed.translation.generatedFrame =>
    value.current.stock.filterMap localDNA?) seed.actualCapture
  rw [captured_source_genome] at captured
  have joined := congrArg (fun value : CPS1LocalChemicalExecution.Source.Cursor seed.translation.generatedFrame =>
    value.stock.filterMap localDNA?) seed.noReload
  have atomized := congrArg (fun value : CPS1AtomicSource.Current.Occurrence seed.translation.generatedFrame =>
    value.current.stock.filterMap atomizedDNA?) seed.actualAtomic
  rw [atomized_source_genome] at atomized
  have recycled := congrArg (fun value : CPS1Recycling.ExecutionAt seed.translation.generatedFrame =>
    value.stock.filterMap recycledDNA?) seed.actualRecycling
  simp only [CPS1Recycling.run,CPS1Recycling.compile,CPS1Recycling.currentStock,
    List.map_nil,List.append_nil,Inventory.execute] at recycled
  rw [mapped_dna nativeDNA? _ recycledDNA? (fun _ => rfl)] at recycled
  have native := congrArg (fun value : CPS1Recycling.Frame => value.native.stock.filterMap nativeDNA?)
    seed.translation.frameSource
  exact atomized.trans (joined.trans (captured.trans (observed.trans (recycled.trans native))))

theorem atomic_source_genome (previous : CPS1AtomicSource.Current.Occurrence frame) :
    (CPS1AtomicDynamics.Source.resume frame (CPS1AtomicDynamics.Source.fromActual frame previous) []).current.stock.filterMap atomicDNA? =
      previous.current.stock.filterMap atomizedDNA? := by
  unfold CPS1AtomicDynamics.Source.resume CPS1AtomicDynamics.Source.advance CPS1AtomicDynamics.Source.fromActual CPS1AtomicDynamics.Source.start CPS1AtomicDynamics.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [atomic_stock_genome,List.flatMap_nil,List.append_nil]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem bath_source_genome (previous : CPS1AtomicDynamics.Source.Occurrence frame) :
    (CPS1EnzymeBath.Source.resume frame (CPS1EnzymeBath.Source.fromActual frame previous) CPS1EnzymeBath.Source.generatedPartnerProgram []).current.stock.filterMap bathDNA? =
      previous.current.stock.filterMap atomicDNA? := by
  unfold CPS1EnzymeBath.Source.resume CPS1EnzymeBath.Source.advance CPS1EnzymeBath.Source.fromActual CPS1EnzymeBath.Source.start CPS1EnzymeBath.Source.generatedPartnerProgram CPS1EnzymeBath.Source.RawAction.material CPS1EnzymeBath.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [bath_stock_genome,List.map_nil,List.append_nil]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [bath_stock_genome]
  have lift : ∀ item, bathDNA? (CPS1EnzymeBath.Source.liftMaterial frame item) = atomicDNA? item := by
    intro item
    cases item <;> rfl
  exact mapped_dna _ _ _ lift _

theorem electronic_source_genome (previous : CPS1EnzymeBath.Source.Occurrence frame) :
    (CPS1ElectronicSource.Source.resume frame (CPS1ElectronicSource.Source.fromActual frame previous) [] []).current.stock.filterMap electronicDNA? =
      previous.current.stock.filterMap bathDNA? := by
  unfold CPS1ElectronicSource.Source.resume CPS1ElectronicSource.Source.advance CPS1ElectronicSource.Source.fromActual CPS1ElectronicSource.Source.start CPS1ElectronicSource.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [electronic_stock_genome,List.map_nil,List.flatMap_nil,List.append_nil]
  have lift : ∀ item, electronicDNA? (CPS1ElectronicSource.Source.liftMaterial frame item) = bathDNA? item := by
    intro item
    cases item <;> rfl
  exact mapped_dna _ _ _ lift _

theorem nuclear_source_genome (previous : CPS1ElectronicSource.Source.Occurrence frame) :
    (CPS1QuantumNuclear.Source.resume frame (CPS1QuantumNuclear.Source.fromActual frame previous) [] []).current.stock.filterMap nuclearDNA? =
      previous.current.stock.filterMap electronicDNA? := by
  unfold CPS1QuantumNuclear.Source.resume CPS1QuantumNuclear.Source.advance CPS1QuantumNuclear.Source.fromActual CPS1QuantumNuclear.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [nuclear_stock_genome,List.map_nil,List.flatMap_nil,List.append_nil]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem following_source_genome (previous : CPS1QuantumNuclear.Source.Occurrence frame) :
    (CPS1Following.Source.resume frame (CPS1Following.Source.fromActual frame previous) [] []).current.stock.filterMap followingDNA? =
      previous.current.stock.filterMap nuclearDNA? := by
  unfold CPS1Following.Source.resume CPS1Following.Source.advance CPS1Following.Source.fromActual CPS1Following.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [following_stock_genome,List.map_nil,List.flatMap_nil,List.append_nil]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem molecular_source_genome (previous : CPS1Following.Source.Occurrence frame) :
    (CPS1MolecularFrame.Source.resume frame (CPS1MolecularFrame.Source.fromActual frame previous) [] []).current.stock.filterMap molecularDNA? =
      previous.current.stock.filterMap followingDNA? := by
  unfold CPS1MolecularFrame.Source.resume CPS1MolecularFrame.Source.advance CPS1MolecularFrame.Source.fromActual CPS1MolecularFrame.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [molecular_stock_genome,List.map_nil,List.flatMap_nil,List.append_nil]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem deformation_source_genome (previous : CPS1MolecularFrame.Source.Occurrence frame) :
    (CPS1Deformation.Source.resume frame (CPS1Deformation.Source.fromActual frame previous) [] []).current.stock.filterMap deformedDNA? =
      previous.current.stock.filterMap molecularDNA? := by
  unfold CPS1Deformation.Source.resume CPS1Deformation.Source.advance CPS1Deformation.Source.fromActual CPS1Deformation.execute
  dsimp only [List.map_nil,List.flatMap_nil,List.append_nil]
  simp only [deformed_stock_genome,List.map_nil,List.flatMap_nil,List.append_nil]
  exact mapped_dna _ _ _ (fun _ => rfl) _

theorem physical_event_genome {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    (event : PhysicalEvent before water raw path [] [] noPhysicalSupply) :
    event.deformation.current.stock.filterMap deformedDNA? =
      event.seed.translation.native.stock.filterMap nativeDNA? := by
  have deformation := congrArg (fun value : CPS1Deformation.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap deformedDNA?) event.deformationSource
  dsimp only [noPhysicalSupply] at deformation
  rw [deformation_source_genome] at deformation
  have molecular := congrArg (fun value : CPS1MolecularFrame.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap molecularDNA?) event.molecularSource
  dsimp only [noPhysicalSupply] at molecular
  rw [molecular_source_genome] at molecular
  have following := congrArg (fun value : CPS1Following.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap followingDNA?) event.followingSource
  dsimp only [noPhysicalSupply] at following
  rw [following_source_genome] at following
  have nuclear := congrArg (fun value : CPS1QuantumNuclear.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap nuclearDNA?) event.nuclearSource
  dsimp only [noPhysicalSupply] at nuclear
  rw [nuclear_source_genome] at nuclear
  have electronic := congrArg (fun value : CPS1ElectronicSource.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap electronicDNA?) event.electronicSource
  dsimp only [noPhysicalSupply] at electronic
  rw [electronic_source_genome] at electronic
  have bath := congrArg (fun value : CPS1EnzymeBath.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap bathDNA?) event.bathSource
  dsimp only [noPhysicalSupply] at bath
  simp only [List.append_nil] at bath
  rw [bath_source_genome] at bath
  have atomic := congrArg (fun value : CPS1AtomicDynamics.Source.Occurrence event.seed.translation.generatedFrame =>
    value.current.stock.filterMap atomicDNA?) event.atomicSource
  dsimp only [noPhysicalSupply] at atomic
  rw [atomic_source_genome] at atomic
  exact deformation.trans (molecular.trans (following.trans (nuclear.trans
    (electronic.trans (bath.trans (atomic.trans (seed_source_genome event.seed)))))))

end
end CPS1BiologicalUpdate
