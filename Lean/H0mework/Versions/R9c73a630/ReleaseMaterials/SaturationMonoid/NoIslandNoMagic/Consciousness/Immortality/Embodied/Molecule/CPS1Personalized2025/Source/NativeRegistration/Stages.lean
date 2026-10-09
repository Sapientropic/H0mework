import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.CurrentGenome

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1BiologicalUpdate

def sourceAfterCapture (frame : CPS1Recycling.Frame)
    (captured : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) (bathActions : List CPS1EnzymeBath.Source.RawAction) :
    CPS1Deformation.Source.Occurrence frame :=
  let joined := CPS1EditingChemicalJoin.Source.fromActual frame captured edits water additional
  let chemical := CPS1EditingChemicalJoin.Source.advance frame joined
    CPS1LocalChemicalExecution.Source.chemicalActions CPS1EditingChemicalJoin.Source.rawFuel
  let atomized := CPS1AtomicSource.Current.fromActual frame chemical
  let atomic := CPS1AtomicDynamics.Source.resume frame (CPS1AtomicDynamics.Source.fromActual frame atomized) []
  let bath := CPS1EnzymeBath.Source.resume frame (CPS1EnzymeBath.Source.fromActual frame atomic)
    (CPS1EnzymeBath.Source.generatedPartnerProgram ++ bathActions) []
  let electronic := CPS1ElectronicSource.Source.resume frame (CPS1ElectronicSource.Source.fromActual frame bath) [] []
  let nuclear := CPS1QuantumNuclear.Source.resume frame (CPS1QuantumNuclear.Source.fromActual frame electronic) [] []
  let following := CPS1Following.Source.resume frame (CPS1Following.Source.fromActual frame nuclear) [] []
  let molecular := CPS1MolecularFrame.Source.resume frame (CPS1MolecularFrame.Source.fromActual frame following) [] []
  CPS1Deformation.Source.resume frame (CPS1Deformation.Source.fromActual frame molecular) [] []

theorem source_after_capture_actual (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (frame : CPS1Recycling.Frame) (captured : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (actual : CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
      recycleFeed scanFeed bodyFeed depth = some ⟨frame,captured⟩)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) :
    CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      [] bathActions [] [] [] [] [] [] [] [] [] [] [] =
      some ⟨frame,sourceAfterCapture frame captured edits water additional bathActions⟩ := by
  simp only [CPS1Deformation.Source.execution,CPS1MolecularFrame.Source.execution,CPS1Following.Source.execution,
    CPS1QuantumNuclear.Source.execution,CPS1ElectronicSource.Source.execution,
    CPS1EnzymeBath.Source.generatedExecution,CPS1EnzymeBath.Source.execution,CPS1AtomicDynamics.Source.execution,
    CPS1AtomicSource.Current.execution,CPS1AtomicSource.Current.sourceExecution,CPS1EditingChemicalJoin.Source.execution,actual]
  rfl

theorem source_after_capture_editing (frame : CPS1Recycling.Frame)
    (captured : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) (bathActions : List CPS1EnzymeBath.Source.RawAction) :
    (CPS1ReactiveField.editingSource (sourceAfterCapture frame captured edits water additional bathActions)).editing =
      CPS1Deamination.Continuation.sourceContinuation edits water additional := rfl

private theorem mapped_genome {S T : Type} (read : S → Option DNA) (lift : S → T)
    (readLift : T → Option DNA) (same : ∀ item, readLift (lift item) = read item) (stock : List S) :
    (stock.map lift).filterMap readLift = stock.filterMap read := by
  induction stock with
  | nil => rfl
  | cons item rest ih => simp only [List.map_cons,List.filterMap_cons,same,ih]

theorem bath_source_actions_genome {frame : CPS1Recycling.Frame}
    (previous : CPS1AtomicDynamics.Source.Occurrence frame) (actions : List CPS1EnzymeBath.Source.RawAction) :
    (CPS1EnzymeBath.Source.resume frame (CPS1EnzymeBath.Source.fromActual frame previous)
      (CPS1EnzymeBath.Source.generatedPartnerProgram ++ actions) []).current.stock.filterMap bathDNA? =
      previous.current.stock.filterMap atomicDNA? := by
  unfold CPS1EnzymeBath.Source.resume CPS1EnzymeBath.Source.advance CPS1EnzymeBath.Source.fromActual
    CPS1EnzymeBath.Source.start CPS1EnzymeBath.execute
  dsimp only
  rw [bath_stock_genome]
  simp only [List.map_nil,List.append_nil,List.filterMap_append]
  have raw : ∀ actions : List CPS1EnzymeBath.Source.RawAction,
      (actions.flatMap (CPS1EnzymeBath.Source.RawAction.material frame)).filterMap bathDNA? = [] := by
    intro requested
    induction requested with
    | nil => rfl
    | cons action rest ih => cases action <;> simpa [CPS1EnzymeBath.Source.RawAction.material,bathDNA?] using ih
  rw [raw,List.append_nil,bath_stock_genome]
  have lift : ∀ item, bathDNA? (CPS1EnzymeBath.Source.liftMaterial frame item) = atomicDNA? item := by
    intro item
    cases item <;> rfl
  exact mapped_genome _ _ _ lift _

theorem source_after_capture_genome (frame : CPS1Recycling.Frame)
    (captured : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) (bathActions : List CPS1EnzymeBath.Source.RawAction) :
    (sourceAfterCapture frame captured edits water additional bathActions).current.stock.filterMap deformedDNA? =
      captured.current.stock.filterMap localDNA? ++
        (CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.filterMap nativeDNA? := by
  unfold sourceAfterCapture
  dsimp only
  rw [deformation_source_genome,molecular_source_genome,following_source_genome,nuclear_source_genome,
    electronic_source_genome,bath_source_actions_genome,atomic_source_genome,atomized_source_genome]
  unfold CPS1EditingChemicalJoin.Source.advance CPS1LocalChemicalExecution.Source.advance
  dsimp only
  unfold CPS1LocalChemicalExecution.execute
  rw [local_stock_genome]
  simp only [List.filterMap_append]
  have raw : (CPS1EditingChemicalJoin.Source.rawFuel.map CPS1EditingChemicalJoin.Source.RawMaterial.local |>.map
      (CPS1LocalChemicalExecution.Source.RawMaterial.species frame)).filterMap localDNA? = [] := rfl
  have actions : (CPS1LocalChemicalExecution.Source.chemicalActions.flatMap
      (CPS1LocalChemicalExecution.Source.LocalAction.material frame)).filterMap localDNA? = [] := rfl
  rw [raw,actions,List.append_nil,List.append_nil]
  change (captured.current.stock ++ (CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map
    (CPS1EditingChemicalJoin.Source.editingSpecies frame)).filterMap localDNA? = _
  rw [List.filterMap_append]
  congr 1
  exact mapped_genome _ _ _ (fun _ => rfl) _

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
