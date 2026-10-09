import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Stages
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.CurrentGenome

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution

-- Explicit noncomputable blocks VM initialization from replaying paid legacy inventories;
-- a noncomputable section alone still permits code generation for pure definitions.
noncomputable def registeredRecycled : CPS1Recycling.ExecutionAt registeredFrame :=
  CPS1Recycling.run registeredFrame (CPS1Recycling.productiveEvents registeredPath) registeredRecycleFeed
noncomputable def registeredScanning : CPS1Reinitiation.Execution registeredFrame :=
  CPS1Reinitiation.run registeredFrame registeredRecycled registeredPath.after Molecules.mrna registeredScanFeed
noncomputable def registeredHandover : CPS1Reinitiation.Handover.Execution registeredFrame :=
  CPS1Reinitiation.Handover.execute registeredFrame
    (CPS1Reinitiation.Handover.fullProgram registeredPath Molecules.mrna 151 Program.originalPeptide.2)
    (registeredScanning.stock ++ registeredBodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species registeredFrame))
noncomputable def registeredObserved : CPS1StockRecursion.Source.Observation registeredFrame :=
  CPS1StockRecursion.Source.requested registeredFrame registeredPath registeredDepth registeredHandover.stock
noncomputable def registeredCaptured : CPS1LocalChemicalExecution.Source.Occurrence registeredFrame := CPS1LocalChemicalExecution.Source.fromCurrent registeredFrame registeredObserved
noncomputable def registeredJoined : CPS1EditingChemicalJoin.Source.Occurrence registeredFrame :=
  CPS1EditingChemicalJoin.Source.fromActual registeredFrame registeredCaptured registeredEdits registeredWater registeredAdditional
noncomputable def registeredChemical : CPS1EditingChemicalJoin.Source.Occurrence registeredFrame :=
  CPS1EditingChemicalJoin.Source.advance registeredFrame registeredJoined
    CPS1LocalChemicalExecution.Source.chemicalActions CPS1EditingChemicalJoin.Source.rawFuel
noncomputable def registeredAtomized : CPS1AtomicSource.Current.Occurrence registeredFrame := CPS1AtomicSource.Current.fromActual registeredFrame registeredChemical
noncomputable def registeredAtomic : CPS1AtomicDynamics.Source.Occurrence registeredFrame := CPS1AtomicDynamics.Source.resume registeredFrame
  (CPS1AtomicDynamics.Source.fromActual registeredFrame registeredAtomized) registeredOldActions
noncomputable def registeredBath : CPS1EnzymeBath.Source.Occurrence registeredFrame := CPS1EnzymeBath.Source.resume registeredFrame
  (CPS1EnzymeBath.Source.fromActual registeredFrame registeredAtomic)
  (CPS1EnzymeBath.Source.generatedPartnerProgram ++ registeredBathActions) []
noncomputable def registeredElectronic : CPS1ElectronicSource.Source.Occurrence registeredFrame := CPS1ElectronicSource.Source.resume registeredFrame
  (CPS1ElectronicSource.Source.fromActual registeredFrame registeredBath) [] []
noncomputable def registeredNuclear : CPS1QuantumNuclear.Source.Occurrence registeredFrame := CPS1QuantumNuclear.Source.resume registeredFrame
  (CPS1QuantumNuclear.Source.fromActual registeredFrame registeredElectronic) [] []
noncomputable def registeredFollowing : CPS1Following.Source.Occurrence registeredFrame := CPS1Following.Source.resume registeredFrame
  (CPS1Following.Source.fromActual registeredFrame registeredNuclear) [] []
noncomputable def registeredMolecular : CPS1MolecularFrame.Source.Occurrence registeredFrame := CPS1MolecularFrame.Source.resume registeredFrame
  (CPS1MolecularFrame.Source.fromActual registeredFrame registeredFollowing) [] []
noncomputable def registeredOld : CPS1Deformation.Source.Occurrence registeredFrame :=
  sourceAfterCapture registeredFrame registeredCaptured registeredEdits registeredWater registeredAdditional registeredBathActions

theorem registered_capture_actual :
    CPS1LocalChemicalExecution.Source.actualCapture registeredEdits registeredWater registeredAdditional registeredPath
      registeredRecycleFeed registeredScanFeed registeredBodyFeed registeredDepth =
      some ⟨registeredFrame,registeredCaptured⟩ := by
  exact (CPS1LocalChemicalExecution.Source.actual_capture_complete registeredEdits registeredWater registeredAdditional registeredPath
    registeredRecycleFeed [] (by simp only [registeredRecycleFeed,List.append_nil]; rfl)
    registeredScanFeed [] (by simp only [registeredScanFeed,List.append_nil]; rfl)
    registeredBodyFeed [] (by simp only [registeredBodyFeed,List.append_nil]; rfl)
    registeredDepth).1

theorem registered_source_actual : registeredSourceExecution = some ⟨registeredFrame,registeredOld⟩ := by
  exact source_after_capture_actual registeredEdits registeredWater registeredAdditional registeredPath
    registeredRecycleFeed registeredScanFeed registeredBodyFeed registeredDepth
    registeredFrame registeredCaptured registered_capture_actual registeredBathActions

noncomputable def registeredProgrammeData : CPS1ReactiveSourceEntry.Programme registeredFrame 0 0 :=
  CPS1ReactiveSourceEntry.programmeFromOld registeredOld [] [] [] 0 (([],[]),[]) 0
noncomputable def registeredBefore : CPS1ReactiveNuclear.SourceCursor registeredFrame := registeredProgrammeData.current

theorem registered_programme_actual :
    registeredProgramme = some ⟨registeredFrame,registeredProgrammeData⟩ := by
  unfold registeredProgramme
  rw [CPS1ReactiveSourceEntry.programme_from_source_stored_exact]
  change registeredSourceExecution.map _ = _
  rw [registered_source_actual]
  rfl

theorem registered_editing_actual :
    (CPS1ReactiveField.editingSource registeredOld).editing =
      CPS1Deamination.Continuation.sourceContinuation registeredEdits registeredWater registeredAdditional :=
  source_after_capture_editing registeredFrame registeredCaptured registeredEdits registeredWater registeredAdditional registeredBathActions

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
