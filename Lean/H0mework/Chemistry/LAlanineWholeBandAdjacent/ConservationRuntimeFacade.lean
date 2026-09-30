import H0mework.Chemistry.LAlanineWholeBandAdjacent.ConservationRuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BandConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root BandConservationSource
noncomputable section

def bandConservationRuntimeProcess : SourceNativeLivingRootProcess N where
  State := AdjacentSpatialRuntime.adjacentSpatialRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, bandConservationLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, bandConservationLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, bandConservationLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := AdjacentSpatialRuntime.adjacentSpatialRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨AdjacentSpatialRuntime.adjacentSpatialRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev BandConservationFace := SourceNativeProjectionCoface AdjacentSpatialRuntime.AdjacentSpatialFace BandConservationProjection

def bandConservationRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := bandConservationRuntimeProcess
  FaceAt := fun _ => BandConservationFace
  componentAt := fun _ face => match face with
    | .component _ => bandConservationProjectionLaw
    | .inherited _ => BandConservationBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => bandConservationComponentInstallation
    | .inherited _ => bandConservationInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def bandConservationRuntimeSeed : LivingRuntimeState bandConservationRuntimeProcess := bandConservationRuntimeFacade.seed
def bandConservationRuntimeAfterFirst : LivingRuntimeState bandConservationRuntimeProcess := bandConservationRuntimeSeed.tick.next

theorem bandConservationRuntime_seed_same_occurrence :
    bandConservationRuntimeSeed.emittedOccurrence = AdjacentSpatialRuntime.adjacentSpatialRuntimeSeed.emittedOccurrence := rfl
theorem bandConservationRuntime_afterFirst_same_visit :
    bandConservationRuntimeAfterFirst.current.visit = bandConservationParentRuntime.current.visit := rfl
theorem bandConservationRuntime_generated_same_next (runtime : LivingRuntimeState bandConservationRuntimeProcess) :
    runtime.tick.next.state = AdjacentSpatialRuntime.adjacentSpatialRuntimeProcess.successor runtime.state := rfl

theorem bandConservationRuntimeFace_factorizes (runtime : LivingRuntimeState bandConservationRuntimeProcess) (face : BandConservationFace) :
    type_of% (bandConservationRuntimeFacade.readoutAt_factorizes runtime face) :=
  bandConservationRuntimeFacade.readoutAt_factorizes runtime face

theorem bandConservationRuntime_material_installed (runtime : LivingRuntimeState bandConservationRuntimeProcess) :
    type_of% (bandConservationRuntimeFace_factorizes runtime (.component .material)) ∧
    bandConservationRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (BandConservationLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedBandConservationMaterial)⟩ :
        SourceNativeProjectionFiberAt bandConservationProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨bandConservationRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem bandConservationRuntime_sourceCertificate :
    type_of% (bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .certificate)) ∧ BandConservationClosure := by
  refine ⟨bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .certificate), ?_⟩
  rcases bandConservationRuntimeFacade.readoutAt bandConservationRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem bandConservationRuntime_original_fifty_six_faces (runtime : LivingRuntimeState bandConservationRuntimeProcess)
    (face : AdjacentSpatialRuntime.AdjacentSpatialFace) :
    type_of% (bandConservationRuntimeFace_factorizes runtime (.inherited face)) ∧
    bandConservationRuntimeFacade.readoutAt runtime (.inherited face) =
      BandConservationBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨bandConservationRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.BandConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
