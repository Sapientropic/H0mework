import H0mework.Chemistry.LAlanineSpatialRuntime.Installation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def spatialRuntimeProcess : SourceNativeLivingRootProcess N where
  State := ContinuousRuntime.bandRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, spatialLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, spatialLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, spatialLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := ContinuousRuntime.bandRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨ContinuousRuntime.bandRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev SpatialFace := SourceNativeProjectionCoface ContinuousRuntime.ContinuousBandFace SpatialProjection

def spatialRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := spatialRuntimeProcess
  FaceAt := fun _ => SpatialFace
  componentAt := fun _ face => match face with
    | .component _ => spatialProjectionLaw
    | .inherited _ => SpatialBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => spatialComponentInstallation
    | .inherited _ => spatialInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def spatialRuntimeSeed : LivingRuntimeState spatialRuntimeProcess := spatialRuntimeFacade.seed
def spatialRuntimeAfterFirst : LivingRuntimeState spatialRuntimeProcess := spatialRuntimeSeed.tick.next

theorem spatialRuntime_seed_same_occurrence :
    spatialRuntimeSeed.emittedOccurrence = ContinuousRuntime.bandRuntimeSeed.emittedOccurrence := rfl
theorem spatialRuntime_afterFirst_same_visit :
    spatialRuntimeAfterFirst.current.visit = spatialParentRuntime.current.visit := rfl
theorem spatialRuntime_generated_same_next (runtime : LivingRuntimeState spatialRuntimeProcess) :
    runtime.tick.next.state = ContinuousRuntime.bandRuntimeProcess.successor runtime.state := rfl

theorem spatialRuntimeFace_factorizes (runtime : LivingRuntimeState spatialRuntimeProcess) (face : SpatialFace) :
    type_of% (spatialRuntimeFacade.readoutAt_factorizes runtime face) :=
  spatialRuntimeFacade.readoutAt_factorizes runtime face

theorem spatialRuntime_material_installed (runtime : LivingRuntimeState spatialRuntimeProcess) :
    type_of% (spatialRuntimeFace_factorizes runtime (.component .material)) ∧
    spatialRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (SpatialLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedSpatialMaterial)⟩ :
        SourceNativeProjectionFiberAt spatialProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨spatialRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem spatialRuntime_sourceCertificate :
    type_of% (spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .certificate)) ∧ spatialSourceClosure := by
  refine ⟨spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .certificate), ?_⟩
  rcases spatialRuntimeFacade.readoutAt spatialRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem spatialRuntime_original_twentyTwo_faces (runtime : LivingRuntimeState spatialRuntimeProcess)
    (face : ContinuousRuntime.ContinuousBandFace) :
    type_of% (spatialRuntimeFace_factorizes runtime (.inherited face)) ∧
    spatialRuntimeFacade.readoutAt runtime (.inherited face) =
      SpatialBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨spatialRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
