import H0mework.Chemistry.LAlanineTrueTubeWhole.RuntimeInstallation

/-! The same occurrence installs its complete original signed-gradient window. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueTubeWholeActual
noncomputable section

def wholeTubeRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueTubeRuntime.tubeRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeTubeLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeTubeLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeTubeLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueTubeRuntime.tubeRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueTubeRuntime.tubeRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeTubeFace := SourceNativeProjectionCoface TrueTubeRuntime.TrueTubeFace WholeTubeProjection

def wholeTubeRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeTubeRuntimeProcess
  FaceAt := fun _ => WholeTubeFace
  componentAt := fun _ face => match face with
    | .component _ => wholeTubeProjectionLaw
    | .inherited _ => WholeTubeBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeTubeComponentInstallation
    | .inherited _ => wholeTubeInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeTubeRuntimeSeed : LivingRuntimeState wholeTubeRuntimeProcess := wholeTubeRuntimeFacade.seed
def wholeTubeRuntimeAfterFirst : LivingRuntimeState wholeTubeRuntimeProcess := wholeTubeRuntimeSeed.tick.next

theorem wholeTubeRuntime_seed_same_occurrence :
    wholeTubeRuntimeSeed.emittedOccurrence = TrueTubeRuntime.tubeRuntimeSeed.emittedOccurrence := rfl
theorem wholeTubeRuntime_afterFirst_same_visit :
    wholeTubeRuntimeAfterFirst.current.visit = wholeTubeParentRuntime.current.visit := rfl
theorem wholeTubeRuntime_generated_same_next (runtime : LivingRuntimeState wholeTubeRuntimeProcess) :
    runtime.tick.next.state = TrueTubeRuntime.tubeRuntimeProcess.successor runtime.state := rfl

theorem wholeTubeRuntimeFace_factorizes (runtime : LivingRuntimeState wholeTubeRuntimeProcess) (face : WholeTubeFace) :
    type_of% (wholeTubeRuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeTubeRuntimeFacade.readoutAt_factorizes runtime face

theorem wholeTubeRuntime_material_installed (runtime : LivingRuntimeState wholeTubeRuntimeProcess) :
    type_of% (wholeTubeRuntimeFace_factorizes runtime (.component .material)) ∧
    wholeTubeRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeTubeLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeTubeMaterial)⟩ :
        SourceNativeProjectionFiberAt wholeTubeProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeTubeRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeTubeRuntime_sourceCertificate :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧ WholeContinuationClosure := by
  refine ⟨wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate), ?_⟩
  rcases wholeTubeRuntimeFacade.readoutAt wholeTubeRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeTubeRuntime_original_thirty_faces (runtime : LivingRuntimeState wholeTubeRuntimeProcess)
    (face : TrueTubeRuntime.TrueTubeFace) :
    type_of% (wholeTubeRuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeTubeRuntimeFacade.readoutAt runtime (.inherited face) =
      WholeTubeBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeTubeRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
