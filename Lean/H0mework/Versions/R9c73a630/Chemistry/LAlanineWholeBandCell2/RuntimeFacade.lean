import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.RuntimeInstallation
/-! Canonical activation of the same root with its original actual field calculation face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def initialFieldRuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeBandSaturation.Runtime.saturationRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, initialFieldLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, initialFieldLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, initialFieldLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeBandSaturation.Runtime.saturationRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeBandSaturation.Runtime.saturationRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev InitialFieldFace := SourceNativeProjectionCoface WholeBandSaturation.Runtime.SaturationFace InitialFieldProjection

def initialFieldRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := initialFieldRuntimeProcess
  FaceAt := fun _ => InitialFieldFace
  componentAt := fun _ face => match face with
    | .component _ => initialFieldProjectionLaw
    | .inherited _ => InitialFieldBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => initialFieldComponentInstallation
    | .inherited _ => initialFieldInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def initialFieldRuntimeSeed : LivingRuntimeState initialFieldRuntimeProcess := initialFieldRuntimeFacade.seed
def initialFieldRuntimeAfterFirst : LivingRuntimeState initialFieldRuntimeProcess := initialFieldRuntimeSeed.tick.next

theorem initialFieldRuntime_seed_same_occurrence :
    initialFieldRuntimeSeed.emittedOccurrence = WholeBandSaturation.Runtime.saturationRuntimeSeed.emittedOccurrence := rfl
theorem initialFieldRuntime_afterFirst_same_visit :
    initialFieldRuntimeAfterFirst.current.visit = initialFieldParentRuntime.current.visit := rfl
theorem initialFieldRuntime_generated_same_next (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    runtime.tick.next.state = WholeBandSaturation.Runtime.saturationRuntimeProcess.successor runtime.state := rfl

theorem initialFieldRuntimeFace_factorizes (runtime : LivingRuntimeState initialFieldRuntimeProcess) (face : InitialFieldFace) :
    type_of% (initialFieldRuntimeFacade.readoutAt_factorizes runtime face) :=
  initialFieldRuntimeFacade.readoutAt_factorizes runtime face

theorem initialFieldRuntime_material_installed (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .material)) ∧
    initialFieldRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (InitialFieldLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedInitialFieldMaterial)⟩ :
        SourceNativeProjectionFiberAt initialFieldProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem initialFieldRuntime_sourceCertificateAt (runtime : LivingRuntimeState initialFieldRuntimeProcess) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.component .certificate)) ∧
    Source.InitialFieldClosure := by
  refine ⟨initialFieldRuntimeFace_factorizes runtime (.component .certificate), ?_⟩
  rcases initialFieldRuntimeFacade.readoutAt runtime (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem initialFieldRuntime_sourceCertificate :
    type_of% (initialFieldRuntime_sourceCertificateAt initialFieldRuntimeSeed) :=
  initialFieldRuntime_sourceCertificateAt initialFieldRuntimeSeed

theorem initialFieldRuntime_original_sixty_two_faces (runtime : LivingRuntimeState initialFieldRuntimeProcess)
    (face : WholeBandSaturation.Runtime.SaturationFace) :
    type_of% (initialFieldRuntimeFace_factorizes runtime (.inherited face)) ∧
    initialFieldRuntimeFacade.readoutAt runtime (.inherited face) =
      InitialFieldBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨initialFieldRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
