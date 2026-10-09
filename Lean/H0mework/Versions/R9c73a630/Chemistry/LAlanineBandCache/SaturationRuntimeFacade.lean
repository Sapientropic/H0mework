import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCache.SaturationRuntimeInstallation

/-! Canonical activation of the same root with its original Gaussian calculation face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def saturationRuntimeProcess : SourceNativeLivingRootProcess N where
  State := LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, saturationLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, saturationLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, saturationLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev SaturationFace := SourceNativeProjectionCoface LAlanine40K2025.AtomicMass.Runtime.AtomicMassFace SaturationProjection

def saturationRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := saturationRuntimeProcess
  FaceAt := fun _ => SaturationFace
  componentAt := fun _ face => match face with
    | .component _ => saturationProjectionLaw
    | .inherited _ => SaturationBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => saturationComponentInstallation
    | .inherited _ => saturationInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def saturationRuntimeSeed : LivingRuntimeState saturationRuntimeProcess := saturationRuntimeFacade.seed
def saturationRuntimeAfterFirst : LivingRuntimeState saturationRuntimeProcess := saturationRuntimeSeed.tick.next

theorem saturationRuntime_seed_same_occurrence :
    saturationRuntimeSeed.emittedOccurrence = LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeSeed.emittedOccurrence := rfl
theorem saturationRuntime_afterFirst_same_visit :
    saturationRuntimeAfterFirst.current.visit = saturationParentRuntime.current.visit := rfl
theorem saturationRuntime_generated_same_next (runtime : LivingRuntimeState saturationRuntimeProcess) :
    runtime.tick.next.state = LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeProcess.successor runtime.state := rfl

theorem saturationRuntimeFace_factorizes (runtime : LivingRuntimeState saturationRuntimeProcess) (face : SaturationFace) :
    type_of% (saturationRuntimeFacade.readoutAt_factorizes runtime face) :=
  saturationRuntimeFacade.readoutAt_factorizes runtime face

theorem saturationRuntime_material_installed (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .material)) ∧
    saturationRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (SaturationLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedSaturationMaterial)⟩ :
        SourceNativeProjectionFiberAt saturationProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨saturationRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem saturationRuntime_sourceCertificateAt (runtime : LivingRuntimeState saturationRuntimeProcess) :
    type_of% (saturationRuntimeFace_factorizes runtime (.component .certificate)) ∧
    Source.Cell2SaturationClosure := by
  refine ⟨saturationRuntimeFace_factorizes runtime (.component .certificate), ?_⟩
  rcases saturationRuntimeFacade.readoutAt runtime (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem saturationRuntime_sourceCertificate :
    type_of% (saturationRuntime_sourceCertificateAt saturationRuntimeSeed) :=
  saturationRuntime_sourceCertificateAt saturationRuntimeSeed

theorem saturationRuntime_original_sixty_faces (runtime : LivingRuntimeState saturationRuntimeProcess)
    (face : LAlanine40K2025.AtomicMass.Runtime.AtomicMassFace) :
    type_of% (saturationRuntimeFace_factorizes runtime (.inherited face)) ∧
    saturationRuntimeFacade.readoutAt runtime (.inherited face) =
      SaturationBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨saturationRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule