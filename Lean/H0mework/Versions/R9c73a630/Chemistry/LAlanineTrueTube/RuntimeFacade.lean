import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.RuntimeInstallation

/-! The same physical occurrence installs its actual true-ODE continuation face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueTubeActual
noncomputable section

def tubeRuntimeProcess : SourceNativeLivingRootProcess N where
  State := BoundaryRuntime.boundaryRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, tubeLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, tubeLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, tubeLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := BoundaryRuntime.boundaryRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨BoundaryRuntime.boundaryRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev TrueTubeFace := SourceNativeProjectionCoface BoundaryRuntime.BoundaryFace TrueTubeProjection

def tubeRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := tubeRuntimeProcess
  FaceAt := fun _ => TrueTubeFace
  componentAt := fun _ face => match face with
    | .component _ => tubeProjectionLaw
    | .inherited _ => TubeBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => tubeComponentInstallation
    | .inherited _ => tubeInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def tubeRuntimeSeed : LivingRuntimeState tubeRuntimeProcess := tubeRuntimeFacade.seed
def tubeRuntimeAfterFirst : LivingRuntimeState tubeRuntimeProcess := tubeRuntimeSeed.tick.next

theorem tubeRuntime_seed_same_occurrence :
    tubeRuntimeSeed.emittedOccurrence = BoundaryRuntime.boundaryRuntimeSeed.emittedOccurrence := rfl
theorem tubeRuntime_afterFirst_same_visit :
    tubeRuntimeAfterFirst.current.visit = tubeParentRuntime.current.visit := rfl
theorem tubeRuntime_generated_same_next (runtime : LivingRuntimeState tubeRuntimeProcess) :
    runtime.tick.next.state = BoundaryRuntime.boundaryRuntimeProcess.successor runtime.state := rfl

theorem tubeRuntimeFace_factorizes (runtime : LivingRuntimeState tubeRuntimeProcess) (face : TrueTubeFace) :
    type_of% (tubeRuntimeFacade.readoutAt_factorizes runtime face) :=
  tubeRuntimeFacade.readoutAt_factorizes runtime face

theorem tubeRuntime_material_installed (runtime : LivingRuntimeState tubeRuntimeProcess) :
    type_of% (tubeRuntimeFace_factorizes runtime (.component .material)) ∧
    tubeRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (TubeLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedTrueTubeMaterial)⟩ :
        SourceNativeProjectionFiberAt tubeProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨tubeRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem tubeRuntime_sourceCertificate :
    type_of% (tubeRuntimeFace_factorizes tubeRuntimeSeed (.component .certificate)) ∧ FirstContinuationClosure := by
  refine ⟨tubeRuntimeFace_factorizes tubeRuntimeSeed (.component .certificate), ?_⟩
  rcases tubeRuntimeFacade.readoutAt tubeRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem tubeRuntime_original_twentyEight_faces (runtime : LivingRuntimeState tubeRuntimeProcess)
    (face : BoundaryRuntime.BoundaryFace) :
    type_of% (tubeRuntimeFace_factorizes runtime (.inherited face)) ∧
    tubeRuntimeFacade.readoutAt runtime (.inherited face) =
      TubeBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨tubeRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
