import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.RuntimeInstallation

/-! The original whole-flow occurrence installs its source-generated differential. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueFlowDifferential
noncomputable section

def differentialRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueTubeWholeRuntime.wholeTubeRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, differentialLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, differentialLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, differentialLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueTubeWholeRuntime.wholeTubeRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueTubeWholeRuntime.wholeTubeRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev DifferentialFace := SourceNativeProjectionCoface TrueTubeWholeRuntime.WholeTubeFace DifferentialProjection

def differentialRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := differentialRuntimeProcess
  FaceAt := fun _ => DifferentialFace
  componentAt := fun _ face => match face with
    | .component _ => differentialProjectionLaw
    | .inherited _ => DifferentialBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => differentialComponentInstallation
    | .inherited _ => differentialInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def differentialRuntimeSeed : LivingRuntimeState differentialRuntimeProcess := differentialRuntimeFacade.seed
def differentialRuntimeAfterFirst : LivingRuntimeState differentialRuntimeProcess := differentialRuntimeSeed.tick.next

theorem differentialRuntime_seed_same_occurrence :
    differentialRuntimeSeed.emittedOccurrence = TrueTubeWholeRuntime.wholeTubeRuntimeSeed.emittedOccurrence := rfl
theorem differentialRuntime_afterFirst_same_visit :
    differentialRuntimeAfterFirst.current.visit = differentialParentRuntime.current.visit := rfl
theorem differentialRuntime_generated_same_next (runtime : LivingRuntimeState differentialRuntimeProcess) :
    runtime.tick.next.state = TrueTubeWholeRuntime.wholeTubeRuntimeProcess.successor runtime.state := rfl

theorem differentialRuntimeFace_factorizes (runtime : LivingRuntimeState differentialRuntimeProcess) (face : DifferentialFace) :
    type_of% (differentialRuntimeFacade.readoutAt_factorizes runtime face) :=
  differentialRuntimeFacade.readoutAt_factorizes runtime face

theorem differentialRuntime_material_installed (runtime : LivingRuntimeState differentialRuntimeProcess) :
    type_of% (differentialRuntimeFace_factorizes runtime (.component .material)) ∧
    differentialRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (DifferentialLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedDifferentialMaterial)⟩ :
        SourceNativeProjectionFiberAt differentialProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨differentialRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem differentialRuntime_sourceCertificate :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧ TrueFlowDifferentialClosure := by
  refine ⟨differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate), ?_⟩
  rcases differentialRuntimeFacade.readoutAt differentialRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem differentialRuntime_original_thirty_two_faces (runtime : LivingRuntimeState differentialRuntimeProcess)
    (face : TrueTubeWholeRuntime.WholeTubeFace) :
    type_of% (differentialRuntimeFace_factorizes runtime (.inherited face)) ∧
    differentialRuntimeFacade.readoutAt runtime (.inherited face) =
      DifferentialBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨differentialRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
