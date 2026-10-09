import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.RuntimeInstallation

/-! The original occurrence installs its actual true-flow conservation. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueFlowConservation
noncomputable section

def conservationRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueFlowBoundaryRuntime.trueBoundaryRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, conservationLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, conservationLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, conservationLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueFlowBoundaryRuntime.trueBoundaryRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueFlowBoundaryRuntime.trueBoundaryRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev ConservationFace := SourceNativeProjectionCoface TrueFlowBoundaryRuntime.TrueBoundaryFace ConservationProjection

def conservationRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := conservationRuntimeProcess
  FaceAt := fun _ => ConservationFace
  componentAt := fun _ face => match face with
    | .component _ => conservationProjectionLaw
    | .inherited _ => ConservationBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => conservationComponentInstallation
    | .inherited _ => conservationInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def conservationRuntimeSeed : LivingRuntimeState conservationRuntimeProcess := conservationRuntimeFacade.seed
def conservationRuntimeAfterFirst : LivingRuntimeState conservationRuntimeProcess := conservationRuntimeSeed.tick.next

theorem conservationRuntime_seed_same_occurrence :
    conservationRuntimeSeed.emittedOccurrence = TrueFlowBoundaryRuntime.trueBoundaryRuntimeSeed.emittedOccurrence := rfl
theorem conservationRuntime_afterFirst_same_visit :
    conservationRuntimeAfterFirst.current.visit = conservationParentRuntime.current.visit := rfl
theorem conservationRuntime_generated_same_next (runtime : LivingRuntimeState conservationRuntimeProcess) :
    runtime.tick.next.state = TrueFlowBoundaryRuntime.trueBoundaryRuntimeProcess.successor runtime.state := rfl

theorem conservationRuntimeFace_factorizes (runtime : LivingRuntimeState conservationRuntimeProcess) (face : ConservationFace) :
    type_of% (conservationRuntimeFacade.readoutAt_factorizes runtime face) :=
  conservationRuntimeFacade.readoutAt_factorizes runtime face

theorem conservationRuntime_material_installed (runtime : LivingRuntimeState conservationRuntimeProcess) :
    type_of% (conservationRuntimeFace_factorizes runtime (.component .material)) ∧
    conservationRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (ConservationLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedConservationMaterial)⟩ :
        SourceNativeProjectionFiberAt conservationProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨conservationRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem conservationRuntime_sourceCertificate :
    type_of% (conservationRuntimeFace_factorizes conservationRuntimeSeed (.component .certificate)) ∧ TrueFlowConservationClosure := by
  refine ⟨conservationRuntimeFace_factorizes conservationRuntimeSeed (.component .certificate), ?_⟩
  rcases conservationRuntimeFacade.readoutAt conservationRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem conservationRuntime_original_thirty_eight_faces (runtime : LivingRuntimeState conservationRuntimeProcess)
    (face : TrueFlowBoundaryRuntime.TrueBoundaryFace) :
    type_of% (conservationRuntimeFace_factorizes runtime (.inherited face)) ∧
    conservationRuntimeFacade.readoutAt runtime (.inherited face) =
      ConservationBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨conservationRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
