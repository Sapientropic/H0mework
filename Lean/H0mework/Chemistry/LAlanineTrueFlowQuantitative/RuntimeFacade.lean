import H0mework.Chemistry.LAlanineTrueFlowQuantitative.RuntimeInstallation

/-! The original occurrence installs its actual true-flow quantitative bounds. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueFlowQuantitative
noncomputable section

def quantitativeRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueFlowConservationRuntime.conservationRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, quantitativeLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, quantitativeLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, quantitativeLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueFlowConservationRuntime.conservationRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueFlowConservationRuntime.conservationRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev QuantitativeFace := SourceNativeProjectionCoface TrueFlowConservationRuntime.ConservationFace QuantitativeProjection

def quantitativeRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := quantitativeRuntimeProcess
  FaceAt := fun _ => QuantitativeFace
  componentAt := fun _ face => match face with
    | .component _ => quantitativeProjectionLaw
    | .inherited _ => QuantitativeBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => quantitativeComponentInstallation
    | .inherited _ => quantitativeInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def quantitativeRuntimeSeed : LivingRuntimeState quantitativeRuntimeProcess := quantitativeRuntimeFacade.seed
def quantitativeRuntimeAfterFirst : LivingRuntimeState quantitativeRuntimeProcess := quantitativeRuntimeSeed.tick.next

theorem quantitativeRuntime_seed_same_occurrence :
    quantitativeRuntimeSeed.emittedOccurrence = TrueFlowConservationRuntime.conservationRuntimeSeed.emittedOccurrence := rfl
theorem quantitativeRuntime_afterFirst_same_visit :
    quantitativeRuntimeAfterFirst.current.visit = quantitativeParentRuntime.current.visit := rfl
theorem quantitativeRuntime_generated_same_next (runtime : LivingRuntimeState quantitativeRuntimeProcess) :
    runtime.tick.next.state = TrueFlowConservationRuntime.conservationRuntimeProcess.successor runtime.state := rfl

theorem quantitativeRuntimeFace_factorizes (runtime : LivingRuntimeState quantitativeRuntimeProcess) (face : QuantitativeFace) :
    type_of% (quantitativeRuntimeFacade.readoutAt_factorizes runtime face) :=
  quantitativeRuntimeFacade.readoutAt_factorizes runtime face

theorem quantitativeRuntime_material_installed (runtime : LivingRuntimeState quantitativeRuntimeProcess) :
    type_of% (quantitativeRuntimeFace_factorizes runtime (.component .material)) ∧
    quantitativeRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (QuantitativeLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedQuantitativeMaterial)⟩ :
        SourceNativeProjectionFiberAt quantitativeProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨quantitativeRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem quantitativeRuntime_sourceCertificate :
    type_of% (quantitativeRuntimeFace_factorizes quantitativeRuntimeSeed (.component .certificate)) ∧ TrueFlowQuantitativeClosure := by
  refine ⟨quantitativeRuntimeFace_factorizes quantitativeRuntimeSeed (.component .certificate), ?_⟩
  rcases quantitativeRuntimeFacade.readoutAt quantitativeRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem quantitativeRuntime_original_forty_faces (runtime : LivingRuntimeState quantitativeRuntimeProcess)
    (face : TrueFlowConservationRuntime.ConservationFace) :
    type_of% (quantitativeRuntimeFace_factorizes runtime (.inherited face)) ∧
    quantitativeRuntimeFacade.readoutAt runtime (.inherited face) =
      QuantitativeBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨quantitativeRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
