import H0mework.Chemistry.LAlanineRefinementRuntime.Installation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def refinementRuntimeProcess : SourceNativeLivingRootProcess N where
  State := BasinPartition.Runtime.basinRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, refinementLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, refinementLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, refinementLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := BasinPartition.Runtime.basinRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨BasinPartition.Runtime.basinRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev RefinementFace := SourceNativeProjectionCoface BasinPartition.Runtime.BasinFace RefinementProjection

def refinementRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := refinementRuntimeProcess
  FaceAt := fun _ => RefinementFace
  componentAt := fun _ face => match face with
    | .component _ => refinementProjectionLaw
    | .inherited _ => RefinementBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => refinementComponentInstallation
    | .inherited _ => refinementInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def refinementRuntimeSeed : LivingRuntimeState refinementRuntimeProcess := refinementRuntimeFacade.seed
def refinementRuntimeAfterFirst : LivingRuntimeState refinementRuntimeProcess := refinementRuntimeSeed.tick.next

theorem refinementRuntime_seed_same_occurrence :
    refinementRuntimeSeed.emittedOccurrence = BasinPartition.Runtime.basinRuntimeSeed.emittedOccurrence := rfl

theorem refinementRuntime_afterFirst_same_visit :
    refinementRuntimeAfterFirst.current.visit = refinementParentRuntime.current.visit := rfl

theorem refinementRuntime_generated_same_next (runtime : LivingRuntimeState refinementRuntimeProcess) :
    runtime.tick.next.state = BasinPartition.Runtime.basinRuntimeProcess.successor runtime.state := rfl

theorem refinementRuntimeFace_factorizes (runtime : LivingRuntimeState refinementRuntimeProcess) (face : RefinementFace) :
    type_of% (refinementRuntimeFacade.readoutAt_factorizes runtime face) :=
  refinementRuntimeFacade.readoutAt_factorizes runtime face

theorem refinementRuntime_material_installed (runtime : LivingRuntimeState refinementRuntimeProcess) :
    type_of% (refinementRuntimeFace_factorizes runtime (.component .material)) ∧
    refinementRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (RefinementLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedRefinementMaterial)⟩ :
        SourceNativeProjectionFiberAt refinementProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨refinementRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem refinementRuntime_sourceCertificate :
    type_of% (refinementRuntimeFace_factorizes refinementRuntimeSeed (.component .certificate)) ∧
    refinementSourceClosure := by
  refine ⟨refinementRuntimeFace_factorizes refinementRuntimeSeed (.component .certificate), ?_⟩
  rcases refinementRuntimeFacade.readoutAt refinementRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem refinementRuntime_original_eighteen_faces (runtime : LivingRuntimeState refinementRuntimeProcess)
    (face : BasinPartition.Runtime.BasinFace) :
    type_of% (refinementRuntimeFace_factorizes runtime (.inherited face)) ∧
    refinementRuntimeFacade.readoutAt runtime (.inherited face) =
      RefinementBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨refinementRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
