import H0mework.Chemistry.LAlanineWholeCell.RuntimeInstallation

/-! A fixed sealed facade exposes the full-cell coordinate and all inherited faces. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeCellSpatial
noncomputable section

def wholeRuntimeProcess : SourceNativeLivingRootProcess N where
  State := SpatialRuntime.spatialRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := SpatialRuntime.spatialRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨SpatialRuntime.spatialRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeCellFace := SourceNativeProjectionCoface SpatialRuntime.SpatialFace WholeCellProjection

def wholeRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeRuntimeProcess
  FaceAt := fun _ => WholeCellFace
  componentAt := fun _ face => match face with
    | .component _ => wholeProjectionLaw
    | .inherited _ => WholeBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeComponentInstallation
    | .inherited _ => wholeInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeRuntimeSeed : LivingRuntimeState wholeRuntimeProcess := wholeRuntimeFacade.seed
def wholeRuntimeAfterFirst : LivingRuntimeState wholeRuntimeProcess := wholeRuntimeSeed.tick.next

theorem wholeRuntime_seed_same_occurrence :
    wholeRuntimeSeed.emittedOccurrence = SpatialRuntime.spatialRuntimeSeed.emittedOccurrence := rfl
theorem wholeRuntime_afterFirst_same_visit :
    wholeRuntimeAfterFirst.current.visit = wholeParentRuntime.current.visit := rfl
theorem wholeRuntime_generated_same_next (runtime : LivingRuntimeState wholeRuntimeProcess) :
    runtime.tick.next.state = SpatialRuntime.spatialRuntimeProcess.successor runtime.state := rfl

theorem wholeRuntimeFace_factorizes (runtime : LivingRuntimeState wholeRuntimeProcess) (face : WholeCellFace) :
    type_of% (wholeRuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeRuntimeFacade.readoutAt_factorizes runtime face

theorem wholeRuntime_material_installed (runtime : LivingRuntimeState wholeRuntimeProcess) :
    type_of% (wholeRuntimeFace_factorizes runtime (.component .material)) ∧
    wholeRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeCellMaterial)⟩ :
        SourceNativeProjectionFiberAt wholeProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeRuntime_sourceCertificate :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate)) ∧ WholeCellClosure := by
  refine ⟨wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate), ?_⟩
  rcases wholeRuntimeFacade.readoutAt wholeRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeRuntime_original_twentyFour_faces (runtime : LivingRuntimeState wholeRuntimeProcess)
    (face : SpatialRuntime.SpatialFace) :
    type_of% (wholeRuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeRuntimeFacade.readoutAt runtime (.inherited face) =
      WholeBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
