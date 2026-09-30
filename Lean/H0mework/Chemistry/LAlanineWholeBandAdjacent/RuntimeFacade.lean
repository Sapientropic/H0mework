import H0mework.Chemistry.LAlanineWholeBandAdjacent.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root AdjacentSpatialSource
noncomputable section

def adjacentSpatialRuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeBandCell1Runtime.wholeBandCell1RuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, adjacentSpatialLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, adjacentSpatialLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, adjacentSpatialLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeBandCell1Runtime.wholeBandCell1RuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeBandCell1Runtime.wholeBandCell1RuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev AdjacentSpatialFace := SourceNativeProjectionCoface WholeBandCell1Runtime.WholeBandCell1Face AdjacentSpatialProjection

def adjacentSpatialRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := adjacentSpatialRuntimeProcess
  FaceAt := fun _ => AdjacentSpatialFace
  componentAt := fun _ face => match face with
    | .component _ => adjacentSpatialProjectionLaw
    | .inherited _ => AdjacentSpatialBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => adjacentSpatialComponentInstallation
    | .inherited _ => adjacentSpatialInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def adjacentSpatialRuntimeSeed : LivingRuntimeState adjacentSpatialRuntimeProcess := adjacentSpatialRuntimeFacade.seed
def adjacentSpatialRuntimeAfterFirst : LivingRuntimeState adjacentSpatialRuntimeProcess := adjacentSpatialRuntimeSeed.tick.next

theorem adjacentSpatialRuntime_seed_same_occurrence :
    adjacentSpatialRuntimeSeed.emittedOccurrence = WholeBandCell1Runtime.wholeBandCell1RuntimeSeed.emittedOccurrence := rfl
theorem adjacentSpatialRuntime_afterFirst_same_visit :
    adjacentSpatialRuntimeAfterFirst.current.visit = adjacentSpatialParentRuntime.current.visit := rfl
theorem adjacentSpatialRuntime_generated_same_next (runtime : LivingRuntimeState adjacentSpatialRuntimeProcess) :
    runtime.tick.next.state = WholeBandCell1Runtime.wholeBandCell1RuntimeProcess.successor runtime.state := rfl

theorem adjacentSpatialRuntimeFace_factorizes (runtime : LivingRuntimeState adjacentSpatialRuntimeProcess) (face : AdjacentSpatialFace) :
    type_of% (adjacentSpatialRuntimeFacade.readoutAt_factorizes runtime face) :=
  adjacentSpatialRuntimeFacade.readoutAt_factorizes runtime face

theorem adjacentSpatialRuntime_material_installed (runtime : LivingRuntimeState adjacentSpatialRuntimeProcess) :
    type_of% (adjacentSpatialRuntimeFace_factorizes runtime (.component .material)) ∧
    adjacentSpatialRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (AdjacentSpatialLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedAdjacentSpatialMaterial)⟩ :
        SourceNativeProjectionFiberAt adjacentSpatialProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨adjacentSpatialRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem adjacentSpatialRuntime_sourceCertificate :
    type_of% (adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .certificate)) ∧ AdjacentSpatialClosure := by
  refine ⟨adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .certificate), ?_⟩
  rcases adjacentSpatialRuntimeFacade.readoutAt adjacentSpatialRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem adjacentSpatialRuntime_original_fifty_four_faces (runtime : LivingRuntimeState adjacentSpatialRuntimeProcess)
    (face : WholeBandCell1Runtime.WholeBandCell1Face) :
    type_of% (adjacentSpatialRuntimeFace_factorizes runtime (.inherited face)) ∧
    adjacentSpatialRuntimeFacade.readoutAt runtime (.inherited face) =
      AdjacentSpatialBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨adjacentSpatialRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
