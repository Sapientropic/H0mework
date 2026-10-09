import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.RuntimeInstallation

/-! The original occurrence installs its generated true-flow geometry. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueFlowGeometry
noncomputable section

def geometryRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueFlowDifferentialRuntime.differentialRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, geometryLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, geometryLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, geometryLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueFlowDifferentialRuntime.differentialRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueFlowDifferentialRuntime.differentialRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev GeometryFace := SourceNativeProjectionCoface TrueFlowDifferentialRuntime.DifferentialFace GeometryProjection

def geometryRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := geometryRuntimeProcess
  FaceAt := fun _ => GeometryFace
  componentAt := fun _ face => match face with
    | .component _ => geometryProjectionLaw
    | .inherited _ => GeometryBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => geometryComponentInstallation
    | .inherited _ => geometryInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def geometryRuntimeSeed : LivingRuntimeState geometryRuntimeProcess := geometryRuntimeFacade.seed
def geometryRuntimeAfterFirst : LivingRuntimeState geometryRuntimeProcess := geometryRuntimeSeed.tick.next

theorem geometryRuntime_seed_same_occurrence :
    geometryRuntimeSeed.emittedOccurrence = TrueFlowDifferentialRuntime.differentialRuntimeSeed.emittedOccurrence := rfl
theorem geometryRuntime_afterFirst_same_visit :
    geometryRuntimeAfterFirst.current.visit = geometryParentRuntime.current.visit := rfl
theorem geometryRuntime_generated_same_next (runtime : LivingRuntimeState geometryRuntimeProcess) :
    runtime.tick.next.state = TrueFlowDifferentialRuntime.differentialRuntimeProcess.successor runtime.state := rfl

theorem geometryRuntimeFace_factorizes (runtime : LivingRuntimeState geometryRuntimeProcess) (face : GeometryFace) :
    type_of% (geometryRuntimeFacade.readoutAt_factorizes runtime face) :=
  geometryRuntimeFacade.readoutAt_factorizes runtime face

theorem geometryRuntime_material_installed (runtime : LivingRuntimeState geometryRuntimeProcess) :
    type_of% (geometryRuntimeFace_factorizes runtime (.component .material)) ∧
    geometryRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (GeometryLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedGeometryMaterial)⟩ :
        SourceNativeProjectionFiberAt geometryProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨geometryRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem geometryRuntime_sourceCertificate :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧ TrueFlowGeometryClosure := by
  refine ⟨geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate), ?_⟩
  rcases geometryRuntimeFacade.readoutAt geometryRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem geometryRuntime_original_thirty_four_faces (runtime : LivingRuntimeState geometryRuntimeProcess)
    (face : TrueFlowDifferentialRuntime.DifferentialFace) :
    type_of% (geometryRuntimeFace_factorizes runtime (.inherited face)) ∧
    geometryRuntimeFacade.readoutAt runtime (.inherited face) =
      GeometryBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨geometryRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
