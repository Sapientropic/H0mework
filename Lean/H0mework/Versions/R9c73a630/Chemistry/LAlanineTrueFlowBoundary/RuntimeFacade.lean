import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.RuntimeInstallation

/-! The original occurrence installs its generated true-flow boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root TrueFlowBoundary
noncomputable section

def trueBoundaryRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueFlowGeometryRuntime.geometryRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, trueBoundaryLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, trueBoundaryLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, trueBoundaryLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueFlowGeometryRuntime.geometryRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueFlowGeometryRuntime.geometryRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev TrueBoundaryFace := SourceNativeProjectionCoface TrueFlowGeometryRuntime.GeometryFace TrueBoundaryProjection

def trueBoundaryRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := trueBoundaryRuntimeProcess
  FaceAt := fun _ => TrueBoundaryFace
  componentAt := fun _ face => match face with
    | .component _ => trueBoundaryProjectionLaw
    | .inherited _ => TrueBoundaryBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => trueBoundaryComponentInstallation
    | .inherited _ => trueBoundaryInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def trueBoundaryRuntimeSeed : LivingRuntimeState trueBoundaryRuntimeProcess := trueBoundaryRuntimeFacade.seed
def trueBoundaryRuntimeAfterFirst : LivingRuntimeState trueBoundaryRuntimeProcess := trueBoundaryRuntimeSeed.tick.next

theorem trueBoundaryRuntime_seed_same_occurrence :
    trueBoundaryRuntimeSeed.emittedOccurrence = TrueFlowGeometryRuntime.geometryRuntimeSeed.emittedOccurrence := rfl
theorem trueBoundaryRuntime_afterFirst_same_visit :
    trueBoundaryRuntimeAfterFirst.current.visit = trueBoundaryParentRuntime.current.visit := rfl
theorem trueBoundaryRuntime_generated_same_next (runtime : LivingRuntimeState trueBoundaryRuntimeProcess) :
    runtime.tick.next.state = TrueFlowGeometryRuntime.geometryRuntimeProcess.successor runtime.state := rfl

theorem trueBoundaryRuntimeFace_factorizes (runtime : LivingRuntimeState trueBoundaryRuntimeProcess) (face : TrueBoundaryFace) :
    type_of% (trueBoundaryRuntimeFacade.readoutAt_factorizes runtime face) :=
  trueBoundaryRuntimeFacade.readoutAt_factorizes runtime face

theorem trueBoundaryRuntime_material_installed (runtime : LivingRuntimeState trueBoundaryRuntimeProcess) :
    type_of% (trueBoundaryRuntimeFace_factorizes runtime (.component .material)) ∧
    trueBoundaryRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (TrueBoundaryLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedTrueBoundaryMaterial)⟩ :
        SourceNativeProjectionFiberAt trueBoundaryProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨trueBoundaryRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem trueBoundaryRuntime_sourceCertificate :
    type_of% (trueBoundaryRuntimeFace_factorizes trueBoundaryRuntimeSeed (.component .certificate)) ∧ TrueFlowBoundaryClosure := by
  refine ⟨trueBoundaryRuntimeFace_factorizes trueBoundaryRuntimeSeed (.component .certificate), ?_⟩
  rcases trueBoundaryRuntimeFacade.readoutAt trueBoundaryRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem trueBoundaryRuntime_original_thirty_six_faces (runtime : LivingRuntimeState trueBoundaryRuntimeProcess)
    (face : TrueFlowGeometryRuntime.GeometryFace) :
    type_of% (trueBoundaryRuntimeFace_factorizes runtime (.inherited face)) ∧
    trueBoundaryRuntimeFacade.readoutAt runtime (.inherited face) =
      TrueBoundaryBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨trueBoundaryRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
