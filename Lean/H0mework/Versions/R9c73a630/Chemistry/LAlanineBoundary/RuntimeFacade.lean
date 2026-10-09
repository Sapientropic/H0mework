import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.RuntimeInstallation

/-! Same-root boundary authority and inherited source inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeCellBoundary
noncomputable section

def boundaryRuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeCellRuntime.wholeRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, boundaryLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, boundaryLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, boundaryLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeCellRuntime.wholeRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeCellRuntime.wholeRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev BoundaryFace := SourceNativeProjectionCoface WholeCellRuntime.WholeCellFace BoundaryProjection

def boundaryRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := boundaryRuntimeProcess
  FaceAt := fun _ => BoundaryFace
  componentAt := fun _ face => match face with
    | .component _ => boundaryProjectionLaw
    | .inherited _ => BoundaryBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => boundaryComponentInstallation
    | .inherited _ => boundaryInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def boundaryRuntimeSeed : LivingRuntimeState boundaryRuntimeProcess := boundaryRuntimeFacade.seed
def boundaryRuntimeAfterFirst : LivingRuntimeState boundaryRuntimeProcess := boundaryRuntimeSeed.tick.next

theorem boundaryRuntime_seed_same_occurrence :
    boundaryRuntimeSeed.emittedOccurrence = WholeCellRuntime.wholeRuntimeSeed.emittedOccurrence := rfl
theorem boundaryRuntime_afterFirst_same_visit :
    boundaryRuntimeAfterFirst.current.visit = boundaryParentRuntime.current.visit := rfl
theorem boundaryRuntime_generated_same_next (runtime : LivingRuntimeState boundaryRuntimeProcess) :
    runtime.tick.next.state = WholeCellRuntime.wholeRuntimeProcess.successor runtime.state := rfl

theorem boundaryRuntimeFace_factorizes (runtime : LivingRuntimeState boundaryRuntimeProcess) (face : BoundaryFace) :
    type_of% (boundaryRuntimeFacade.readoutAt_factorizes runtime face) :=
  boundaryRuntimeFacade.readoutAt_factorizes runtime face

theorem boundaryRuntime_material_installed (runtime : LivingRuntimeState boundaryRuntimeProcess) :
    type_of% (boundaryRuntimeFace_factorizes runtime (.component .material)) ∧
    boundaryRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (BoundaryLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedBoundaryMaterial)⟩ :
        SourceNativeProjectionFiberAt boundaryProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨boundaryRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem boundaryRuntime_sourceCertificate :
    type_of% (boundaryRuntimeFace_factorizes boundaryRuntimeSeed (.component .certificate)) ∧ GradientBoundaryClosure := by
  refine ⟨boundaryRuntimeFace_factorizes boundaryRuntimeSeed (.component .certificate), ?_⟩
  rcases boundaryRuntimeFacade.readoutAt boundaryRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem boundaryRuntime_original_twentySix_faces (runtime : LivingRuntimeState boundaryRuntimeProcess)
    (face : WholeCellRuntime.WholeCellFace) :
    type_of% (boundaryRuntimeFace_factorizes runtime (.inherited face)) ∧
    boundaryRuntimeFacade.readoutAt runtime (.inherited face) =
      BoundaryBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨boundaryRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.BoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
