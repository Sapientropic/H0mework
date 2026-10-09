import H0mework.Versions.R9c73a630.Chemistry.LAlanineRuntime.Installation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.ContinuousRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def bandRuntimeProcess : SourceNativeLivingRootProcess N where
  State := Runtime.refinementRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, bandLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, bandLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, bandLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := Runtime.refinementRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨Runtime.refinementRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev ContinuousBandFace := SourceNativeProjectionCoface Runtime.RefinementFace ContinuousBandProjection

def bandRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := bandRuntimeProcess
  FaceAt := fun _ => ContinuousBandFace
  componentAt := fun _ face => match face with
    | .component _ => bandProjectionLaw
    | .inherited _ => BandBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => bandComponentInstallation
    | .inherited _ => bandInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def bandRuntimeSeed : LivingRuntimeState bandRuntimeProcess := bandRuntimeFacade.seed
def bandRuntimeAfterFirst : LivingRuntimeState bandRuntimeProcess := bandRuntimeSeed.tick.next

theorem bandRuntime_seed_same_occurrence :
    bandRuntimeSeed.emittedOccurrence = Runtime.refinementRuntimeSeed.emittedOccurrence := rfl
theorem bandRuntime_afterFirst_same_visit :
    bandRuntimeAfterFirst.current.visit = bandParentRuntime.current.visit := rfl
theorem bandRuntime_generated_same_next (runtime : LivingRuntimeState bandRuntimeProcess) :
    runtime.tick.next.state = Runtime.refinementRuntimeProcess.successor runtime.state := rfl

theorem bandRuntimeFace_factorizes (runtime : LivingRuntimeState bandRuntimeProcess) (face : ContinuousBandFace) :
    type_of% (bandRuntimeFacade.readoutAt_factorizes runtime face) := bandRuntimeFacade.readoutAt_factorizes runtime face

theorem bandRuntime_material_installed (runtime : LivingRuntimeState bandRuntimeProcess) :
    type_of% (bandRuntimeFace_factorizes runtime (.component .material)) ∧
    bandRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (BandLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedContinuousBandMaterial)⟩ :
        SourceNativeProjectionFiberAt bandProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨bandRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem bandRuntime_sourceCertificate :
    type_of% (bandRuntimeFace_factorizes bandRuntimeSeed (.component .certificate)) ∧ bandSourceClosure := by
  refine ⟨bandRuntimeFace_factorizes bandRuntimeSeed (.component .certificate), ?_⟩
  rcases bandRuntimeFacade.readoutAt bandRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem bandRuntime_original_twenty_faces (runtime : LivingRuntimeState bandRuntimeProcess) (face : Runtime.RefinementFace) :
    type_of% (bandRuntimeFace_factorizes runtime (.inherited face)) ∧
    bandRuntimeFacade.readoutAt runtime (.inherited face) = BandBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨bandRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.ContinuousRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
