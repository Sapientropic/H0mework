import H0mework.Versions.R9c73a630.Chemistry.LAlanineAtomicMass.RuntimeInstallation

/-! Canonical activation of the same root with its isotope-mass face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def atomicMassRuntimeProcess : SourceNativeLivingRootProcess N where
  State := BasinRefinement.BandConservationRuntime.bandConservationRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, atomicMassLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, atomicMassLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, atomicMassLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := BasinRefinement.BandConservationRuntime.bandConservationRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨BasinRefinement.BandConservationRuntime.bandConservationRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev AtomicMassFace := SourceNativeProjectionCoface BasinRefinement.BandConservationRuntime.BandConservationFace AtomicMassProjection

def atomicMassRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := atomicMassRuntimeProcess
  FaceAt := fun _ => AtomicMassFace
  componentAt := fun _ face => match face with
    | .component _ => atomicMassProjectionLaw
    | .inherited _ => AtomicMassBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => atomicMassComponentInstallation
    | .inherited _ => atomicMassInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def atomicMassRuntimeSeed : LivingRuntimeState atomicMassRuntimeProcess := atomicMassRuntimeFacade.seed
def atomicMassRuntimeAfterFirst : LivingRuntimeState atomicMassRuntimeProcess := atomicMassRuntimeSeed.tick.next

theorem atomicMassRuntime_seed_same_occurrence :
    atomicMassRuntimeSeed.emittedOccurrence = BasinRefinement.BandConservationRuntime.bandConservationRuntimeSeed.emittedOccurrence := rfl
theorem atomicMassRuntime_afterFirst_same_visit :
    atomicMassRuntimeAfterFirst.current.visit = atomicMassParentRuntime.current.visit := rfl
theorem atomicMassRuntime_generated_same_next (runtime : LivingRuntimeState atomicMassRuntimeProcess) :
    runtime.tick.next.state = BasinRefinement.BandConservationRuntime.bandConservationRuntimeProcess.successor runtime.state := rfl

theorem atomicMassRuntimeFace_factorizes (runtime : LivingRuntimeState atomicMassRuntimeProcess) (face : AtomicMassFace) :
    type_of% (atomicMassRuntimeFacade.readoutAt_factorizes runtime face) :=
  atomicMassRuntimeFacade.readoutAt_factorizes runtime face

theorem atomicMassRuntime_material_installed (runtime : LivingRuntimeState atomicMassRuntimeProcess) :
    type_of% (atomicMassRuntimeFace_factorizes runtime (.component .material)) ∧
    atomicMassRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (AtomicMassLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedAtomicMassMaterial)⟩ :
        SourceNativeProjectionFiberAt atomicMassProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨atomicMassRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem atomicMassRuntime_sourceCertificate :
    type_of% (atomicMassRuntimeFace_factorizes atomicMassRuntimeSeed (.component .certificate)) ∧ AtomicMassClosure := by
  refine ⟨atomicMassRuntimeFace_factorizes atomicMassRuntimeSeed (.component .certificate), ?_⟩
  rcases atomicMassRuntimeFacade.readoutAt atomicMassRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem atomicMassRuntime_original_fifty_eight_faces (runtime : LivingRuntimeState atomicMassRuntimeProcess)
    (face : BasinRefinement.BandConservationRuntime.BandConservationFace) :
    type_of% (atomicMassRuntimeFace_factorizes runtime (.inherited face)) ∧
    atomicMassRuntimeFacade.readoutAt runtime (.inherited face) =
      AtomicMassBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨atomicMassRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.AtomicMass.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
