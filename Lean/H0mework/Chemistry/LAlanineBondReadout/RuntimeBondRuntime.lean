import H0mework.Chemistry.LAlanineBondReadout.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def bondRuntimeProcess : SourceNativeLivingRootProcess N where
  State := Reentry.Runtime.reentryRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, bondLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, bondLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, bondLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := Reentry.Runtime.reentryRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨Reentry.Runtime.reentryRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev BondFace := SourceNativeProjectionCoface Reentry.Runtime.ReentryProjection BondProjection

def bondRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := bondRuntimeProcess
  FaceAt := fun _ => BondFace
  componentAt := fun _ face => match face with
    | .component _ => bondProjectionLaw
    | .inherited _ => BondBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => bondComponentInstallation
    | .inherited _ => bondInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def bondRuntimeSeed : LivingRuntimeState bondRuntimeProcess := bondRuntimeFacade.seed
def bondRuntimeAfterFirst : LivingRuntimeState bondRuntimeProcess := bondRuntimeSeed.tick.next

theorem bondRuntime_seed_same_occurrence :
    bondRuntimeSeed.emittedOccurrence = Reentry.Runtime.reentryRuntimeSeed.emittedOccurrence := rfl

theorem bondRuntime_afterFirst_same_visit :
    bondRuntimeAfterFirst.current.visit = Reentry.Runtime.reentryRuntimeAfterFirst.current.visit := rfl

theorem bondRuntime_generated_same_next (runtime : LivingRuntimeState bondRuntimeProcess) :
    runtime.tick.next.state = Reentry.Runtime.reentryRuntimeProcess.successor runtime.state := rfl

theorem bondRuntimeFace_factorizes (runtime : LivingRuntimeState bondRuntimeProcess) (face : BondFace) :
    type_of% (bondRuntimeFacade.readoutAt_factorizes runtime face) :=
  bondRuntimeFacade.readoutAt_factorizes runtime face

theorem bondRuntime_material_installed (runtime : LivingRuntimeState bondRuntimeProcess) :
    type_of% (bondRuntimeFace_factorizes runtime (.component .material)) ∧
    bondRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (BondLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedBondMaterial)⟩ :
        SourceNativeProjectionFiberAt bondProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨bondRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem bondRuntime_sourceCertificate :
    type_of% (bondRuntimeFace_factorizes bondRuntimeSeed (.component .certificate)) ∧ Producer.bondReadoutClosure := by
  refine ⟨bondRuntimeFace_factorizes bondRuntimeSeed (.component .certificate), ?_⟩
  rcases bondRuntimeFacade.readoutAt bondRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem bondRuntime_original_twelve_faces (runtime : LivingRuntimeState bondRuntimeProcess)
    (face : Reentry.Runtime.ReentryProjection) :
    type_of% (bondRuntimeFace_factorizes runtime (.inherited face)) ∧
    bondRuntimeFacade.readoutAt runtime (.inherited face) =
      Reentry.Runtime.reentryProjectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨bondRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BondReadout.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
