import H0mework.Chemistry.LAlanineBasinPartition.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def basinRuntimeProcess : SourceNativeLivingRootProcess N where
  State := ChargeIdentity.Runtime.chargeRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, basinLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, basinLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, basinLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := ChargeIdentity.Runtime.chargeRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨ChargeIdentity.Runtime.chargeRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev BasinFace := SourceNativeProjectionCoface ChargeIdentity.Runtime.ChargeFace BasinProjection

def basinRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := basinRuntimeProcess
  FaceAt := fun _ => BasinFace
  componentAt := fun _ face => match face with
    | .component _ => basinProjectionLaw
    | .inherited _ => BasinBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => basinComponentInstallation
    | .inherited _ => basinInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def basinRuntimeSeed : LivingRuntimeState basinRuntimeProcess := basinRuntimeFacade.seed
def basinRuntimeAfterFirst : LivingRuntimeState basinRuntimeProcess := basinRuntimeSeed.tick.next

theorem basinRuntime_seed_same_occurrence :
    basinRuntimeSeed.emittedOccurrence = ChargeIdentity.Runtime.chargeRuntimeSeed.emittedOccurrence := rfl

theorem basinRuntime_afterFirst_same_visit :
    basinRuntimeAfterFirst.current.visit = basinParentRuntime.current.visit := rfl

theorem basinRuntime_generated_same_next (runtime : LivingRuntimeState basinRuntimeProcess) :
    runtime.tick.next.state = ChargeIdentity.Runtime.chargeRuntimeProcess.successor runtime.state := rfl

theorem basinRuntimeFace_factorizes (runtime : LivingRuntimeState basinRuntimeProcess) (face : BasinFace) :
    type_of% (basinRuntimeFacade.readoutAt_factorizes runtime face) :=
  basinRuntimeFacade.readoutAt_factorizes runtime face

theorem basinRuntime_material_installed (runtime : LivingRuntimeState basinRuntimeProcess) :
    type_of% (basinRuntimeFace_factorizes runtime (.component .material)) ∧
    basinRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (BasinLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedBasinMaterial)⟩ :
        SourceNativeProjectionFiberAt basinProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨basinRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem basinRuntime_sourceCertificate :
    type_of% (basinRuntimeFace_factorizes basinRuntimeSeed (.component .certificate)) ∧
    Producer.basinPartitionClosure := by
  refine ⟨basinRuntimeFace_factorizes basinRuntimeSeed (.component .certificate), ?_⟩
  rcases basinRuntimeFacade.readoutAt basinRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem basinRuntime_original_sixteen_faces (runtime : LivingRuntimeState basinRuntimeProcess)
    (face : ChargeIdentity.Runtime.ChargeFace) :
    type_of% (basinRuntimeFace_factorizes runtime (.inherited face)) ∧
    basinRuntimeFacade.readoutAt runtime (.inherited face) =
      BasinBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨basinRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinPartition.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
