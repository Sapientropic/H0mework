import H0mework.Chemistry.LAlanineChargeIdentity.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def chargeRuntimeProcess : SourceNativeLivingRootProcess N where
  State := BondReadout.Runtime.bondRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, chargeLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, chargeLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, chargeLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := BondReadout.Runtime.bondRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨BondReadout.Runtime.bondRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev ChargeFace := SourceNativeProjectionCoface BondReadout.Runtime.BondFace ChargeProjection

def chargeRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := chargeRuntimeProcess
  FaceAt := fun _ => ChargeFace
  componentAt := fun _ face => match face with
    | .component _ => chargeProjectionLaw
    | .inherited _ => ChargeBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => chargeComponentInstallation
    | .inherited _ => chargeInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def chargeRuntimeSeed : LivingRuntimeState chargeRuntimeProcess := chargeRuntimeFacade.seed
def chargeRuntimeAfterFirst : LivingRuntimeState chargeRuntimeProcess := chargeRuntimeSeed.tick.next

theorem chargeRuntime_seed_same_occurrence :
    chargeRuntimeSeed.emittedOccurrence = BondReadout.Runtime.bondRuntimeSeed.emittedOccurrence := rfl

theorem chargeRuntime_afterFirst_same_visit :
    chargeRuntimeAfterFirst.current.visit = chargeParentRuntime.current.visit := rfl

theorem chargeRuntime_generated_same_next (runtime : LivingRuntimeState chargeRuntimeProcess) :
    runtime.tick.next.state = BondReadout.Runtime.bondRuntimeProcess.successor runtime.state := rfl

theorem chargeRuntimeFace_factorizes (runtime : LivingRuntimeState chargeRuntimeProcess) (face : ChargeFace) :
    type_of% (chargeRuntimeFacade.readoutAt_factorizes runtime face) :=
  chargeRuntimeFacade.readoutAt_factorizes runtime face

theorem chargeRuntime_material_installed (runtime : LivingRuntimeState chargeRuntimeProcess) :
    type_of% (chargeRuntimeFace_factorizes runtime (.component .material)) ∧
    chargeRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (ChargeLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedChargeMaterial)⟩ :
        SourceNativeProjectionFiberAt chargeProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨chargeRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem chargeRuntime_sourceCertificate :
    type_of% (chargeRuntimeFace_factorizes chargeRuntimeSeed (.component .certificate)) ∧
    Producer.chargeIdentityClosure := by
  refine ⟨chargeRuntimeFace_factorizes chargeRuntimeSeed (.component .certificate), ?_⟩
  rcases chargeRuntimeFacade.readoutAt chargeRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem chargeRuntime_original_fourteen_faces (runtime : LivingRuntimeState chargeRuntimeProcess)
    (face : BondReadout.Runtime.BondFace) :
    type_of% (chargeRuntimeFace_factorizes runtime (.inherited face)) ∧
    chargeRuntimeFacade.readoutAt runtime (.inherited face) =
      ChargeBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨chargeRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.ChargeIdentity.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
