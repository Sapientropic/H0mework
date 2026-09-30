import H0mework.Chemistry.LAlanineBandRuntime.Installation

/-! The original occurrence installs the whole-band source and its paid dependent restrictions. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeBandSource
noncomputable section

def wholeBandRuntimeProcess : SourceNativeLivingRootProcess N where
  State := TrueFlowQuantitativeRuntime.quantitativeRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeBandLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeBandLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeBandLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := TrueFlowQuantitativeRuntime.quantitativeRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨TrueFlowQuantitativeRuntime.quantitativeRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeBandFace := SourceNativeProjectionCoface TrueFlowQuantitativeRuntime.QuantitativeFace WholeBandProjection

def wholeBandRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeBandRuntimeProcess
  FaceAt := fun _ => WholeBandFace
  componentAt := fun _ face => match face with
    | .component _ => wholeBandProjectionLaw
    | .inherited _ => WholeBandBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeBandComponentInstallation
    | .inherited _ => wholeBandInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeBandRuntimeSeed : LivingRuntimeState wholeBandRuntimeProcess := wholeBandRuntimeFacade.seed
def wholeBandRuntimeAfterFirst : LivingRuntimeState wholeBandRuntimeProcess := wholeBandRuntimeSeed.tick.next

theorem wholeBandRuntime_seed_same_occurrence :
    wholeBandRuntimeSeed.emittedOccurrence = TrueFlowQuantitativeRuntime.quantitativeRuntimeSeed.emittedOccurrence := rfl
theorem wholeBandRuntime_afterFirst_same_visit :
    wholeBandRuntimeAfterFirst.current.visit = wholeBandParentRuntime.current.visit := rfl
theorem wholeBandRuntime_generated_same_next (runtime : LivingRuntimeState wholeBandRuntimeProcess) :
    runtime.tick.next.state = TrueFlowQuantitativeRuntime.quantitativeRuntimeProcess.successor runtime.state := rfl

theorem wholeBandRuntimeFace_factorizes (runtime : LivingRuntimeState wholeBandRuntimeProcess) (face : WholeBandFace) :
    type_of% (wholeBandRuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeBandRuntimeFacade.readoutAt_factorizes runtime face

theorem wholeBandRuntime_material_installed (runtime : LivingRuntimeState wholeBandRuntimeProcess) :
    type_of% (wholeBandRuntimeFace_factorizes runtime (.component .material)) ∧
    wholeBandRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeBandLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeBandMaterial)⟩ :
        SourceNativeProjectionFiberAt wholeBandProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeBandRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeBandRuntime_sourceCertificate :
    type_of% (wholeBandRuntimeFace_factorizes wholeBandRuntimeSeed (.component .certificate)) ∧ WholeBandSourceClosure := by
  refine ⟨wholeBandRuntimeFace_factorizes wholeBandRuntimeSeed (.component .certificate), ?_⟩
  rcases wholeBandRuntimeFacade.readoutAt wholeBandRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeBandRuntime_original_forty_two_faces (runtime : LivingRuntimeState wholeBandRuntimeProcess)
    (face : TrueFlowQuantitativeRuntime.QuantitativeFace) :
    type_of% (wholeBandRuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeBandRuntimeFacade.readoutAt runtime (.inherited face) =
      WholeBandBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeBandRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
