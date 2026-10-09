import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlow.RuntimeInstallation

/-! The original occurrence installs the whole-band source and its paid dependent restrictions. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeBandFlowSource
noncomputable section

def wholeBandFlowRuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeBandRuntime.wholeBandRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeBandFlowLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeBandFlowLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeBandFlowLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeBandRuntime.wholeBandRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeBandRuntime.wholeBandRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeBandFlowFace := SourceNativeProjectionCoface WholeBandRuntime.WholeBandFace WholeBandFlowProjection

def wholeBandFlowRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeBandFlowRuntimeProcess
  FaceAt := fun _ => WholeBandFlowFace
  componentAt := fun _ face => match face with
    | .component _ => wholeBandFlowProjectionLaw
    | .inherited _ => WholeBandFlowBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeBandFlowComponentInstallation
    | .inherited _ => wholeBandFlowInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeBandFlowRuntimeSeed : LivingRuntimeState wholeBandFlowRuntimeProcess := wholeBandFlowRuntimeFacade.seed
def wholeBandFlowRuntimeAfterFirst : LivingRuntimeState wholeBandFlowRuntimeProcess := wholeBandFlowRuntimeSeed.tick.next

theorem wholeBandFlowRuntime_seed_same_occurrence :
    wholeBandFlowRuntimeSeed.emittedOccurrence = WholeBandRuntime.wholeBandRuntimeSeed.emittedOccurrence := rfl
theorem wholeBandFlowRuntime_afterFirst_same_visit :
    wholeBandFlowRuntimeAfterFirst.current.visit = wholeBandFlowParentRuntime.current.visit := rfl
theorem wholeBandFlowRuntime_generated_same_next (runtime : LivingRuntimeState wholeBandFlowRuntimeProcess) :
    runtime.tick.next.state = WholeBandRuntime.wholeBandRuntimeProcess.successor runtime.state := rfl

theorem wholeBandFlowRuntimeFace_factorizes (runtime : LivingRuntimeState wholeBandFlowRuntimeProcess) (face : WholeBandFlowFace) :
    type_of% (wholeBandFlowRuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeBandFlowRuntimeFacade.readoutAt_factorizes runtime face

theorem wholeBandFlowRuntime_material_installed (runtime : LivingRuntimeState wholeBandFlowRuntimeProcess) :
    type_of% (wholeBandFlowRuntimeFace_factorizes runtime (.component .material)) ∧
    wholeBandFlowRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeBandFlowLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeBandFlowMaterial)⟩ :
        SourceNativeProjectionFiberAt wholeBandFlowProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeBandFlowRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeBandFlowRuntime_sourceCertificate :
    type_of% (wholeBandFlowRuntimeFace_factorizes wholeBandFlowRuntimeSeed (.component .certificate)) ∧ WholeBandFlowClosure := by
  refine ⟨wholeBandFlowRuntimeFace_factorizes wholeBandFlowRuntimeSeed (.component .certificate), ?_⟩
  rcases wholeBandFlowRuntimeFacade.readoutAt wholeBandFlowRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeBandFlowRuntime_original_forty_four_faces (runtime : LivingRuntimeState wholeBandFlowRuntimeProcess)
    (face : WholeBandRuntime.WholeBandFace) :
    type_of% (wholeBandFlowRuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeBandFlowRuntimeFacade.readoutAt runtime (.inherited face) =
      WholeBandFlowBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeBandFlowRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
