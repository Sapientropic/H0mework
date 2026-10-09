import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeBandCell0Source
noncomputable section

def wholeBandCell0RuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeBandFlowRuntime.wholeBandFlowRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeBandCell0LivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeBandCell0LivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeBandCell0LivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeBandFlowRuntime.wholeBandFlowRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeBandFlowRuntime.wholeBandFlowRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeBandCell0Face := SourceNativeProjectionCoface WholeBandFlowRuntime.WholeBandFlowFace WholeBandCell0Projection

def wholeBandCell0RuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeBandCell0RuntimeProcess
  FaceAt := fun _ => WholeBandCell0Face
  componentAt := fun _ face => match face with
    | .component _ => wholeBandCell0ProjectionLaw
    | .inherited _ => WholeBandCell0Base.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeBandCell0ComponentInstallation
    | .inherited _ => wholeBandCell0InheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeBandCell0RuntimeSeed : LivingRuntimeState wholeBandCell0RuntimeProcess := wholeBandCell0RuntimeFacade.seed
def wholeBandCell0RuntimeAfterFirst : LivingRuntimeState wholeBandCell0RuntimeProcess := wholeBandCell0RuntimeSeed.tick.next

theorem wholeBandCell0Runtime_seed_same_occurrence :
    wholeBandCell0RuntimeSeed.emittedOccurrence = WholeBandFlowRuntime.wholeBandFlowRuntimeSeed.emittedOccurrence := rfl
theorem wholeBandCell0Runtime_afterFirst_same_visit :
    wholeBandCell0RuntimeAfterFirst.current.visit = wholeBandCell0ParentRuntime.current.visit := rfl
theorem wholeBandCell0Runtime_generated_same_next (runtime : LivingRuntimeState wholeBandCell0RuntimeProcess) :
    runtime.tick.next.state = WholeBandFlowRuntime.wholeBandFlowRuntimeProcess.successor runtime.state := rfl

theorem wholeBandCell0RuntimeFace_factorizes (runtime : LivingRuntimeState wholeBandCell0RuntimeProcess) (face : WholeBandCell0Face) :
    type_of% (wholeBandCell0RuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeBandCell0RuntimeFacade.readoutAt_factorizes runtime face

theorem wholeBandCell0Runtime_material_installed (runtime : LivingRuntimeState wholeBandCell0RuntimeProcess) :
    type_of% (wholeBandCell0RuntimeFace_factorizes runtime (.component .material)) ∧
    wholeBandCell0RuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeBandCell0Ledger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeBandCell0Material)⟩ :
        SourceNativeProjectionFiberAt wholeBandCell0ProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeBandCell0RuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeBandCell0Runtime_sourceCertificate :
    type_of% (wholeBandCell0RuntimeFace_factorizes wholeBandCell0RuntimeSeed (.component .certificate)) ∧ WholeBandCell0Closure := by
  refine ⟨wholeBandCell0RuntimeFace_factorizes wholeBandCell0RuntimeSeed (.component .certificate), ?_⟩
  rcases wholeBandCell0RuntimeFacade.readoutAt wholeBandCell0RuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeBandCell0Runtime_original_forty_six_faces (runtime : LivingRuntimeState wholeBandCell0RuntimeProcess)
    (face : WholeBandFlowRuntime.WholeBandFlowFace) :
    type_of% (wholeBandCell0RuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeBandCell0RuntimeFacade.readoutAt runtime (.inherited face) =
      WholeBandCell0Base.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeBandCell0RuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
