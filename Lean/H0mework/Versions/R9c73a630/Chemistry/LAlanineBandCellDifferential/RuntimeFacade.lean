import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeBandCell0DifferentialSource
noncomputable section

def wholeBandCell0DifferentialRuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeBandCell0Runtime.wholeBandCell0RuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeBandCell0DifferentialLivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeBandCell0DifferentialLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeBandCell0DifferentialLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeBandCell0Runtime.wholeBandCell0RuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeBandCell0Runtime.wholeBandCell0RuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeBandCell0DifferentialFace := SourceNativeProjectionCoface WholeBandCell0Runtime.WholeBandCell0Face WholeBandCell0DifferentialProjection

def wholeBandCell0DifferentialRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeBandCell0DifferentialRuntimeProcess
  FaceAt := fun _ => WholeBandCell0DifferentialFace
  componentAt := fun _ face => match face with
    | .component _ => wholeBandCell0DifferentialProjectionLaw
    | .inherited _ => WholeBandCell0DifferentialBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeBandCell0DifferentialComponentInstallation
    | .inherited _ => wholeBandCell0DifferentialInheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeBandCell0DifferentialRuntimeSeed : LivingRuntimeState wholeBandCell0DifferentialRuntimeProcess := wholeBandCell0DifferentialRuntimeFacade.seed
def wholeBandCell0DifferentialRuntimeAfterFirst : LivingRuntimeState wholeBandCell0DifferentialRuntimeProcess := wholeBandCell0DifferentialRuntimeSeed.tick.next

theorem wholeBandCell0DifferentialRuntime_seed_same_occurrence :
    wholeBandCell0DifferentialRuntimeSeed.emittedOccurrence = WholeBandCell0Runtime.wholeBandCell0RuntimeSeed.emittedOccurrence := rfl
theorem wholeBandCell0DifferentialRuntime_afterFirst_same_visit :
    wholeBandCell0DifferentialRuntimeAfterFirst.current.visit = wholeBandCell0DifferentialParentRuntime.current.visit := rfl
theorem wholeBandCell0DifferentialRuntime_generated_same_next (runtime : LivingRuntimeState wholeBandCell0DifferentialRuntimeProcess) :
    runtime.tick.next.state = WholeBandCell0Runtime.wholeBandCell0RuntimeProcess.successor runtime.state := rfl

theorem wholeBandCell0DifferentialRuntimeFace_factorizes (runtime : LivingRuntimeState wholeBandCell0DifferentialRuntimeProcess) (face : WholeBandCell0DifferentialFace) :
    type_of% (wholeBandCell0DifferentialRuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeBandCell0DifferentialRuntimeFacade.readoutAt_factorizes runtime face

theorem wholeBandCell0DifferentialRuntime_material_installed (runtime : LivingRuntimeState wholeBandCell0DifferentialRuntimeProcess) :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes runtime (.component .material)) ∧
    wholeBandCell0DifferentialRuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeBandCell0DifferentialLedger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeBandCell0DifferentialMaterial)⟩ :
        SourceNativeProjectionFiberAt wholeBandCell0DifferentialProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeBandCell0DifferentialRuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeBandCell0DifferentialRuntime_sourceCertificate :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate)) ∧ WholeBandCell0DifferentialClosure := by
  refine ⟨wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate), ?_⟩
  rcases wholeBandCell0DifferentialRuntimeFacade.readoutAt wholeBandCell0DifferentialRuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeBandCell0DifferentialRuntime_original_forty_eight_faces (runtime : LivingRuntimeState wholeBandCell0DifferentialRuntimeProcess)
    (face : WholeBandCell0Runtime.WholeBandCell0Face) :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeBandCell0DifferentialRuntimeFacade.readoutAt runtime (.inherited face) =
      WholeBandCell0DifferentialBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeBandCell0DifferentialRuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
