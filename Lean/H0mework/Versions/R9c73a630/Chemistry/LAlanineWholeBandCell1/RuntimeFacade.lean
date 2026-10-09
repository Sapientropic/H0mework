import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.RuntimeInstallation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root WholeBandCell1Source
noncomputable section

def wholeBandCell1RuntimeProcess : SourceNativeLivingRootProcess N where
  State := WholeBandCell0SpatialRuntime.wholeBandCell0SpatialRuntimeProcess.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV, wholeBandCell1LivingRoot, .finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV, wholeBandCell1LivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV, wholeBandCell1LivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := WholeBandCell0SpatialRuntime.wholeBandCell0SpatialRuntimeProcess.initial
  successorAt := by
    intro visit
    refine ⟨WholeBandCell0SpatialRuntime.wholeBandCell0SpatialRuntimeProcess.successor visit, ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

abbrev WholeBandCell1Face := SourceNativeProjectionCoface WholeBandCell0SpatialRuntime.WholeBandCell0SpatialFace WholeBandCell1Projection

def wholeBandCell1RuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := wholeBandCell1RuntimeProcess
  FaceAt := fun _ => WholeBandCell1Face
  componentAt := fun _ face => match face with
    | .component _ => wholeBandCell1ProjectionLaw
    | .inherited _ => WholeBandCell1Base.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => wholeBandCell1ComponentInstallation
    | .inherited _ => wholeBandCell1InheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def wholeBandCell1RuntimeSeed : LivingRuntimeState wholeBandCell1RuntimeProcess := wholeBandCell1RuntimeFacade.seed
def wholeBandCell1RuntimeAfterFirst : LivingRuntimeState wholeBandCell1RuntimeProcess := wholeBandCell1RuntimeSeed.tick.next

theorem wholeBandCell1Runtime_seed_same_occurrence :
    wholeBandCell1RuntimeSeed.emittedOccurrence = WholeBandCell0SpatialRuntime.wholeBandCell0SpatialRuntimeSeed.emittedOccurrence := rfl
theorem wholeBandCell1Runtime_afterFirst_same_visit :
    wholeBandCell1RuntimeAfterFirst.current.visit = wholeBandCell1ParentRuntime.current.visit := rfl
theorem wholeBandCell1Runtime_generated_same_next (runtime : LivingRuntimeState wholeBandCell1RuntimeProcess) :
    runtime.tick.next.state = WholeBandCell0SpatialRuntime.wholeBandCell0SpatialRuntimeProcess.successor runtime.state := rfl

theorem wholeBandCell1RuntimeFace_factorizes (runtime : LivingRuntimeState wholeBandCell1RuntimeProcess) (face : WholeBandCell1Face) :
    type_of% (wholeBandCell1RuntimeFacade.readoutAt_factorizes runtime face) :=
  wholeBandCell1RuntimeFacade.readoutAt_factorizes runtime face

theorem wholeBandCell1Runtime_material_installed (runtime : LivingRuntimeState wholeBandCell1RuntimeProcess) :
    type_of% (wholeBandCell1RuntimeFace_factorizes runtime (.component .material)) ∧
    wholeBandCell1RuntimeFacade.readoutAt runtime (.component .material) =
      (.inl ⟨PUnit.unit, (WholeBandCell1Ledger.ledgerCompiler.compile runtime.emittedOccurrence, generatedWholeBandCell1Material)⟩ :
        SourceNativeProjectionFiberAt wholeBandCell1ProjectionLaw .material runtime.emittedOccurrence) :=
  ⟨wholeBandCell1RuntimeFace_factorizes runtime (.component .material), rfl⟩

theorem wholeBandCell1Runtime_sourceCertificate :
    type_of% (wholeBandCell1RuntimeFace_factorizes wholeBandCell1RuntimeSeed (.component .certificate)) ∧ WholeBandCell1Closure := by
  refine ⟨wholeBandCell1RuntimeFace_factorizes wholeBandCell1RuntimeSeed (.component .certificate), ?_⟩
  rcases wholeBandCell1RuntimeFacade.readoutAt wholeBandCell1RuntimeSeed (.component .certificate) with ⟨_, received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem wholeBandCell1Runtime_original_fifty_two_faces (runtime : LivingRuntimeState wholeBandCell1RuntimeProcess)
    (face : WholeBandCell0SpatialRuntime.WholeBandCell0SpatialFace) :
    type_of% (wholeBandCell1RuntimeFace_factorizes runtime (.inherited face)) ∧
    wholeBandCell1RuntimeFacade.readoutAt runtime (.inherited face) =
      WholeBandCell1Base.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨wholeBandCell1RuntimeFace_factorizes runtime (.inherited face), rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
