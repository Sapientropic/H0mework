import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Runtime.Installation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def process : SourceNativeLivingRootProcess N where
  State := UnifiedRuntime.process.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := UnifiedRuntime.process.initial
  successorAt := by
    intro visit
    refine ⟨UnifiedRuntime.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩
      cases current <;> rfl
    · rcases visit with ⟨current,history⟩
      cases current <;> exact HEq.rfl

abbrev BasinFace := SourceNativeProjectionCoface UnifiedRuntime.UnifiedFace BasinProjection

def facade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _ => BasinFace
  componentAt := fun _ face => match face with
    | .component _ => projectionLaw
    | .inherited _ => ParentBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => componentInstallation
    | .inherited _ => inheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face
    | .inherited face => face

def seed : LivingRuntimeState process := facade.seed
def afterFirst : LivingRuntimeState process := seed.tick.next

theorem seed_same_occurrence : seed.emittedOccurrence = UnifiedRuntime.seed.emittedOccurrence := rfl
theorem afterFirst_same_visit : afterFirst.current.visit = parentRuntime.current.visit := rfl

theorem generated_same_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.state = UnifiedRuntime.process.successor runtime.state := rfl

theorem face_factorizes (runtime : LivingRuntimeState process) (face : BasinFace) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

def readMaterial (runtime : LivingRuntimeState process) : BasinInstalledMaterial :=
  match facade.readoutAt runtime (.component .material) with
  | .inl ⟨_,_,material⟩ => material
  | .inr impossible => nomatch impossible

theorem material_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧ readMaterial runtime = generatedMaterial :=
  ⟨face_factorizes runtime (.component .material),rfl⟩

theorem certificate_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧ WholeBandBasin.BasinClosure := by
  refine ⟨face_factorizes runtime (.component .certificate),?_⟩
  rcases facade.readoutAt runtime (.component .certificate) with ⟨_,received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem all_original_faces (runtime : LivingRuntimeState process) (face : UnifiedRuntime.UnifiedFace) :
    type_of% (face_factorizes runtime (.inherited face)) ∧
    facade.readoutAt runtime (.inherited face) = ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨face_factorizes runtime (.inherited face),rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
