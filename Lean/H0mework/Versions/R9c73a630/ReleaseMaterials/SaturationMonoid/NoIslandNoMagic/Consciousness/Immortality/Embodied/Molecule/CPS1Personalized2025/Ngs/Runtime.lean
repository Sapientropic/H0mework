import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Installation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def process : SourceNativeLivingRootProcess ParentN where
  State := CPS1Personalized2025.Runtime.process.State
  stateAt := fun visit => ⟨ParentV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨ParentV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt ParentN) =
      ⟨ParentV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := CPS1Personalized2025.Runtime.process.initial
  successorAt := by
    intro visit
    refine ⟨CPS1Personalized2025.Runtime.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩; rfl
    · rcases visit with ⟨current,history⟩; exact HEq.rfl

abbrev Face := SourceNativeProjectionCoface Root.Projection Projection

def facade : SourceNativeLivingRuntimeFacade ParentN where
  process := process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .component _ => projectionLaw | .inherited _ => ParentBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => componentInstallation | .inherited _ => inheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face | .inherited face => face

def seed : LivingRuntimeState process := facade.seed
def atParent : LivingRuntimeState process := seed.tick.next.tick.next
def afterParent : LivingRuntimeState process := atParent.tick.next

theorem exact_parent_and_literal_next :
    atParent.state = parentRuntime.state ∧
    atParent.emittedOccurrence = parentRuntime.emittedOccurrence ∧
    afterParent = atParent.tick.next ∧ afterParent.state = parentRuntime.tick.next.state := ⟨rfl,rfl,rfl,rfl⟩

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

theorem original_five_faces_retained (runtime : LivingRuntimeState process) (face : Root.Projection) :
    facade.readoutAt runtime (.inherited face) = ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence := rfl

def readMaterial (runtime : LivingRuntimeState process) : Material :=
  match facade.readoutAt runtime (.component .material) with
  | .inl ⟨_,payload⟩ => payload.2 | .inr impossible => PEmpty.elim impossible

theorem readCertificate (runtime : LivingRuntimeState process) : JointAlleleClosure :=
  match facade.readoutAt runtime (.component .certificate) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_program (runtime : LivingRuntimeState process) : OriginalProgramClosure :=
  match facade.readoutAt runtime (.inherited .certificate) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem readMaterial_eq (runtime : LivingRuntimeState process) : readMaterial runtime = material := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
