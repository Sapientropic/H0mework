import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Installation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def process : SourceNativeLivingRootProcess ParentN where
  State := Ngs.process.State
  stateAt := fun visit => ⟨ParentV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨ParentV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt ParentN) =
      ⟨ParentV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := Ngs.process.initial
  successorAt := by
    intro visit
    refine ⟨Ngs.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩; rfl
    · rcases visit with ⟨current,history⟩; exact HEq.rfl

/-- Nine faces: the five root faces and the two Ngs faces are inherited, and this
module installs its own material/certificate coface. -/
abbrev Face := SourceNativeProjectionCoface Ngs.Face Projection

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

/-- Three ticks: the parent Ngs analysis occupied ticks one and two (its own
`atParent`) plus its literal next; this module's `atParent` is the fourth
analysis current, i.e. exactly the parent runtime state. -/
def atParent : LivingRuntimeState process := seed.tick.next.tick.next.tick.next
def afterParent : LivingRuntimeState process := atParent.tick.next

theorem exact_parent_and_literal_next :
    atParent.state = parentRuntime.state ∧
    atParent.emittedOccurrence = parentRuntime.emittedOccurrence ∧
    afterParent = atParent.tick.next ∧ afterParent.state = parentRuntime.tick.next.state := ⟨rfl,rfl,rfl,rfl⟩

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

theorem original_seven_faces_retained (runtime : LivingRuntimeState process) (face : Ngs.Face) :
    facade.readoutAt runtime (.inherited face) = ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence := rfl

def readMaterial (runtime : LivingRuntimeState process) : Material :=
  match facade.readoutAt runtime (.component .material) with
  | .inl ⟨_,payload⟩ => payload.2 | .inr impossible => PEmpty.elim impossible

theorem readCertificate (runtime : LivingRuntimeState process) : LongitudinalClosure :=
  match facade.readoutAt runtime (.component .certificate) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_joint_alleles (runtime : LivingRuntimeState process) : Ngs.JointAlleleClosure :=
  match facade.readoutAt runtime (.inherited (.component .certificate)) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_program (runtime : LivingRuntimeState process) : OriginalProgramClosure :=
  match facade.readoutAt runtime (.inherited (.inherited .certificate)) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem readMaterial_eq (runtime : LivingRuntimeState process) : readMaterial runtime = material := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
