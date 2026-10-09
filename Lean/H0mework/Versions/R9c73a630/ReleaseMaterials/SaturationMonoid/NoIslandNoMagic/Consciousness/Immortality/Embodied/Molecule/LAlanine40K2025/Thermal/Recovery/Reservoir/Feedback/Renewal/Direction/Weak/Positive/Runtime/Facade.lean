import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Positive.Runtime.Installation
set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Positive.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Thermal.Recovery.Runtime
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
noncomputable section

private abbrev ParentProcess := SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.process
private abbrev ParentProjection := SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.Projection

def process : SourceNativeLivingRootProcess RecoveryN where
  State := ParentProcess.State
  stateAt := fun visit => ⟨WeakV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨WeakV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN)=
      ⟨WeakV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := ParentProcess.initial
  successorAt := fun visit => ⟨ParentProcess.successor visit,rfl,HEq.rfl⟩

abbrev Face := SourceNativeProjectionCoface ParentProjection Projection

def facade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := process
  FaceAt := fun _ => Face
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
def afterSecond : LivingRuntimeState process := afterFirst.tick.next

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

theorem all_original_faces (runtime : LivingRuntimeState process) (face : ParentProjection) :
    type_of% (face_factorizes runtime (.inherited face)) ∧
      facade.readoutAt runtime (.inherited face)=ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨face_factorizes runtime (.inherited face),rfl⟩

theorem generated_same_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.state=ParentProcess.successor runtime.state := rfl

theorem readCertificate (runtime : LivingRuntimeState process) : OriginalNineElevenGain :=
  match facade.readoutAt runtime (.component .originalNineElevenGain) with
  | .inl ⟨_,_,certificate⟩ => certificate.down
  | .inr impossible => nomatch impossible

def readCurrent (runtime : LivingRuntimeState process) : Live.State :=
  match facade.readoutAt runtime (.inherited .current) with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

theorem certificate_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .originalNineElevenGain)) ∧
      readCertificate runtime=sourceOriginalNineElevenGain :=
  ⟨face_factorizes runtime (.component .originalNineElevenGain),rfl⟩

def faceSumEquiv : Face ≃ Fin 1 ⊕ Fin 18 where
  toFun := fun face => match face with
    | .component .originalNineElevenGain => .inl 0
    | .inherited face => .inr (SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl _ => .component .originalNineElevenGain
    | .inr i => .inherited (SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.faceEquiv.symm i)
  left_inv := by
    intro face
    rcases face with face | face
    · cases face; rfl
    · simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro index
    rcases index with i | i
    · fin_cases i; rfl
    · simp only [Equiv.apply_symm_apply]

def faceEquiv : Face ≃ Fin 19 := faceSumEquiv.trans finSumFinEquiv

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Positive.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
