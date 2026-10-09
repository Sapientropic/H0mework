import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.SharpNet.Runtime.Installation
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.SharpNet.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Thermal.Recovery.Runtime
open LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime
noncomputable section

private abbrev ParentProcess :=
  LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime.process
private abbrev ParentProjection :=
  LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime.Projection
private abbrev ParentSeed :=
  LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime.seed

def process : SourceNativeLivingRootProcess RecoveryN where
  State := ParentProcess.State
  stateAt := fun visit => ⟨RenewalV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨RenewalV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨RenewalV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := ParentProcess.initial
  successorAt := by
    intro visit
    refine ⟨ParentProcess.successor visit,?_,?_⟩
    · rfl
    · exact HEq.rfl

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

theorem seed_same_occurrence : seed.emittedOccurrence = ParentSeed.emittedOccurrence := rfl

theorem generated_same_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.state = ParentProcess.successor runtime.state := rfl

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

def readMaterial (runtime : LivingRuntimeState process) : SharpNet.Material :=
  match facade.readoutAt runtime (.component .comparison) with
  | .inl ⟨_,_,material⟩ => material
  | .inr impossible => nomatch impossible

theorem material_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .comparison)) ∧
      readMaterial runtime = SharpNet.material :=
  ⟨face_factorizes runtime (.component .comparison),rfl⟩

theorem all_original_faces (runtime : LivingRuntimeState process) (face : ParentProjection) :
    type_of% (face_factorizes runtime (.inherited face)) ∧
      facade.readoutAt runtime (.inherited face) =
        ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨face_factorizes runtime (.inherited face),rfl⟩

def parentFaceCode : ParentProjection → Fin 9
  | .current => 0
  | .next => 1
  | .joint => 2
  | .resources => 3
  | .thermal => 4
  | .netAccount => 5
  | .parent => 6
  | .firstRenewal => 7
  | .wholeLedger => 8

def parentFaceEquiv : ParentProjection ≃ Fin 9 := Equiv.ofBijective parentFaceCode
  ⟨by
    intro left right same
    cases left <;> cases right <;> simp [parentFaceCode] at same ⊢,
   by
    intro i
    fin_cases i
    all_goals first
      | exact ⟨.current,rfl⟩
      | exact ⟨.next,rfl⟩
      | exact ⟨.joint,rfl⟩
      | exact ⟨.resources,rfl⟩
      | exact ⟨.thermal,rfl⟩
      | exact ⟨.netAccount,rfl⟩
      | exact ⟨.parent,rfl⟩
      | exact ⟨.firstRenewal,rfl⟩
      | exact ⟨.wholeLedger,rfl⟩⟩

def faceSumEquiv : Face ≃ Fin 1 ⊕ Fin 9 where
  toFun := fun face => match face with
    | .component .comparison => .inl 0
    | .inherited face => .inr (parentFaceEquiv face)
  invFun := fun index => match index with
    | .inl _ => .component .comparison
    | .inr i => .inherited (parentFaceEquiv.symm i)
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

def faceEquiv : Face ≃ Fin 10 := faceSumEquiv.trans finSumFinEquiv

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.SharpNet.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
