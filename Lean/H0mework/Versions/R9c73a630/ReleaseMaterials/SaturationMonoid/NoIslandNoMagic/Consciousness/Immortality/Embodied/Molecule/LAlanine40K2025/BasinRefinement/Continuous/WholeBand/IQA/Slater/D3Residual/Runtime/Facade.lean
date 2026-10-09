import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.D3Residual.Runtime.Installation
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.D3Residual.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def process : SourceNativeLivingRootProcess N where
  State := Slater.Runtime.process.State
  stateAt := fun visit => ⟨Reentry.Runtime.ReentryV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨Reentry.Runtime.ReentryV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨Reentry.Runtime.ReentryV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := Slater.Runtime.process.initial
  successorAt := by
    intro visit
    refine ⟨Slater.Runtime.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩
      cases current <;> rfl
    · rcases visit with ⟨current,history⟩
      cases current <;> exact HEq.rfl

abbrev Face := SourceNativeProjectionCoface Slater.Runtime.Face Projection

def facade : SourceNativeLivingRuntimeFacade N where
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

theorem seed_same_occurrence : seed.emittedOccurrence = Slater.Runtime.seed.emittedOccurrence := rfl
theorem afterFirst_same_visit : afterFirst.current.visit = parentRuntime.current.visit := rfl

theorem generated_same_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.state = Slater.Runtime.process.successor runtime.state := rfl

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

def readMaterial (runtime : LivingRuntimeState process) : D3Residual.Material :=
  match facade.readoutAt runtime (.component .material) with
  | .inl ⟨_,_,material⟩ => material
  | .inr impossible => nomatch impossible

theorem material_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
      readMaterial runtime = D3Residual.material :=
  ⟨face_factorizes runtime (.component .material),rfl⟩

theorem certificate_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧ D3Residual.Closure := by
  refine ⟨face_factorizes runtime (.component .certificate),?_⟩
  rcases facade.readoutAt runtime (.component .certificate) with ⟨_,received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem all_original_faces (runtime : LivingRuntimeState process) (face : Slater.Runtime.Face) :
    type_of% (face_factorizes runtime (.inherited face)) ∧
    facade.readoutAt runtime (.inherited face) =
      ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨face_factorizes runtime (.inherited face),rfl⟩

def faceSumEquiv : Face ≃ Fin 2 ⊕ Fin 140 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (Slater.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (Slater.Runtime.faceEquiv.symm i)
  left_inv := by
    intro face
    rcases face with face | face
    · cases face <;> rfl
    · simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro index
    rcases index with i | i
    · fin_cases i <;> rfl
    · simp only [Equiv.apply_symm_apply]

def faceEquiv : Face ≃ Fin 142 := faceSumEquiv.trans finSumFinEquiv
def faceAt (i : Fin 142) : Face := faceEquiv.symm i
def faceIndex (face : Face) : Fin 142 := faceEquiv face
theorem face_at_index (face : Face) : faceAt (faceIndex face) = face :=
  faceEquiv.symm_apply_apply face
theorem face_index_at (i : Fin 142) : faceIndex (faceAt i) = i :=
  faceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.D3Residual.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
