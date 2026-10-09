import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime.Installation

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

def process : SourceNativeLivingRootProcess RecoveryN where
  State := FiniteContinuation.Runtime.process.State
  stateAt := fun visit => ⟨FiniteContinuation.Runtime.BodyV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨FiniteContinuation.Runtime.BodyV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN)=
      ⟨FiniteContinuation.Runtime.BodyV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := FiniteContinuation.Runtime.process.initial
  successorAt := by
    intro visit
    refine ⟨FiniteContinuation.Runtime.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩
      rfl
    · rcases visit with ⟨current,history⟩
      exact HEq.rfl

abbrev Face := SourceNativeProjectionCoface FiniteContinuation.Runtime.Projection Projection

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

theorem seed_same_occurrence : seed.emittedOccurrence=FiniteContinuation.Runtime.seed.emittedOccurrence := rfl

theorem generated_same_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.state=FiniteContinuation.Runtime.process.successor runtime.state := rfl

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

def readWork (runtime : LivingRuntimeState process) : WorkReadout :=
  match facade.readoutAt runtime (.component .work) with
  | .inl ⟨_,_,work⟩ => work
  | .inr impossible => nomatch impossible

def readCurrent (runtime : LivingRuntimeState process) : FiniteContinuation.Material :=
  match facade.readoutAt runtime (.inherited .current) with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

theorem work_read (runtime : LivingRuntimeState process) : readWork runtime=workOf (readCurrent runtime) := rfl

theorem current_read (runtime : LivingRuntimeState process) : readCurrent runtime=runtime.state.current.1 := rfl

theorem next_read (runtime : LivingRuntimeState process) :
    readCurrent runtime.tick.next=FiniteContinuation.nextMaterial (readCurrent runtime) := rfl

theorem certificate_read (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧ CalibratedAction runtime.state.current := by
  refine ⟨face_factorizes runtime _,?_⟩
  rcases facade.readoutAt runtime (.component .certificate) with ⟨_,received⟩ | impossible
  · exact received.down
  · exact PEmpty.elim impossible

theorem all_parent_faces (runtime : LivingRuntimeState process) (face : FiniteContinuation.Runtime.Projection) :
    type_of% (face_factorizes runtime (.inherited face)) ∧
    facade.readoutAt runtime (.inherited face)=ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨face_factorizes runtime _,rfl⟩

def faceSumEquiv : Face ≃ Fin 2 ⊕ Fin 287 where
  toFun := fun face => match face with
    | .component .work => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (FiniteContinuation.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i=0 then .component .work else .component .certificate
    | .inr i => .inherited (FiniteContinuation.Runtime.faceEquiv.symm i)
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

def faceEquiv : Face ≃ Fin 289 := faceSumEquiv.trans finSumFinEquiv

def materialHistory (depth : Nat) : SourceGeneratedRuntimeMaterialHistoryAt seed depth :=
  SourceGeneratedRuntimeMaterialHistoryAt.generate seed depth

def atDepth (depth : Nat) : LivingRuntimeState process := (materialHistory depth).target

theorem depth_zero : atDepth 0=seed := rfl

theorem depth_succ (depth : Nat) : atDepth (depth+1)=(atDepth depth).tick.next := rfl

theorem history_factorizes (depth : Nat) : type_of% (materialHistory depth).target_factorizes :=
  (materialHistory depth).target_factorizes

theorem current_history_unchanged (depth : Nat) :
    readCurrent (atDepth depth)=FiniteContinuation.Runtime.readCurrent (FiniteContinuation.Runtime.atDepth depth) := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      rw [depth_succ,FiniteContinuation.Runtime.depth_succ,next_read,FiniteContinuation.Runtime.next_current,prior]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime
