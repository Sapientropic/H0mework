import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime.Installation
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open BasinRefinement.WholeBandBasin.Family.All
noncomputable section

def process : SourceNativeLivingRootProcess RecoveryN where
  State := ReceiverBody.Runtime.process.State
  stateAt := fun visit => ⟨ReceiverBody.Runtime.BodyV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨ReceiverBody.Runtime.BodyV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN)=
      ⟨ReceiverBody.Runtime.BodyV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := ReceiverBody.Runtime.process.initial
  successorAt := by
    intro visit
    refine ⟨ReceiverBody.Runtime.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩
      cases current <;> rfl
    · rcases visit with ⟨current,history⟩
      cases current <;> exact HEq.rfl

abbrev Face := SourceNativeProjectionCoface ReceiverBody.Runtime.Projection Projection

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

theorem seed_same_occurrence : seed.emittedOccurrence=ReceiverBody.Runtime.seed.emittedOccurrence := rfl

theorem generated_same_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.state=ReceiverBody.Runtime.process.successor runtime.state := rfl

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

theorem next_ready (runtime : LivingRuntimeState process) : Ready runtime.tick.next.state.current := by
  have keeps : ∀ {state : process.State}, SourceNativeRuntimeReachableAt process state →
      state.current=.ingress ∨ state.current=.ready ReceiverBody.Runtime.sourceOutput := by
    intro state reachable
    induction reachable with
    | initial => exact .inl rfl
    | step prior kept =>
      change ReceiverBody.Runtime.nextCurrent _=.ingress ∨
        ReceiverBody.Runtime.nextCurrent _=.ready ReceiverBody.Runtime.sourceOutput
      rcases kept with initial | ready
      · rw [initial]; exact .inr rfl
      · rw [ready]; exact .inr rfl
  change Ready (ReceiverBody.Runtime.nextCurrent runtime.state.current)
  rcases keeps runtime.reachable with initial | ready
  · rw [initial]; exact rfl
  · rw [ready]; exact rfl

theorem first_ready : Ready afterFirst.state.current := next_ready seed

def readMaterial (runtime : LivingRuntimeState process) (ready : Ready runtime.state.current) : Spatial.Material :=
  match facade.readoutAt runtime (.component (.component .material)) with
  | .inl ⟨_,_,material⟩ => material
  | .inr impossible => False.elim (impossible.down ready)

theorem material_read (runtime : LivingRuntimeState process) (ready : Ready runtime.state.current) :
    type_of% (face_factorizes runtime (.component (.component .material))) ∧
    readMaterial runtime ready=materialOf (ReceiverBody.Runtime.currentResult runtime.state.current) := by
  refine ⟨face_factorizes runtime _,?_⟩
  change readMaterial runtime ready=materialOf
    (ReceiverBody.Runtime.currentResult runtime.current.visit.current)
  have active : Ready runtime.current.visit.current := ready
  simp only [readMaterial,SourceNativeLivingRuntimeFacade.readoutAt,facade,
    SourceNativeProjectionLaw.outcomeAt,projectionLaw,dif_pos active]

theorem certificate_read (runtime : LivingRuntimeState process) (ready : Ready runtime.state.current) :
    type_of% (face_factorizes runtime (.component (.component .certificate))) ∧
    Spatial.Closure (readMaterial runtime ready) := by
  refine ⟨face_factorizes runtime _,?_⟩
  rw [(material_read runtime ready).2]
  rcases facade.readoutAt runtime (.component (.component .certificate)) with ⟨_,received⟩ | impossible
  · exact received.down
  · exact False.elim (impossible.down ready)

theorem all_joint_faces (runtime : LivingRuntimeState process) (face : ReceiverBody.Runtime.Projection) :
    type_of% (face_factorizes runtime (.inherited face)) ∧
    facade.readoutAt runtime (.inherited face)=
      ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence :=
  ⟨face_factorizes runtime _,rfl⟩

def projectionSumEquiv : Projection ≃ Fin 2 ⊕ Fin 184 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (PreciseAtomicIQA.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i=0 then .component .material else .component .certificate
    | .inr i => .inherited (PreciseAtomicIQA.Runtime.faceEquiv.symm i)
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

def projectionEquiv : Projection ≃ Fin 186 := projectionSumEquiv.trans finSumFinEquiv

def faceSumEquiv : Face ≃ Fin 186 ⊕ Fin 83 where
  toFun := fun face => match face with
    | .component face => .inl (projectionEquiv face)
    | .inherited face => .inr (ReceiverBody.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl i => .component (projectionEquiv.symm i)
    | .inr i => .inherited (ReceiverBody.Runtime.faceEquiv.symm i)
  left_inv := by
    intro face
    rcases face with face | face <;> simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro index
    rcases index with i | i <;> simp only [Equiv.apply_symm_apply]

def faceEquiv : Face ≃ Fin 269 := faceSumEquiv.trans finSumFinEquiv

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime
