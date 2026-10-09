import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime.Runtime

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

def bodyFaceEquiv : Reentry.Runtime.ReentryProjection ≃ Fin 12 where
  toFun := fun face => match face with
    | .physical => 0 | .history => 1 | .clock => 2 | .held => 3 | .realization => 4 | .generator => 5
    | .gradient => 6 | .residual => 7 | .mode => 8 | .firstReentry => 9 | .readiness => 10 | .wholeLedger => 11
  invFun := fun i => ![.physical,.history,.clock,.held,.realization,.generator,.gradient,.residual,
    .mode,.firstReentry,.readiness,.wholeLedger] i
  left_inv := by intro face; cases face <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def faceSumEquiv : Projection ≃ Fin 8 ⊕ (ControlRecovery.Runtime.Projection ⊕ Reentry.Runtime.ReentryProjection) where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .clocks => .inl 2 | .history => .inl 3
    | .energy => .inl 4 | .firstActuation => .inl 5 | .readiness => .inl 6 | .wholeLedger => .inl 7
    | .parent face => .inr (.inl face) | .bodyParent face => .inr (.inr face)
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.clocks,.history,.energy,.firstActuation,.readiness,.wholeLedger] i
    | .inr (.inl face) => .parent face | .inr (.inr face) => .bodyParent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | (face | face)
    · fin_cases i <;> rfl
    · rfl
    · rfl

def faceEquiv : Projection ≃ Fin 83 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr ControlRecovery.Runtime.faceEquiv bodyFaceEquiv).trans finSumFinEquiv)).trans finSumFinEquiv)

theorem actual_history : afterFirst.state.history=seed.state.history.step (compiled_next .ingress) := rfl

theorem actual_resource_energy : type_of% (face_factorizes afterFirst .current) ∧
    Thermal.Collision.energy Thermal.Recovery.Reservoir.Pointer.baselineHamiltonian (readCurrent afterFirst).resource.quantum.joint+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic (readCurrent afterFirst).resource.momentum+
      ((readCurrent afterFirst).frame.total : ℝ)=
    Thermal.Recovery.Reservoir.Pointer.Live.baselineEnergy resourceBefore.quantum+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic receiverInitial+
      (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential := by
  refine ⟨face_factorizes afterFirst .current,?_⟩
  rw [first_generated,generated_action_answer]
  change Thermal.Collision.energy Thermal.Recovery.Reservoir.Pointer.baselineHamiltonian resourceAfter.quantum.joint+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic receiverTarget+(targetFrame.total : ℝ)=_
  rw [← resource_path_target]
  exact combined_target_energy

theorem actual_realization : type_of% (face_factorizes afterFirst .current) ∧
    (readCurrent afterFirst).realized=(readCurrent afterFirst).held+
      (readCurrent afterFirst).inheritedResidual+(readCurrent afterFirst).newNumericalResidual := by
  refine ⟨face_factorizes afterFirst .current,?_⟩
  rw [first_generated,generated_action_answer]
  exact source_output_realization

theorem old_load_is_not_joint_action :
    (readCurrent afterFirst).resource.momentum ≠
      (ControlRecovery.Runtime.readNext ControlRecovery.Runtime.afterSecond).momentum := by
  have nextRead (runtime : LivingRuntimeState ControlRecovery.Runtime.process) :
      ControlRecovery.Runtime.readNext runtime=ControlRecovery.Runtime.readCurrent runtime.tick.next := rfl
  have sourceRead : resourceBefore=ControlRecovery.Runtime.readCurrent ControlRecovery.Runtime.afterSecond := rfl
  have initialReceiver : resourceBefore.momentum=ControlRecovery.Receiver.output.momentum :=
    (congrArg Material.momentum sourceRead).trans
      (ControlRecovery.Runtime.actual_receiver_stored ControlRecovery.Runtime.afterFirst)
  have nextReceiver : (ControlRecovery.Runtime.readNext ControlRecovery.Runtime.afterSecond).momentum=
      resourceBefore.momentum :=
    ((congrArg Material.momentum (nextRead ControlRecovery.Runtime.afterSecond)).trans
      (ControlRecovery.Runtime.actual_receiver_stored ControlRecovery.Runtime.afterSecond)).trans initialReceiver.symm
  rw [first_generated,generated_action_answer,nextReceiver]
  exact body_resource_not_unchanged

structure InstalledJointActuation : Prop where
  source : OriginalJointActuation
  parent : ControlRecovery.Runtime.InstalledControlExtraction
  generatedAnswer : type_of% generated_action_answer
  generatedNext : type_of% generated_action_next
  generatedVisit : type_of% generated_visit
  first : type_of% first_generated
  history : type_of% actual_history
  clocks : type_of% actual_clocks
  generatedBody : ∀ i, type_of% (actual_generated i)
  positive : type_of% actual_positive
  nonzero : type_of% actual_nonzero
  energy : type_of% actual_resource_energy
  realization : type_of% actual_realization
  factorization : type_of% face_factorizes
  parentFaces : type_of% parent_is_installed
  bodyFaces : type_of% body_parent_is_installed
  wholeLedger : type_of% whole_ledger_installed
  noReissue : type_of% action_not_reissued
  retained : type_of% retained_without_tick
  oldLoadDifferent : type_of% old_load_is_not_joint_action
  allFaces : Nonempty (Projection ≃ Fin 83)

theorem sourceGeneratedJointActuation : InstalledJointActuation :=
  ⟨action_certificate.2,ControlRecovery.Runtime.sourceGeneratedControlExtraction,
    generated_action_answer,generated_action_next,generated_visit,first_generated,actual_history,
    actual_clocks,actual_generated,actual_positive,actual_nonzero,actual_resource_energy,actual_realization,
    face_factorizes,parent_is_installed,body_parent_is_installed,whole_ledger_installed,
    action_not_reissued,retained_without_tick,old_load_is_not_joint_action,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
