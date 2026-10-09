import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime.Runtime

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

def faceSumEquiv : Projection ≃ Fin 8 ⊕ Coulomb.Runtime.Face where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .clocks => .inl 2 | .history => .inl 3
    | .energy => .inl 4 | .firstActuation => .inl 5 | .readiness => .inl 6 | .wholeLedger => .inl 7
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.clocks,.history,.energy,.firstActuation,.readiness,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 279 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) Coulomb.Runtime.faceEquiv).trans finSumFinEquiv)

theorem actual_history : afterFirst.state.history=seed.state.history.step (compiled_next .ingress) := rfl

theorem actual_energy : type_of% (face_factorizes afterFirst .current) ∧
    Live.baselineEnergy (readCurrent afterFirst).resource.quantum+
      Extract.Port.kinetic (readCurrent afterFirst).resource.momentum+((readCurrent afterFirst).frame.total : ℝ)=
    Live.baselineEnergy (readCurrent seed).resource.quantum+
      Extract.Port.kinetic (readCurrent seed).resource.momentum+((readCurrent seed).frame.total : ℝ) :=
  ⟨face_factorizes afterFirst .current,target_resource_account⟩

theorem actual_entropy_account : type_of% (face_factorizes afterFirst .current) ∧
    Live.freeEnergy (readCurrent afterFirst).resource.quantum+Live.entropyProduction (readCurrent afterFirst).resource.quantum+
      Extract.Port.kinetic (readCurrent afterFirst).resource.momentum+((readCurrent afterFirst).frame.total : ℝ)=
    Live.freeEnergy (readCurrent seed).resource.quantum+Live.entropyProduction (readCurrent seed).resource.quantum+
      Extract.Port.kinetic (readCurrent seed).resource.momentum+((readCurrent seed).frame.total : ℝ) :=
  ⟨face_factorizes afterFirst .current,target_free_energy_entropy_account⟩

theorem actual_realization : type_of% (face_factorizes afterFirst .current) ∧
    (readCurrent afterFirst).realized=(readCurrent afterFirst).held+
      (readCurrent afterFirst).inheritedResidual+(readCurrent afterFirst).newNumericalResidual :=
  ⟨face_factorizes afterFirst .current,generatedReceipt.realization⟩

theorem actual_positive_debit : type_of% (face_factorizes afterFirst .current) ∧
    0 < (readCurrent seed).resource.momentum-(readCurrent afterFirst).resource.momentum := by
  refine ⟨face_factorizes afterFirst .current,?_⟩
  change 0 < initialReceiver-plateauReceiver 1
  unfold plateauReceiver
  linarith only [target_debit_positive_and_bounded.1]

theorem actual_retained_configuration (i : Coordinate) : type_of% (face_factorizes afterFirst .current) ∧
    (readCurrent afterFirst).frame.position i.1 i.2=FiniteActuation.input.joint.body.frame.position i.1 i.2 ∧
    (readCurrent afterFirst).realized=FiniteActuation.input.joint.body.realized ∧
    (readCurrent afterFirst).held=FiniteActuation.input.joint.body.held ∧
    (readCurrent afterFirst).inheritedResidual=FiniteActuation.input.joint.body.inheritedResidual ∧
    (readCurrent afterFirst).newNumericalResidual=FiniteActuation.input.joint.body.newNumericalResidual :=
  ⟨face_factorizes afterFirst .current,target_configuration_preserved i⟩

theorem actual_integrated_update (i : Coordinate) : type_of% (face_factorizes afterFirst .current) ∧
    ((readCurrent afterFirst).frame.momentum i.1 i.2 : ℝ)-((readCurrent seed).frame.momentum i.1 i.2 : ℝ)=
      (∫ t in (0 : ℝ)..duration, nuclearForce .enter t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce .drive t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce .leave t i) :=
  ⟨face_factorizes afterFirst .current,total_momentum_update i⟩

theorem old_transport_is_not_finite_action : readCurrent afterFirst ≠ FiniteActuation.input.joint.body := by
  intro same
  have frame := congrArg (fun body : ActuationResult => body.frame.momentum) same
  exact target_momentum_changed frame

structure InstalledFiniteActuation : Prop where
  source : OriginalFiniteActuation
  parent : Coulomb.Runtime.InstalledJointCoulomb
  input : type_of% input_is_parent
  generatedAnswer : type_of% generated_action_answer
  generatedNext : type_of% generated_action_next
  generatedVisit : type_of% generated_visit
  first : type_of% first_generated
  history : type_of% actual_history
  clocks : type_of% actual_clocks
  generatedBody : type_of% actual_generated
  positive : type_of% actual_positive
  debit : type_of% actual_positive_debit
  nonzero : type_of% actual_nonzero
  energy : type_of% actual_energy
  entropy : type_of% actual_entropy_account
  realization : type_of% actual_realization
  configuration : type_of% actual_retained_configuration
  integrated : type_of% actual_integrated_update
  factorization : type_of% face_factorizes
  inherited : type_of% parent_is_installed
  wholeLedger : type_of% whole_ledger_installed
  noReissue : type_of% action_not_reissued
  retained : type_of% retained_without_tick
  oldTransportDifferent : type_of% old_transport_is_not_finite_action
  allFaces : Nonempty (Projection ≃ Fin 279)

theorem sourceGeneratedFiniteActuation : InstalledFiniteActuation :=
  ⟨action_certificate.2,Coulomb.Runtime.sourceGeneratedJointCoulomb,input_is_parent,
    generated_action_answer,generated_action_next,generated_visit,first_generated,actual_history,
    actual_clocks,actual_generated,actual_positive,actual_positive_debit,actual_nonzero,actual_energy,
    actual_entropy_account,actual_realization,actual_retained_configuration,actual_integrated_update,
    face_factorizes,parent_is_installed,whole_ledger_installed,action_not_reissued,retained_without_tick,
    old_transport_is_not_finite_action,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
