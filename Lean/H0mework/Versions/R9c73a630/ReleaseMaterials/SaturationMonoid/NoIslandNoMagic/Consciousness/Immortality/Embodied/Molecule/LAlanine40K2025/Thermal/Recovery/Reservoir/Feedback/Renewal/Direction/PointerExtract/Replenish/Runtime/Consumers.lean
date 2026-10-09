import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime.Invariants
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

def readCurrent (runtime : LivingRuntimeState process) : Material :=
  match facade.readoutAt runtime .current with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

def readNext (runtime : LivingRuntimeState process) : Material :=
  match facade.readoutAt runtime .next with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

theorem actual_sequence : readCurrent seed=Replenish.material ∧ readCurrent afterFirst=suppliedMaterial ∧
    readCurrent afterSecond=Account.output := ⟨rfl,rfl,second_is_execution⟩

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem actual_clocks : (readCurrent seed).quantum.localClock=14*nativeClockStep ∧
    (readCurrent afterFirst).quantum.localClock=15*nativeClockStep ∧
    (readCurrent afterSecond).quantum.localClock=16*nativeClockStep := by
  refine ⟨Replenish.origin_clock,first_clock,?_⟩
  rw [actual_sequence.2.2,Account.output_quantum]
  exact Account.clocks.2

theorem actual_history : afterFirst.state.history=seed.state.history.step rfl ∧
    afterSecond.state.history=afterFirst.state.history.step rfl := ⟨rfl,rfl⟩

theorem actual_joint (runtime : LivingRuntimeState process) :
    (readNext runtime).quantum.joint=Quantum.conjugation (action runtime.state.current) (readCurrent runtime).quantum.joint :=
  next_joint runtime.state.current

theorem actual_first_gain : type_of% (face_factorizes seed .firstSupply) ∧
    type_of% (face_factorizes afterFirst .current) ∧
    (69/100 : ℝ) < pcEnergyOf (bodyRead (readCurrent afterFirst).quantum.joint)-pcEnergyOf (bodyRead (readCurrent seed).quantum.joint) :=
  ⟨supply_certificate.1,face_factorizes afterFirst .current,supply_certificate.2.supplyPositive⟩

theorem actual_net_gain : type_of% (face_factorizes seed .firstSupply) ∧
    type_of% (face_factorizes afterSecond .current) ∧
    (1/2 : ℝ) < pcEnergyOf (bodyRead (readCurrent afterSecond).quantum.joint)-pcEnergyOf (bodyRead (readCurrent seed).quantum.joint) := by
  refine ⟨supply_certificate.1,face_factorizes afterSecond .current,?_⟩
  rw [actual_sequence.2.2,Account.output_quantum]
  exact supply_certificate.2.actualGain

theorem actual_memory (runtime : LivingRuntimeState process) :
    decodedMemory runtime.state.current=oneRead Replenish.origin.joint :=
  (runtime_invariants runtime).2.2.1

theorem complete_account (runtime : LivingRuntimeState process) : type_of% (runtime_complete_account runtime) :=
  runtime_complete_account runtime

theorem complete_debit (runtime : LivingRuntimeState process) : type_of% (runtime_complete_debit runtime) :=
  runtime_complete_debit runtime

theorem actual_empty (runtime : LivingRuntimeState process) : (readCurrent runtime).momentum=0 := runtime_receiver_empty runtime

theorem no_receiver_reissue (runtime : LivingRuntimeState process) :
    Extract.Port.kinetic (readCurrent runtime).momentum=0 := by
  rw [actual_empty,Extract.Port.kinetic,abs_zero]

theorem new_next_not_old_load :
    (readCurrent afterFirst).quantum.joint ≠ (Restore.Runtime.readCurrent Restore.Runtime.afterSecond).quantum.joint :=
  supply_certificate.2.oldLoadDifferent

theorem actual_donor_decrease : type_of% (face_factorizes afterSecond .resources) ∧
    donorRemainingOf (suppliedBlock (readCurrent afterSecond).quantum)<
      donorRemainingOf (suppliedBlock (readCurrent seed).quantum) := by
  refine ⟨face_factorizes afterSecond .resources,?_⟩
  rw [actual_sequence.2.2,Account.output_quantum]
  exact supply_certificate.2.remaining

def faceSumEquiv : Projection ≃ Fin 9 ⊕ Restore.Runtime.Projection where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .joint => .inl 2 | .resources => .inl 3
    | .receiver => .inl 4 | .thermal => .inl 5 | .netAccount => .inl 6 | .firstSupply => .inl 7 | .wholeLedger => .inl 8
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.joint,.resources,.receiver,.thermal,.netAccount,.firstSupply,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 54 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) Restore.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledReplenishment : Prop where
  parent : Restore.Runtime.InstalledPayment
  source : OriginalReplenishment
  generatedAnswer : type_of% generated_action_answer
  generatedNext : type_of% generated_action_next
  generatedVisit : type_of% generated_visit
  sequence : type_of% actual_sequence
  clocks : type_of% actual_clocks
  history : type_of% actual_history
  joint : type_of% actual_joint
  factorization : type_of% face_factorizes
  inherited : type_of% parent_is_installed
  ledger : type_of% whole_ledger_installed
  first : type_of% supply_is_installed
  noReissue : type_of% supply_receipt_not_reissued
  account : type_of% complete_account
  debit : type_of% complete_debit
  finiteBudget : type_of% runtime_finite_budget
  finiteHistory : type_of% all_finite_paid
  memory : type_of% actual_memory
  supplyGain : type_of% actual_first_gain
  executionGain : type_of% actual_net_gain
  donorDecrease : type_of% actual_donor_decrease
  receiver : type_of% actual_empty
  receiverEnergy : type_of% no_receiver_reissue
  oldLoadDifferent : type_of% new_next_not_old_load
  allFaces : Nonempty (Projection ≃ Fin 54)

theorem sourceGeneratedReplenishment : InstalledReplenishment :=
  ⟨Restore.Runtime.sourceGeneratedPointerPayment,supply_certificate.2,generated_action_answer,generated_action_next,
    generated_visit,actual_sequence,actual_clocks,actual_history,actual_joint,face_factorizes,parent_is_installed,
    whole_ledger_installed,supply_is_installed,supply_receipt_not_reissued,complete_account,complete_debit,
    runtime_finite_budget,all_finite_paid,actual_memory,actual_first_gain,actual_net_gain,actual_donor_decrease,
    actual_empty,no_receiver_reissue,new_next_not_old_load,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
