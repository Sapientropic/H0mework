import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime.Invariants
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
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

theorem actual_sequence : readCurrent seed=ControlRecovery.material ∧ readCurrent afterFirst=Receiver.output ∧
    readCurrent afterSecond=loadNext Receiver.output := ⟨rfl,rfl,rfl⟩

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem actual_clocks : (readCurrent seed).quantum.localClock=16*nativeClockStep ∧
    (readCurrent afterFirst).quantum.localClock=17*nativeClockStep ∧
    (readCurrent afterSecond).quantum.localClock=18*nativeClockStep :=
  ⟨ControlRecovery.origin_clock,first_clock,second_clock⟩

theorem actual_history : afterFirst.state.history=seed.state.history.step rfl ∧
    afterSecond.state.history=afterFirst.state.history.step rfl := ⟨rfl,rfl⟩

theorem actual_joint (runtime : LivingRuntimeState process) :
    (readNext runtime).quantum.joint=Quantum.conjugation (action runtime.state.current) (readCurrent runtime).quantum.joint :=
  next_joint runtime.state.current

theorem actual_first_action : type_of% (face_factorizes afterFirst .current) ∧
    (readCurrent afterFirst).quantum.action=
      Receiver.coupledPulse (nativeClockStep : ℝ)*(readCurrent seed).quantum.action :=
  ⟨face_factorizes afterFirst .current,generatedReceipt.actualAction⟩

theorem actual_first_gain : type_of% (face_factorizes seed .firstControl) ∧
    type_of% (face_factorizes afterFirst .current) ∧
    (2/25 : ℝ) < Extract.Port.kinetic (readCurrent afterFirst).momentum-Extract.Port.kinetic (readCurrent seed).momentum :=
  ⟨control_certificate.1,face_factorizes afterFirst .current,control_certificate.2.actualGain⟩

theorem actual_retained_gain : type_of% (face_factorizes seed .firstControl) ∧
    type_of% (face_factorizes afterSecond .current) ∧
    (2/25 : ℝ) < Extract.Port.kinetic (readCurrent afterSecond).momentum-Extract.Port.kinetic (readCurrent seed).momentum :=
  ⟨control_certificate.1,face_factorizes afterSecond .current,control_certificate.2.actualGain⟩

theorem actual_memory (runtime : LivingRuntimeState process) :
    decodedMemory runtime.state.current=oneRead ControlRecovery.origin.joint :=
  (runtime_invariants runtime).2.2.1

theorem complete_account (runtime : LivingRuntimeState process) : type_of% (runtime_complete_account runtime) :=
  runtime_complete_account runtime

theorem complete_debit (runtime : LivingRuntimeState process) : type_of% (runtime_complete_debit runtime) :=
  runtime_complete_debit runtime

theorem actual_receiver_stored (runtime : LivingRuntimeState process) :
    (readCurrent runtime.tick.next).momentum=Receiver.output.momentum := runtime_receiver_stored runtime

theorem actual_receiver_positive (runtime : LivingRuntimeState process) :
    (2/25 : ℝ) < Extract.Port.kinetic (readCurrent runtime.tick.next).momentum := runtime_receiver_positive runtime

theorem no_receiver_reissue (runtime : LivingRuntimeState process) :
    (readCurrent runtime.tick.next.tick.next).momentum=(readCurrent runtime.tick.next).momentum := by
  have kept := congrArg Material.momentum (next_is_load runtime)
  exact kept

theorem new_next_not_old_load :
    (readCurrent afterFirst).quantum ≠ (Replenish.Runtime.readNext Replenish.Runtime.afterSecond).quantum :=
  control_certificate.2.oldLoadDifferent

theorem no_new_donor_debit (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .resources) ∧
    donorRemainingOf (suppliedBlock (readCurrent runtime.tick.next).quantum)=
      donorRemainingOf (suppliedBlock (readCurrent runtime).quantum) :=
  ⟨face_factorizes runtime .resources,next_remaining runtime.state.current⟩

def faceSumEquiv : Projection ≃ Fin 9 ⊕ Replenish.Runtime.Projection where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .joint => .inl 2 | .resources => .inl 3
    | .receiver => .inl 4 | .thermal => .inl 5 | .netAccount => .inl 6 | .firstControl => .inl 7 | .wholeLedger => .inl 8
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.joint,.resources,.receiver,.thermal,.netAccount,.firstControl,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 63 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) Replenish.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledControlExtraction : Prop where
  parent : Replenish.Runtime.InstalledReplenishment
  source : OriginalControlExtraction
  generatedAnswer : type_of% generated_action_answer
  generatedNext : type_of% generated_action_next
  generatedVisit : type_of% generated_visit
  sequence : type_of% actual_sequence
  clocks : type_of% actual_clocks
  history : type_of% actual_history
  joint : type_of% actual_joint
  actualAction : type_of% actual_first_action
  factorization : type_of% face_factorizes
  inherited : type_of% parent_is_installed
  ledger : type_of% whole_ledger_installed
  first : type_of% control_is_installed
  noReissue : type_of% control_receipt_not_reissued
  account : type_of% complete_account
  debit : type_of% complete_debit
  finiteBudget : type_of% runtime_finite_budget
  finiteHistory : type_of% all_finite_paid
  memory : type_of% actual_memory
  firstGain : type_of% actual_first_gain
  retainedGain : type_of% actual_retained_gain
  noNewDebit : type_of% no_new_donor_debit
  receiver : type_of% actual_receiver_stored
  positive : type_of% actual_receiver_positive
  noNewReceiver : type_of% no_receiver_reissue
  oldLoadDifferent : type_of% new_next_not_old_load
  allFaces : Nonempty (Projection ≃ Fin 63)

theorem sourceGeneratedControlExtraction : InstalledControlExtraction :=
  ⟨Replenish.Runtime.sourceGeneratedReplenishment,control_certificate.2,generated_action_answer,generated_action_next,
    generated_visit,actual_sequence,actual_clocks,actual_history,actual_joint,actual_first_action,face_factorizes,parent_is_installed,
    whole_ledger_installed,control_is_installed,control_receipt_not_reissued,complete_account,complete_debit,
    runtime_finite_budget,all_finite_paid,actual_memory,actual_first_gain,actual_retained_gain,no_new_donor_debit,
    actual_receiver_stored,actual_receiver_positive,no_receiver_reissue,new_next_not_old_load,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
