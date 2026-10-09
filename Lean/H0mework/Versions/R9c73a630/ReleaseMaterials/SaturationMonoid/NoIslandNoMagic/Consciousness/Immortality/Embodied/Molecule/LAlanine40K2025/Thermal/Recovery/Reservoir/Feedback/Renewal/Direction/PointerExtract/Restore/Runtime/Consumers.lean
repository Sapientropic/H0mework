import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime.Invariants

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime
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

theorem actual_sequence : readCurrent seed=input ∧ readCurrent afterFirst=output ∧
    readCurrent afterSecond=loadNext output := ⟨rfl,rfl,rfl⟩

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem actual_clocks : (readCurrent seed).quantum.localClock=13*nativeClockStep ∧
    (readCurrent afterFirst).quantum.localClock=14*nativeClockStep ∧
    (readCurrent afterSecond).quantum.localClock=15*nativeClockStep := by
  refine ⟨PointerExtract.Runtime.actual_clocks.2.1,first_clock,?_⟩
  change output.quantum.localClock+nativeClockStep=15*nativeClockStep
  rw [output_clock]
  ring

theorem actual_history : afterFirst.state.history=seed.state.history.step rfl ∧
    afterSecond.state.history=afterFirst.state.history.step rfl := ⟨rfl,rfl⟩

theorem actual_joint (runtime : LivingRuntimeState process) :
    (readNext runtime).quantum.joint=Quantum.conjugation (action runtime.state.current) (readCurrent runtime).quantum.joint :=
  next_joint runtime.state.current

theorem actual_demand : 0 < Extract.Port.kinetic (readCurrent seed).momentum-
    Extract.Port.kinetic (readCurrent afterFirst).momentum := payment_certificate.2.demand

theorem actual_empty : (readCurrent afterFirst).momentum=0 := payment_certificate.2.emptied

theorem actual_payment : pointerEnergy (readCurrent afterFirst).quantum.joint-
    pointerEnergy (readCurrent seed).quantum.joint=Extract.Port.kinetic (readCurrent seed).momentum :=
  payment_certificate.2.pointerPayment

theorem actual_body : bodyRead (readCurrent afterFirst).quantum.joint=bodyRead (readCurrent seed).quantum.joint :=
  payment_certificate.2.body

theorem actual_restoration : (readCurrent afterFirst).quantum.joint=sourceEntry.quantum.joint :=
  payment_certificate.2.restoration

theorem actual_branch_history : loadBlock (readCurrent afterFirst).quantum=loadBlock sourceEntry.quantum ∧
    suppliedBlock (readCurrent afterFirst).quantum=suppliedBlock sourceEntry.quantum :=
  payment_certificate.2.branches

theorem actual_memory (runtime : LivingRuntimeState process) :
    decodedMemory runtime.state.current=oneRead sourceEntry.quantum.joint := by
  have memory := (runtime_invariants runtime).2.2.1
  change decodedMemory runtime.state.current=zeroRead input.quantum.joint at memory
  exact memory.trans (next_pointer_zero sourceEntry)

theorem complete_account (runtime : LivingRuntimeState process) : type_of% (runtime_complete_account runtime) :=
  runtime_complete_account runtime

theorem complete_debit (runtime : LivingRuntimeState process) : type_of% (runtime_complete_debit runtime) :=
  runtime_complete_debit runtime

theorem consumed_receiver (runtime : LivingRuntimeState process) :
    (readCurrent runtime.tick.next).momentum=0 :=
  (runtime_invariants runtime.tick.next).2.2.2

theorem no_reissue_energy (runtime : LivingRuntimeState process) :
    Extract.Port.kinetic (readCurrent runtime.tick.next).momentum=0 := by
  rw [consumed_receiver,Extract.Port.kinetic,abs_zero]

theorem new_next_not_old_load :
    (readCurrent afterFirst).quantum.joint ≠ (PointerExtract.Runtime.readCurrent PointerExtract.Runtime.afterSecond).quantum.joint := by
  intro same
  have reads := congrArg pointerEnergy same
  change pointerEnergy output.quantum.joint=pointerEnergy (Live.loadNext input.quantum).joint at reads
  have preserved : pointerEnergy (Live.loadNext input.quantum).joint=pointerEnergy input.quantum.joint := by
    unfold pointerEnergy
    rw [Live.loadNext_pointer_one]
  rw [preserved] at reads
  have strict := pointer_recharge_positive
  linarith only [reads,strict]

def faceSumEquiv : Projection ≃ Fin 9 ⊕ PointerExtract.Runtime.Projection where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .joint => .inl 2 | .resources => .inl 3
    | .receiver => .inl 4 | .thermal => .inl 5 | .netAccount => .inl 6 | .firstPayment => .inl 7 | .wholeLedger => .inl 8
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.joint,.resources,.receiver,.thermal,.netAccount,.firstPayment,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 45 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) PointerExtract.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledPayment : Prop where
  parent : PointerExtract.Runtime.InstalledReceiver
  source : OriginalPayment
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
  first : type_of% payment_is_installed
  noReissue : type_of% payment_receipt_not_reissued
  account : type_of% complete_account
  debit : type_of% complete_debit
  memory : type_of% actual_memory
  demand : type_of% actual_demand
  emptied : type_of% actual_empty
  payment : type_of% actual_payment
  consumed : type_of% consumed_receiver
  noEnergyReissue : type_of% no_reissue_energy
  distinct : type_of% new_next_not_old_load
  body : type_of% actual_body
  branches : type_of% actual_branch_history
  restoration : type_of% actual_restoration
  allFaces : Nonempty (Projection ≃ Fin 45)

theorem sourceGeneratedPointerPayment : InstalledPayment :=
  ⟨PointerExtract.Runtime.sourceGeneratedPointerReceiver,payment_certificate.2,generated_action_answer,generated_action_next,
    generated_visit,actual_sequence,actual_clocks,actual_history,actual_joint,face_factorizes,parent_is_installed,
    whole_ledger_installed,payment_is_installed,payment_receipt_not_reissued,complete_account,complete_debit,
    actual_memory,actual_demand,actual_empty,actual_payment,consumed_receiver,no_reissue_energy,new_next_not_old_load,
    actual_body,actual_branch_history,actual_restoration,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime
