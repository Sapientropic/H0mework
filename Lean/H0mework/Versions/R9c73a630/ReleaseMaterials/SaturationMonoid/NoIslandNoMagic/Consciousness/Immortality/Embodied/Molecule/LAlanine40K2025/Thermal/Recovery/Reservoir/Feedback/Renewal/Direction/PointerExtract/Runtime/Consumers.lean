import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Runtime.Invariants

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
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

theorem actual_sequence : readCurrent seed=sourceEntry ∧ readCurrent afterFirst=advance sourceEntry ∧
    readCurrent afterSecond=loadNext (advance sourceEntry) := ⟨rfl,rfl,rfl⟩

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem actual_clocks : (readCurrent seed).quantum.localClock=12*nativeClockStep ∧
    (readCurrent afterFirst).quantum.localClock=13*nativeClockStep ∧
    (readCurrent afterSecond).quantum.localClock=14*nativeClockStep := by
  refine ⟨Extract.Runtime.actual_clocks.2.1,first_clock,?_⟩
  change (advance sourceEntry).quantum.localClock+nativeClockStep=14*nativeClockStep
  rw [source_clock]
  ring

theorem actual_history : afterFirst.state.history=seed.state.history.step rfl ∧
    afterSecond.state.history=afterFirst.state.history.step rfl := ⟨rfl,rfl⟩

theorem actual_joint (runtime : LivingRuntimeState process) :
    (readNext runtime).quantum.joint=Quantum.conjugation (action runtime.state.current) (readCurrent runtime).quantum.joint :=
  next_joint runtime.state.current

theorem actual_output : 0 < Extract.Port.kinetic (readCurrent afterFirst).momentum-
    Extract.Port.kinetic (readCurrent seed).momentum := receiver_certificate.2.output

theorem actual_payment : pointerEnergy (readCurrent afterFirst).quantum.joint+
    Extract.Port.kinetic (readCurrent afterFirst).momentum=pointerEnergy (readCurrent seed).quantum.joint :=
  receiver_certificate.2.pointerPayment

theorem actual_body : bodyRead (readCurrent afterFirst).quantum.joint=bodyRead (readCurrent seed).quantum.joint :=
  receiver_certificate.2.body sourceEntry

theorem actual_branch_history : loadBlock (readCurrent afterFirst).quantum=suppliedBlock (readCurrent seed).quantum ∧
    suppliedBlock (readCurrent afterFirst).quantum=loadBlock (readCurrent seed).quantum :=
  ⟨receiver_certificate.2.branches.1 sourceEntry,receiver_certificate.2.branches.2 sourceEntry⟩

theorem actual_memory (runtime : LivingRuntimeState process) :
    decodedMemory runtime.state.current=oneRead sourceEntry.quantum.joint := (runtime_invariants runtime).2.2.1

theorem complete_account (runtime : LivingRuntimeState process) : type_of% (runtime_complete_account runtime) :=
  runtime_complete_account runtime

theorem complete_debit (runtime : LivingRuntimeState process) : type_of% (runtime_complete_debit runtime) :=
  runtime_complete_debit runtime

theorem retained_receiver (runtime : LivingRuntimeState process) :
    (readCurrent runtime.tick.next).momentum=(advance sourceEntry).momentum := by
  have balance := (runtime_invariants runtime.tick.next).2.2.2
  exact balance

theorem retained_output (runtime : LivingRuntimeState process) :
    0 < Extract.Port.kinetic (readCurrent runtime.tick.next).momentum := by
  rw [retained_receiver,Extract.Port.kinetic,abs_of_pos source_momentum_positive]
  exact source_momentum_positive

theorem new_next_not_old_load :
    (readCurrent afterFirst).quantum.joint ≠ (Extract.Runtime.readCurrent Extract.Runtime.afterSecond).joint := by
  intro same
  have reads := congrArg oneRead same
  change oneRead (advance sourceEntry).quantum.joint=oneRead (Live.loadNext (Extract.next Weak.execution)).joint at reads
  rw [next_pointer_one,Live.loadNext_pointer_one,Extract.next_pointer] at reads
  have original : oneRead sourceEntry.quantum.joint=oneRead Weak.execution.joint :=
    Extract.Runtime.actual_retained_memory
  have total := reads_sum sourceEntry.quantum.joint
  rw [sourceEntry.quantum.normalized,Complex.one_re] at total
  have high : (1/2 : ℝ) < oneRead sourceEntry.quantum.joint := current_pointer_population
  linarith only [reads,original,total,high]

def faceSumEquiv : Projection ≃ Fin 9 ⊕ Extract.Runtime.Projection where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .joint => .inl 2 | .resources => .inl 3
    | .receiver => .inl 4 | .thermal => .inl 5 | .netAccount => .inl 6 | .firstReceiver => .inl 7 | .wholeLedger => .inl 8
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.joint,.resources,.receiver,.thermal,.netAccount,.firstReceiver,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 36 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) Extract.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledReceiver : Prop where
  parent : Extract.Runtime.InstalledExtraction
  source : OriginalReceiver
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
  first : type_of% receiver_is_installed
  noReissue : type_of% receiver_receipt_not_reissued
  account : type_of% complete_account
  debit : type_of% complete_debit
  memory : type_of% actual_memory
  output : type_of% actual_output
  payment : type_of% actual_payment
  retained : type_of% retained_output
  distinct : type_of% new_next_not_old_load
  body : type_of% actual_body
  branches : type_of% actual_branch_history
  allFaces : Nonempty (Projection ≃ Fin 36)

theorem sourceGeneratedPointerReceiver : InstalledReceiver :=
  ⟨Extract.Runtime.sourceGeneratedExtraction,receiver_certificate.2,generated_action_answer,generated_action_next,
    generated_visit,actual_sequence,actual_clocks,actual_history,actual_joint,face_factorizes,parent_is_installed,
    whole_ledger_installed,receiver_is_installed,receiver_receipt_not_reissued,complete_account,complete_debit,
    actual_memory,actual_output,actual_payment,retained_output,new_next_not_old_load,actual_body,actual_branch_history,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
