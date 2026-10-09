import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Runtime.Invariants

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

def readCurrent (runtime : LivingRuntimeState process) : Live.State :=
  match facade.readoutAt runtime .current with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

def readNext (runtime : LivingRuntimeState process) : Live.State :=
  match facade.readoutAt runtime .next with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

theorem actual_sequence :
    readCurrent seed=Weak.execution ∧
    readCurrent afterFirst=Extract.next Weak.execution ∧
    readCurrent afterSecond=Live.loadNext (Extract.next Weak.execution) := ⟨rfl,rfl,rfl⟩

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem actual_clocks :
    (readCurrent seed).localClock=11*nativeClockStep ∧
    (readCurrent afterFirst).localClock=12*nativeClockStep ∧
    (readCurrent afterSecond).localClock=13*nativeClockStep := by
  refine ⟨Weak.clocks.2.2,first_clock,?_⟩
  change (Extract.next Weak.execution).localClock+nativeClockStep=13*nativeClockStep
  have clock : (Extract.next Weak.execution).localClock=12*nativeClockStep := first_clock
  rw [clock]
  ring

theorem actual_history :
    afterFirst.state.history=seed.state.history.step rfl ∧
    afterSecond.state.history=afterFirst.state.history.step rfl := ⟨rfl,rfl⟩

theorem actual_joint (runtime : LivingRuntimeState process) :
    (readNext runtime).joint=Quantum.conjugation (action runtime.state.current) (readCurrent runtime).joint :=
  next_joint runtime.state.current

theorem actual_pc_output :
    (17/5 : ℝ) < pcEnergyOf (bodyRead (readCurrent seed).joint) -
      pcEnergyOf (bodyRead (readCurrent afterFirst).joint) :=
  extraction_certificate.2.pcPositive

theorem actual_net_output : (7/5 : ℝ) < -eventWork seed.state.current :=
  extraction_certificate.2.netPositive

theorem retained_output (runtime : LivingRuntimeState process) :
    (7/5 : ℝ) < -accumulatedWork runtime.tick.next.state.current :=
  extraction_certificate.2.netPositive

theorem actual_capacity : type_of% Extract.original_capacity_lower :=
  extraction_certificate.2.capacity

theorem complete_account (runtime : LivingRuntimeState process) :
    Live.entropyProduction (readCurrent runtime)+Live.freeEnergy (readCurrent runtime)=
      Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+
      Live.measurementWork Live.initial+responseWork receivedState+responseWork received+
      Weak.pulseWork Weak.origin+accumulatedWork runtime.state.current :=
  runtime_complete_account runtime

theorem complete_debit (runtime : LivingRuntimeState process) :
    donorRemainingOf (suppliedBlock (readCurrent runtime))+
      Weak.transfer+supplyTransfer received+supplyTransfer receivedState=
      donorRemainingOf (suppliedBlock receivedState) :=
  runtime_complete_debit runtime

theorem actual_retained_memory :
    oneRead (readCurrent afterFirst).joint=oneRead (readCurrent seed).joint :=
  extraction_certificate.2.memory Weak.execution

theorem actual_resource_balance :
    (pcEnergyOf (bodyRead (readCurrent afterFirst).joint)-pcEnergyOf (bodyRead (readCurrent seed).joint))+
      (donorEnergyOf (bodyRead (readCurrent afterFirst).joint)-donorEnergyOf (bodyRead (readCurrent seed).joint))+
      (environmentEnergyOf (bodyRead (readCurrent afterFirst).joint)-environmentEnergyOf (bodyRead (readCurrent seed).joint))+
      (boundaryEnergyOf (bodyRead (readCurrent afterFirst).joint)-boundaryEnergyOf (bodyRead (readCurrent seed).joint))=
      Extract.pulseWork (readCurrent seed) := next_resource_balance .ingress

def faceSumEquiv : Projection ≃ Fin 8 ⊕ Weak.Positive.Runtime.Face where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .joint => .inl 2 | .resources => .inl 3
    | .thermal => .inl 4 | .netAccount => .inl 5 | .firstExtraction => .inl 6 | .wholeLedger => .inl 7
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.joint,.resources,.thermal,.netAccount,.firstExtraction,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 27 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) Weak.Positive.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledExtraction : Prop where
  parent : Weak.Positive.Runtime.InstalledPositiveWeakContinuation
  source : OriginalExtraction
  generatedAnswer : type_of% generated_action_answer
  generatedNext : type_of% generated_action_next
  generatedVisit : type_of% generated_visit
  actual : type_of% actual_sequence
  clocks : type_of% actual_clocks
  history : type_of% actual_history
  joint : type_of% actual_joint
  factorization : type_of% face_factorizes
  inherited : type_of% parent_is_installed
  ledger : type_of% whole_ledger_installed
  firstExtraction : type_of% extraction_is_installed
  noReissue : type_of% extraction_receipt_not_reissued
  account : type_of% complete_account
  debit : type_of% complete_debit
  finiteBudget : type_of% runtime_finite_budget
  resources : type_of% actual_resource_balance
  retained : type_of% actual_retained_memory
  pcPositive : type_of% actual_pc_output
  netPositive : type_of% actual_net_output
  retainedOutput : type_of% retained_output
  capacity : type_of% actual_capacity
  allFaces : Nonempty (Projection ≃ Fin 27)

theorem sourceGeneratedExtraction : InstalledExtraction :=
  ⟨Weak.Positive.Runtime.sourceGeneratedPositiveWeakContinuation,extraction_certificate.2,
    generated_action_answer,generated_action_next,generated_visit,actual_sequence,actual_clocks,actual_history,
    actual_joint,face_factorizes,parent_is_installed,whole_ledger_installed,extraction_is_installed,
    extraction_receipt_not_reissued,complete_account,complete_debit,runtime_finite_budget,actual_resource_balance,
    actual_retained_memory,actual_pc_output,actual_net_output,retained_output,actual_capacity,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
