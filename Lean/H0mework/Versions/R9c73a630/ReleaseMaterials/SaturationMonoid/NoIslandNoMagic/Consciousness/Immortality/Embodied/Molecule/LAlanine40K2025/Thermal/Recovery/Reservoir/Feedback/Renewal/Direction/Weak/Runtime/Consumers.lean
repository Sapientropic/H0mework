import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Runtime.Invariants
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.Address
set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Resource Propagation.Producer
open Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
noncomputable section

attribute [local irreducible] Spec.netGain

def readCurrent (runtime : LivingRuntimeState process) : Live.State :=
  match facade.readoutAt runtime .current with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

def readNext (runtime : LivingRuntimeState process) : Live.State :=
  match facade.readoutAt runtime .next with
  | .inl ⟨_,current⟩ => current
  | .inr impossible => nomatch impossible

theorem actual_sequence :
    readCurrent seed=origin ∧ readCurrent afterFirst=target ∧ readCurrent afterSecond=execution :=
  ⟨rfl,rfl,rfl⟩

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem actual_clocks :
    (readCurrent seed).localClock=9*nativeClockStep ∧
    (readCurrent afterFirst).localClock=10*nativeClockStep ∧
    (readCurrent afterSecond).localClock=11*nativeClockStep := clocks

theorem actual_history :
    afterFirst.state.history=seed.state.history.step rfl ∧
    afterSecond.state.history=afterFirst.state.history.step rfl := ⟨rfl,rfl⟩

theorem actual_joint (runtime : LivingRuntimeState process) :
    (readNext runtime).joint=Quantum.conjugation (action runtime.state.current) (readCurrent runtime).joint :=
  next_joint runtime.state.current

theorem complete_account (runtime : LivingRuntimeState process) :
    Live.entropyProduction (readCurrent runtime)+Live.freeEnergy (readCurrent runtime)=
      Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+
      Live.measurementWork Live.initial+responseWork receivedState+responseWork received+
      accumulatedWork runtime.state.current :=
  runtime_complete_account runtime

theorem complete_debit (runtime : LivingRuntimeState process) :
    donorRemainingOf (suppliedBlock (readCurrent runtime))+
      accumulatedTransfer runtime.state.current+supplyTransfer received+supplyTransfer receivedState=
      donorRemainingOf (suppliedBlock receivedState) :=
  runtime_complete_debit runtime

theorem actual_resource_balance :
    (pcEnergyOf (bodyRead (readCurrent afterSecond).joint)-pcEnergyOf (bodyRead (readCurrent seed).joint))+
      (donorEnergyOf (bodyRead (readCurrent afterSecond).joint)-donorEnergyOf (bodyRead (readCurrent seed).joint))+
      (environmentEnergyOf (bodyRead (readCurrent afterSecond).joint)-environmentEnergyOf (bodyRead (readCurrent seed).joint))+
      (boundaryEnergyOf (bodyRead (readCurrent afterSecond).joint)-boundaryEnergyOf (bodyRead (readCurrent seed).joint))=
      pulseWork (readCurrent seed) := execution_resource_balance

theorem actual_heat : type_of% execution_heat_account := execution_heat_account

theorem actual_retained_memory :
    oneRead (readCurrent afterSecond).joint=oneRead (readCurrent seed).joint ∧
      (readCurrent afterSecond).joint ≠ sourceInitial :=
  ⟨execution_pointer_memory,execution_not_reset⟩

theorem original_comparison :
    |(pcEnergyOf (bodyRead (readCurrent afterSecond).joint)-pcEnergyOf (bodyRead (readCurrent seed).joint))-
      ((SharpNet.Runtime.readMaterial parentMaterial).rationalGain : ℝ)| ≤ (80/10^7 : ℝ) :=
  SharpNet.Runtime.target_comparison parentMaterial

theorem original_remaining_gain :
    headRestLowOriginalGain+(675/10^9 : ℝ) <
      pcEnergyOf (bodyRead (readCurrent afterSecond).joint)-pcEnergyOf (bodyRead (readCurrent seed).joint) := by
  have comparison := (abs_le.mp original_comparison).1
  have rational_same : (SharpNet.Runtime.readMaterial parentMaterial).rationalGain=Spec.netGain := by
    rw [(SharpNet.Runtime.material_read parentMaterial).2]
    rfl
  rw [rational_same] at comparison
  linarith only [comparison,SharpNet.original_net_remaining_low_lower]

theorem staged_remaining_gain :
    (headRestLowStagedGain : ℝ)+(6747/10^10 : ℝ) <
      pcEnergyOf (bodyRead (readCurrent afterSecond).joint)-pcEnergyOf (bodyRead (readCurrent seed).joint) := by
  linarith only [original_remaining_gain,(abs_lt.mp head_low_original_staged_error).2]

def faceSumEquiv : Projection ≃ Fin 8 ⊕ SharpNet.Runtime.Face where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .joint => .inl 2 | .resources => .inl 3
    | .thermal => .inl 4 | .netAccount => .inl 5 | .firstSupply => .inl 6 | .wholeLedger => .inl 7
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.joint,.resources,.thermal,.netAccount,.firstSupply,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 18 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) SharpNet.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledWeakContinuation : Prop where
  parent : type_of% parent_source
  source : WeakSupplyAndLoadCandidate
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
  firstSupply : type_of% supply_is_installed
  noReissue : type_of% supply_receipt_not_reissued
  account : type_of% complete_account
  debit : type_of% complete_debit
  finiteBudget : type_of% runtime_finite_budget
  resources : type_of% actual_resource_balance
  heat : type_of% actual_heat
  retained : type_of% actual_retained_memory
  comparison : type_of% original_comparison
  remainingGain : type_of% original_remaining_gain
  stagedGain : type_of% staged_remaining_gain
  lowCoverage : type_of% low_canonical_address_bijective
  lowOriginal : type_of% low_original_gain_source_sum
  lowStaged : type_of% low_staged_gain_source_sum
  lowError : type_of% head_low_original_staged_error
  allFaces : Nonempty (Projection ≃ Fin 18)

theorem sourceGeneratedWeakContinuation : InstalledWeakContinuation :=
  ⟨parent_source,sourceGeneratedWeakSupplyAndLoad,generated_action_answer,generated_action_next,
    generated_visit,actual_sequence,actual_clocks,actual_history,actual_joint,
    face_factorizes,parent_is_installed,whole_ledger_installed,supply_is_installed,
    supply_receipt_not_reissued,complete_account,complete_debit,runtime_finite_budget,
    actual_resource_balance,actual_heat,actual_retained_memory,original_comparison,
    original_remaining_gain,staged_remaining_gain,low_canonical_address_bijective,
    low_original_gain_source_sum,low_staged_gain_source_sum,head_low_original_staged_error,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
