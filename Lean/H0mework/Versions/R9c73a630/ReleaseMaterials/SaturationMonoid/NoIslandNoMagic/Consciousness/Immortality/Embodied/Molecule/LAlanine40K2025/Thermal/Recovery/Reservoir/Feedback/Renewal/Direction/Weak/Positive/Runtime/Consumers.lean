import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Positive.Runtime.Facade
set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Positive.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Resource Propagation.Producer
open Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
noncomputable section
attribute [local irreducible] Spec.netGain

theorem original_integer_family (runtime : LivingRuntimeState process) :
    type_of% low_complete_integer_gain := (readCertificate runtime).lowIntegers

theorem original_spectral_family (runtime : LivingRuntimeState process) :
    type_of% low_complete_qnet_floor := (readCertificate runtime).lowSpectra

theorem original_staged_total (runtime : LivingRuntimeState process) :
    type_of% low_complete_staged_gain_literal := (readCertificate runtime).lowTotal

theorem original_low_gain (runtime : LivingRuntimeState process) :
    type_of% low_complete_original_gain_lower := (readCertificate runtime).lowOriginal

theorem original_rational_positive (runtime : LivingRuntimeState process) :
    (80/10^7 : ℝ) < (Spec.netGain : ℝ) := (readCertificate runtime).rationalNet

theorem seed_is_origin : readCurrent seed=origin := rfl

theorem executed_current : readCurrent afterSecond=execution := rfl

theorem actual_pc_positive :
    0 < pcEnergyOf (bodyRead (readCurrent afterSecond).joint)-
      pcEnergyOf (bodyRead (readCurrent seed).joint) := by
  rw [executed_current,seed_is_origin]
  simpa only [SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.actual_sequence.1,
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.actual_sequence.2.2] using
    (readCertificate afterSecond).actualPC

theorem actual_clocks :
    (readCurrent seed).localClock=9*nativeClockStep ∧
    (readCurrent afterFirst).localClock=10*nativeClockStep ∧
    (readCurrent afterSecond).localClock=11*nativeClockStep := SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.clocks

theorem original_generated_visit :
    afterFirst.current.visit=SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.generatedAction.target.targetVisit := rfl

theorem executed_history :
    afterSecond.state.history=afterFirst.state.history.step rfl := rfl

theorem actual_next_is_load :
    readCurrent afterSecond.tick.next=Live.loadNext (readCurrent afterSecond) := rfl

theorem executed_complete_account :
    Live.entropyProduction (readCurrent afterSecond)+Live.freeEnergy (readCurrent afterSecond)=
      Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+
      Live.measurementWork Live.initial+responseWork receivedState+responseWork received+
      pulseWork (readCurrent seed) := by
  rw [executed_current,seed_is_origin]
  exact SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.execution_complete_account

theorem executed_complete_debit :
    donorRemainingOf (suppliedBlock (readCurrent afterSecond))+transfer+
      supplyTransfer received+supplyTransfer receivedState=
      donorRemainingOf (suppliedBlock receivedState) := by
  rw [executed_current]
  exact execution_complete_debit

theorem executed_retained_memory :
    oneRead (readCurrent afterSecond).joint=oneRead (readCurrent seed).joint ∧
      (readCurrent afterSecond).joint ≠ sourceInitial := by
  rw [executed_current,seed_is_origin]
  exact ⟨execution_pointer_memory,execution_not_reset⟩

theorem gain_ledger_same_occurrence (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime (.component .originalNineElevenGain)=
      (.inl ⟨PUnit.unit,
        (ParentLedger.ledgerCompiler.compile runtime.emittedOccurrence,⟨sourceOriginalNineElevenGain⟩)⟩ :
        SourceNativeProjectionFiberAt projectionLaw .originalNineElevenGain runtime.emittedOccurrence) := rfl

structure InstalledPositiveWeakContinuation : Prop where
  parent : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.InstalledWeakContinuation
  source : OriginalNineElevenGain
  integerFamily : type_of% original_integer_family
  spectralFamily : type_of% original_spectral_family
  stagedTotal : type_of% original_staged_total
  lowGain : type_of% original_low_gain
  rationalPositive : type_of% original_rational_positive
  actualPositive : type_of% actual_pc_positive
  actualCurrent : type_of% executed_current
  clocks : type_of% actual_clocks
  generatedVisit : type_of% original_generated_visit
  history : type_of% executed_history
  nextLoad : type_of% actual_next_is_load
  account : type_of% executed_complete_account
  debit : type_of% executed_complete_debit
  retained : type_of% executed_retained_memory
  sourceAndLaw : type_of% source_and_law_unchanged
  factorization : type_of% face_factorizes
  inherited : type_of% all_original_faces
  ledger : type_of% gain_ledger_same_occurrence
  generatedNext : type_of% generated_same_next
  allFaces : Nonempty (Face ≃ Fin 19)

theorem sourceGeneratedPositiveWeakContinuation : InstalledPositiveWeakContinuation :=
  ⟨SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime.sourceGeneratedWeakContinuation,sourceOriginalNineElevenGain,
    original_integer_family,original_spectral_family,original_staged_total,original_low_gain,
    original_rational_positive,actual_pc_positive,executed_current,actual_clocks,
    original_generated_visit,executed_history,actual_next_is_load,executed_complete_account,
    executed_complete_debit,executed_retained_memory,source_and_law_unchanged,
    face_factorizes,all_original_faces,gain_ledger_same_occurrence,generated_same_next,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Positive.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
