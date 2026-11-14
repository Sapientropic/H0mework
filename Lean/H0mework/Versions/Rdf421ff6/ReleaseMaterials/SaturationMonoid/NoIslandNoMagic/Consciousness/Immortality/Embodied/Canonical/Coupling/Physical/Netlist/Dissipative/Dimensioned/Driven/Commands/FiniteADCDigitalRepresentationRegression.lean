import H0mework.Computation.ADCWire.DigitalRepresentation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.SourceOwnedFiniteADCClockedNoisyMeteredSynchronousCoupling

/-!
# Addressed digital execution consumers and hostile controls

All source parameters remain universally quantified. Positives exercise
mixed commands and single-channel interventions. Controls remove addresses,
omit one consumer, overwrite the ADC frames while retaining the clock, and
attempt a nine-bit representation of the full input family.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Regression

open Physical.Interface Physical.Producer
open Physical.Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Producer
open NoIslandNoMagic.Consciousness.Representation

noncomputable section

theorem every_binary_request_executes_and_roundTrips
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt source drive ∧
      decodeDigitalSample source (compiledADCDigitalSample source drive) = drive :=
  ⟨(sourceGeneratedAddressedADCCrown source).everyExecution drive,
    (sourceGeneratedAddressedADCCrown source).exactDigitalReadback drive⟩

/-- An explicit mixed override: the write and learned-state ports act, the receipt port does not. -/
def mixedDigitalRequest : FiniteBinaryDrive :=
  fun channel => decide (channel = .machineToNeuralWrite ∨ channel = .learnedStateTrace)

theorem mixed_request_keeps_receiving_address
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    decodeDigitalSample source (compiledADCDigitalSample source mixedDigitalRequest)
        .machineToNeuralWrite = true ∧
      decodeDigitalSample source (compiledADCDigitalSample source mixedDigitalRequest)
        .learnedStateTrace = true ∧
      decodeDigitalSample source (compiledADCDigitalSample source mixedDigitalRequest)
        .neuralToMachineReceipt = false := by
  rw [decodeDigitalSample_compiled]
  decide

theorem native_noPower_receipt_consumes_addressed_execution
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    SourceGeneratedAddressedADCCrownAt source ∧
      ∀ other, other ≠ FiniteEmbodimentChannel.noPowerMinting →
        decodeDigitalSample source
          (compiledADCDigitalSample source (singleBinaryDrive .noPowerMinting)) other = false := by
  let receipt := (sourceOwnedFiniteADCClockedNoisyMeteredSynchronousCouplingLaw source).noPowerMinting
  exact ⟨receipt.addressedDigitalCrown, by
    simpa only [decodeFiniteADC128EnergySample_pack, decodeDigitalSample_compiled] using
      receipt.otherReceiverIsolation⟩

theorem generated_quotient_preserves_every_channel
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Nonempty (binaryDriveConsumers.Quotient ≃ Set.range (compiledADCDigitalSample source)) ∧
      Nat.card (Set.range (compiledADCDigitalSample source)) = 1024 :=
  ⟨(sourceGeneratedAddressedADCCrown source).quotientRange,
    (sourceGeneratedAddressedADCCrown source).imageCapacity⟩

/-- Equal numbers of active ports do not imply equal addressed commands. -/
def activeChannelCount (drive : FiniteBinaryDrive) : Nat :=
  ∑ channel : FiniteEmbodimentChannel, if drive channel then 1 else 0

theorem singleDrive_count (selected : FiniteEmbodimentChannel) :
    activeChannelCount (singleBinaryDrive selected) = 1 := by
  simp [activeChannelCount, singleBinaryDrive]

theorem equal_counts_have_different_digital_faces
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    activeChannelCount (singleBinaryDrive .machineToNeuralWrite) =
        activeChannelCount (singleBinaryDrive .neuralToMachineReceipt) ∧
      compiledADCDigitalSample source (singleBinaryDrive .machineToNeuralWrite) ≠
        compiledADCDigitalSample source (singleBinaryDrive .neuralToMachineReceipt) := by
  constructor
  · rw [singleDrive_count, singleDrive_count]
  · intro same
    have sameDrive := compiledADCDigitalSample_injective source same
    have coordinate := congrFun sameDrive .machineToNeuralWrite
    norm_num [singleBinaryDrive] at coordinate
    cases coordinate

theorem digital_face_does_not_factor_through_active_count
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    ¬ Function.FactorsThrough (compiledADCDigitalSample source) activeChannelCount := by
  intro factors
  have hostile := equal_counts_have_different_digital_faces source
  exact hostile.2 (factors hostile.1)

/-- Every one of the ten consumers is needed to classify the full execution family. -/
theorem deleting_any_address_loses_a_real_difference
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (deleted : FiniteEmbodimentChannel) :
    (∀ channel, channel ≠ deleted →
      binaryDriveConsumers.read channel (uniformBinaryDrive false) =
        binaryDriveConsumers.read channel (singleBinaryDrive deleted)) ∧
      compiledADCDigitalSample source (uniformBinaryDrive false) ≠
        compiledADCDigitalSample source (singleBinaryDrive deleted) := by
  constructor
  · intro channel different
    simp [binaryDriveConsumers, uniformBinaryDrive, singleBinaryDrive, different]
  · intro same
    have coordinate := congrFun (compiledADCDigitalSample_injective source same) deleted
    simp [uniformBinaryDrive, singleBinaryDrive] at coordinate

/-- Retain the actual clock while overwriting all ADC frames with one recorded word. -/
def overwrittenWords
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) : FiniteADCDigitalSample source where
  sampleTick := sample.sampleTick
  wordsAt := fun _ _ _ => sample.wordsAt .zeroReference .resistor .sourceBound

theorem overwritten_words_erase_readback
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) :
    decodeDigitalSample source (overwrittenWords source sample) = uniformBinaryDrive false := by
  funext channel
  simp [decodeDigitalSample, digitalSampleState, digitalSampleLeg, overwrittenWords,
    finiteADCClockedDecodedVoltageAt, decodedFiniteAffineMeterNormalizedRead,
    synchronousDemodulatedPortAt, targetPort, uniformBinaryDrive]

theorem retained_clock_cannot_substitute_for_ADC_words
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    (overwrittenWords source
        (compiledADCDigitalSample source (uniformBinaryDrive true))).sampleTick =
      (compiledADCDigitalSample source (uniformBinaryDrive true)).sampleTick ∧
      decodeDigitalSample source (overwrittenWords source
          (compiledADCDigitalSample source (uniformBinaryDrive true))) ≠
        uniformBinaryDrive true := by
  constructor
  · rfl
  · rw [overwritten_words_erase_readback]
    intro same
    have impossible := congrFun same .sourceBound
    exact Bool.false_ne_true impossible

theorem nine_bits_cannot_classify_all_executions
    (representation : FiniteBinaryDrive → Fin (2 ^ 9)) :
    ¬ FaceKernelExactAt binaryDriveConsumers representation := by
  intro exactKernel
  have impossible := addressedADC_completeBitWord_minimum 9 representation exactKernel
  omega

/-- Same-root uniqueness is checked with a second, independently complete source carrier. -/
theorem source_bit_carrier_commutes_uniquely
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    ∃! equivalence : Set.range (compiledADCDigitalSample source) ≃
        Set.range (id : FiniteBinaryDrive → FiniteBinaryDrive),
      ∀ drive, equivalence ⟨compiledADCDigitalSample source drive, drive, rfl⟩ =
        ⟨drive, drive, rfl⟩ := by
  apply addressedADC_sameRoot_uniqueIso source id
  intro left right
  exact (binaryDriveConsumers_indistinguishable_iff_eq left right).symm

end

end Netlist.Dissipative.Dimensioned.Driven.Regression
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
