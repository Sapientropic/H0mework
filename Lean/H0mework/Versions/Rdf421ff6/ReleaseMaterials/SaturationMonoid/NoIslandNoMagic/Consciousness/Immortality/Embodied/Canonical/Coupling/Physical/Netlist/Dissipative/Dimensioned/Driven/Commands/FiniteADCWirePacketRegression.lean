import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Commands.FiniteADCDigitalRepresentationRegression

/-!
# Finite wire execution consumers and malformed-packet controls

Numeric examples execute the arithmetic encoder and parser. The remaining
consumers are universal over physical source parameters and all addressed
commands. Invalid words and off-schedule counters are rejected explicitly;
syntactic admission is never promoted to source provenance.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Regression

open Physical.Interface
open Physical.Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Producer
open NoIslandNoMagic.Consciousness.Representation

def coarseLowerADCWord : FiniteADCWord .coarse := ⟨-4000000, by decide⟩
def coarseUpperADCWord : FiniteADCWord .coarse := ⟨4000000, by decide⟩
def coarseHalfModulusADCWord : FiniteADCWord .coarse := ⟨194304, by decide⟩

theorem coarse_endpoints_pack_exactly :
    (packADCWord .coarse coarseLowerADCWord).val = 0 ∧
      (packADCWord .coarse coarseUpperADCWord).val = 8000000 := by decide

theorem unused_coarse_binary_code_rejected :
    parseADCWord .coarse ⟨8000001, by decide⟩ = none := by decide

/-- Reducing the coarse converter to 22 bits silently aliases two different valid voltages. -/
theorem truncated_ADC_word_aliases_distinct_symbols :
    coarseLowerADCWord ≠ coarseHalfModulusADCWord ∧
      (packADCWord .coarse coarseLowerADCWord).val % 2 ^ 22 =
        (packADCWord .coarse coarseHalfModulusADCWord).val % 2 ^ 22 := by decide

noncomputable section

theorem every_generated_wire_packet_parses_and_reads
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    parseADCWirePacket source (maxADCSampleTick source) (packADCExecution source drive) =
        some (compiledADCDigitalSample source drive) ∧
      decodeDigitalSample source (unpackADCWirePacket source (packADCExecution source drive)) =
        drive :=
  ⟨(sourceGeneratedADCWireCrown source).exactParse drive,
    (sourceGeneratedADCWireCrown source).exactReadback drive⟩

theorem mixed_override_survives_wire_encoding
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    decodeDigitalSample source
        (unpackADCWirePacket source (packADCExecution source mixedDigitalRequest))
        .machineToNeuralWrite = true ∧
      decodeDigitalSample source
        (unpackADCWirePacket source (packADCExecution source mixedDigitalRequest))
        .neuralToMachineReceipt = false := by
  rw [decode_packADCExecution]
  decide

theorem off_schedule_header_rejected
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (packet : FiniteADCWirePacket source)
    (offSchedule : maxADCSampleTick source < packet.1.val) :
    parseADCWirePacket source (maxADCSampleTick source) packet = none := by
  apply parseADCWirePacket_rejects_invalid
  intro valid
  exact (not_le_of_gt offSchedule) valid.1

theorem unused_payload_word_rejected
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (packet : FiniteADCWirePacket source)
    (frame : FiniteAffineMeterFrame) (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (invalid : ¬ validADCWord source.adcCode (packet.2 frame leg channel)) :
    parseADCWirePacket source (maxADCSampleTick source) packet = none := by
  apply parseADCWirePacket_rejects_invalid
  intro valid
  exact invalid (valid.2 frame leg channel)

/-- A well-shaped packet is not an execution certificate: its header can be forged. -/
def zeroTickForgedPacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    FiniteADCWirePacket source :=
  (⟨0, Nat.two_pow_pos _⟩, (packADCExecution source (uniformBinaryDrive false)).2)

theorem syntactic_admission_does_not_mint_source_provenance
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    validADCWirePacket source (maxADCSampleTick source) (zeroTickForgedPacket source) ∧
      zeroTickForgedPacket source ∉ Set.range (packADCExecution source) := by
  constructor
  · exact ⟨Nat.zero_le _, (packADCExecution_valid source (uniformBinaryDrive false)).2⟩
  · rintro ⟨drive, same⟩
    have tickZero : finiteADCClockedSampleTick source drive = 0 :=
      congrArg (fun packet => packet.1.val) same
    have positive := finiteADCClockedSampleTime_pos source drive
    change 0 < (finiteSamplingClockSampleTime source.meteredSource.fixture.coreSource
      source.clockCode (finiteADCClockedRequiredDuration source drive)).value at positive
    simp only [finiteSamplingClockSampleTime, SIQuantity.smul_value] at positive
    change 0 < (finiteADCClockedSampleTick source drive : ℝ) * _ at positive
    simp only [tickZero, Nat.cast_zero, zero_mul, lt_self_iff_false] at positive

/-- The native receipt now actually reads the word-encoded execution. -/
theorem native_noPower_receipt_consumes_wire_execution
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    SourceGeneratedADCWireCrownAt source ∧
      ∀ other, other ≠ FiniteEmbodimentChannel.noPowerMinting →
        decodeDigitalSample source
          (unpackADCWirePacket source
            (packADCExecution source (singleBinaryDrive .noPowerMinting))) other = false := by
  let receipt := (sourceOwnedFiniteADCClockedNoisyMeteredSynchronousCouplingLaw source).noPowerMinting
  exact ⟨receipt.wireCrown, by
    simpa only [unpack_packADCExecution, decodeFiniteADC128EnergySample_compiled,
      decodeDigitalSample_compiled] using receipt.otherReceiverIsolation⟩

theorem wire_factorization_is_unique
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (consumer : binaryDriveConsumers.Consumer) :
    ∃! factor : Set.range (packADCExecution source) → binaryDriveConsumers.Output consumer,
      ∀ drive, factor ⟨packADCExecution source drive, drive, rfl⟩ =
        binaryDriveConsumers.read consumer drive :=
  (sourceGeneratedADCWireCrown source).kernelExact.everyConsumer_unique_factorization consumer

theorem generated_wire_image_and_budget
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Nat.card (Set.range (packADCExecution source)) = 1024 ∧
      Fintype.card (FiniteADCWirePacket source) =
        2 ^ (adcClockBits source + 60 * adcWordBits source.adcCode) :=
  ⟨(sourceGeneratedADCWireCrown source).imageCapacity,
    (sourceGeneratedADCWireCrown source).packetBudget⟩

theorem same_source_wire_encoding_commutes_uniquely
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    ∃! equivalence : Set.range (compiledADCDigitalSample source) ≃
        Set.range (packADCExecution source),
      ∀ drive, equivalence ⟨compiledADCDigitalSample source drive, drive, rfl⟩ =
        ⟨packADCExecution source drive, drive, rfl⟩ :=
  addressedADCWire_sameRoot_uniqueIso source

end

end Netlist.Dissipative.Dimensioned.Driven.Regression
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
