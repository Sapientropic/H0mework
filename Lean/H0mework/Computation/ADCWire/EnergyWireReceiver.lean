import H0mework.Computation.ADCWire.EnergyReadback
import H0mework.Computation.ADCWire.WireRepresentation
import H0mework.Computation.ADC.EnergyCircuit

/-!
# Executable 128-bit operand receiver for generated ADC wire packets

The receiver parses the finite payload, validates positive calibration spans
and compares bounded integer energy operands. Real dynamics remains in the
source specification and correctness proof, not in this receiving algorithm.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface Physical.Producer

/-- Encode the words already stored in a run. Code/tick alignment is proof-only;
neither the command nor the real circuit solver is evaluated by this projection. -/
def recordedADCWirePacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (run : FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence)
    (codeExact : run.adcCode = source.adcCode)
    {counterBits : Nat}
    (tickFits : run.sampleTick < 2 ^ counterBits) : FiniteADCWirePacketAt source counterBits :=
  (⟨run.sampleTick, tickFits⟩,
    fun frame leg channel => packADCWord source.adcCode
      ⟨(run.adcWordAt frame leg channel).val, by
        simpa only [codeExact] using (run.adcWordAt frame leg channel).property⟩)

theorem recordedADCWirePacket_compiled
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    recordedADCWirePacket source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) rfl
        (adcSampleTick_no_counter_overflow source drive) =
      packADCExecution source drive := rfl

/-- The receiving comparison uses the explicit unsigned 128-bit operands. -/
def decodeFiniteADC128EnergySample
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) : FiniteBinaryDrive :=
  fun channel => finiteADCBitVectorEnergyCircuit source.adcCode
    (sample.wordsAt .zeroReference .resistor channel)
    (sample.wordsAt .spanReference .resistor channel)
    (sample.wordsAt .operational .resistor channel)
    (sample.wordsAt .zeroReference .inductor channel)
    (sample.wordsAt .spanReference .inductor channel)
    (sample.wordsAt .operational .inductor channel)

theorem decodeFiniteADC128EnergySample_exact
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) :
    decodeFiniteADC128EnergySample sample = decodeFiniteADCEnergySample sample := by
  funext channel
  unfold decodeFiniteADC128EnergySample
  rw [finiteADCBitVectorEnergyCircuit_exact]
  exact finiteADCWordEnergyDecision128_exact source.adcCode _ _ _ _ _ _

def validADCEnergyCalibration
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) : Prop :=
  ∀ leg channel, 0 < finiteADCDigitalWordDifference sample .spanReference leg channel

instance {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) :
    Decidable (validADCEnergyCalibration sample) :=
  inferInstanceAs (Decidable (∀ _ _, _ < _))

/-- An invalid packet or a nonpositive span is a visible rejection, not a zero command. -/
def receiveADC128WirePacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    Option FiniteBinaryDrive := do
  let sample ← parseADCWirePacket source lastTick packet
  if validADCEnergyCalibration sample then some (decodeFiniteADC128EnergySample sample)
  else none

theorem validADCEnergyCalibration_compiled
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    validADCEnergyCalibration (compiledADCDigitalSample source drive) :=
  finiteADCDigitalWordDifference_span_pos source drive

/-- A positive physical target read implies the executable energy decision, using
the recorded calibration spans. No command bit is used in this transfer. -/
theorem decodeFiniteADC128EnergySample_true_of_target
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) (channel : FiniteEmbodimentChannel)
    (valid : validADCEnergyCalibration sample)
    (positive : (1 : ℝ) / 2 < targetPort (digitalSampleState source sample) channel) :
    decodeFiniteADC128EnergySample sample channel = true := by
  rw [decodeFiniteADC128EnergySample_exact]
  apply (finiteADCEnergyIntegerAboveQuarter_correct _ _ _ _
    (valid .resistor channel) (valid .inductor channel)).mpr
  have castEq := finiteADCDigitalChannelEnergy_cast_eq source sample channel
    (ne_of_gt (valid .resistor channel)) (ne_of_gt (valid .inductor channel))
  rw [digitalSampleLeg_energy_eq_state_channelEnergy, channelEnergy] at castEq
  have energyPositive : (1 : ℝ) / 4 <
      ((finiteADCDigitalChannelEnergy sample channel : ℚ) : ℝ) := by
    nlinarith [sq_nonneg (sourcePort (digitalSampleState source sample) channel)]
  change (1 : ℚ) / 4 < finiteADCDigitalChannelEnergy sample channel
  have castPositive : (((1 : ℚ) / 4 : ℚ) : ℝ) <
      ((finiteADCDigitalChannelEnergy sample channel : ℚ) : ℝ) := by
    norm_num
    exact energyPositive
  exact_mod_cast castPositive

@[simp] theorem decodeFiniteADC128EnergySample_compiled
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    decodeFiniteADC128EnergySample (compiledADCDigitalSample source drive) = drive := by
  rw [decodeFiniteADC128EnergySample_exact, decodeFiniteADCEnergySample_compiled]

@[simp] theorem decodeFiniteADC128EnergySample_pack
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    decodeFiniteADC128EnergySample
        (unpackADCWirePacket source (packADCExecution source drive)) = drive := by
  rw [unpack_packADCExecution, decodeFiniteADC128EnergySample_compiled]

theorem receiveADC128WirePacket_compiled
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    receiveADC128WirePacket source (maxADCSampleTick source) (packADCExecution source drive) =
      some drive := by
  simp [receiveADC128WirePacket, validADCEnergyCalibration_compiled]

theorem receiveADC128WirePacket_rejects_invalid_calibration
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits)
    (invalid : ¬ validADCEnergyCalibration (unpackADCWirePacket source packet)) :
    receiveADC128WirePacket source lastTick packet = none := by
  unfold receiveADC128WirePacket parseADCWirePacket
  split <;> simp [invalid]

/-- Data-path and provenance certificates are generated together without conflating them. -/
structure SourceGeneratedADCExecutableReceiverAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Prop
    extends SourceGeneratedADCWireCrownAt source where
  actualCalibration : ∀ drive, validADCEnergyCalibration (compiledADCDigitalSample source drive)
  executableReadback : ∀ drive,
    receiveADC128WirePacket source (maxADCSampleTick source) (packADCExecution source drive) =
      some drive
  boundedComparisonReadback : ∀ drive,
    decodeFiniteADC128EnergySample
        (unpackADCWirePacket source (packADCExecution source drive)) = drive

theorem sourceGeneratedADCExecutableReceiver
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    SourceGeneratedADCExecutableReceiverAt source where
  toSourceGeneratedADCWireCrownAt := sourceGeneratedADCWireCrown source
  actualCalibration := validADCEnergyCalibration_compiled source
  executableReadback := receiveADC128WirePacket_compiled source
  boundedComparisonReadback := decodeFiniteADC128EnergySample_pack source

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
