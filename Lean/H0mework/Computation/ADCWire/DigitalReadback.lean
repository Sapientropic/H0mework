import H0mework.Physics.ADCSource.ClockedNoisyMeteredSynchronousRunSource

/-!
# Exact readback of independently addressed commands from ADC words

The digital sample contains only the sampled tick and the three ADC word
frames. It contains no input command, raw analog voltage, initial condition,
or correctness certificate. Its decoder reconstructs the sample time from
the fixed source clock, calibrates the word frames and demodulates at that
actual time. The circuit's generated error bound proves exact recovery of
all ten independently chosen input bits.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface Physical.Producer
open Physical.Units.Interface

noncomputable section

/-- Wire-visible data at one fixed hardware source. -/
@[ext] structure FiniteADCDigitalSample
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) where
  sampleTick : Nat
  wordsAt : FiniteAffineMeterFrame → SynchronousSenseLeg →
    FiniteEmbodimentChannel → FiniteADCWord source.adcCode

/-- Project digital data from the actual generated occurrence. -/
def compiledADCDigitalSample
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : FiniteADCDigitalSample source where
  sampleTick := (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive).sampleTick
  wordsAt := (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive).adcWordAt

/-- Blind calibrated read of one leg; only finite words and the fixed scale are read. -/
def digitalSampleLeg
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source)
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : ℝ :=
  decodedFiniteAffineMeterNormalizedRead
    (finiteADCClockedDecodedVoltageAt source source.adcCode sample.wordsAt
      .zeroReference leg channel)
    (finiteADCClockedDecodedVoltageAt source source.adcCode sample.wordsAt
      .spanReference leg channel)
    (finiteADCClockedDecodedVoltageAt source source.adcCode sample.wordsAt
      .operational leg channel)
    (finiteAffineMeterSenseScaleAt source.meteredSource.fixture.coreSource leg channel)

/-- The sampled tick regenerates the physical time used by the demodulator. -/
def digitalSampleState
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) : FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source.meteredSource.fixture.coreSource channel
      ((sample.sampleTick : ℝ) • finiteSamplingClockTickPeriod
        source.meteredSource.fixture.coreSource source.clockCode))
    (digitalSampleLeg source sample .resistor channel)
    (digitalSampleLeg source sample .inductor channel)

/-- Independent receiving electronics use the same fixed threshold on each addressed port. -/
def decodeDigitalSample
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) : FiniteBinaryDrive :=
  fun channel => decide ((1 : ℝ) / 2 < targetPort (digitalSampleState source sample) channel)

theorem digitalSampleState_commutes
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    digitalSampleState source (compiledADCDigitalSample source drive) =
      finiteADCClockedDecodedStateAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) := rfl

theorem digitalSample_target_error_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel) :
    |targetPort (digitalSampleState source (compiledADCDigitalSample source drive)) channel -
        (if drive channel then 1 else 0)| < (1 : ℝ) / 8 := by
  have endpoint := compiledFiniteADCClockedHilbertError_lt source drive
  rw [idealQuarterOperator_apply] at endpoint
  have coordinate := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (finiteADCClockedDecodedStateAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive))
      (harmonicFlow (Real.pi / 2) (binaryDriveState drive)) channel) endpoint
  cases bit : drive channel <;>
    simpa [digitalSampleState_commutes, harmonicFlow, targetPort, sourcePort,
      binaryDriveState, bit] using coordinate

/-- Every source command is recovered through circuit execution, ADC and the blind decoder. -/
theorem decodeDigitalSample_compiled
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    decodeDigitalSample source (compiledADCDigitalSample source drive) = drive := by
  funext channel
  have bounded := digitalSample_target_error_lt source drive channel
  unfold decodeDigitalSample
  cases bit : drive channel
  · simp only [bit, Bool.false_eq_true, ↓reduceIte, sub_zero] at bounded
    apply decide_eq_false_iff_not.mpr
    have upper := (abs_lt.mp bounded).2
    linarith
  · simp only [bit, ↓reduceIte] at bounded
    apply decide_eq_true_eq.mpr
    have lower := (abs_lt.mp bounded).1
    linarith

theorem compiledADCDigitalSample_injective
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Function.Injective (compiledADCDigitalSample source) :=
  Function.LeftInverse.injective (decodeDigitalSample_compiled source)

/-- A local request cannot create a positive threshold response on another inactive channel. -/
theorem singleBinaryDrive_received_exactly
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (selected : FiniteEmbodimentChannel) :
    decodeDigitalSample source
        (compiledADCDigitalSample source (singleBinaryDrive selected)) selected = true ∧
      ∀ other, other ≠ selected →
        decodeDigitalSample source
          (compiledADCDigitalSample source (singleBinaryDrive selected)) other = false := by
  rw [decodeDigitalSample_compiled]
  constructor
  · simp [singleBinaryDrive]
  · intro other different
    simp [singleBinaryDrive, different]

/-- Receiving a bit depends only on the command at the same address, even when
other commands change the whole-port settling schedule. -/
theorem digitalSample_receiver_local
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (left right : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel)
    (sameRequest : left channel = right channel) :
    decodeDigitalSample source (compiledADCDigitalSample source left) channel =
      decodeDigitalSample source (compiledADCDigitalSample source right) channel := by
  simpa only [decodeDigitalSample_compiled] using sameRequest

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
