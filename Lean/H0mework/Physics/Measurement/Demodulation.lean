import H0mework.Physics.RLCResponse.Transient
import H0mework.Physics.RLCResponse.SourceResponse

/-!
# Finite-time synchronous demodulation of the driven RLC output

The periodic phasor is not used as the executed output.  At an arbitrary
physical initial state we read the resistor voltage `R I_total` and the
inductor voltage `L I'_total` from the same total-response occurrence.  An
inverse rotation at the actual channel phase synchronously demodulates those
two real samples.

The periodic part demodulates exactly to the quarter-phase operator.  The
homogeneous remainder is controlled by the already generated voltage/current
envelopes: subtracting the periodic and total KVL equations cancels the drive
and bounds `L delta I'` without assuming that pointwise convergence controls a
derivative.  A source-generated finite duration then places the full ten-port
Hilbert disturbance strictly below `1/8`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

def resonantSynchronousPhaseAt
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  (sourceOwnedResonantDrivenFrequencyAt source channel).value *
    physicalTime.value

def resonantActualResistorVoltageAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : SIVolt :=
  resistanceTimesCurrent
    ((compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource source)).seriesResistanceAt channel)
    (drivenTotalCurrentAt
      (resonantDrivenCoreDimensionedSource source)
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input)
      initial channel physicalTime)

def resonantActualInductorVoltageAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : SIVolt :=
  inductanceTimesCurrentRate
    ((compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource source)).inductanceAt channel)
    (drivenTotalCurrentDerivativeAt
      (resonantDrivenCoreDimensionedSource source)
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input)
      initial channel physicalTime)

def resonantPeriodicResistorVoltageAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : SIVolt :=
  resistanceTimesCurrent
    ((compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource source)).seriesResistanceAt channel)
    (drivenPeriodicCurrentAt
      (resonantDrivenCoreDimensionedSource source) channel
      (sourceOwnedResonantDrivenFrequencyAt source channel)
      (sourceOwnedResonantDrivenDriveAt source input channel) physicalTime)

def resonantPeriodicInductorVoltageAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : SIVolt :=
  inductanceTimesCurrentRate
    ((compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource source)).inductanceAt channel)
    (currentWaveformDerivativeAt
      (sourceOwnedResonantDrivenFrequencyAt source channel)
      (drivenPeriodicCurrentPhasorAt
        (resonantDrivenCoreDimensionedSource source) channel
        (sourceOwnedResonantDrivenFrequencyAt source channel)
        (sourceOwnedResonantDrivenDriveAt source input channel)) physicalTime)

def resonantActualNormalizedResistorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  (resonantActualResistorVoltageAt source input initial channel
    physicalTime).value / source.2.voltageScale.value

def resonantActualNormalizedInductorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  (resonantActualInductorVoltageAt source input initial channel
    physicalTime).value /
      (resonantInductorOutputScaleAt
        (resonantDrivenCoreDimensionedSource source) channel).value

def resonantPeriodicNormalizedResistorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  (resonantPeriodicResistorVoltageAt source input channel physicalTime).value /
    source.2.voltageScale.value

def resonantPeriodicNormalizedInductorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  (resonantPeriodicInductorVoltageAt source input channel physicalTime).value /
    (resonantInductorOutputScaleAt
      (resonantDrivenCoreDimensionedSource source) channel).value

def synchronousDemodulatedPortAt
    (phase resistorSample inductorSample : ℝ) : ℝ × ℝ :=
  (Real.sin phase * inductorSample - Real.cos phase * resistorSample,
    Real.cos phase * inductorSample + Real.sin phase * resistorSample)

def resonantActualSynchronousStateAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond) : FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source channel physicalTime)
    (resonantActualNormalizedResistorAt
      source input initial channel physicalTime)
    (resonantActualNormalizedInductorAt
      source input initial channel physicalTime)

def resonantPeriodicSynchronousStateAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (physicalTime : SISecond) : FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source channel physicalTime)
    (resonantPeriodicNormalizedResistorAt source input channel physicalTime)
    (resonantPeriodicNormalizedInductorAt source input channel physicalTime)

theorem resonantPeriodicResistorVoltage_eq_driveWaveform
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantPeriodicResistorVoltageAt source input channel physicalTime =
      voltageWaveformAt
        (sourceOwnedResonantDrivenFrequencyAt source channel)
        (sourceOwnedResonantDrivenDriveAt source input channel) physicalTime := by
  unfold resonantPeriodicResistorVoltageAt
  rw [drivenPeriodic_resistorConstitutiveLaw]
  congr 2
  exact resonantResistorComponentPhasor_eq_drive
    (resonantDrivenCoreDimensionedSource source) input channel

theorem normalizedVoltageWaveformAt_eq
    (frequency : SIHertz) (scale : SIVolt) (phasor : SIVoltagePhasor)
    (physicalTime : SISecond) (scaleNonzero : scale.value ≠ 0) :
    (voltageWaveformAt frequency phasor physicalTime).value / scale.value =
      Real.cos (frequency.value * physicalTime.value) *
          (normalizeVoltagePhasor scale phasor).re +
        Real.sin (frequency.value * physicalTime.value) *
          (normalizeVoltagePhasor scale phasor).im := by
  simp only [voltageWaveformAt_value, normalizeVoltagePhasor]
  field_simp [scaleNonzero]

theorem resonantPeriodicInductorVoltage_eq_waveform
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantPeriodicInductorVoltageAt source input channel physicalTime =
      voltageWaveformAt
        (sourceOwnedResonantDrivenFrequencyAt source channel)
        (resonantInductorVoltagePhasorAt
          (resonantDrivenCoreDimensionedSource source) input channel)
        physicalTime := by
  unfold resonantPeriodicInductorVoltageAt
  rw [drivenPeriodic_inductorConstitutiveLaw]
  rfl

theorem resonantPeriodicNormalizedResistor_eq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantPeriodicNormalizedResistorAt source input channel physicalTime =
      Real.cos (resonantSynchronousPhaseAt source channel physicalTime) *
          targetPort input channel +
        Real.sin (resonantSynchronousPhaseAt source channel physicalTime) *
          sourcePort input channel := by
  rw [resonantPeriodicNormalizedResistorAt,
    resonantPeriodicResistorVoltage_eq_driveWaveform]
  simp only [voltageWaveformAt_value, sourceOwnedResonantDrivenDriveAt,
    resonantDrivenRunDrivePhasorAt, sourceOwnedResonantDrivenFrequencyAt,
    resonantSynchronousPhaseAt]
  simp [compileFiniteResonantDrivenSeriesRLCRun,
    resonantDrivenCoreDimensionedSource, voltagePhasorOfNormalized,
    encodePort, sourcePort, targetPort]
  field_simp [source.2.voltageScale_ne]

theorem resonantPeriodicNormalizedInductor_eq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantPeriodicNormalizedInductorAt source input channel physicalTime =
      Real.cos (resonantSynchronousPhaseAt source channel physicalTime) *
          sourcePort input channel -
        Real.sin (resonantSynchronousPhaseAt source channel physicalTime) *
          targetPort input channel := by
  rw [resonantPeriodicNormalizedInductorAt,
    resonantPeriodicInductorVoltage_eq_waveform,
    normalizedVoltageWaveformAt_eq _ _ _ _
      (ne_of_gt (resonantInductorOutputScale_pos
        (resonantDrivenCoreDimensionedSource source) channel))]
  change
    Real.cos (resonantSynchronousPhaseAt source channel physicalTime) *
          (resonantInductorPortOutputAt
            (resonantDrivenCoreDimensionedSource source) input channel).re +
        Real.sin (resonantSynchronousPhaseAt source channel physicalTime) *
          (resonantInductorPortOutputAt
            (resonantDrivenCoreDimensionedSource source) input channel).im = _
  rw [resonantInductorPortOutput_eq_minusI]
  rcases hinput : input channel with ⟨sourceCoordinate, targetCoordinate⟩
  simp [Complex.mul_re, Complex.mul_im, encodePort, sourcePort, targetPort,
    hinput]
  ring

theorem resonantPeriodicSynchronousState_eq_idealQuarter
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState) (physicalTime : SISecond) :
    resonantPeriodicSynchronousStateAt source input physicalTime =
      harmonicFlow (Real.pi / 2) input := by
  funext channel
  rw [resonantPeriodicSynchronousStateAt,
    resonantPeriodicNormalizedResistor_eq,
    resonantPeriodicNormalizedInductor_eq]
  simp only [synchronousDemodulatedPortAt, harmonicFlow, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul]
  have circle := Real.sin_sq_add_cos_sq
    (resonantSynchronousPhaseAt source channel physicalTime)
  rcases hinput : input channel with ⟨sourceCoordinate, targetCoordinate⟩
  simp only [sourcePort, targetPort, hinput]
  apply Prod.ext <;> dsimp
  · calc
      _ = -(Real.sin
              (resonantSynchronousPhaseAt source channel physicalTime) ^ 2 +
            Real.cos
              (resonantSynchronousPhaseAt source channel physicalTime) ^ 2) *
            targetCoordinate := by ring
      _ = -targetCoordinate := by rw [circle]; ring
      _ = 0 - targetCoordinate := by ring
  · calc
      _ = (Real.sin
              (resonantSynchronousPhaseAt source channel physicalTime) ^ 2 +
            Real.cos
              (resonantSynchronousPhaseAt source channel physicalTime) ^ 2) *
            sourceCoordinate := by ring
      _ = sourceCoordinate := by rw [circle]; ring
      _ = sourceCoordinate + 0 := by ring

/-! ## The same-drive KVL controls the inductor transient -/

theorem resonantActualInductor_sub_periodic_eq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantActualInductorVoltageAt source input initial channel physicalTime -
        resonantPeriodicInductorVoltageAt source input channel physicalTime =
      -(resonantActualResistorVoltageAt
          source input initial channel physicalTime -
        resonantPeriodicResistorVoltageAt
          source input channel physicalTime) -
      (drivenTotalVoltageAt
          (resonantDrivenCoreDimensionedSource source)
          (sourceOwnedResonantDrivenFrequencyAt source)
          (sourceOwnedResonantDrivenDriveAt source input)
          initial channel physicalTime -
        drivenPeriodicVoltageAt
          (resonantDrivenCoreDimensionedSource source) channel
          (sourceOwnedResonantDrivenFrequencyAt source channel)
          (sourceOwnedResonantDrivenDriveAt source input channel)
          physicalTime) := by
  have totalKVL := congrArg SIQuantity.value
    (drivenTotal_forcedKirchhoffVoltageLaw
      (resonantDrivenCoreDimensionedSource source)
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenFrequencyAt_positive source)
      (sourceOwnedResonantDrivenDriveAt source input)
      initial channel physicalTime)
  have periodicKVL := congrArg SIQuantity.value
    (drivenPeriodic_forcedKirchhoffVoltageLaw
      (resonantDrivenCoreDimensionedSource source) channel
      (sourceOwnedResonantDrivenFrequencyAt source channel)
      (sourceOwnedResonantDrivenFrequencyAt_positive source channel)
      (sourceOwnedResonantDrivenDriveAt source input channel) physicalTime)
  apply SIQuantity.ext
  simp only [resonantActualInductorVoltageAt,
    resonantPeriodicInductorVoltageAt, resonantActualResistorVoltageAt,
    resonantPeriodicResistorVoltageAt, inductanceTimesCurrentRate_value,
    resistanceTimesCurrent_value, SIQuantity.add_value, SIQuantity.sub_value,
    SIQuantity.neg_value] at totalKVL periodicKVL ⊢
  linear_combination totalKVL - periodicKVL

def resonantNormalizedResistorErrorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  resonantActualNormalizedResistorAt
      source input initial channel physicalTime -
    resonantPeriodicNormalizedResistorAt source input channel physicalTime

def resonantNormalizedInductorErrorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) : ℝ :=
  resonantActualNormalizedInductorAt
      source input initial channel physicalTime -
    resonantPeriodicNormalizedInductorAt source input channel physicalTime

def resonantNormalizedResistorEnvelopeAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  let physicalSource := resonantDrivenCoreDimensionedSource source
  ((compileFiniteDimensionedSeriesRLCNetlistRun physicalSource
      ).seriesResistanceAt channel).value /
      source.2.voltageScale.value *
    (drivenHomogeneousCurrentEnvelopeAt physicalSource
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input) initial channel).value

def resonantNormalizedInductorEnvelopeAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  let physicalSource := resonantDrivenCoreDimensionedSource source
  (((compileFiniteDimensionedSeriesRLCNetlistRun physicalSource
        ).seriesResistanceAt channel).value *
      (drivenHomogeneousCurrentEnvelopeAt physicalSource
        (sourceOwnedResonantDrivenFrequencyAt source)
        (sourceOwnedResonantDrivenDriveAt source input) initial channel).value +
    (drivenHomogeneousVoltageEnvelopeAt physicalSource
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input) initial channel).value) /
    (resonantInductorOutputScaleAt physicalSource channel).value

theorem resonantNormalizedResistorEnvelope_nonneg
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ resonantNormalizedResistorEnvelopeAt
      source input initial channel := by
  unfold resonantNormalizedResistorEnvelopeAt
  exact mul_nonneg
    (div_nonneg
      (compiledFiniteDimensionedSeriesRLC_resistance_pos
        (resonantDrivenCoreDimensionedSource source) channel).le
      source.2.voltageScalePositive.le)
    (drivenHomogeneousCurrentEnvelope_nonneg
      (resonantDrivenCoreDimensionedSource source)
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input) initial channel)

theorem resonantNormalizedInductorEnvelope_nonneg
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ resonantNormalizedInductorEnvelopeAt
      source input initial channel := by
  unfold resonantNormalizedInductorEnvelopeAt
  exact div_nonneg
    (add_nonneg
      (mul_nonneg
        (compiledFiniteDimensionedSeriesRLC_resistance_pos
          (resonantDrivenCoreDimensionedSource source) channel).le
        (drivenHomogeneousCurrentEnvelope_nonneg
          (resonantDrivenCoreDimensionedSource source)
          (sourceOwnedResonantDrivenFrequencyAt source)
          (sourceOwnedResonantDrivenDriveAt source input) initial channel))
      (drivenHomogeneousVoltageEnvelope_nonneg
        (resonantDrivenCoreDimensionedSource source)
        (sourceOwnedResonantDrivenFrequencyAt source)
        (sourceOwnedResonantDrivenDriveAt source input) initial channel))
    (resonantInductorOutputScale_pos
      (resonantDrivenCoreDimensionedSource source) channel).le

theorem resonantNormalizedResistorError_eq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantNormalizedResistorErrorAt
        source input initial channel physicalTime =
      ((compileFiniteDimensionedSeriesRLCNetlistRun
        (resonantDrivenCoreDimensionedSource source)).seriesResistanceAt
          channel).value / source.2.voltageScale.value *
        (drivenTotalCurrentAt
            (resonantDrivenCoreDimensionedSource source)
            (sourceOwnedResonantDrivenFrequencyAt source)
            (sourceOwnedResonantDrivenDriveAt source input)
            initial channel physicalTime -
          drivenPeriodicCurrentAt
            (resonantDrivenCoreDimensionedSource source) channel
            (sourceOwnedResonantDrivenFrequencyAt source channel)
            (sourceOwnedResonantDrivenDriveAt source input channel)
            physicalTime).value := by
  unfold resonantNormalizedResistorErrorAt
    resonantActualNormalizedResistorAt
    resonantPeriodicNormalizedResistorAt
    resonantActualResistorVoltageAt resonantPeriodicResistorVoltageAt
  simp only [resistanceTimesCurrent_value, SIQuantity.sub_value]
  ring

theorem resonantNormalizedResistorError_abs_le
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    |resonantNormalizedResistorErrorAt
        source input initial channel physicalTime| ≤
      drivenHomogeneousDecayAt
          (resonantDrivenCoreDimensionedSource source) channel physicalTime *
        resonantNormalizedResistorEnvelopeAt
          source input initial channel := by
  rw [resonantNormalizedResistorError_eq]
  have currentBound := drivenTotal_currentError_abs_le_envelope
    (resonantDrivenCoreDimensionedSource source)
    (sourceOwnedResonantDrivenFrequencyAt source)
    (sourceOwnedResonantDrivenDriveAt source input)
    initial channel physicalTime
  have coefficientPositive :
      0 < ((compileFiniteDimensionedSeriesRLCNetlistRun
        (resonantDrivenCoreDimensionedSource source)).seriesResistanceAt
          channel).value / source.2.voltageScale.value :=
    div_pos
      (compiledFiniteDimensionedSeriesRLC_resistance_pos
        (resonantDrivenCoreDimensionedSource source) channel)
      source.2.voltageScalePositive
  rw [abs_mul, abs_of_pos coefficientPositive]
  calc
    _ ≤ ((compileFiniteDimensionedSeriesRLCNetlistRun
          (resonantDrivenCoreDimensionedSource source)).seriesResistanceAt
            channel).value / source.2.voltageScale.value *
        (drivenHomogeneousDecayAt
            (resonantDrivenCoreDimensionedSource source) channel physicalTime *
          (drivenHomogeneousCurrentEnvelopeAt
            (resonantDrivenCoreDimensionedSource source)
            (sourceOwnedResonantDrivenFrequencyAt source)
            (sourceOwnedResonantDrivenDriveAt source input)
            initial channel).value) :=
      mul_le_mul_of_nonneg_left currentBound coefficientPositive.le
    _ = _ := by
      unfold resonantNormalizedResistorEnvelopeAt
      ring

theorem resonantNormalizedInductorError_eq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    resonantNormalizedInductorErrorAt
        source input initial channel physicalTime =
      (-(resonantActualResistorVoltageAt
          source input initial channel physicalTime -
        resonantPeriodicResistorVoltageAt
          source input channel physicalTime).value -
        (drivenTotalVoltageAt
            (resonantDrivenCoreDimensionedSource source)
            (sourceOwnedResonantDrivenFrequencyAt source)
            (sourceOwnedResonantDrivenDriveAt source input)
            initial channel physicalTime -
          drivenPeriodicVoltageAt
            (resonantDrivenCoreDimensionedSource source) channel
            (sourceOwnedResonantDrivenFrequencyAt source channel)
            (sourceOwnedResonantDrivenDriveAt source input channel)
            physicalTime).value) /
        (resonantInductorOutputScaleAt
          (resonantDrivenCoreDimensionedSource source) channel).value := by
  unfold resonantNormalizedInductorErrorAt
    resonantActualNormalizedInductorAt
    resonantPeriodicNormalizedInductorAt
  rw [← sub_div]
  congr 1
  exact congrArg SIQuantity.value
    (resonantActualInductor_sub_periodic_eq
      source input initial channel physicalTime)

theorem resonantNormalizedInductorError_abs_le
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    |resonantNormalizedInductorErrorAt
        source input initial channel physicalTime| ≤
      drivenHomogeneousDecayAt
          (resonantDrivenCoreDimensionedSource source) channel physicalTime *
        resonantNormalizedInductorEnvelopeAt
          source input initial channel := by
  rw [resonantNormalizedInductorError_eq]
  let physicalSource := resonantDrivenCoreDimensionedSource source
  let resistance := ((compileFiniteDimensionedSeriesRLCNetlistRun
    physicalSource).seriesResistanceAt channel).value
  let currentError := (drivenTotalCurrentAt physicalSource
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input)
      initial channel physicalTime -
    drivenPeriodicCurrentAt physicalSource channel
      (sourceOwnedResonantDrivenFrequencyAt source channel)
      (sourceOwnedResonantDrivenDriveAt source input channel)
      physicalTime).value
  let voltageError := (drivenTotalVoltageAt physicalSource
      (sourceOwnedResonantDrivenFrequencyAt source)
      (sourceOwnedResonantDrivenDriveAt source input)
      initial channel physicalTime -
    drivenPeriodicVoltageAt physicalSource channel
      (sourceOwnedResonantDrivenFrequencyAt source channel)
      (sourceOwnedResonantDrivenDriveAt source input channel)
      physicalTime).value
  let outputScale :=
    (resonantInductorOutputScaleAt physicalSource channel).value
  have resistancePositive : 0 < resistance :=
    compiledFiniteDimensionedSeriesRLC_resistance_pos physicalSource channel
  have outputScalePositive : 0 < outputScale :=
    resonantInductorOutputScale_pos physicalSource channel
  have resistorErrorEq :
      (resonantActualResistorVoltageAt
          source input initial channel physicalTime -
        resonantPeriodicResistorVoltageAt
          source input channel physicalTime).value =
        resistance * currentError := by
    simp only [resonantActualResistorVoltageAt,
      resonantPeriodicResistorVoltageAt, resistanceTimesCurrent_value,
      SIQuantity.sub_value]
    change resistance *
          (drivenTotalCurrentAt physicalSource
            (sourceOwnedResonantDrivenFrequencyAt source)
            (sourceOwnedResonantDrivenDriveAt source input)
            initial channel physicalTime).value -
        resistance *
          (drivenPeriodicCurrentAt physicalSource channel
            (sourceOwnedResonantDrivenFrequencyAt source channel)
            (sourceOwnedResonantDrivenDriveAt source input channel)
            physicalTime).value =
      resistance * currentError
    dsimp only [currentError]
    simp only [SIQuantity.sub_value]
    ring
  have voltageErrorEq :
      (drivenTotalVoltageAt
          (resonantDrivenCoreDimensionedSource source)
          (sourceOwnedResonantDrivenFrequencyAt source)
          (sourceOwnedResonantDrivenDriveAt source input)
          initial channel physicalTime -
        drivenPeriodicVoltageAt
          (resonantDrivenCoreDimensionedSource source) channel
          (sourceOwnedResonantDrivenFrequencyAt source channel)
          (sourceOwnedResonantDrivenDriveAt source input channel)
          physicalTime).value = voltageError := rfl
  have outputScaleEq :
      (resonantInductorOutputScaleAt
        (resonantDrivenCoreDimensionedSource source) channel).value =
        outputScale := rfl
  have currentBound := drivenTotal_currentError_abs_le_envelope
    physicalSource (sourceOwnedResonantDrivenFrequencyAt source)
    (sourceOwnedResonantDrivenDriveAt source input)
    initial channel physicalTime
  have voltageBound := drivenTotal_voltageError_abs_le_envelope
    physicalSource (sourceOwnedResonantDrivenFrequencyAt source)
    (sourceOwnedResonantDrivenDriveAt source input)
    initial channel physicalTime
  rw [resistorErrorEq, voltageErrorEq, outputScaleEq]
  change |(-(resistance * currentError) - voltageError) / outputScale| ≤ _
  rw [abs_div, abs_of_pos outputScalePositive]
  calc
    |-(resistance * currentError) - voltageError| / outputScale ≤
        (resistance * |currentError| + |voltageError|) / outputScale := by
      apply div_le_div_of_nonneg_right _ outputScalePositive.le
      calc
        |-(resistance * currentError) - voltageError| ≤
            |-(resistance * currentError)| + |voltageError| := abs_sub _ _
        _ = resistance * |currentError| + |voltageError| := by
          rw [abs_neg, abs_mul, abs_of_pos resistancePositive]
    _ ≤ (resistance *
          (drivenHomogeneousDecayAt physicalSource channel physicalTime *
            (drivenHomogeneousCurrentEnvelopeAt physicalSource
              (sourceOwnedResonantDrivenFrequencyAt source)
              (sourceOwnedResonantDrivenDriveAt source input)
              initial channel).value) +
        drivenHomogeneousDecayAt physicalSource channel physicalTime *
          (drivenHomogeneousVoltageEnvelopeAt physicalSource
            (sourceOwnedResonantDrivenFrequencyAt source)
            (sourceOwnedResonantDrivenDriveAt source input)
            initial channel).value) / outputScale := by
      apply div_le_div_of_nonneg_right _ outputScalePositive.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left currentBound resistancePositive.le)
        voltageBound
    _ = _ := by
      unfold resonantNormalizedInductorEnvelopeAt
      simp only [physicalSource, resistance, outputScale]
      ring

end

end Producer
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.resonantPeriodicSynchronousState_eq_idealQuarter
