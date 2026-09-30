import Mathlib.Analysis.SpecialFunctions.Exp
import H0mework.Physics.RLCResponse.Tolerance
import H0mework.Physics.RLCResponse.Response

/-!
# Quantitative transient envelope and finite settling time

The qualitative moving-orbit limit is strengthened to an explicit exponential
bound.  Voltage and current are bounded in their own SI dimensions; only their
ratios to matching positive tolerances are combined into a dimensionless
settling budget.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

/-- A total, explicit finite settling time.  The dimensionless `+1` makes the
eventual inequality strict while retaining a purely algebraic compiler. -/
def positiveExponentialSettlingTime
    (decayRate envelope tolerance : ℝ) : ℝ :=
  (envelope / tolerance + 1) / decayRate

theorem positiveExponentialSettlingTime_pos
    {decayRate envelope tolerance : ℝ}
    (decayRatePositive : 0 < decayRate)
    (envelopeNonnegative : 0 ≤ envelope)
    (tolerancePositive : 0 < tolerance) :
    0 < positiveExponentialSettlingTime decayRate envelope tolerance := by
  unfold positiveExponentialSettlingTime
  exact div_pos
    (add_pos_of_nonneg_of_pos
      (div_nonneg envelopeNonnegative tolerancePositive.le) zero_lt_one)
    decayRatePositive

theorem positiveExponentialEnvelope_settles
    {decayRate envelope tolerance physicalTime : ℝ}
    (decayRatePositive : 0 < decayRate)
    (tolerancePositive : 0 < tolerance)
    (afterSettling :
      positiveExponentialSettlingTime decayRate envelope tolerance ≤
        physicalTime) :
    envelope * Real.exp (-decayRate * physicalTime) < tolerance := by
  let exponent := decayRate * physicalTime
  have thresholdLeExponent : envelope / tolerance + 1 ≤ exponent := by
    have scaled := (div_le_iff₀ decayRatePositive).mp afterSettling
    simpa [positiveExponentialSettlingTime, exponent,
      mul_comm] using scaled
  have normalizedEnvelopeLt : envelope / tolerance < exponent :=
    lt_of_lt_of_le (lt_add_one _) thresholdLeExponent
  have envelopeLtLinear : envelope < exponent * tolerance :=
    (div_lt_iff₀ tolerancePositive).mp normalizedEnvelopeLt
  have exponentLtExp : exponent < Real.exp exponent :=
    lt_of_lt_of_le (lt_add_one exponent) (Real.add_one_le_exp exponent)
  have envelopeLtExp : envelope < tolerance * Real.exp exponent := by
    calc
      envelope < exponent * tolerance := envelopeLtLinear
      _ = tolerance * exponent := mul_comm _ _
      _ < tolerance * Real.exp exponent :=
        mul_lt_mul_of_pos_left exponentLtExp tolerancePositive
  have negExponent : -decayRate * physicalTime = -exponent := by
    simp [exponent]
  rw [negExponent, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.exp_pos exponent)).2 envelopeLtExp

/-! ## Explicit bounds for the compiled homogeneous trajectory -/

def finiteSeriesRLCInitialCoordinateEnvelopeAt
    (initial : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  |sourcePort initial channel| + |targetPort initial channel|

theorem finiteSeriesRLCInitialCoordinateEnvelopeAt_nonneg
    (initial : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem finiteSeriesRLC_sourcePort_abs_le_envelope
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (time : ℝ) :
    |sourcePort (finiteSeriesRLCFlowAt run initial time) channel| ≤
      finiteSeriesRLCScaleAt run channel time *
        finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel := by
  have harmonicBound :
      |Real.cos (run.baseRun.frequencyAt channel * time) *
            sourcePort initial channel -
          Real.sin (run.baseRun.frequencyAt channel * time) *
            targetPort initial channel| ≤
        finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel := by
    calc
      |Real.cos (run.baseRun.frequencyAt channel * time) *
            sourcePort initial channel -
          Real.sin (run.baseRun.frequencyAt channel * time) *
            targetPort initial channel| ≤
          |Real.cos (run.baseRun.frequencyAt channel * time) *
              sourcePort initial channel| +
            |Real.sin (run.baseRun.frequencyAt channel * time) *
              targetPort initial channel| := abs_sub _ _
      _ = |Real.cos (run.baseRun.frequencyAt channel * time)| *
              |sourcePort initial channel| +
            |Real.sin (run.baseRun.frequencyAt channel * time)| *
              |targetPort initial channel| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |sourcePort initial channel| +
            1 * |targetPort initial channel| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
              (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _)
              (abs_nonneg _))
      _ = finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel := by
          simp [finiteSeriesRLCInitialCoordinateEnvelopeAt]
  change
    |finiteSeriesRLCScaleAt run channel time *
        (Real.cos (run.baseRun.frequencyAt channel * time) *
            sourcePort initial channel -
          Real.sin (run.baseRun.frequencyAt channel * time) *
            targetPort initial channel)| ≤ _
  have scalePositive : 0 < finiteSeriesRLCScaleAt run channel time :=
    Real.exp_pos _
  rw [abs_mul, abs_of_pos scalePositive]
  exact mul_le_mul_of_nonneg_left harmonicBound (Real.exp_pos _).le

theorem finiteSeriesRLC_targetPort_abs_le_envelope
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) (time : ℝ) :
    |targetPort (finiteSeriesRLCFlowAt run initial time) channel| ≤
      finiteSeriesRLCScaleAt run channel time *
        finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel := by
  have harmonicBound :
      |Real.sin (run.baseRun.frequencyAt channel * time) *
            sourcePort initial channel +
          Real.cos (run.baseRun.frequencyAt channel * time) *
            targetPort initial channel| ≤
        finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel := by
    calc
      |Real.sin (run.baseRun.frequencyAt channel * time) *
            sourcePort initial channel +
          Real.cos (run.baseRun.frequencyAt channel * time) *
            targetPort initial channel| ≤
          |Real.sin (run.baseRun.frequencyAt channel * time) *
              sourcePort initial channel| +
            |Real.cos (run.baseRun.frequencyAt channel * time) *
              targetPort initial channel| := abs_add_le _ _
      _ = |Real.sin (run.baseRun.frequencyAt channel * time)| *
              |sourcePort initial channel| +
            |Real.cos (run.baseRun.frequencyAt channel * time)| *
              |targetPort initial channel| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |sourcePort initial channel| +
            1 * |targetPort initial channel| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _)
              (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
              (abs_nonneg _))
      _ = finiteSeriesRLCInitialCoordinateEnvelopeAt initial channel := by
          simp [finiteSeriesRLCInitialCoordinateEnvelopeAt]
  change
    |finiteSeriesRLCScaleAt run channel time *
        (Real.sin (run.baseRun.frequencyAt channel * time) *
            sourcePort initial channel +
          Real.cos (run.baseRun.frequencyAt channel * time) *
            targetPort initial channel)| ≤ _
  have scalePositive : 0 < finiteSeriesRLCScaleAt run channel time :=
    Real.exp_pos _
  rw [abs_mul, abs_of_pos scalePositive]
  exact mul_le_mul_of_nonneg_left harmonicBound (Real.exp_pos _).le

def drivenHomogeneousCoordinateEnvelopeAt
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  finiteSeriesRLCInitialCoordinateEnvelopeAt
    (drivenHomogeneousInitialAt source frequencyAt driveAt initial) channel

def drivenHomogeneousVoltageEnvelopeAt
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  SIQuantity.scale
    (drivenHomogeneousCoordinateEnvelopeAt
      source frequencyAt driveAt initial channel)
    source.2.voltageScale

def drivenHomogeneousCurrentEnvelopeAt
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) : SIAmpere :=
  let run := compileFiniteSeriesRLCNetlistRun source.1
  SIQuantity.scale
    ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) *
      drivenHomogeneousCoordinateEnvelopeAt
        source frequencyAt driveAt initial channel)
    source.2.currentScale

def drivenHomogeneousDecayAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : ℝ :=
  Real.exp
    (-((compileFiniteDimensionedSeriesRLCNetlistRun source
      ).dampingRateAt channel).value * physicalTime.value)

theorem drivenHomogeneousDecayAt_eq_normalizedScale
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    drivenHomogeneousDecayAt source channel physicalTime =
      finiteSeriesRLCScaleAt (compileFiniteSeriesRLCNetlistRun source.1)
        channel
        (finiteDimensionedSeriesRLCNormalizedTimeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          physicalTime) := by
  unfold drivenHomogeneousDecayAt finiteSeriesRLCScaleAt
    finiteDimensionedSeriesRLCNormalizedTimeAt
  congr 1
  simp only [compiledFiniteDimensionedSeriesRLC_damping_scaling,
    SIQuantity.castDimension_value, SIQuantity.div_value,
    SIQuantity.dimensionlessValue_value,
    compiledFiniteDimensionedSeriesRLC_scale,
    SIQuantity.sameDimensionRatio_value]
  field_simp [source.2.timeScale_ne]

theorem drivenHomogeneousVoltageEnvelope_nonneg
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ (drivenHomogeneousVoltageEnvelopeAt
      source frequencyAt driveAt initial channel).value := by
  simp only [drivenHomogeneousVoltageEnvelopeAt, SIQuantity.scale_value]
  exact mul_nonneg
    (finiteSeriesRLCInitialCoordinateEnvelopeAt_nonneg _ _)
    source.2.voltageScalePositive.le

theorem drivenHomogeneousCurrentEnvelope_nonneg
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ (drivenHomogeneousCurrentEnvelopeAt
      source frequencyAt driveAt initial channel).value := by
  simp only [drivenHomogeneousCurrentEnvelopeAt, SIQuantity.scale_value]
  exact mul_nonneg
    (mul_nonneg
      (add_nonneg
        (compiledFiniteSeriesRLCNetlistRun_frequency_pos source.1 channel).le
        (by
          rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
          exact finiteSeriesRLCDampingRate_pos.le))
      (finiteSeriesRLCInitialCoordinateEnvelopeAt_nonneg _ _))
    source.2.currentScalePositive.le

theorem compiledDrivenHomogeneous_voltage_abs_le_envelope
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    |(finiteDimensionedSeriesRLCVoltageAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source)
      (drivenHomogeneousInitialAt source frequencyAt driveAt initial)
      channel physicalTime).value| ≤
      drivenHomogeneousDecayAt source channel physicalTime *
        (drivenHomogeneousVoltageEnvelopeAt
          source frequencyAt driveAt initial channel).value := by
  have normalizedBound := finiteSeriesRLC_targetPort_abs_le_envelope
    (compileFiniteSeriesRLCNetlistRun source.1)
    (drivenHomogeneousInitialAt source frequencyAt driveAt initial) channel
    (finiteDimensionedSeriesRLCNormalizedTimeAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) physicalTime)
  simp only [finiteDimensionedSeriesRLCVoltageAt,
    compiledFiniteDimensionedSeriesRLC_normalizedRun,
    compiledFiniteDimensionedSeriesRLC_scale,
    SIQuantity.scale_value, abs_mul]
  rw [abs_of_pos source.2.voltageScalePositive]
  rw [drivenHomogeneousDecayAt_eq_normalizedScale]
  calc
    |finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun source.1)
          (drivenHomogeneousInitialAt source frequencyAt driveAt initial)
          channel
          (finiteDimensionedSeriesRLCNormalizedTimeAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source)
            physicalTime)| * source.2.voltageScale.value ≤
        (finiteSeriesRLCScaleAt
            (compileFiniteSeriesRLCNetlistRun source.1) channel
            (finiteDimensionedSeriesRLCNormalizedTimeAt
              (compileFiniteDimensionedSeriesRLCNetlistRun source)
              physicalTime) *
          drivenHomogeneousCoordinateEnvelopeAt
            source frequencyAt driveAt initial channel) *
          source.2.voltageScale.value :=
      mul_le_mul_of_nonneg_right normalizedBound
        source.2.voltageScalePositive.le
    _ = _ := by
      simp [drivenHomogeneousVoltageEnvelopeAt,
        drivenHomogeneousCoordinateEnvelopeAt]
      ring

theorem compiledDrivenHomogeneous_current_abs_le_envelope
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    |(finiteDimensionedSeriesRLCCurrentAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source)
      (drivenHomogeneousInitialAt source frequencyAt driveAt initial)
      channel physicalTime).value| ≤
      drivenHomogeneousDecayAt source channel physicalTime *
        (drivenHomogeneousCurrentEnvelopeAt
          source frequencyAt driveAt initial channel).value := by
  let run := compileFiniteSeriesRLCNetlistRun source.1
  let residual := drivenHomogeneousInitialAt source frequencyAt driveAt initial
  let normalizedTime := finiteDimensionedSeriesRLCNormalizedTimeAt
    (compileFiniteDimensionedSeriesRLCNetlistRun source) physicalTime
  have sourceBound := finiteSeriesRLC_sourcePort_abs_le_envelope
    run residual channel normalizedTime
  have targetBound := finiteSeriesRLC_targetPort_abs_le_envelope
    run residual channel normalizedTime
  have frequencyPositive : 0 < run.baseRun.frequencyAt channel :=
    compiledFiniteSeriesRLCNetlistRun_frequency_pos source.1 channel
  have dampingPositive : 0 < run.dampingRateAt channel := by
    rw [show run.dampingRateAt channel = finiteSeriesRLCDampingRate by rfl]
    exact finiteSeriesRLCDampingRate_pos
  have normalizedCurrentBound :
      |finiteSeriesRLCCurrentAt run residual channel normalizedTime| ≤
        finiteSeriesRLCScaleAt run channel normalizedTime *
          ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) *
            finiteSeriesRLCInitialCoordinateEnvelopeAt residual channel) := by
    simp only [finiteSeriesRLCCurrentAt]
    calc
      |run.baseRun.frequencyAt channel *
            sourcePort (finiteSeriesRLCFlowAt run residual normalizedTime)
              channel -
          run.dampingRateAt channel *
            targetPort (finiteSeriesRLCFlowAt run residual normalizedTime)
              channel| ≤
          |run.baseRun.frequencyAt channel *
            sourcePort (finiteSeriesRLCFlowAt run residual normalizedTime)
              channel| +
          |run.dampingRateAt channel *
            targetPort (finiteSeriesRLCFlowAt run residual normalizedTime)
              channel| := abs_sub _ _
      _ = run.baseRun.frequencyAt channel *
              |sourcePort (finiteSeriesRLCFlowAt run residual normalizedTime)
                channel| +
            run.dampingRateAt channel *
              |targetPort (finiteSeriesRLCFlowAt run residual normalizedTime)
                channel| := by
          rw [abs_mul, abs_mul, abs_of_pos frequencyPositive,
            abs_of_pos dampingPositive]
      _ ≤ run.baseRun.frequencyAt channel *
              (finiteSeriesRLCScaleAt run channel normalizedTime *
                finiteSeriesRLCInitialCoordinateEnvelopeAt residual channel) +
            run.dampingRateAt channel *
              (finiteSeriesRLCScaleAt run channel normalizedTime *
                finiteSeriesRLCInitialCoordinateEnvelopeAt residual channel) :=
          add_le_add
            (mul_le_mul_of_nonneg_left sourceBound frequencyPositive.le)
            (mul_le_mul_of_nonneg_left targetBound dampingPositive.le)
      _ = _ := by ring
  simp only [finiteDimensionedSeriesRLCCurrentAt,
    compiledFiniteDimensionedSeriesRLC_normalizedRun,
    compiledFiniteDimensionedSeriesRLC_scale,
    SIQuantity.scale_value, abs_mul]
  rw [abs_of_pos source.2.currentScalePositive]
  rw [drivenHomogeneousDecayAt_eq_normalizedScale]
  calc
    |finiteSeriesRLCCurrentAt run residual channel normalizedTime| *
        source.2.currentScale.value ≤
      (finiteSeriesRLCScaleAt run channel normalizedTime *
        ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) *
          finiteSeriesRLCInitialCoordinateEnvelopeAt residual channel)) *
        source.2.currentScale.value :=
      mul_le_mul_of_nonneg_right normalizedCurrentBound
        source.2.currentScalePositive.le
    _ = _ := by
      simp [drivenHomogeneousCurrentEnvelopeAt,
        drivenHomogeneousCoordinateEnvelopeAt, run, residual,
        normalizedTime]
      ring

theorem drivenTotal_voltageError_abs_le_envelope
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    |(drivenTotalVoltageAt source frequencyAt driveAt initial channel
          physicalTime -
        drivenPeriodicVoltageAt source channel (frequencyAt channel)
          (driveAt channel) physicalTime).value| ≤
      drivenHomogeneousDecayAt source channel physicalTime *
        (drivenHomogeneousVoltageEnvelopeAt
          source frequencyAt driveAt initial channel).value := by
  simpa [drivenTotalVoltageAt] using
    compiledDrivenHomogeneous_voltage_abs_le_envelope
      source frequencyAt driveAt initial channel physicalTime

theorem drivenTotal_currentError_abs_le_envelope
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    |(drivenTotalCurrentAt source frequencyAt driveAt initial channel
          physicalTime -
        drivenPeriodicCurrentAt source channel (frequencyAt channel)
          (driveAt channel) physicalTime).value| ≤
      drivenHomogeneousDecayAt source channel physicalTime *
        (drivenHomogeneousCurrentEnvelopeAt
          source frequencyAt driveAt initial channel).value := by
  simpa [drivenTotalCurrentAt] using
    compiledDrivenHomogeneous_current_abs_le_envelope
      source frequencyAt driveAt initial channel physicalTime

def drivenCommonPhysicalDampingRate
    (source : DimensionedSeriesRLCSource) : ℝ :=
  finiteSeriesRLCDampingRate / source.2.timeScale.value

theorem drivenCommonPhysicalDampingRate_pos
    (source : DimensionedSeriesRLCSource) :
    0 < drivenCommonPhysicalDampingRate source :=
  div_pos finiteSeriesRLCDampingRate_pos source.2.timeScalePositive

theorem compiledDrivenPhysicalDamping_eq_common
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    ((compileFiniteDimensionedSeriesRLCNetlistRun source).dampingRateAt
      channel).value = drivenCommonPhysicalDampingRate source := by
  simp [drivenCommonPhysicalDampingRate,
    compiledFiniteSeriesRLCNetlistRun_dampingRateAt]

theorem drivenHomogeneousDecayAt_eq_commonExponential
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    drivenHomogeneousDecayAt source channel physicalTime =
      Real.exp
        (-drivenCommonPhysicalDampingRate source * physicalTime.value) := by
  unfold drivenHomogeneousDecayAt
  rw [compiledDrivenPhysicalDamping_eq_common]

def drivenPortToleranceEnvelopeBudgetAt
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (drivenHomogeneousVoltageEnvelopeAt
      source frequencyAt driveAt initial channel).value /
      tolerance.voltageTolerance.value +
    (drivenHomogeneousCurrentEnvelopeAt
      source frequencyAt driveAt initial channel).value /
      tolerance.currentTolerance.value

theorem drivenPortToleranceEnvelopeBudgetAt_nonneg
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ drivenPortToleranceEnvelopeBudgetAt
      source frequencyAt driveAt initial tolerance channel :=
  add_nonneg
    (div_nonneg
      (drivenHomogeneousVoltageEnvelope_nonneg
        source frequencyAt driveAt initial channel)
      tolerance.voltageTolerancePositive.le)
    (div_nonneg
      (drivenHomogeneousCurrentEnvelope_nonneg
        source frequencyAt driveAt initial channel)
      tolerance.currentTolerancePositive.le)

def drivenWholePortToleranceEnvelopeBudget
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance) : ℝ :=
  ∑ channel : FiniteEmbodimentChannel,
    drivenPortToleranceEnvelopeBudgetAt
      source frequencyAt driveAt initial tolerance channel

theorem drivenWholePortToleranceEnvelopeBudget_nonneg
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance) :
    0 ≤ drivenWholePortToleranceEnvelopeBudget
      source frequencyAt driveAt initial tolerance := by
  unfold drivenWholePortToleranceEnvelopeBudget
  exact Finset.sum_nonneg fun channel _ =>
    drivenPortToleranceEnvelopeBudgetAt_nonneg
      source frequencyAt driveAt initial tolerance channel

theorem drivenVoltageEnvelopeRatio_le_wholeBudget
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (channel : FiniteEmbodimentChannel) :
    (drivenHomogeneousVoltageEnvelopeAt
        source frequencyAt driveAt initial channel).value /
        tolerance.voltageTolerance.value ≤
      drivenWholePortToleranceEnvelopeBudget
        source frequencyAt driveAt initial tolerance := by
  have currentRatioNonnegative :
      0 ≤ (drivenHomogeneousCurrentEnvelopeAt
        source frequencyAt driveAt initial channel).value /
          tolerance.currentTolerance.value :=
    div_nonneg
      (drivenHomogeneousCurrentEnvelope_nonneg
        source frequencyAt driveAt initial channel)
      tolerance.currentTolerancePositive.le
  have termLeSum :
      drivenPortToleranceEnvelopeBudgetAt
          source frequencyAt driveAt initial tolerance channel ≤
        drivenWholePortToleranceEnvelopeBudget
          source frequencyAt driveAt initial tolerance := by
    unfold drivenWholePortToleranceEnvelopeBudget
    exact Finset.single_le_sum
      (fun other _ => drivenPortToleranceEnvelopeBudgetAt_nonneg
        source frequencyAt driveAt initial tolerance other)
      (Finset.mem_univ channel)
  unfold drivenPortToleranceEnvelopeBudgetAt at termLeSum
  linarith

theorem drivenCurrentEnvelopeRatio_le_wholeBudget
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (channel : FiniteEmbodimentChannel) :
    (drivenHomogeneousCurrentEnvelopeAt
        source frequencyAt driveAt initial channel).value /
        tolerance.currentTolerance.value ≤
      drivenWholePortToleranceEnvelopeBudget
        source frequencyAt driveAt initial tolerance := by
  have voltageRatioNonnegative :
      0 ≤ (drivenHomogeneousVoltageEnvelopeAt
        source frequencyAt driveAt initial channel).value /
          tolerance.voltageTolerance.value :=
    div_nonneg
      (drivenHomogeneousVoltageEnvelope_nonneg
        source frequencyAt driveAt initial channel)
      tolerance.voltageTolerancePositive.le
  have termLeSum :
      drivenPortToleranceEnvelopeBudgetAt
          source frequencyAt driveAt initial tolerance channel ≤
        drivenWholePortToleranceEnvelopeBudget
          source frequencyAt driveAt initial tolerance := by
    unfold drivenWholePortToleranceEnvelopeBudget
    exact Finset.single_le_sum
      (fun other _ => drivenPortToleranceEnvelopeBudgetAt_nonneg
        source frequencyAt driveAt initial tolerance other)
      (Finset.mem_univ channel)
  unfold drivenPortToleranceEnvelopeBudgetAt at termLeSum
  linarith

def drivenWholePortSettlingDuration
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance) : SISecond :=
  ⟨positiveExponentialSettlingTime
    (drivenCommonPhysicalDampingRate source)
    (drivenWholePortToleranceEnvelopeBudget
      source frequencyAt driveAt initial tolerance)
    1⟩

theorem drivenWholePortSettlingDuration_pos
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance) :
    0 < (drivenWholePortSettlingDuration
      source frequencyAt driveAt initial tolerance).value :=
  positiveExponentialSettlingTime_pos
    (drivenCommonPhysicalDampingRate_pos source)
    (drivenWholePortToleranceEnvelopeBudget_nonneg
      source frequencyAt driveAt initial tolerance)
    zero_lt_one

theorem drivenWholePort_afterSettling_envelope_lt_one
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (physicalTime : SISecond)
    (afterSettling :
      (drivenWholePortSettlingDuration
        source frequencyAt driveAt initial tolerance).value ≤
        physicalTime.value) :
    drivenWholePortToleranceEnvelopeBudget
        source frequencyAt driveAt initial tolerance *
      Real.exp
        (-drivenCommonPhysicalDampingRate source * physicalTime.value) < 1 :=
  positiveExponentialEnvelope_settles
    (drivenCommonPhysicalDampingRate_pos source) zero_lt_one afterSettling

theorem drivenTotal_afterSettling_voltageError_lt
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (physicalTime : SISecond)
    (afterSettling :
      (drivenWholePortSettlingDuration
        source frequencyAt driveAt initial tolerance).value ≤
        physicalTime.value)
    (channel : FiniteEmbodimentChannel) :
    |(drivenTotalVoltageAt source frequencyAt driveAt initial channel
          physicalTime -
        drivenPeriodicVoltageAt source channel (frequencyAt channel)
          (driveAt channel) physicalTime).value| <
      tolerance.voltageTolerance.value := by
  have pointwise := drivenTotal_voltageError_abs_le_envelope
    source frequencyAt driveAt initial channel physicalTime
  have ratioLe := drivenVoltageEnvelopeRatio_le_wholeBudget
    source frequencyAt driveAt initial tolerance channel
  have decayPositive :
      0 < drivenHomogeneousDecayAt source channel physicalTime :=
    Real.exp_pos _
  have wholeSettles := drivenWholePort_afterSettling_envelope_lt_one
    source frequencyAt driveAt initial tolerance physicalTime afterSettling
  rw [drivenHomogeneousDecayAt_eq_commonExponential] at pointwise
  have normalizedEnvelopeSettles :
      ((drivenHomogeneousVoltageEnvelopeAt
          source frequencyAt driveAt initial channel).value /
          tolerance.voltageTolerance.value) *
        Real.exp
          (-drivenCommonPhysicalDampingRate source * physicalTime.value) <
        1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right ratioLe decayPositive.le) wholeSettles
  have envelopeSettles :
      Real.exp
          (-drivenCommonPhysicalDampingRate source * physicalTime.value) *
        (drivenHomogeneousVoltageEnvelopeAt
          source frequencyAt driveAt initial channel).value <
        tolerance.voltageTolerance.value := by
    have quotientLt :
        (Real.exp
              (-drivenCommonPhysicalDampingRate source * physicalTime.value) *
            (drivenHomogeneousVoltageEnvelopeAt
              source frequencyAt driveAt initial channel).value) /
            tolerance.voltageTolerance.value < 1 := by
      calc
        (Real.exp
              (-drivenCommonPhysicalDampingRate source * physicalTime.value) *
            (drivenHomogeneousVoltageEnvelopeAt
              source frequencyAt driveAt initial channel).value) /
            tolerance.voltageTolerance.value =
          ((drivenHomogeneousVoltageEnvelopeAt
              source frequencyAt driveAt initial channel).value /
              tolerance.voltageTolerance.value) *
            Real.exp
              (-drivenCommonPhysicalDampingRate source * physicalTime.value) := by
            ring
        _ < 1 := normalizedEnvelopeSettles
    have productLt :=
      (div_lt_iff₀ tolerance.voltageTolerancePositive).mp quotientLt
    simpa using productLt
  exact lt_of_le_of_lt pointwise envelopeSettles

theorem drivenTotal_afterSettling_currentError_lt
    (source : DimensionedSeriesRLCSource)
    (frequencyAt : FiniteEmbodimentChannel → SIHertz)
    (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (tolerance : PositiveDrivenPortTolerance)
    (physicalTime : SISecond)
    (afterSettling :
      (drivenWholePortSettlingDuration
        source frequencyAt driveAt initial tolerance).value ≤
        physicalTime.value)
    (channel : FiniteEmbodimentChannel) :
    |(drivenTotalCurrentAt source frequencyAt driveAt initial channel
          physicalTime -
        drivenPeriodicCurrentAt source channel (frequencyAt channel)
          (driveAt channel) physicalTime).value| <
      tolerance.currentTolerance.value := by
  have pointwise := drivenTotal_currentError_abs_le_envelope
    source frequencyAt driveAt initial channel physicalTime
  have ratioLe := drivenCurrentEnvelopeRatio_le_wholeBudget
    source frequencyAt driveAt initial tolerance channel
  have decayPositive :
      0 < drivenHomogeneousDecayAt source channel physicalTime :=
    Real.exp_pos _
  have wholeSettles := drivenWholePort_afterSettling_envelope_lt_one
    source frequencyAt driveAt initial tolerance physicalTime afterSettling
  rw [drivenHomogeneousDecayAt_eq_commonExponential] at pointwise
  have normalizedEnvelopeSettles :
      ((drivenHomogeneousCurrentEnvelopeAt
          source frequencyAt driveAt initial channel).value /
          tolerance.currentTolerance.value) *
        Real.exp
          (-drivenCommonPhysicalDampingRate source * physicalTime.value) <
        1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right ratioLe decayPositive.le) wholeSettles
  have envelopeSettles :
      Real.exp
          (-drivenCommonPhysicalDampingRate source * physicalTime.value) *
        (drivenHomogeneousCurrentEnvelopeAt
          source frequencyAt driveAt initial channel).value <
        tolerance.currentTolerance.value := by
    have quotientLt :
        (Real.exp
              (-drivenCommonPhysicalDampingRate source * physicalTime.value) *
            (drivenHomogeneousCurrentEnvelopeAt
              source frequencyAt driveAt initial channel).value) /
            tolerance.currentTolerance.value < 1 := by
      calc
        (Real.exp
              (-drivenCommonPhysicalDampingRate source * physicalTime.value) *
            (drivenHomogeneousCurrentEnvelopeAt
              source frequencyAt driveAt initial channel).value) /
            tolerance.currentTolerance.value =
          ((drivenHomogeneousCurrentEnvelopeAt
              source frequencyAt driveAt initial channel).value /
              tolerance.currentTolerance.value) *
            Real.exp
              (-drivenCommonPhysicalDampingRate source * physicalTime.value) := by
            ring
        _ < 1 := normalizedEnvelopeSettles
    have productLt :=
      (div_lt_iff₀ tolerance.currentTolerancePositive).mp quotientLt
    simpa using productLt
  exact lt_of_le_of_lt pointwise envelopeSettles

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.positiveExponentialEnvelope_settles
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compiledDrivenHomogeneous_voltage_abs_le_envelope
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compiledDrivenHomogeneous_current_abs_le_envelope
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.drivenWholePortSettlingDuration_pos
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.drivenTotal_afterSettling_voltageError_lt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.drivenTotal_afterSettling_currentError_lt
