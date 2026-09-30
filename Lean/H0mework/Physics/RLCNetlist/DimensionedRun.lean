import H0mework.Physics.Measurement.Units
import H0mework.Physics.RLCNetlist.Run

/-!
# Finite dimensioned series-RLC netlist run kernel

An arbitrary positive typed `(T₀,V₀,I₀)` scale joins the finite code at the
source.  Compilation emits a literal source-only physical run containing the
normalized run, the scale, and generated SI-valued C/L/R, damping, damped
frequency, and executed duration.  No operator, tolerance, receipt, or crown
is a run field.

The normalized trajectory is pulled back along
`normalizedTime = physicalTime / T₀`. Charge, voltage,
and current use the generated scales; current is related to the stored charge
coordinate by the exact damped shear.  Circuit laws, energy dissipation,
whole-state normalization, and endpoint commuting are all derived afterward.
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
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

/-! ## Source-owned scale and physical run -/

@[ext] structure PositiveElectricalScale where
  timeScale : SISecond
  voltageScale : SIVolt
  currentScale : SIAmpere
  timeScalePositive : 0 < timeScale.value
  voltageScalePositive : 0 < voltageScale.value
  currentScalePositive : 0 < currentScale.value

theorem PositiveElectricalScale.timeScale_ne
    (scale : PositiveElectricalScale) : scale.timeScale.value ≠ 0 :=
  ne_of_gt scale.timeScalePositive

theorem PositiveElectricalScale.voltageScale_ne
    (scale : PositiveElectricalScale) : scale.voltageScale.value ≠ 0 :=
  ne_of_gt scale.voltageScalePositive

theorem PositiveElectricalScale.currentScale_ne
    (scale : PositiveElectricalScale) : scale.currentScale.value ≠ 0 :=
  ne_of_gt scale.currentScalePositive

abbrev DimensionedSeriesRLCSource :=
  SourceOwnedNetlistCrosstalkCode × PositiveElectricalScale

def generatedPhysicalCapacitanceAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (scale : PositiveElectricalScale)
    (channel : FiniteEmbodimentChannel) : SIFarad :=
  SIQuantity.scale (run.capacitanceAt channel)
    (SIQuantity.castDimension current_time_div_voltage_dimension
      (SIQuantity.div
        (SIQuantity.mul scale.currentScale scale.timeScale)
        scale.voltageScale))

def generatedPhysicalInductanceAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (scale : PositiveElectricalScale)
    (channel : FiniteEmbodimentChannel) : SIHenry :=
  SIQuantity.scale (run.inductanceAt channel)
    (SIQuantity.castDimension voltage_time_div_current_dimension
      (SIQuantity.div
        (SIQuantity.mul scale.voltageScale scale.timeScale)
        scale.currentScale))

def generatedPhysicalResistanceAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (scale : PositiveElectricalScale)
    (channel : FiniteEmbodimentChannel) : SIOhm :=
  SIQuantity.scale (run.seriesResistanceAt channel)
    (SIQuantity.castDimension voltage_div_current_dimension
      (SIQuantity.div scale.voltageScale scale.currentScale))

def generatedPhysicalDampingRateAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (scale : PositiveElectricalScale)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  SIQuantity.castDimension dimensionless_div_time_dimension
    (SIQuantity.div
      (SIQuantity.dimensionlessValue (run.dampingRateAt channel))
      scale.timeScale)

def generatedPhysicalDampedFrequencyAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (scale : PositiveElectricalScale)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  SIQuantity.castDimension dimensionless_div_time_dimension
    (SIQuantity.div
      (SIQuantity.dimensionlessValue
        (finiteSeriesRLCDampedAngularFrequencyAt run channel))
      scale.timeScale)

def generatedPhysicalExecutedDuration
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (scale : PositiveElectricalScale) : SISecond :=
  SIQuantity.scale run.baseRun.executedDuration scale.timeScale

/-- Source-only physical fixture.  All fields are fixed before trajectory or
endpoint solution. -/
structure FiniteDimensionedSeriesRLCNetlistRunOccurrence where
  normalizedRun : FiniteSeriesRLCNetlistRunOccurrence
  scale : PositiveElectricalScale
  capacitanceAt : FiniteEmbodimentChannel → SIFarad
  inductanceAt : FiniteEmbodimentChannel → SIHenry
  seriesResistanceAt : FiniteEmbodimentChannel → SIOhm
  dampingRateAt : FiniteEmbodimentChannel → SIHertz
  dampedFrequencyAt : FiniteEmbodimentChannel → SIHertz
  executedDuration : SISecond

def compileFiniteDimensionedSeriesRLCNetlistRun
    (source : DimensionedSeriesRLCSource) :
    FiniteDimensionedSeriesRLCNetlistRunOccurrence where
  normalizedRun := compileFiniteSeriesRLCNetlistRun source.1
  scale := source.2
  capacitanceAt := generatedPhysicalCapacitanceAt
    (compileFiniteSeriesRLCNetlistRun source.1) source.2
  inductanceAt := generatedPhysicalInductanceAt
    (compileFiniteSeriesRLCNetlistRun source.1) source.2
  seriesResistanceAt := generatedPhysicalResistanceAt
    (compileFiniteSeriesRLCNetlistRun source.1) source.2
  dampingRateAt := generatedPhysicalDampingRateAt
    (compileFiniteSeriesRLCNetlistRun source.1) source.2
  dampedFrequencyAt := generatedPhysicalDampedFrequencyAt
    (compileFiniteSeriesRLCNetlistRun source.1) source.2
  executedDuration := generatedPhysicalExecutedDuration
    (compileFiniteSeriesRLCNetlistRun source.1) source.2

theorem compileFiniteDimensionedSeriesRLCNetlistRun_injective :
    Function.Injective compileFiniteDimensionedSeriesRLCNetlistRun := by
  rintro ⟨leftCode, leftScale⟩ ⟨rightCode, rightScale⟩ sameRun
  apply Prod.ext
  · exact compileFiniteSeriesRLCNetlistRun_injective
      (congrArg FiniteDimensionedSeriesRLCNetlistRunOccurrence.normalizedRun
        sameRun)
  · exact congrArg FiniteDimensionedSeriesRLCNetlistRunOccurrence.scale sameRun

@[simp] theorem compiledFiniteDimensionedSeriesRLC_normalizedRun
    (source : DimensionedSeriesRLCSource) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).normalizedRun =
      compileFiniteSeriesRLCNetlistRun source.1 :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_scale
    (source : DimensionedSeriesRLCSource) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).scale = source.2 :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_capacitance_scaling
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).capacitanceAt
        channel =
      SIQuantity.scale
        ((compileFiniteSeriesRLCNetlistRun source.1).capacitanceAt channel)
        (SIQuantity.castDimension current_time_div_voltage_dimension
          (SIQuantity.div
            (SIQuantity.mul source.2.currentScale source.2.timeScale)
            source.2.voltageScale)) :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_inductance_scaling
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt channel =
      SIQuantity.scale
        ((compileFiniteSeriesRLCNetlistRun source.1).inductanceAt channel)
        (SIQuantity.castDimension voltage_time_div_current_dimension
          (SIQuantity.div
            (SIQuantity.mul source.2.voltageScale source.2.timeScale)
            source.2.currentScale)) :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_resistance_scaling
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).seriesResistanceAt
        channel =
      SIQuantity.scale
        ((compileFiniteSeriesRLCNetlistRun source.1).seriesResistanceAt channel)
        (SIQuantity.castDimension voltage_div_current_dimension
          (SIQuantity.div source.2.voltageScale source.2.currentScale)) :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_damping_scaling
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).dampingRateAt channel =
      SIQuantity.castDimension dimensionless_div_time_dimension
        (SIQuantity.div
          (SIQuantity.dimensionlessValue
            ((compileFiniteSeriesRLCNetlistRun source.1).dampingRateAt channel))
          source.2.timeScale) :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_frequency_scaling
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).dampedFrequencyAt
        channel =
      SIQuantity.castDimension dimensionless_div_time_dimension
        (SIQuantity.div
          (SIQuantity.dimensionlessValue
            (finiteSeriesRLCDampedAngularFrequencyAt
              (compileFiniteSeriesRLCNetlistRun source.1) channel))
          source.2.timeScale) :=
  rfl

@[simp] theorem compiledFiniteDimensionedSeriesRLC_duration_scaling
    (source : DimensionedSeriesRLCSource) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).executedDuration =
      SIQuantity.scale
        (compileFiniteSeriesRLCNetlistRun source.1).baseRun.executedDuration
        source.2.timeScale :=
  rfl

theorem compiledFiniteDimensionedSeriesRLC_capacitance_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < ((compileFiniteDimensionedSeriesRLCNetlistRun source).capacitanceAt
      channel).value := by
  rw [compiledFiniteDimensionedSeriesRLC_capacitance_scaling,
    compiledFiniteSeriesRLCNetlistRun_capacitanceAt]
  exact mul_pos zero_lt_one
    (div_pos (mul_pos source.2.currentScalePositive
      source.2.timeScalePositive) source.2.voltageScalePositive)

theorem compiledFiniteDimensionedSeriesRLC_inductance_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < ((compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt
      channel).value := by
  rw [compiledFiniteDimensionedSeriesRLC_inductance_scaling]
  exact mul_pos
    (compiledFiniteSeriesRLCNetlistRun_inductance_pos source.1 channel)
    (div_pos (mul_pos source.2.voltageScalePositive
      source.2.timeScalePositive) source.2.currentScalePositive)

theorem compiledFiniteDimensionedSeriesRLC_resistance_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < ((compileFiniteDimensionedSeriesRLCNetlistRun source).seriesResistanceAt
      channel).value := by
  rw [compiledFiniteDimensionedSeriesRLC_resistance_scaling]
  exact mul_pos (compiledFiniteSeriesRLC_resistance_pos source.1 channel)
    (div_pos source.2.voltageScalePositive
      source.2.currentScalePositive)

theorem compiledFiniteDimensionedSeriesRLC_damping_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < ((compileFiniteDimensionedSeriesRLCNetlistRun source).dampingRateAt
      channel).value := by
  rw [compiledFiniteDimensionedSeriesRLC_damping_scaling,
    compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
  exact div_pos finiteSeriesRLCDampingRate_pos source.2.timeScalePositive

theorem compiledFiniteDimensionedSeriesRLC_frequency_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < ((compileFiniteDimensionedSeriesRLCNetlistRun source).dampedFrequencyAt
      channel).value := by
  rw [compiledFiniteDimensionedSeriesRLC_frequency_scaling]
  exact div_pos
    (compiledFiniteSeriesRLC_dampedFrequency_pos source.1 channel)
    source.2.timeScalePositive

theorem compiledFiniteDimensionedSeriesRLC_duration_pos
    (source : DimensionedSeriesRLCSource) :
    0 < (compileFiniteDimensionedSeriesRLCNetlistRun source).executedDuration.value := by
  rw [compiledFiniteDimensionedSeriesRLC_duration_scaling]
  exact mul_pos (quantizedExecutedDuration_pos source.1.1)
    source.2.timeScalePositive

abbrev FrequencySquaredQuantity :=
  SIQuantity (frequencyDimension + frequencyDimension)

def finiteDimensionedSeriesRLCResistanceDampingAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  SIQuantity.castDimension resistance_div_inductance_dimension
    (SIQuantity.div (run.seriesResistanceAt channel)
      ((2 : ℝ) • run.inductanceAt channel))

def finiteDimensionedSeriesRLCNaturalFrequencySqAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) : FrequencySquaredQuantity :=
  SIQuantity.castDimension inverse_inductance_capacitance_dimension
    (SIQuantity.div (SIQuantity.dimensionlessValue 1)
      (SIQuantity.mul (run.inductanceAt channel)
        (run.capacitanceAt channel)))

/-- The generated physical parameters retain `α = R/(2L)`. -/
theorem compiledFiniteDimensionedSeriesRLC_damping_eq_resistanceDamping
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).dampingRateAt channel =
      finiteDimensionedSeriesRLCResistanceDampingAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel := by
  have normalized :=
    compiledFiniteSeriesRLC_damping_eq_resistance_div_two_inductance
      source.1 channel
  have inductanceNonzero :
      (compileFiniteSeriesRLCNetlistRun source.1).inductanceAt channel ≠ 0 :=
    ne_of_gt (compiledFiniteSeriesRLCNetlistRun_inductance_pos
      source.1 channel)
  apply SIQuantity.ext
  simp only [finiteDimensionedSeriesRLCResistanceDampingAt,
    compiledFiniteDimensionedSeriesRLC_damping_scaling,
    compiledFiniteDimensionedSeriesRLC_resistance_scaling,
    compiledFiniteDimensionedSeriesRLC_inductance_scaling,
    SIQuantity.castDimension_value, SIQuantity.div_value,
    SIQuantity.smul_value, SIQuantity.scale_value, SIQuantity.mul_value,
    SIQuantity.dimensionlessValue_value]
  field_simp [source.2.timeScale_ne, source.2.voltageScale_ne,
    source.2.currentScale_ne, inductanceNonzero] at normalized ⊢
  nlinarith

/-- `1/(LC) = ν² + α²` survives every positive nonunit scale. -/
theorem compiledFiniteDimensionedSeriesRLC_naturalFrequencySq_eq
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    finiteDimensionedSeriesRLCNaturalFrequencySqAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel =
      SIQuantity.square
          ((compileFiniteDimensionedSeriesRLCNetlistRun source
            ).dampedFrequencyAt channel) +
        SIQuantity.square
          ((compileFiniteDimensionedSeriesRLCNetlistRun source
            ).dampingRateAt channel) := by
  have normalized :=
    compiledFiniteSeriesRLC_naturalFrequencySq_eq_damped_add_damping
      source.1 channel
  have inductanceNonzero :
      (compileFiniteSeriesRLCNetlistRun source.1).inductanceAt channel ≠ 0 :=
    ne_of_gt (compiledFiniteSeriesRLCNetlistRun_inductance_pos
      source.1 channel)
  have capacitanceExact :=
    compiledFiniteSeriesRLCNetlistRun_capacitanceAt source.1 channel
  apply SIQuantity.ext
  simp only [finiteDimensionedSeriesRLCNaturalFrequencySqAt,
    compiledFiniteDimensionedSeriesRLC_inductance_scaling,
    compiledFiniteDimensionedSeriesRLC_capacitance_scaling,
    compiledFiniteDimensionedSeriesRLC_frequency_scaling,
    compiledFiniteDimensionedSeriesRLC_damping_scaling,
    SIQuantity.castDimension_value, SIQuantity.div_value,
    SIQuantity.dimensionlessValue_value, SIQuantity.mul_value,
    SIQuantity.scale_value, SIQuantity.add_value, SIQuantity.square_value]
  change
    1 /
        ((compileFiniteSeriesRLCNetlistRun source.1).inductanceAt channel *
          (compileFiniteSeriesRLCNetlistRun source.1).capacitanceAt channel) =
      finiteSeriesRLCDampedAngularFrequencyAt
          (compileFiniteSeriesRLCNetlistRun source.1) channel ^ 2 +
        (compileFiniteSeriesRLCNetlistRun source.1).dampingRateAt channel ^ 2
      at normalized
  rw [capacitanceExact] at normalized ⊢
  field_simp [source.2.timeScale_ne, source.2.voltageScale_ne,
    source.2.currentScale_ne, inductanceNonzero] at normalized ⊢
  nlinarith

theorem compiledFiniteDimensionedSeriesRLC_underdamped
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (finiteDimensionedSeriesRLCNaturalFrequencySqAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value -
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).dampingRateAt channel).value ^ 2 := by
  have balance := congrArg SIQuantity.value
    (compiledFiniteDimensionedSeriesRLC_naturalFrequencySq_eq source channel)
  simp only [SIQuantity.add_value, SIQuantity.square_value] at balance
  nlinarith [sq_pos_of_pos
    (compiledFiniteDimensionedSeriesRLC_frequency_pos source channel)]

/-! ## Dimensioned state, time pullback, and inverse shear -/

structure FiniteDimensionedSeriesRLCState where
  chargeCoordinateAt : FiniteEmbodimentChannel → SICoulomb
  voltageAt : FiniteEmbodimentChannel → SIVolt
  currentAt : FiniteEmbodimentChannel → SIAmpere

def finiteDimensionedSeriesRLCNormalizedTimeAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (physicalTime : SISecond) : ℝ :=
  (SIQuantity.sameDimensionRatio physicalTime run.scale.timeScale).value

theorem compiledFiniteDimensionedSeriesRLC_normalizedTime_executedDuration
    (source : DimensionedSeriesRLCSource) :
    finiteDimensionedSeriesRLCNormalizedTimeAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (compileFiniteDimensionedSeriesRLCNetlistRun source).executedDuration =
      (compileFiniteSeriesRLCNetlistRun source.1).baseRun.executedDuration := by
  simp only [finiteDimensionedSeriesRLCNormalizedTimeAt,
    compiledFiniteDimensionedSeriesRLC_duration_scaling,
    compiledFiniteDimensionedSeriesRLC_scale,
    SIQuantity.sameDimensionRatio_value, SIQuantity.scale_value]
  field_simp [source.2.timeScale_ne]

/-- Physical lift of an arbitrary normalized state.  The charge coordinate
scales the harmonic source coordinate; current is independently generated by
the damped shear. -/
def finiteDimensionedSeriesRLCStateOfNormalized
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (state : FiniteEmbodimentState) : FiniteDimensionedSeriesRLCState where
  chargeCoordinateAt := fun channel =>
    SIQuantity.scale (sourcePort state channel)
      (SIQuantity.castDimension current_time_dimension
        (SIQuantity.mul run.scale.currentScale run.scale.timeScale))
  voltageAt := fun channel =>
    SIQuantity.scale (targetPort state channel) run.scale.voltageScale
  currentAt := fun channel =>
    SIQuantity.scale
      (run.normalizedRun.baseRun.frequencyAt channel *
          sourcePort state channel -
        run.normalizedRun.dampingRateAt channel * targetPort state channel)
      run.scale.currentScale

def finiteDimensionedSeriesRLCFlowAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (physicalTime : SISecond) :
    FiniteDimensionedSeriesRLCState :=
  finiteDimensionedSeriesRLCStateOfNormalized run
    (finiteSeriesRLCFlowAt run.normalizedRun initial
      (finiteDimensionedSeriesRLCNormalizedTimeAt run physicalTime))

def finiteDimensionedSeriesRLCChargeCoordinateAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SICoulomb :=
  SIQuantity.scale
    (sourcePort (finiteSeriesRLCFlowAt run.normalizedRun initial
      (finiteDimensionedSeriesRLCNormalizedTimeAt run physicalTime)) channel)
    (SIQuantity.castDimension current_time_dimension
      (SIQuantity.mul run.scale.currentScale run.scale.timeScale))

def finiteDimensionedSeriesRLCVoltageAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIVolt :=
  SIQuantity.scale
    (finiteSeriesRLCVoltageAt run.normalizedRun initial channel
      (finiteDimensionedSeriesRLCNormalizedTimeAt run physicalTime))
    run.scale.voltageScale

def finiteDimensionedSeriesRLCCurrentAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIAmpere :=
  SIQuantity.scale
    (finiteSeriesRLCCurrentAt run.normalizedRun initial channel
      (finiteDimensionedSeriesRLCNormalizedTimeAt run physicalTime))
    run.scale.currentScale

/-- Normalize a dimensioned state by recovering the harmonic source
coordinate from physical current and voltage through the inverse damped shear. -/
def normalizeFiniteDimensionedSeriesRLCState
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (state : FiniteDimensionedSeriesRLCState) : FiniteEmbodimentState :=
  fun channel =>
    (((state.currentAt channel).value / run.scale.currentScale.value +
          run.normalizedRun.dampingRateAt channel *
            ((state.voltageAt channel).value /
              run.scale.voltageScale.value)) /
        run.normalizedRun.baseRun.frequencyAt channel,
      (state.voltageAt channel).value / run.scale.voltageScale.value)

/-- The inverse shear recovers every normalized state, not just one solution
or one endpoint. -/
theorem compiledFiniteDimensionedSeriesRLC_normalize_stateOfNormalized
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) :
    normalizeFiniteDimensionedSeriesRLCState
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (finiteDimensionedSeriesRLCStateOfNormalized
          (compileFiniteDimensionedSeriesRLCNetlistRun source) state) = state := by
  funext channel
  rcases hstate : state channel with ⟨charge, voltage⟩
  apply Prod.ext
  · simp only [normalizeFiniteDimensionedSeriesRLCState,
      finiteDimensionedSeriesRLCStateOfNormalized, sourcePort, targetPort,
      hstate, SIQuantity.scale_value]
    have frequencyNonzero :
        (compileFiniteSeriesRLCNetlistRun source.1).baseRun.frequencyAt
          channel ≠ 0 :=
      ne_of_gt (compiledFiniteSeriesRLCNetlistRun_frequency_pos
        source.1 channel)
    rw [compiledFiniteDimensionedSeriesRLC_normalizedRun]
    field_simp [source.2.currentScale_ne, source.2.voltageScale_ne,
      frequencyNonzero]
    ring
  · simp only [normalizeFiniteDimensionedSeriesRLCState,
      finiteDimensionedSeriesRLCStateOfNormalized, sourcePort, targetPort,
      hstate, SIQuantity.scale_value]
    field_simp [source.2.voltageScale_ne]

/-- Whole-state normalization of the physical pullback at every physical
time. -/
theorem compiledFiniteDimensionedSeriesRLC_normalize_flow
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (physicalTime : SISecond) :
    normalizeFiniteDimensionedSeriesRLCState
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (finiteDimensionedSeriesRLCFlowAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          initial physicalTime) =
      finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun source.1)
        initial
        (finiteDimensionedSeriesRLCNormalizedTimeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          physicalTime) := by
  exact compiledFiniteDimensionedSeriesRLC_normalize_stateOfNormalized source _

/-- The independently scaled current equals the fully typed physical shear
`I = ν Q - α C V`. -/
theorem compiledFiniteDimensionedSeriesRLCCurrent_shear
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    finiteDimensionedSeriesRLCCurrentAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel physicalTime =
      frequencyTimesCharge
          ((compileFiniteDimensionedSeriesRLCNetlistRun source
            ).dampedFrequencyAt channel)
          (finiteDimensionedSeriesRLCChargeCoordinateAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source)
            initial channel physicalTime) -
        frequencyTimesCapacitanceVoltage
          ((compileFiniteDimensionedSeriesRLCNetlistRun source
            ).dampingRateAt channel)
          ((compileFiniteDimensionedSeriesRLCNetlistRun source
            ).capacitanceAt channel)
          (finiteDimensionedSeriesRLCVoltageAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source)
            initial channel physicalTime) := by
  apply SIQuantity.ext
  simp only [finiteDimensionedSeriesRLCCurrentAt,
    finiteDimensionedSeriesRLCChargeCoordinateAt,
    finiteDimensionedSeriesRLCVoltageAt,
    frequencyTimesCharge_value, frequencyTimesCapacitanceVoltage_value,
    SIQuantity.sub_value,
    SIQuantity.scale_value, SIQuantity.castDimension_value,
    SIQuantity.mul_value, SIQuantity.div_value,
    SIQuantity.dimensionlessValue_value,
    compiledFiniteDimensionedSeriesRLC_frequency_scaling,
    compiledFiniteDimensionedSeriesRLC_damping_scaling,
    compiledFiniteDimensionedSeriesRLC_capacitance_scaling,
    compiledFiniteSeriesRLCNetlistRun_capacitanceAt,
    compiledFiniteDimensionedSeriesRLC_normalizedRun,
    compiledFiniteDimensionedSeriesRLC_scale,
    finiteSeriesRLCCurrentAt, finiteSeriesRLCVoltageAt,
    finiteSeriesRLCDampedAngularFrequencyAt]
  field_simp [source.2.timeScale_ne, source.2.voltageScale_ne]

def finiteDimensionedSeriesRLCVoltageDerivativeAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : VoltageRateQuantity :=
  SIQuantity.scale
    (finiteSeriesRLCCurrentAt run.normalizedRun initial channel
      (finiteDimensionedSeriesRLCNormalizedTimeAt run physicalTime))
    (SIQuantity.div run.scale.voltageScale run.scale.timeScale)

def finiteDimensionedSeriesRLCCurrentDerivativeAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : CurrentRateQuantity :=
  SIQuantity.scale
    (finiteSeriesRLCCurrentDerivativeAt run.normalizedRun initial channel
      (finiteDimensionedSeriesRLCNormalizedTimeAt run physicalTime))
    (SIQuantity.div run.scale.currentScale run.scale.timeScale)

theorem finiteDimensionedSeriesRLCVoltage_hasSIQuantityDerivAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (finiteDimensionedSeriesRLCVoltageAt run initial channel)
      (finiteDimensionedSeriesRLCVoltageDerivativeAt
        run initial channel physicalTime) physicalTime := by
  refine ⟨?_⟩
  have inner : HasDerivAt
      (fun time : ℝ => time / run.scale.timeScale.value)
      (1 / run.scale.timeScale.value) physicalTime.value := by
    simpa using (hasDerivAt_id' physicalTime.value).div_const
      run.scale.timeScale.value
  have normalized := finiteSeriesRLC_voltage_hasDerivAt
    run.normalizedRun initial channel
    (physicalTime.value / run.scale.timeScale.value)
  have composed := normalized.comp physicalTime.value inner
  have scaled := composed.const_mul run.scale.voltageScale.value
  simp only [finiteDimensionedSeriesRLCVoltageAt,
    finiteDimensionedSeriesRLCVoltageDerivativeAt,
    finiteDimensionedSeriesRLCNormalizedTimeAt,
    SIQuantity.sameDimensionRatio_value, SIQuantity.scale_value,
    SIQuantity.div_value]
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using scaled

theorem finiteDimensionedSeriesRLCCurrent_hasSIQuantityDerivAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (finiteDimensionedSeriesRLCCurrentAt run initial channel)
      (finiteDimensionedSeriesRLCCurrentDerivativeAt
        run initial channel physicalTime) physicalTime := by
  refine ⟨?_⟩
  have inner : HasDerivAt
      (fun time : ℝ => time / run.scale.timeScale.value)
      (1 / run.scale.timeScale.value) physicalTime.value := by
    simpa using (hasDerivAt_id' physicalTime.value).div_const
      run.scale.timeScale.value
  have normalized := finiteSeriesRLC_current_hasDerivAt
    run.normalizedRun initial channel
    (physicalTime.value / run.scale.timeScale.value)
  have composed := normalized.comp physicalTime.value inner
  have scaled := composed.const_mul run.scale.currentScale.value
  simp only [finiteDimensionedSeriesRLCCurrentAt,
    finiteDimensionedSeriesRLCCurrentDerivativeAt,
    finiteDimensionedSeriesRLCNormalizedTimeAt,
    SIQuantity.sameDimensionRatio_value, SIQuantity.scale_value,
    SIQuantity.div_value]
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using scaled

/-! ## Typed three-node circuit laws -/

def finiteDimensionedSeriesRLCElementCurrentAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) (_element : SeriesRLCCoreElementKind) :
    SIAmpere :=
  finiteDimensionedSeriesRLCCurrentAt run initial channel physicalTime

def finiteDimensionedSeriesRLCNodeCurrentAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) (node : SeriesRLCLocalNode) : SIAmpere :=
  ((seriesRLCCoreIncidence node .seriesResistor : ℝ) •
      finiteDimensionedSeriesRLCElementCurrentAt
        run initial channel physicalTime .seriesResistor) +
    ((seriesRLCCoreIncidence node .inductor : ℝ) •
      finiteDimensionedSeriesRLCElementCurrentAt
        run initial channel physicalTime .inductor) +
    ((seriesRLCCoreIncidence node .capacitor : ℝ) •
      finiteDimensionedSeriesRLCElementCurrentAt
        run initial channel physicalTime .capacitor)

theorem finiteDimensionedSeriesRLC_kirchhoffCurrentLaw
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) (node : SeriesRLCLocalNode) :
    finiteDimensionedSeriesRLCNodeCurrentAt
      run initial channel physicalTime node = 0 := by
  apply SIQuantity.ext
  cases node <;>
    simp [finiteDimensionedSeriesRLCNodeCurrentAt,
      finiteDimensionedSeriesRLCElementCurrentAt,
      seriesRLCCoreIncidence]

/-- Typed physical capacitor law `C · dV/d physicalTime = I`. -/
theorem compiledFiniteDimensionedSeriesRLC_capacitorConstitutiveLaw
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    capacitanceTimesVoltageRate
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).capacitanceAt channel)
        (finiteDimensionedSeriesRLCVoltageDerivativeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          initial channel physicalTime) =
      finiteDimensionedSeriesRLCCurrentAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel physicalTime := by
  apply SIQuantity.ext
  simp only [capacitanceTimesVoltageRate_value,
    compiledFiniteDimensionedSeriesRLC_capacitance_scaling,
    finiteDimensionedSeriesRLCVoltageDerivativeAt,
    finiteDimensionedSeriesRLCCurrentAt,
    compiledFiniteDimensionedSeriesRLC_normalizedRun,
    compiledFiniteDimensionedSeriesRLC_scale,
    SIQuantity.scale_value, SIQuantity.castDimension_value,
    SIQuantity.div_value, SIQuantity.mul_value,
    compiledFiniteSeriesRLCNetlistRun_capacitanceAt]
  field_simp [source.2.timeScale_ne, source.2.voltageScale_ne]

/-- Typed series equation `L · dI/d physicalTime + R · I + V = 0`. -/
theorem compiledFiniteDimensionedSeriesRLC_kirchhoffVoltageLaw
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    (inductanceTimesCurrentRate
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).inductanceAt channel)
        (finiteDimensionedSeriesRLCCurrentDerivativeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          initial channel physicalTime) +
      resistanceTimesCurrent
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).seriesResistanceAt channel)
        (finiteDimensionedSeriesRLCCurrentAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          initial channel physicalTime)) +
      finiteDimensionedSeriesRLCVoltageAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel physicalTime = 0 := by
  have normalized := compiledFiniteSeriesRLC_kirchhoffVoltageLaw
    source.1 initial channel
    (finiteDimensionedSeriesRLCNormalizedTimeAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) physicalTime)
  change
    (compileFiniteSeriesRLCNetlistRun source.1).inductanceAt channel *
        finiteSeriesRLCCurrentDerivativeAt
          (compileFiniteSeriesRLCNetlistRun source.1) initial channel
          (finiteDimensionedSeriesRLCNormalizedTimeAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source)
            physicalTime) +
      (compileFiniteSeriesRLCNetlistRun source.1).seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt
          (compileFiniteSeriesRLCNetlistRun source.1) initial channel
          (finiteDimensionedSeriesRLCNormalizedTimeAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source)
            physicalTime) +
      finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun source.1)
        initial channel
        (finiteDimensionedSeriesRLCNormalizedTimeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          physicalTime) = 0 at normalized
  apply SIQuantity.ext
  simp only [SIQuantity.add_value, SIQuantity.zero_value,
    inductanceTimesCurrentRate_value, resistanceTimesCurrent_value,
    compiledFiniteDimensionedSeriesRLC_inductance_scaling,
    compiledFiniteDimensionedSeriesRLC_resistance_scaling,
    finiteDimensionedSeriesRLCCurrentDerivativeAt,
    finiteDimensionedSeriesRLCCurrentAt,
    finiteDimensionedSeriesRLCVoltageAt,
    compiledFiniteDimensionedSeriesRLC_normalizedRun,
    compiledFiniteDimensionedSeriesRLC_scale,
    SIQuantity.scale_value, SIQuantity.castDimension_value,
    SIQuantity.div_value, SIQuantity.mul_value]
  field_simp [source.2.timeScale_ne, source.2.currentScale_ne]
  rw [normalized]
  ring

/-- Node potentials make the three element voltages literal oriented
source-minus-target differences. -/
def finiteDimensionedSeriesRLCNodePotentialAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SeriesRLCLocalNode → SIVolt
  | .signal =>
      finiteDimensionedSeriesRLCVoltageAt run initial channel physicalTime
  | .seriesJunction =>
      -resistanceTimesCurrent (run.seriesResistanceAt channel)
        (finiteDimensionedSeriesRLCCurrentAt
          run initial channel physicalTime)
  | .reference => 0

def finiteDimensionedSeriesRLCElementVoltageAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) (element : SeriesRLCCoreElementKind) : SIVolt :=
  finiteDimensionedSeriesRLCNodePotentialAt run initial channel physicalTime
      (seriesRLCCoreElementSource element) -
    finiteDimensionedSeriesRLCNodePotentialAt run initial channel physicalTime
      (seriesRLCCoreElementTarget element)

/-- `V_R = R I` from the generated node potentials. -/
theorem finiteDimensionedSeriesRLC_resistorVoltageLaw
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    finiteDimensionedSeriesRLCElementVoltageAt
        run initial channel physicalTime .seriesResistor =
      resistanceTimesCurrent (run.seriesResistanceAt channel)
        (finiteDimensionedSeriesRLCCurrentAt
          run initial channel physicalTime) := by
  apply SIQuantity.ext
  simp [finiteDimensionedSeriesRLCElementVoltageAt,
    finiteDimensionedSeriesRLCNodePotentialAt,
    seriesRLCCoreElementSource, seriesRLCCoreElementTarget]

theorem finiteDimensionedSeriesRLC_capacitorVoltageLaw
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    finiteDimensionedSeriesRLCElementVoltageAt
        run initial channel physicalTime .capacitor =
      finiteDimensionedSeriesRLCVoltageAt
        run initial channel physicalTime := by
  apply SIQuantity.ext
  simp [finiteDimensionedSeriesRLCElementVoltageAt,
    finiteDimensionedSeriesRLCNodePotentialAt,
    seriesRLCCoreElementSource, seriesRLCCoreElementTarget]

/-- The three typed source-minus-target voltage drops telescope around the
explicit R/L/C loop independently of the dynamical equations. -/
theorem finiteDimensionedSeriesRLC_elementVoltageLoop_telescope
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    (finiteDimensionedSeriesRLCElementVoltageAt
        run initial channel physicalTime .seriesResistor +
      finiteDimensionedSeriesRLCElementVoltageAt
        run initial channel physicalTime .inductor) +
      finiteDimensionedSeriesRLCElementVoltageAt
        run initial channel physicalTime .capacitor = 0 := by
  apply SIQuantity.ext
  simp [finiteDimensionedSeriesRLCElementVoltageAt,
    finiteDimensionedSeriesRLCNodePotentialAt,
    seriesRLCCoreElementSource, seriesRLCCoreElementTarget]
  ring

/-- `V_L = L dI/d physicalTime`; KVL identifies the oriented junction-to-signal
potential difference with the generated inductive drop. -/
theorem compiledFiniteDimensionedSeriesRLC_inductorVoltageLaw
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    finiteDimensionedSeriesRLCElementVoltageAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel physicalTime .inductor =
      inductanceTimesCurrentRate
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).inductanceAt channel)
        (finiteDimensionedSeriesRLCCurrentDerivativeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          initial channel physicalTime) := by
  have kvl := congrArg SIQuantity.value
    (compiledFiniteDimensionedSeriesRLC_kirchhoffVoltageLaw
      source initial channel physicalTime)
  apply SIQuantity.ext
  simp only [finiteDimensionedSeriesRLCElementVoltageAt,
    finiteDimensionedSeriesRLCNodePotentialAt,
    seriesRLCCoreElementSource, seriesRLCCoreElementTarget,
    SIQuantity.sub_value, SIQuantity.neg_value,
    resistanceTimesCurrent_value, inductanceTimesCurrentRate_value,
    SIQuantity.add_value, SIQuantity.zero_value] at kvl ⊢
  linarith

/-! ## Typed energy and strict dissipation -/

def finiteDimensionedSeriesRLCEnergyScale
    (scale : PositiveElectricalScale) : SIJoule :=
  SIQuantity.castDimension voltage_current_time_dimension
    (SIQuantity.mul
      (SIQuantity.mul scale.voltageScale scale.currentScale)
      scale.timeScale)

def finiteDimensionedSeriesRLCEnergyAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIJoule :=
  inductiveEnergy (run.inductanceAt channel)
      (finiteDimensionedSeriesRLCCurrentAt
        run initial channel physicalTime) +
    capacitiveEnergy (run.capacitanceAt channel)
      (finiteDimensionedSeriesRLCVoltageAt
        run initial channel physicalTime)

def finiteDimensionedSeriesRLCEnergyDissipationAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIWatt :=
  (-2 : ℝ) • resistivePower (run.seriesResistanceAt channel)
    (finiteDimensionedSeriesRLCCurrentAt
      run initial channel physicalTime)

/-- Physical energy is the normalized energy multiplied by the generated
typed scale `V₀ I₀ T₀`. -/
theorem compiledFiniteDimensionedSeriesRLC_energy_scaling
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    finiteDimensionedSeriesRLCEnergyAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel physicalTime =
      SIQuantity.scale
        (finiteSeriesRLCEnergyAt (compileFiniteSeriesRLCNetlistRun source.1)
          initial channel
          (finiteDimensionedSeriesRLCNormalizedTimeAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source)
            physicalTime))
        (finiteDimensionedSeriesRLCEnergyScale source.2) := by
  apply SIQuantity.ext
  simp only [finiteDimensionedSeriesRLCEnergyAt,
    finiteDimensionedSeriesRLCEnergyScale,
    inductiveEnergy_value, capacitiveEnergy_value,
    finiteDimensionedSeriesRLCCurrentAt,
    finiteDimensionedSeriesRLCVoltageAt,
    compiledFiniteDimensionedSeriesRLC_inductance_scaling,
    compiledFiniteDimensionedSeriesRLC_capacitance_scaling,
    compiledFiniteDimensionedSeriesRLC_normalizedRun,
    compiledFiniteDimensionedSeriesRLC_scale,
    finiteSeriesRLCEnergyAt,
    SIQuantity.add_value, SIQuantity.scale_value,
    SIQuantity.castDimension_value, SIQuantity.mul_value,
    SIQuantity.div_value]
  field_simp [source.2.timeScale_ne, source.2.voltageScale_ne,
    source.2.currentScale_ne]

/-- Typed Joule derivative with exact Watt output `-2 R I²`. -/
theorem compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (finiteDimensionedSeriesRLCEnergyAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel)
      (finiteDimensionedSeriesRLCEnergyDissipationAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel physicalTime) physicalTime := by
  refine ⟨?_⟩
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  have inner : HasDerivAt
      (fun time : ℝ => time / source.2.timeScale.value)
      (1 / source.2.timeScale.value) physicalTime.value := by
    simpa using (hasDerivAt_id' physicalTime.value).div_const
      source.2.timeScale.value
  have normalized := compiledFiniteSeriesRLC_energy_hasDerivAt
    source.1 initial channel
    (physicalTime.value / source.2.timeScale.value)
  have composed := normalized.comp physicalTime.value inner
  have scaled := composed.const_mul
    (source.2.voltageScale.value * source.2.currentScale.value *
      source.2.timeScale.value)
  have energyFunctionEq :
      (fun time : ℝ =>
        (finiteDimensionedSeriesRLCEnergyAt run initial channel
          ⟨time⟩).value) =
        (fun time : ℝ =>
          source.2.voltageScale.value * source.2.currentScale.value *
            source.2.timeScale.value *
          finiteSeriesRLCEnergyAt (compileFiniteSeriesRLCNetlistRun source.1)
            initial channel (time / source.2.timeScale.value)) := by
    funext time
    have scaling := congrArg SIQuantity.value
      (compiledFiniteDimensionedSeriesRLC_energy_scaling
        source initial channel ⟨time⟩)
    calc
      _ = finiteSeriesRLCEnergyAt
            (compileFiniteSeriesRLCNetlistRun source.1) initial channel
            (time / source.2.timeScale.value) *
          (source.2.voltageScale.value * source.2.currentScale.value *
            source.2.timeScale.value) := by
        simpa [run, finiteDimensionedSeriesRLCNormalizedTimeAt,
          finiteDimensionedSeriesRLCEnergyScale] using scaling
      _ = _ := by ring
  have derivativeEq :
      (finiteDimensionedSeriesRLCEnergyDissipationAt
        run initial channel physicalTime).value =
        source.2.voltageScale.value * source.2.currentScale.value *
          source.2.timeScale.value *
        (-2 * (compileFiniteSeriesRLCNetlistRun source.1
          ).seriesResistanceAt channel *
          finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun source.1)
              initial channel
              (physicalTime.value / source.2.timeScale.value) ^ 2 *
          (1 / source.2.timeScale.value)) := by
    dsimp [run]
    simp only [finiteDimensionedSeriesRLCEnergyDissipationAt,
      resistivePower_value, SIQuantity.smul_value,
      finiteDimensionedSeriesRLCCurrentAt,
      compiledFiniteDimensionedSeriesRLC_resistance_scaling,
      compiledFiniteDimensionedSeriesRLC_normalizedRun,
      compiledFiniteDimensionedSeriesRLC_scale,
      finiteDimensionedSeriesRLCNormalizedTimeAt,
      SIQuantity.sameDimensionRatio_value, SIQuantity.scale_value,
      SIQuantity.castDimension_value, SIQuantity.div_value]
    field_simp [source.2.timeScale_ne, source.2.currentScale_ne]
    rw [compiledFiniteSeriesRLCNetlistRun_seriesResistanceAt,
      compiledFiniteSeriesRLCNetlistRun_inductanceAt,
      compiledFiniteParallelLCNetlistRun_frequencyAt]
    ring
  rw [energyFunctionEq, derivativeEq]
  simpa [Function.comp_def] using scaled

theorem compiledFiniteDimensionedSeriesRLC_energy_antitone
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    Antitone (fun time : ℝ =>
      (finiteDimensionedSeriesRLCEnergyAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel ⟨time⟩).value) := by
  apply antitone_of_deriv_nonpos
  · intro time
    exact (compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt
      source initial channel ⟨time⟩).valueHasDerivAt.differentiableAt
  · intro time
    rw [(compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt
      source initial channel ⟨time⟩).valueHasDerivAt.deriv]
    have resistancePositive :=
      compiledFiniteDimensionedSeriesRLC_resistance_pos source channel
    have currentSquareNonnegative := sq_nonneg
      ((finiteDimensionedSeriesRLCCurrentAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial channel ⟨time⟩).value)
    simp only [finiteDimensionedSeriesRLCEnergyDissipationAt,
      SIQuantity.smul_value, resistivePower_value]
    nlinarith

theorem compiledFiniteDimensionedSeriesRLC_sourceImpulse_strictDissipation
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    let run := compileFiniteDimensionedSeriesRLCNetlistRun source
    HasSIQuantityDerivAt
        (finiteDimensionedSeriesRLCEnergyAt
          run (intervention channel 1) channel)
        (finiteDimensionedSeriesRLCEnergyDissipationAt
          run (intervention channel 1) channel ⟨0⟩) ⟨0⟩ ∧
      (finiteDimensionedSeriesRLCEnergyDissipationAt
        run (intervention channel 1) channel ⟨0⟩).value < 0 := by
  dsimp
  constructor
  · exact compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt
      source (intervention channel 1) channel ⟨0⟩
  · have currentPositive :
        0 < (finiteDimensionedSeriesRLCCurrentAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          (intervention channel 1) channel ⟨0⟩).value := by
      simp only [finiteDimensionedSeriesRLCCurrentAt,
        compiledFiniteDimensionedSeriesRLC_normalizedRun,
        compiledFiniteDimensionedSeriesRLC_scale,
        finiteDimensionedSeriesRLCNormalizedTimeAt,
        SIQuantity.sameDimensionRatio_value, SIQuantity.scale_value]
      rw [show (0 : ℝ) / source.2.timeScale.value = 0 by simp]
      rw [compiledFiniteSeriesRLCCurrentAt_zero_intervention]
      exact mul_pos
        (compiledFiniteSeriesRLCNetlistRun_frequency_pos source.1 channel)
        source.2.currentScalePositive
    have resistancePositive :=
      compiledFiniteDimensionedSeriesRLC_resistance_pos source channel
    simp only [finiteDimensionedSeriesRLCEnergyDissipationAt,
      SIQuantity.smul_value, resistivePower_value]
    nlinarith [sq_pos_of_pos currentPositive]

/-! ## Physical executed endpoint and exact commuting -/

/-- The physical transducer is solved from the dimensioned flow, normalized
through the inverse shear, encoded channelwise, and only then multiplied by
the literal gain row. -/
def finiteDimensionedSeriesRLCTransducerOutputAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (physicalTime : SISecond) :
    HilbertEmbodimentState :=
  WithLp.toLp 2 (fun channel =>
    ((run.normalizedRun.baseRun.branchAt channel).transferGain : ℂ) *
      encodePort
        ((normalizeFiniteDimensionedSeriesRLCState run
          (finiteDimensionedSeriesRLCFlowAt run initial physicalTime)) channel))

/-- General-time commuting: the physical pullback solver produces exactly the
existing normalized transducer output at `physicalTime / T₀`. -/
theorem compiledFiniteDimensionedSeriesRLCTransducerOutput_eq_normalized
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) (physicalTime : SISecond) :
    finiteDimensionedSeriesRLCTransducerOutputAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        initial physicalTime =
      finiteSeriesRLCTransducerOutputAt
        (compileFiniteSeriesRLCNetlistRun source.1) initial
        (finiteDimensionedSeriesRLCNormalizedTimeAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          physicalTime) := by
  unfold finiteDimensionedSeriesRLCTransducerOutputAt
    finiteSeriesRLCTransducerOutputAt
  rw [compiledFiniteDimensionedSeriesRLC_normalize_flow]
  simp only [compiledFiniteDimensionedSeriesRLC_normalizedRun]

/-- The linear output uses the physical emitted duration and then adds the
literal crosstalk row from this run. -/
def finiteDimensionedSeriesRLCLinearOutputAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) : HilbertEmbodimentState :=
  finiteDimensionedSeriesRLCTransducerOutputAt
      run initial run.executedDuration +
    (run.normalizedRun.baseRun.directedCrosstalkAmplitude : ℂ) •
      rankOneCrosstalkOperator (encodeHilbert initial)

/-- The endpoint adds the literal independent bias row from the same run. -/
def finiteDimensionedSeriesRLCEndpointOutputAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) : HilbertEmbodimentState :=
  finiteDimensionedSeriesRLCLinearOutputAt run initial +
    (run.normalizedRun.baseRun.endpointBiasAmplitude : ℂ) •
      finiteParallelLCBiasDirection

theorem compiledFiniteDimensionedSeriesRLCEndpointOutput_eq_existing
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) :
    finiteDimensionedSeriesRLCEndpointOutputAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) initial =
      finiteSeriesRLCEndpointOutputAt
        (compileFiniteSeriesRLCNetlistRun source.1) initial := by
  unfold finiteDimensionedSeriesRLCEndpointOutputAt
    finiteDimensionedSeriesRLCLinearOutputAt
    finiteSeriesRLCEndpointOutputAt finiteSeriesRLCLinearOutputAt
  rw [compiledFiniteDimensionedSeriesRLCTransducerOutput_eq_normalized,
    compiledFiniteDimensionedSeriesRLC_normalizedTime_executedDuration]
  simp only [compiledFiniteDimensionedSeriesRLC_normalizedRun]

def finiteDimensionedSeriesRLCEndpointStateAt
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) : FiniteDimensionedSeriesRLCState :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  finiteDimensionedSeriesRLCStateOfNormalized run
    (decodeHilbert
      (finiteDimensionedSeriesRLCEndpointOutputAt run initial))

theorem compiledFiniteDimensionedSeriesRLCEndpoint_normalizes
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) :
    normalizeFiniteDimensionedSeriesRLCState
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (finiteDimensionedSeriesRLCEndpointStateAt source initial) =
      decodeHilbert
        (finiteDimensionedSeriesRLCEndpointOutputAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) initial) := by
  unfold finiteDimensionedSeriesRLCEndpointStateAt
  exact compiledFiniteDimensionedSeriesRLC_normalize_stateOfNormalized source _

theorem compiledFiniteDimensionedSeriesRLCEndpoint_commutes
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) :
    encodeHilbert
        (normalizeFiniteDimensionedSeriesRLCState
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          (finiteDimensionedSeriesRLCEndpointStateAt source initial)) =
      finiteSeriesRLCEndpointOutputAt
        (compileFiniteSeriesRLCNetlistRun source.1) initial := by
  calc
    _ = finiteDimensionedSeriesRLCEndpointOutputAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) initial := by
      rw [compiledFiniteDimensionedSeriesRLCEndpoint_normalizes,
        encodeHilbert_decodeHilbert]
    _ = _ :=
      compiledFiniteDimensionedSeriesRLCEndpointOutput_eq_existing
        source initial

theorem compiledFiniteDimensionedSeriesRLCEndpoint_eq_disturbed
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) :
    normalizeFiniteDimensionedSeriesRLCState
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (finiteDimensionedSeriesRLCEndpointStateAt source initial) =
      disturbedImplementedState
        (finiteSeriesRLCImplementation source.1)
        smallNonzeroConstantBias initial := by
  rw [compiledFiniteDimensionedSeriesRLCEndpoint_normalizes,
    compiledFiniteDimensionedSeriesRLCEndpointOutput_eq_existing,
    compiledFiniteSeriesRLCEndpointOutput_commutes,
    decodeHilbert_encodeHilbert]

/-- The physical emitted duration and endpoint square are consumed together. -/
theorem compiledFiniteDimensionedSeriesRLC_actualExecutedEndpoint_commutes
    (source : DimensionedSeriesRLCSource)
    (initial : FiniteEmbodimentState) :
    finiteDimensionedSeriesRLCNormalizedTimeAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (compileFiniteDimensionedSeriesRLCNetlistRun source).executedDuration =
      (compileFiniteSeriesRLCNetlistRun source.1).baseRun.executedDuration ∧
    encodeHilbert
        (normalizeFiniteDimensionedSeriesRLCState
          (compileFiniteDimensionedSeriesRLCNetlistRun source)
          (finiteDimensionedSeriesRLCEndpointStateAt source initial)) =
      finiteSeriesRLCEndpointOutputAt
        (compileFiniteSeriesRLCNetlistRun source.1) initial :=
  ⟨compiledFiniteDimensionedSeriesRLC_normalizedTime_executedDuration source,
    compiledFiniteDimensionedSeriesRLCEndpoint_commutes source initial⟩

end
end Producer
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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compileFiniteDimensionedSeriesRLCNetlistRun_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_damping_eq_resistanceDamping
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_naturalFrequencySq_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_normalize_flow
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLCCurrent_shear
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_capacitorConstitutiveLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_kirchhoffVoltageLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_sourceImpulse_strictDissipation
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.compiledFiniteDimensionedSeriesRLC_actualExecutedEndpoint_commutes
