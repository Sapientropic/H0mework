import H0mework.Physics.RLCResponse.Bandwidth
import H0mework.Physics.RLCResponse.Run
import H0mework.Physics.RLCNetlist.DimensionedCoupling
import H0mework.Physics.PortCoupling.OperatorTolerance

/-!
# Resonant driven series-RLC realization of the quarter-phase coupling

Each channel is driven at its own source-generated natural frequency.  The
resistor sense phasor is proved equal to the resistor component voltage of the
actual periodic circuit solution.  At resonance that response is unity.  The
same current's actual inductor voltage supplies the minus-i phase; normalization
uses its positive source-generated physical voltage scale.  Thus no stipulated
coordinate swap is the phase producer.
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
open _root_.SaturationMonoid.AffineRelaxation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

private theorem resistorSense_cosine_algebra
    {inductance capacitance resistance frequency driveCosine driveSine : ℝ}
    (capacitance_ne : capacitance ≠ 0) (frequency_ne : frequency ≠ 0)
    (_transferDenominator_ne :
      (1 - inductance * capacitance * frequency ^ 2) ^ 2 +
        (resistance * capacitance * frequency) ^ 2 ≠ 0)
    (_senseDenominator_ne :
      resistance ^ 2 +
        (inductance * frequency - 1 / (capacitance * frequency)) ^ 2 ≠ 0) :
    resistance ^ 2 /
          (resistance ^ 2 +
            (inductance * frequency - 1 / (capacitance * frequency)) ^ 2) *
        driveCosine -
      resistance * (inductance * frequency - 1 / (capacitance * frequency)) /
          (resistance ^ 2 +
            (inductance * frequency - 1 / (capacitance * frequency)) ^ 2) *
        driveSine =
      resistance * (capacitance * frequency) *
        ((resistance * capacitance * frequency /
            ((1 - inductance * capacitance * frequency ^ 2) ^ 2 +
              (resistance * capacitance * frequency) ^ 2)) * driveCosine +
          ((1 - inductance * capacitance * frequency ^ 2) /
            ((1 - inductance * capacitance * frequency ^ 2) ^ 2 +
              (resistance * capacitance * frequency) ^ 2)) * driveSine) := by
  field_simp [capacitance_ne, frequency_ne, _transferDenominator_ne,
    _senseDenominator_ne]
  ring

private theorem resistorSense_sine_algebra
    {inductance capacitance resistance frequency driveCosine driveSine : ℝ}
    (capacitance_ne : capacitance ≠ 0) (frequency_ne : frequency ≠ 0)
    (_transferDenominator_ne :
      (1 - inductance * capacitance * frequency ^ 2) ^ 2 +
        (resistance * capacitance * frequency) ^ 2 ≠ 0)
    (_senseDenominator_ne :
      resistance ^ 2 +
        (inductance * frequency - 1 / (capacitance * frequency)) ^ 2 ≠ 0) :
    resistance * (inductance * frequency - 1 / (capacitance * frequency)) /
          (resistance ^ 2 +
            (inductance * frequency - 1 / (capacitance * frequency)) ^ 2) *
        driveCosine +
      resistance ^ 2 /
          (resistance ^ 2 +
            (inductance * frequency - 1 / (capacitance * frequency)) ^ 2) *
        driveSine =
      -(resistance * (capacitance * frequency) *
        (((1 - inductance * capacitance * frequency ^ 2) /
            ((1 - inductance * capacitance * frequency ^ 2) ^ 2 +
              (resistance * capacitance * frequency) ^ 2)) * driveCosine -
          ((resistance * capacitance * frequency) /
            ((1 - inductance * capacitance * frequency ^ 2) ^ 2 +
              (resistance * capacitance * frequency) ^ 2)) * driveSine)) := by
  field_simp [capacitance_ne, frequency_ne, _transferDenominator_ne,
    _senseDenominator_ne]
  ring

theorem resistorSenseVoltageResponse_eq_resistorComponent
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) (drive : SIVoltagePhasor) :
    resistorSenseVoltageResponseAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
        drive =
      drivenResistorVoltagePhasorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenCapacitorCurrentPhasorAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
          (drivenVoltageResponseAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
            frequency drive)) := by
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  have capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have resistancePositive :=
    compiledFiniteDimensionedSeriesRLC_resistance_pos source channel
  have transferDenominatorPositive :=
    drivenTransferDenominator_pos source channel frequency frequencyPositive
  have senseDenominatorPositive :
      0 < (run.seriesResistanceAt channel).value ^ 2 +
        (drivenNetReactanceAt run channel frequency).value ^ 2 := by
    nlinarith [sq_pos_of_pos resistancePositive,
      sq_nonneg (drivenNetReactanceAt run channel frequency).value]
  have transferDenominatorExpanded :
      0 < (1 - (run.inductanceAt channel).value *
              (run.capacitanceAt channel).value * frequency.value ^ 2) ^ 2 +
        ((run.seriesResistanceAt channel).value *
              (run.capacitanceAt channel).value * frequency.value) ^ 2 := by
    simpa only [drivenTransferDenominatorAt, drivenDetuningAt,
      drivenDampingAt, drivenReactiveCoefficientAt_value,
      drivenResistiveCoefficientAt_value] using transferDenominatorPositive
  have senseDenominatorExpanded :
      0 < (run.seriesResistanceAt channel).value ^ 2 +
        ((run.inductanceAt channel).value * frequency.value -
          1 / ((run.capacitanceAt channel).value * frequency.value)) ^ 2 := by
    simpa only [drivenNetReactanceAt_value] using senseDenominatorPositive
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext
  · simp only [resistorSenseVoltageResponseAt, drivenResistorVoltagePhasorAt,
      drivenCapacitorCurrentPhasorAt, drivenVoltageResponseAt,
      resistanceTimesCurrent_value, frequencyTimesCapacitanceVoltage_value,
      SIQuantity.add_value, SIQuantity.sub_value, SIQuantity.smul_value,
      drivenTransferDenominatorAt, drivenDetuningAt, drivenDampingAt,
      drivenReactiveCoefficientAt_value,
      drivenResistiveCoefficientAt_value, drivenNetReactanceAt_value]
    convert (resistorSense_cosine_algebra
      (inductance := (run.inductanceAt channel).value)
      (capacitance := (run.capacitanceAt channel).value)
      (resistance := (run.seriesResistanceAt channel).value)
      (frequency := frequency.value)
      (driveCosine := drive.cosine.value)
      (driveSine := drive.sine.value)
      (ne_of_gt capacitancePositive) (ne_of_gt frequencyPositive)
      (ne_of_gt transferDenominatorExpanded)
      (ne_of_gt senseDenominatorExpanded)) using 1
    all_goals ring
  · simp only [resistorSenseVoltageResponseAt, drivenResistorVoltagePhasorAt,
      drivenCapacitorCurrentPhasorAt, drivenVoltageResponseAt,
      resistanceTimesCurrent_value, frequencyTimesCapacitanceVoltage_value,
      SIQuantity.add_value, SIQuantity.sub_value, SIQuantity.neg_value,
      SIQuantity.smul_value, drivenTransferDenominatorAt,
      drivenDetuningAt, drivenDampingAt,
      drivenReactiveCoefficientAt_value, drivenResistiveCoefficientAt_value,
      drivenNetReactanceAt_value]
    convert (resistorSense_sine_algebra
      (inductance := (run.inductanceAt channel).value)
      (capacitance := (run.capacitanceAt channel).value)
      (resistance := (run.seriesResistanceAt channel).value)
      (frequency := frequency.value)
      (driveCosine := drive.cosine.value)
      (driveSine := drive.sine.value)
      (ne_of_gt capacitancePositive) (ne_of_gt frequencyPositive)
      (ne_of_gt transferDenominatorExpanded)
      (ne_of_gt senseDenominatorExpanded)) using 1
    all_goals ring

def minusIQuadratureVoltagePhasor
    (phasor : SIVoltagePhasor) : SIVoltagePhasor :=
  ⟨phasor.sine, -phasor.cosine⟩

theorem normalize_minusIQuadratureVoltagePhasor
    (voltageScale : SIVolt) (phasor : SIVoltagePhasor) :
    normalizeVoltagePhasor voltageScale
        (minusIQuadratureVoltagePhasor phasor) =
      (-Complex.I) * normalizeVoltagePhasor voltageScale phasor := by
  apply Complex.ext
  · simp [normalizeVoltagePhasor, minusIQuadratureVoltagePhasor]
  · simp [normalizeVoltagePhasor, minusIQuadratureVoltagePhasor]
    ring

def resonantDrivePhasorAt
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SIVoltagePhasor :=
  voltagePhasorOfNormalized source.2.voltageScale
    (encodePort (state channel))

def resonantResistorSensePhasorAt
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SIVoltagePhasor :=
  resistorSenseVoltageResponseAt
    (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
    (drivenNaturalAngularFrequencyAt source channel)
    (resonantDrivePhasorAt source state channel)

def resonantInductorVoltagePhasorAt
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SIVoltagePhasor :=
  drivenInductorVoltagePhasorAt
    (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
    (drivenNaturalAngularFrequencyAt source channel)
    (drivenPeriodicCurrentPhasorAt source channel
      (drivenNaturalAngularFrequencyAt source channel)
      (resonantDrivePhasorAt source state channel))

def resonantInductorVoltageRatioAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  ((compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt
      channel).value *
    (drivenNaturalAngularFrequencyAt source channel).value /
    ((compileFiniteDimensionedSeriesRLCNetlistRun source).seriesResistanceAt
      channel).value

def resonantInductorOutputScaleAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  resonantInductorVoltageRatioAt source channel • source.2.voltageScale

theorem resonantResistorSensePhasor_eq_drive
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    resonantResistorSensePhasorAt source state channel =
      resonantDrivePhasorAt source state channel :=
  resistorSense_resonance_response_eq_drive source channel _

theorem resonantResistorComponentPhasor_eq_drive
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    drivenResistorVoltagePhasorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenPeriodicCurrentPhasorAt source channel
          (drivenNaturalAngularFrequencyAt source channel)
          (resonantDrivePhasorAt source state channel)) =
      resonantDrivePhasorAt source state channel := by
  calc
    _ = resonantResistorSensePhasorAt source state channel :=
      (resistorSenseVoltageResponse_eq_resistorComponent source channel
        (drivenNaturalAngularFrequencyAt source channel)
        (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos source channel))
        (resonantDrivePhasorAt source state channel)).symm
    _ = _ := resonantResistorSensePhasor_eq_drive source state channel

theorem resonantInductorVoltageRatio_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < resonantInductorVoltageRatioAt source channel := by
  unfold resonantInductorVoltageRatioAt
  exact div_pos
    (mul_pos
      (compiledFiniteDimensionedSeriesRLC_inductance_pos source channel)
      (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos source channel)))
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)

theorem resonantInductorOutputScale_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (resonantInductorOutputScaleAt source channel).value := by
  simp only [resonantInductorOutputScaleAt, SIQuantity.smul_value]
  exact mul_pos (resonantInductorVoltageRatio_pos source channel)
    source.2.voltageScalePositive

/-- The actual inductor component, not a stipulated coordinate swap, produces
the minus-i phase at resonance. -/
theorem resonantInductorVoltagePhasor_eq_physicalMinusI
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    resonantInductorVoltagePhasorAt source state channel =
      resonantInductorVoltageRatioAt source channel •
        minusIQuadratureVoltagePhasor
          (resonantDrivePhasorAt source state channel) := by
  have resistorEq :=
    resonantResistorComponentPhasor_eq_drive source state channel
  have cosineEq := congrArg (fun phasor => phasor.cosine.value) resistorEq
  have sineEq := congrArg (fun phasor => phasor.sine.value) resistorEq
  have resistanceNonzero := ne_of_gt
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext
  · simp only [resonantInductorVoltagePhasorAt,
      drivenInductorVoltagePhasorAt, inductanceTimesCurrentRate_value,
      frequencyTimesCurrent_value, resonantInductorVoltageRatioAt,
      minusIQuadratureVoltagePhasor, voltagePhasor_smul_cosine,
      SIQuantity.smul_value]
    simp only [drivenResistorVoltagePhasorAt,
      resistanceTimesCurrent_value] at sineEq
    rw [← sineEq]
    field_simp [resistanceNonzero]
  · simp only [resonantInductorVoltagePhasorAt,
      drivenInductorVoltagePhasorAt, inductanceTimesCurrentRate_value,
      frequencyTimesCurrent_value, SIQuantity.neg_value,
      resonantInductorVoltageRatioAt, minusIQuadratureVoltagePhasor,
      voltagePhasor_smul_sine, SIQuantity.smul_value]
    simp only [drivenResistorVoltagePhasorAt,
      resistanceTimesCurrent_value] at cosineEq
    rw [← cosineEq]
    field_simp [resistanceNonzero]

def resonantInductorPortOutputAt
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) : ℂ :=
  normalizeVoltagePhasor (resonantInductorOutputScaleAt source channel)
    (resonantInductorVoltagePhasorAt source state channel)

theorem resonantInductorPortOutput_eq_minusI
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    resonantInductorPortOutputAt source state channel =
      (-Complex.I) * encodePort (state channel) := by
  rw [resonantInductorPortOutputAt,
    resonantInductorVoltagePhasor_eq_physicalMinusI]
  unfold resonantInductorOutputScaleAt resonantDrivePhasorAt
  have ratioNonzero := ne_of_gt
    (resonantInductorVoltageRatio_pos source channel)
  have voltageNonzero := source.2.voltageScale_ne
  apply Complex.ext
  · simp [normalizeVoltagePhasor, minusIQuadratureVoltagePhasor,
      voltagePhasorOfNormalized]
    field_simp [ratioNonzero, voltageNonzero]
  · simp [normalizeVoltagePhasor, minusIQuadratureVoltagePhasor,
      voltagePhasorOfNormalized]
    field_simp [ratioNonzero, voltageNonzero]

def resonantDrivenHilbertOutputAt
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) : HilbertEmbodimentState :=
  WithLp.toLp 2 (fun channel =>
    resonantInductorPortOutputAt source state channel)

theorem resonantDrivenHilbertOutput_eq_idealQuarter
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) :
    resonantDrivenHilbertOutputAt source state =
      idealQuarterOperator (encodeHilbert state) := by
  rw [idealQuarterOperator_apply]
  have phase :
      schrodingerScalarPhase 1 (Real.pi / 2) = -Complex.I := by
    rw [schrodingerScalarPhase_one_eq]
    simp
  ext channel
  change resonantInductorPortOutputAt source state channel =
    encodePort ((harmonicFlow (Real.pi / 2) state) channel)
  rw [resonantInductorPortOutput_eq_minusI,
    encodePort_harmonicFlow, phase]
  rfl

theorem resonantDrivenImplementedState_eq_idealQuarter
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) :
    decodeHilbert (resonantDrivenHilbertOutputAt source state) =
      implementedState idealQuarterOperator state := by
  unfold implementedState
  rw [resonantDrivenHilbertOutput_eq_idealQuarter]

/-- Crown-free physical periodic occurrence, exact bandwidth and actual
inductor-phase output. -/
structure SourceGeneratedResonantDrivenBandwidthAt
    (source : DimensionedSeriesRLCSource) : Prop where
  dimensionedRun : SourceGeneratedFiniteDimensionedSeriesRLCNetlistRunAt source
  periodicParticular : ∀ state channel,
    SourceGeneratedDrivenPeriodicParticularAt source channel
      (drivenNaturalAngularFrequencyAt source channel)
      (resonantDrivePhasorAt source state channel)
  exactHalfPowerBandwidth : ∀ channel,
    SourceGeneratedExactHalfPowerBandwidthAt source channel
  resistorSenseIsComponent : ∀ state channel,
    resistorSenseVoltageResponseAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenNaturalAngularFrequencyAt source channel)
        (resonantDrivePhasorAt source state channel) =
      drivenResistorVoltagePhasorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenPeriodicCurrentPhasorAt source channel
          (drivenNaturalAngularFrequencyAt source channel)
          (resonantDrivePhasorAt source state channel))
  inductorProducesMinusI : ∀ state channel,
    resonantInductorVoltagePhasorAt source state channel =
      resonantInductorVoltageRatioAt source channel •
        minusIQuadratureVoltagePhasor
          (resonantDrivePhasorAt source state channel)
  outputScalePositive : ∀ channel,
    0 < (resonantInductorOutputScaleAt source channel).value
  physicalOutputCommutes : ∀ state,
    resonantDrivenHilbertOutputAt source state =
      idealQuarterOperator (encodeHilbert state)

theorem everyDimensionedSeriesRLCSource_generatesResonantDrivenBandwidth
    (source : DimensionedSeriesRLCSource) :
    SourceGeneratedResonantDrivenBandwidthAt source where
  dimensionedRun := sourceGeneratedFiniteDimensionedSeriesRLCNetlistRun source
  periodicParticular := fun state channel =>
    sourceGeneratedDrivenPeriodicParticular source channel
      (drivenNaturalAngularFrequencyAt source channel)
      (resonantDrivePhasorAt source state channel)
      (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos source channel))
  exactHalfPowerBandwidth := sourceGeneratedExactHalfPowerBandwidth source
  resistorSenseIsComponent := fun state channel =>
    resistorSenseVoltageResponse_eq_resistorComponent source channel
      (drivenNaturalAngularFrequencyAt source channel)
      (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos source channel))
      (resonantDrivePhasorAt source state channel)
  inductorProducesMinusI :=
    resonantInductorVoltagePhasor_eq_physicalMinusI source
  outputScalePositive := resonantInductorOutputScale_pos source
  physicalOutputCommutes := resonantDrivenHilbertOutput_eq_idealQuarter source

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.everyDimensionedSeriesRLCSource_generatesResonantDrivenBandwidth
