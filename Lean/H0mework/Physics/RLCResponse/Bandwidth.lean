import H0mework.Physics.RLCResponse.Transfer

/-!
# Exact half-power bandwidth of the dimensioned series-RLC resistor port

The resistor sense port has transfer magnitude squared

`R² / (R² + (ωL - 1/(ωC))²)`.

For every source-generated positive R/L/C row, two positive frequencies are
constructed at which the power gain is exactly one half.  Their difference is
exactly `R/L = 2α`, and the generated natural resonance lies strictly between
them with unit gain.
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
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

theorem inductance_frequency_dimension :
    inductanceDimension + frequencyDimension = resistanceDimension := by
  decide

theorem inverse_capacitance_frequency_dimension :
    dimensionless - (capacitanceDimension + frequencyDimension) =
      resistanceDimension := by
  decide

def drivenInductiveReactanceAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : SIOhm :=
  SIQuantity.castDimension inductance_frequency_dimension
    (SIQuantity.mul (run.inductanceAt channel) frequency)

def drivenCapacitiveReactanceAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : SIOhm :=
  SIQuantity.castDimension inverse_capacitance_frequency_dimension
    (SIQuantity.div (SIQuantity.dimensionlessValue 1)
      (SIQuantity.mul (run.capacitanceAt channel) frequency))

def drivenNetReactanceAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : SIOhm :=
  drivenInductiveReactanceAt run channel frequency -
    drivenCapacitiveReactanceAt run channel frequency

@[simp] theorem drivenInductiveReactanceAt_value
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    (drivenInductiveReactanceAt run channel frequency).value =
      (run.inductanceAt channel).value * frequency.value := by
  simp [drivenInductiveReactanceAt]

@[simp] theorem drivenCapacitiveReactanceAt_value
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    (drivenCapacitiveReactanceAt run channel frequency).value =
      1 / ((run.capacitanceAt channel).value * frequency.value) := by
  simp [drivenCapacitiveReactanceAt]

@[simp] theorem drivenNetReactanceAt_value
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    (drivenNetReactanceAt run channel frequency).value =
      (run.inductanceAt channel).value * frequency.value -
        1 / ((run.capacitanceAt channel).value * frequency.value) := by
  simp [drivenNetReactanceAt]

def resistorSenseTransferGainSqAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : ℝ :=
  let resistance := (run.seriesResistanceAt channel).value
  let reactance := (drivenNetReactanceAt run channel frequency).value
  resistance ^ 2 / (resistance ^ 2 + reactance ^ 2)

/-- The actual two-quadrature resistor voltage readout. -/
def resistorSenseVoltageResponseAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) : SIVoltagePhasor :=
  let resistance := (run.seriesResistanceAt channel).value
  let reactance := (drivenNetReactanceAt run channel frequency).value
  let denominator := resistance ^ 2 + reactance ^ 2
  ⟨(resistance ^ 2 / denominator) • drive.cosine -
      (resistance * reactance / denominator) • drive.sine,
    (resistance * reactance / denominator) • drive.cosine +
      (resistance ^ 2 / denominator) • drive.sine⟩

def resistanceBandwidthRateAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  SIQuantity.castDimension resistance_div_inductance_dimension
    (SIQuantity.div (run.seriesResistanceAt channel)
      (run.inductanceAt channel))

def halfPowerDiscriminantAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  let bandwidth :=
    (resistanceBandwidthRateAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value
  let naturalSq :=
    (finiteDimensionedSeriesRLCNaturalFrequencySqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value
  ⟨Real.sqrt (bandwidth ^ 2 + 4 * naturalSq)⟩

def lowerHalfPowerFrequencyAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  (1 / 2 : ℝ) •
    (halfPowerDiscriminantAt source channel -
      resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel)

def upperHalfPowerFrequencyAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  (1 / 2 : ℝ) •
    (halfPowerDiscriminantAt source channel +
      resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel)

@[simp] theorem resistanceBandwidthRateAt_value
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) :
    (resistanceBandwidthRateAt run channel).value =
      (run.seriesResistanceAt channel).value /
        (run.inductanceAt channel).value := by
  simp [resistanceBandwidthRateAt]

@[simp] theorem halfPowerDiscriminantAt_value
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (halfPowerDiscriminantAt source channel).value =
      Real.sqrt
        ((resistanceBandwidthRateAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value ^ 2 +
          4 * (finiteDimensionedSeriesRLCNaturalFrequencySqAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value) := by
  rfl

@[simp] theorem lowerHalfPowerFrequencyAt_value
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (lowerHalfPowerFrequencyAt source channel).value =
      (1 / 2 : ℝ) *
        ((halfPowerDiscriminantAt source channel).value -
          (resistanceBandwidthRateAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value) := by
  rfl

@[simp] theorem upperHalfPowerFrequencyAt_value
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (upperHalfPowerFrequencyAt source channel).value =
      (1 / 2 : ℝ) *
        ((halfPowerDiscriminantAt source channel).value +
          (resistanceBandwidthRateAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value) := by
  rfl

theorem resistanceBandwidthRate_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (resistanceBandwidthRateAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value := by
  rw [resistanceBandwidthRateAt_value]
  exact div_pos
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)
    (compiledFiniteDimensionedSeriesRLC_inductance_pos source channel)

theorem halfPowerDiscriminant_sq
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (halfPowerDiscriminantAt source channel).value ^ 2 =
      (resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value ^ 2 +
        4 * (finiteDimensionedSeriesRLCNaturalFrequencySqAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value := by
  rw [halfPowerDiscriminantAt_value]
  exact Real.sq_sqrt (by
    have naturalPositive := drivenNaturalFrequencySq_pos source channel
    nlinarith [sq_nonneg
      (resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value])

theorem halfPowerDiscriminant_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (halfPowerDiscriminantAt source channel).value := by
  rw [halfPowerDiscriminantAt_value]
  apply Real.sqrt_pos.2
  have naturalPositive := drivenNaturalFrequencySq_pos source channel
  nlinarith [sq_nonneg
    (resistanceBandwidthRateAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value]

theorem bandwidth_lt_halfPowerDiscriminant
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value <
      (halfPowerDiscriminantAt source channel).value := by
  have bandwidthPositive := resistanceBandwidthRate_pos source channel
  have naturalPositive := drivenNaturalFrequencySq_pos source channel
  have discriminantPositive := halfPowerDiscriminant_pos source channel
  have discriminantSq := halfPowerDiscriminant_sq source channel
  nlinarith

theorem lowerHalfPowerFrequency_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (lowerHalfPowerFrequencyAt source channel).value := by
  rw [lowerHalfPowerFrequencyAt_value]
  nlinarith [bandwidth_lt_halfPowerDiscriminant source channel]

theorem lowerHalfPower_lt_upperHalfPower
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (lowerHalfPowerFrequencyAt source channel).value <
      (upperHalfPowerFrequencyAt source channel).value := by
  rw [lowerHalfPowerFrequencyAt_value, upperHalfPowerFrequencyAt_value]
  nlinarith [resistanceBandwidthRate_pos source channel]

theorem halfPowerBandwidth_width_exact
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    upperHalfPowerFrequencyAt source channel -
        lowerHalfPowerFrequencyAt source channel =
      resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel := by
  apply SIQuantity.ext
  simp only [SIQuantity.sub_value, upperHalfPowerFrequencyAt_value,
    lowerHalfPowerFrequencyAt_value]
  ring

theorem resistanceBandwidth_eq_two_damping
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel =
      (2 : ℝ) •
        (compileFiniteDimensionedSeriesRLCNetlistRun source).dampingRateAt
          channel := by
  have dampingIdentity := congrArg SIQuantity.value
    (compiledFiniteDimensionedSeriesRLC_damping_eq_resistanceDamping
      source channel)
  have inductanceNonzero := ne_of_gt
    (compiledFiniteDimensionedSeriesRLC_inductance_pos source channel)
  apply SIQuantity.ext
  simp only [resistanceBandwidthRateAt_value, SIQuantity.smul_value]
  simp only [finiteDimensionedSeriesRLCResistanceDampingAt,
    SIQuantity.castDimension_value, SIQuantity.div_value,
    SIQuantity.smul_value] at dampingIdentity
  field_simp [inductanceNonzero] at dampingIdentity ⊢
  nlinarith

private theorem lowerHalfPower_polynomial
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (lowerHalfPowerFrequencyAt source channel).value ^ 2 +
        (resistanceBandwidthRateAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value *
          (lowerHalfPowerFrequencyAt source channel).value -
        (finiteDimensionedSeriesRLCNaturalFrequencySqAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value = 0 := by
  have discriminantSq := halfPowerDiscriminant_sq source channel
  rw [lowerHalfPowerFrequencyAt_value]
  nlinarith

private theorem upperHalfPower_polynomial
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (upperHalfPowerFrequencyAt source channel).value ^ 2 -
        (resistanceBandwidthRateAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value *
          (upperHalfPowerFrequencyAt source channel).value -
        (finiteDimensionedSeriesRLCNaturalFrequencySqAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value = 0 := by
  have discriminantSq := halfPowerDiscriminant_sq source channel
  rw [upperHalfPowerFrequencyAt_value]
  nlinarith

private theorem lowerReactance_algebra
    {inductance capacitance resistance frequency : ℝ}
    (inductance_ne : inductance ≠ 0)
    (capacitance_ne : capacitance ≠ 0)
    (frequency_ne : frequency ≠ 0)
    (polynomial :
      frequency ^ 2 + (resistance / inductance) * frequency -
        1 / (inductance * capacitance) = 0) :
    inductance * frequency - 1 / (capacitance * frequency) =
      -resistance := by
  field_simp [inductance_ne, capacitance_ne, frequency_ne] at polynomial ⊢
  nlinarith

private theorem upperReactance_algebra
    {inductance capacitance resistance frequency : ℝ}
    (inductance_ne : inductance ≠ 0)
    (capacitance_ne : capacitance ≠ 0)
    (frequency_ne : frequency ≠ 0)
    (polynomial :
      frequency ^ 2 - (resistance / inductance) * frequency -
        1 / (inductance * capacitance) = 0) :
    inductance * frequency - 1 / (capacitance * frequency) =
      resistance := by
  field_simp [inductance_ne, capacitance_ne, frequency_ne] at polynomial ⊢
  nlinarith

private theorem resonantReactance_algebra
    {inductance capacitance frequency : ℝ}
    (inductance_ne : inductance ≠ 0)
    (capacitance_ne : capacitance ≠ 0)
    (frequency_ne : frequency ≠ 0)
    (frequencySq :
      frequency ^ 2 = 1 / (inductance * capacitance)) :
    inductance * frequency - 1 / (capacitance * frequency) = 0 := by
  field_simp [inductance_ne, capacitance_ne, frequency_ne] at frequencySq ⊢
  nlinarith

theorem lowerHalfPower_netReactance_eq_neg_resistance
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (lowerHalfPowerFrequencyAt source channel) =
      -(compileFiniteDimensionedSeriesRLCNetlistRun source
        ).seriesResistanceAt channel := by
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  have lowerPositive := lowerHalfPowerFrequency_pos source channel
  have capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have inductancePositive :=
    compiledFiniteDimensionedSeriesRLC_inductance_pos source channel
  have lowerPolynomial := lowerHalfPower_polynomial source channel
  have naturalValue :
      (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value =
        1 / ((run.inductanceAt channel).value *
          (run.capacitanceAt channel).value) := by
    simp [finiteDimensionedSeriesRLCNaturalFrequencySqAt]
  have bandwidthValue :
      (resistanceBandwidthRateAt run channel).value =
        (run.seriesResistanceAt channel).value /
          (run.inductanceAt channel).value :=
    resistanceBandwidthRateAt_value run channel
  apply SIQuantity.ext
  simp only [SIQuantity.neg_value, drivenNetReactanceAt_value]
  rw [show compileFiniteDimensionedSeriesRLCNetlistRun source = run by rfl]
  rw [naturalValue, bandwidthValue] at lowerPolynomial
  exact lowerReactance_algebra
    (ne_of_gt inductancePositive) (ne_of_gt capacitancePositive)
    (ne_of_gt lowerPositive) lowerPolynomial

theorem upperHalfPower_netReactance_eq_resistance
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (upperHalfPowerFrequencyAt source channel) =
      (compileFiniteDimensionedSeriesRLCNetlistRun source
        ).seriesResistanceAt channel := by
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  have upperPositive : 0 < (upperHalfPowerFrequencyAt source channel).value :=
    lt_trans (lowerHalfPowerFrequency_pos source channel)
      (lowerHalfPower_lt_upperHalfPower source channel)
  have capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have inductancePositive :=
    compiledFiniteDimensionedSeriesRLC_inductance_pos source channel
  have upperPolynomial := upperHalfPower_polynomial source channel
  have naturalValue :
      (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value =
        1 / ((run.inductanceAt channel).value *
          (run.capacitanceAt channel).value) := by
    simp [finiteDimensionedSeriesRLCNaturalFrequencySqAt]
  have bandwidthValue :
      (resistanceBandwidthRateAt run channel).value =
        (run.seriesResistanceAt channel).value /
          (run.inductanceAt channel).value :=
    resistanceBandwidthRateAt_value run channel
  apply SIQuantity.ext
  simp only [drivenNetReactanceAt_value]
  rw [show compileFiniteDimensionedSeriesRLCNetlistRun source = run by rfl]
  rw [naturalValue, bandwidthValue] at upperPolynomial
  exact upperReactance_algebra
    (ne_of_gt inductancePositive) (ne_of_gt capacitancePositive)
    (ne_of_gt upperPositive) upperPolynomial

theorem resistorSense_lowerHalfPower_exact
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    resistorSenseTransferGainSqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (lowerHalfPowerFrequencyAt source channel) = (1 : ℝ) / 2 := by
  have reactance := congrArg SIQuantity.value
    (lowerHalfPower_netReactance_eq_neg_resistance source channel)
  have resistanceNonzero := ne_of_gt
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)
  simp only [SIQuantity.neg_value] at reactance
  unfold resistorSenseTransferGainSqAt
  dsimp only
  rw [reactance]
  field_simp [resistanceNonzero]
  ring

theorem resistorSense_upperHalfPower_exact
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    resistorSenseTransferGainSqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (upperHalfPowerFrequencyAt source channel) = (1 : ℝ) / 2 := by
  have reactance := congrArg SIQuantity.value
    (upperHalfPower_netReactance_eq_resistance source channel)
  have resistanceNonzero := ne_of_gt
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)
  unfold resistorSenseTransferGainSqAt
  dsimp only
  rw [reactance]
  field_simp [resistanceNonzero]
  ring

theorem drivenNaturalFrequency_netReactance_eq_zero
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenNaturalAngularFrequencyAt source channel) = 0 := by
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  have frequencyPositive :
      0 < (drivenNaturalAngularFrequencyAt source channel).value := by
    exact Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos source channel)
  have inductancePositive :=
    compiledFiniteDimensionedSeriesRLC_inductance_pos source channel
  have capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have naturalValue :
      (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value =
        1 / ((run.inductanceAt channel).value *
          (run.capacitanceAt channel).value) := by
    simp [finiteDimensionedSeriesRLCNaturalFrequencySqAt]
  have frequencySq := Real.sq_sqrt
    (drivenNaturalFrequencySq_pos source channel).le
  apply SIQuantity.ext
  simp only [SIQuantity.zero_value, drivenNetReactanceAt_value,
    drivenNaturalAngularFrequencyAt]
  apply resonantReactance_algebra
    (ne_of_gt inductancePositive) (ne_of_gt capacitancePositive)
    (ne_of_gt frequencyPositive)
  exact frequencySq.trans (by simpa only [run] using naturalValue)

theorem resistorSense_resonance_gain_exact
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    resistorSenseTransferGainSqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (drivenNaturalAngularFrequencyAt source channel) = 1 := by
  have reactance :
      (drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenNaturalAngularFrequencyAt source channel)).value = 0 := by
    simpa using congrArg SIQuantity.value
      (drivenNaturalFrequency_netReactance_eq_zero source channel)
  have resistanceNonzero := ne_of_gt
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)
  unfold resistorSenseTransferGainSqAt
  dsimp only
  rw [reactance]
  field_simp [resistanceNonzero]
  ring

theorem resistorSense_resonance_response_eq_drive
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (drive : SIVoltagePhasor) :
    resistorSenseVoltageResponseAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (drivenNaturalAngularFrequencyAt source channel) drive = drive := by
  have reactance :
      (drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenNaturalAngularFrequencyAt source channel)).value = 0 := by
    simpa using congrArg SIQuantity.value
      (drivenNaturalFrequency_netReactance_eq_zero source channel)
  have resistanceNonzero := ne_of_gt
    (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel)
  unfold resistorSenseVoltageResponseAt
  dsimp only
  rw [reactance]
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext <;>
    simp only [SIQuantity.add_value, SIQuantity.sub_value,
      SIQuantity.smul_value, mul_zero]
  · field_simp [resistanceNonzero]
    ring
  · field_simp [resistanceNonzero]
    ring

theorem naturalFrequency_inside_halfPowerBand
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (lowerHalfPowerFrequencyAt source channel).value <
        (drivenNaturalAngularFrequencyAt source channel).value ∧
      (drivenNaturalAngularFrequencyAt source channel).value <
        (upperHalfPowerFrequencyAt source channel).value := by
  have bandwidthPositive := resistanceBandwidthRate_pos source channel
  have discriminantPositive := halfPowerDiscriminant_pos source channel
  have discriminantSq := halfPowerDiscriminant_sq source channel
  have naturalPositive := drivenNaturalFrequencySq_pos source channel
  have naturalSqrtPositive :
      0 < (drivenNaturalAngularFrequencyAt source channel).value :=
    Real.sqrt_pos.2 naturalPositive
  have naturalSqrtSq :
      (drivenNaturalAngularFrequencyAt source channel).value ^ 2 =
        (finiteDimensionedSeriesRLCNaturalFrequencySqAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value := by
    exact Real.sq_sqrt naturalPositive.le
  rw [lowerHalfPowerFrequencyAt_value, upperHalfPowerFrequencyAt_value]
  constructor <;> nlinarith

theorem resistorSense_halfPower_iff_reactanceInterval
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    (1 : ℝ) / 2 ≤ resistorSenseTransferGainSqAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency ↔
      -((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).seriesResistanceAt channel).value ≤
          (drivenNetReactanceAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
            frequency).value ∧
        (drivenNetReactanceAt
            (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
            frequency).value ≤
          ((compileFiniteDimensionedSeriesRLCNetlistRun source
            ).seriesResistanceAt channel).value := by
  let resistance :=
    ((compileFiniteDimensionedSeriesRLCNetlistRun source
      ).seriesResistanceAt channel).value
  let reactance :=
    (drivenNetReactanceAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      frequency).value
  have resistancePositive : 0 < resistance :=
    compiledFiniteDimensionedSeriesRLC_resistance_pos source channel
  have denominatorPositive : 0 < resistance ^ 2 + reactance ^ 2 := by
    nlinarith [sq_pos_of_pos resistancePositive, sq_nonneg reactance]
  change (1 : ℝ) / 2 ≤
      resistance ^ 2 / (resistance ^ 2 + reactance ^ 2) ↔
    -resistance ≤ reactance ∧ reactance ≤ resistance
  constructor
  · intro gain
    have multiplied := (le_div_iff₀ denominatorPositive).mp gain
    constructor <;> nlinarith
  · rintro ⟨lower, upper⟩
    have productNonnegative :
        0 ≤ (resistance - reactance) * (resistance + reactance) :=
      mul_nonneg (sub_nonneg.mpr upper) (by nlinarith)
    apply (le_div_iff₀ denominatorPositive).2
    nlinarith

theorem drivenNetReactance_strictMonoOnPositive
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel)
    (left right : SIHertz) (leftPositive : 0 < left.value)
    (leftBeforeRight : left.value < right.value) :
    (drivenNetReactanceAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel left).value <
      (drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel right).value := by
  let inductance :=
    ((compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt
      channel).value
  let capacitance :=
    ((compileFiniteDimensionedSeriesRLCNetlistRun source).capacitanceAt
      channel).value
  have inductancePositive : 0 < inductance :=
    compiledFiniteDimensionedSeriesRLC_inductance_pos source channel
  have capacitancePositive : 0 < capacitance :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have rightPositive : 0 < right.value := lt_trans leftPositive leftBeforeRight
  have capacitanceLeftPositive : 0 < capacitance * left.value :=
    mul_pos capacitancePositive leftPositive
  have capacitanceOrder :
      capacitance * left.value < capacitance * right.value :=
    mul_lt_mul_of_pos_left leftBeforeRight capacitancePositive
  have reciprocalOrder :
      1 / (capacitance * right.value) <
        1 / (capacitance * left.value) :=
    one_div_lt_one_div_of_lt capacitanceLeftPositive capacitanceOrder
  have inductiveOrder :
      inductance * left.value < inductance * right.value :=
    mul_lt_mul_of_pos_left leftBeforeRight inductancePositive
  simp only [drivenNetReactanceAt_value]
  exact sub_lt_sub inductiveOrder reciprocalOrder

theorem lowerHalfPower_le_iff_negResistance_le_reactance
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) :
    (lowerHalfPowerFrequencyAt source channel).value ≤ frequency.value ↔
      -((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).seriesResistanceAt channel).value ≤
        (drivenNetReactanceAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
          frequency).value := by
  have lowerPositive := lowerHalfPowerFrequency_pos source channel
  have lowerReactance :
      (drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (lowerHalfPowerFrequencyAt source channel)).value =
      -((compileFiniteDimensionedSeriesRLCNetlistRun source
        ).seriesResistanceAt channel).value := by
    simpa using congrArg SIQuantity.value
      (lowerHalfPower_netReactance_eq_neg_resistance source channel)
  constructor
  · intro lowerLe
    rcases lowerLe.eq_or_lt with equal | strict
    · have sameFrequency :
          lowerHalfPowerFrequencyAt source channel = frequency :=
        SIQuantity.ext equal
      subst frequency
      rw [lowerReactance]
    · have monotone := drivenNetReactance_strictMonoOnPositive
        source channel (lowerHalfPowerFrequencyAt source channel) frequency
        lowerPositive strict
      nlinarith
  · intro reactanceBound
    by_contra notLowerLe
    have frequencyBeforeLower :
        frequency.value < (lowerHalfPowerFrequencyAt source channel).value :=
      lt_of_not_ge notLowerLe
    have monotone := drivenNetReactance_strictMonoOnPositive
      source channel frequency (lowerHalfPowerFrequencyAt source channel)
      frequencyPositive frequencyBeforeLower
    nlinarith

theorem le_upperHalfPower_iff_reactance_le_resistance
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) :
    frequency.value ≤ (upperHalfPowerFrequencyAt source channel).value ↔
      (drivenNetReactanceAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
          frequency).value ≤
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).seriesResistanceAt channel).value := by
  have upperPositive : 0 < (upperHalfPowerFrequencyAt source channel).value :=
    lt_trans (lowerHalfPowerFrequency_pos source channel)
      (lowerHalfPower_lt_upperHalfPower source channel)
  have upperReactance :
      (drivenNetReactanceAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (upperHalfPowerFrequencyAt source channel)).value =
      ((compileFiniteDimensionedSeriesRLCNetlistRun source
        ).seriesResistanceAt channel).value := by
    simpa using congrArg SIQuantity.value
      (upperHalfPower_netReactance_eq_resistance source channel)
  constructor
  · intro leUpper
    rcases leUpper.eq_or_lt with equal | strict
    · have sameFrequency : frequency = upperHalfPowerFrequencyAt source channel :=
        SIQuantity.ext equal
      subst frequency
      rw [upperReactance]
    · have monotone := drivenNetReactance_strictMonoOnPositive
        source channel frequency (upperHalfPowerFrequencyAt source channel)
        frequencyPositive strict
      nlinarith
  · intro reactanceBound
    by_contra notLeUpper
    have upperBeforeFrequency :
        (upperHalfPowerFrequencyAt source channel).value < frequency.value :=
      lt_of_not_ge notLeUpper
    have monotone := drivenNetReactance_strictMonoOnPositive
      source channel (upperHalfPowerFrequencyAt source channel) frequency
      upperPositive upperBeforeFrequency
    nlinarith

theorem resistorSense_passband_iff
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) :
    (1 : ℝ) / 2 ≤ resistorSenseTransferGainSqAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency ↔
      (lowerHalfPowerFrequencyAt source channel).value ≤ frequency.value ∧
        frequency.value ≤ (upperHalfPowerFrequencyAt source channel).value := by
  rw [resistorSense_halfPower_iff_reactanceInterval,
    ← lowerHalfPower_le_iff_negResistance_le_reactance
      source channel frequency frequencyPositive,
    ← le_upperHalfPower_iff_reactance_le_resistance
      source channel frequency frequencyPositive]

structure SourceGeneratedExactHalfPowerBandwidthAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : Prop where
  lowerPositive : 0 < (lowerHalfPowerFrequencyAt source channel).value
  lowerBeforeUpper :
    (lowerHalfPowerFrequencyAt source channel).value <
      (upperHalfPowerFrequencyAt source channel).value
  resonanceInside :
    (lowerHalfPowerFrequencyAt source channel).value <
        (drivenNaturalAngularFrequencyAt source channel).value ∧
      (drivenNaturalAngularFrequencyAt source channel).value <
        (upperHalfPowerFrequencyAt source channel).value
  lowerHalfPower :
    resistorSenseTransferGainSqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (lowerHalfPowerFrequencyAt source channel) = (1 : ℝ) / 2
  upperHalfPower :
    resistorSenseTransferGainSqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (upperHalfPowerFrequencyAt source channel) = (1 : ℝ) / 2
  resonanceUnitGain :
    resistorSenseTransferGainSqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (drivenNaturalAngularFrequencyAt source channel) = 1
  widthExact :
    upperHalfPowerFrequencyAt source channel -
        lowerHalfPowerFrequencyAt source channel =
      resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
  widthEqTwoDamping :
    resistanceBandwidthRateAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel =
      (2 : ℝ) •
        (compileFiniteDimensionedSeriesRLCNetlistRun source).dampingRateAt
          channel
  passbandExact : ∀ frequency, 0 < frequency.value →
    ((1 : ℝ) / 2 ≤ resistorSenseTransferGainSqAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency ↔
      (lowerHalfPowerFrequencyAt source channel).value ≤ frequency.value ∧
        frequency.value ≤ (upperHalfPowerFrequencyAt source channel).value)

theorem sourceGeneratedExactHalfPowerBandwidth
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    SourceGeneratedExactHalfPowerBandwidthAt source channel where
  lowerPositive := lowerHalfPowerFrequency_pos source channel
  lowerBeforeUpper := lowerHalfPower_lt_upperHalfPower source channel
  resonanceInside := naturalFrequency_inside_halfPowerBand source channel
  lowerHalfPower := resistorSense_lowerHalfPower_exact source channel
  upperHalfPower := resistorSense_upperHalfPower_exact source channel
  resonanceUnitGain := resistorSense_resonance_gain_exact source channel
  widthExact := halfPowerBandwidth_width_exact source channel
  widthEqTwoDamping := resistanceBandwidth_eq_two_damping source channel
  passbandExact := resistorSense_passband_iff source channel

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.sourceGeneratedExactHalfPowerBandwidth
