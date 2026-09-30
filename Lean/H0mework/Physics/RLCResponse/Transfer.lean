import H0mework.Physics.RLCResponse.Drive
import H0mework.Physics.RLCNetlist.DimensionedRun

/-!
# Exact driven transfer kernel for the dimensioned series-RLC core

The source-side physical run generates the two real quadratures of a voltage
drive and of the capacitor response.  The response is the inverse of the
literal R/L/C phasor equation, not an assumed transfer receipt.  A generated
high-frequency witness gives a quantitative finite low-pass roll-off.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

theorem inductance_capacitance_frequency_frequency_dimension :
    ((inductanceDimension + capacitanceDimension) + frequencyDimension) +
        frequencyDimension = dimensionless := by
  decide

theorem resistance_capacitance_frequency_dimension :
    (resistanceDimension + capacitanceDimension) + frequencyDimension =
      dimensionless := by
  decide

theorem frequency_current_dimension :
    frequencyDimension + currentDimension =
      currentDimension - timeDimension := by
  decide

def drivenReactiveCoefficientAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    DimensionlessQuantity :=
  SIQuantity.castDimension
    inductance_capacitance_frequency_frequency_dimension
    (SIQuantity.mul
      (SIQuantity.mul
        (SIQuantity.mul (run.inductanceAt channel)
          (run.capacitanceAt channel)) frequency) frequency)

def drivenResistiveCoefficientAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    DimensionlessQuantity :=
  SIQuantity.castDimension resistance_capacitance_frequency_dimension
    (SIQuantity.mul
      (SIQuantity.mul (run.seriesResistanceAt channel)
        (run.capacitanceAt channel)) frequency)

def drivenDetuningAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : ℝ :=
  1 - (drivenReactiveCoefficientAt run channel frequency).value

def drivenDampingAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : ℝ :=
  (drivenResistiveCoefficientAt run channel frequency).value

def drivenTransferDenominatorAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) : ℝ :=
  drivenDetuningAt run channel frequency ^ 2 +
    drivenDampingAt run channel frequency ^ 2

@[simp] theorem drivenReactiveCoefficientAt_value
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    (drivenReactiveCoefficientAt run channel frequency).value =
      (run.inductanceAt channel).value *
        (run.capacitanceAt channel).value * frequency.value ^ 2 := by
  simp [drivenReactiveCoefficientAt, pow_two]
  ring

@[simp] theorem drivenResistiveCoefficientAt_value
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz) :
    (drivenResistiveCoefficientAt run channel frequency).value =
      (run.seriesResistanceAt channel).value *
        (run.capacitanceAt channel).value * frequency.value := by
  simp [drivenResistiveCoefficientAt]

def drivenVoltageResponseAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) : SIVoltagePhasor :=
  let a := drivenDetuningAt run channel frequency
  let b := drivenDampingAt run channel frequency
  let denominator := drivenTransferDenominatorAt run channel frequency
  ⟨(a / denominator) • drive.cosine -
      (b / denominator) • drive.sine,
    (b / denominator) • drive.cosine +
      (a / denominator) • drive.sine⟩

/-- Feed-forward voltage command generated from a requested capacitor-voltage
phasor by the same R/L/C row. -/
def drivenVoltageCommandForAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (requestedResponse : SIVoltagePhasor) : SIVoltagePhasor :=
  let a := drivenDetuningAt run channel frequency
  let b := drivenDampingAt run channel frequency
  ⟨a • requestedResponse.cosine + b • requestedResponse.sine,
    (-b) • requestedResponse.cosine + a • requestedResponse.sine⟩

def drivenCapacitorCurrentPhasorAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (response : SIVoltagePhasor) : SICurrentPhasor :=
  ⟨frequencyTimesCapacitanceVoltage frequency
      (run.capacitanceAt channel) response.sine,
    -frequencyTimesCapacitanceVoltage frequency
      (run.capacitanceAt channel) response.cosine⟩

def frequencyTimesCurrent
    (frequency : SIHertz) (current : SIAmpere) : CurrentRateQuantity :=
  SIQuantity.castDimension frequency_current_dimension
    (SIQuantity.mul frequency current)

def drivenResistorVoltagePhasorAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (current : SICurrentPhasor) :
    SIVoltagePhasor :=
  ⟨resistanceTimesCurrent (run.seriesResistanceAt channel) current.cosine,
    resistanceTimesCurrent (run.seriesResistanceAt channel) current.sine⟩

def drivenInductorVoltagePhasorAt
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (current : SICurrentPhasor) : SIVoltagePhasor :=
  ⟨inductanceTimesCurrentRate (run.inductanceAt channel)
      (frequencyTimesCurrent frequency current.sine),
    -inductanceTimesCurrentRate (run.inductanceAt channel)
      (frequencyTimesCurrent frequency current.cosine)⟩

theorem drivenTransferDenominator_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) :
    0 < drivenTransferDenominatorAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency := by
  have resistancePositive :=
    compiledFiniteDimensionedSeriesRLC_resistance_pos source channel
  have capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have dampingPositive :
      0 < drivenDampingAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency := by
    simp only [drivenDampingAt, drivenResistiveCoefficientAt_value]
    exact mul_pos (mul_pos resistancePositive capacitancePositive)
      frequencyPositive
  unfold drivenTransferDenominatorAt
  nlinarith [sq_pos_of_pos dampingPositive,
    sq_nonneg (drivenDetuningAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency)]

theorem drivenVoltageResponse_command_eq
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value)
    (requestedResponse : SIVoltagePhasor) :
    drivenVoltageResponseAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
        (drivenVoltageCommandForAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
          requestedResponse) =
      requestedResponse := by
  have denominatorPositive :=
    drivenTransferDenominator_pos source channel frequency frequencyPositive
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext <;>
    simp only [drivenVoltageResponseAt, drivenVoltageCommandForAt,
      SIQuantity.sub_value, SIQuantity.add_value, SIQuantity.smul_value]
  · field_simp [ne_of_gt denominatorPositive]
    unfold drivenTransferDenominatorAt
    ring
  · field_simp [ne_of_gt denominatorPositive]
    unfold drivenTransferDenominatorAt
    ring

theorem drivenVoltageCommand_response_eq
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value)
    (drive : SIVoltagePhasor) :
    drivenVoltageCommandForAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
        (drivenVoltageResponseAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
          drive) =
      drive := by
  have denominatorPositive :=
    drivenTransferDenominator_pos source channel frequency frequencyPositive
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext <;>
    simp only [drivenVoltageResponseAt, drivenVoltageCommandForAt,
      SIQuantity.sub_value, SIQuantity.add_value, SIQuantity.smul_value]
  · field_simp [ne_of_gt denominatorPositive]
    unfold drivenTransferDenominatorAt
    ring
  · field_simp [ne_of_gt denominatorPositive]
    unfold drivenTransferDenominatorAt
    ring

theorem drivenVoltageCommandFor_eq_componentKVL
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (response : SIVoltagePhasor) :
    drivenVoltageCommandForAt run channel frequency response =
      response +
        drivenResistorVoltagePhasorAt run channel
          (drivenCapacitorCurrentPhasorAt run channel frequency response) +
        drivenInductorVoltagePhasorAt run channel frequency
          (drivenCapacitorCurrentPhasorAt run channel frequency response) := by
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext <;>
    simp [drivenVoltageCommandForAt, drivenDetuningAt, drivenDampingAt,
      drivenCapacitorCurrentPhasorAt, drivenResistorVoltagePhasorAt,
      drivenInductorVoltagePhasorAt, frequencyTimesCurrent,
      drivenReactiveCoefficientAt, drivenResistiveCoefficientAt]
    <;> ring

theorem drivenVoltageResponse_magnitude_sq
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) (drive : SIVoltagePhasor) :
    voltagePhasorMagnitudeSq
        (drivenVoltageResponseAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
          drive) =
      (1 / drivenTransferDenominatorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency) •
        voltagePhasorMagnitudeSq drive := by
  have denominatorPositive :=
    drivenTransferDenominator_pos source channel frequency frequencyPositive
  apply SIQuantity.ext
  simp only [voltagePhasorMagnitudeSq_value, drivenVoltageResponseAt,
    SIQuantity.sub_value, SIQuantity.add_value, SIQuantity.smul_value]
  field_simp [ne_of_gt denominatorPositive]
  unfold drivenTransferDenominatorAt
  ring

theorem drivenVoltageResponseAt_zeroFrequency
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (drive : SIVoltagePhasor) :
    drivenVoltageResponseAt run channel (0 : SIHertz) drive = drive := by
  apply SIVoltagePhasor.ext <;> apply SIQuantity.ext <;>
    simp [drivenVoltageResponseAt, drivenTransferDenominatorAt,
      drivenDetuningAt, drivenDampingAt, drivenReactiveCoefficientAt,
      drivenResistiveCoefficientAt]

def drivenNaturalAngularFrequencyAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  ⟨Real.sqrt
    (finiteDimensionedSeriesRLCNaturalFrequencySqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value⟩

def drivenHighFrequencyWitnessAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : SIHertz :=
  (2 : ℝ) • drivenNaturalAngularFrequencyAt source channel

theorem drivenNaturalFrequencySq_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (finiteDimensionedSeriesRLCNaturalFrequencySqAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel).value := by
  rw [compiledFiniteDimensionedSeriesRLC_naturalFrequencySq_eq]
  simp only [SIQuantity.add_value, SIQuantity.square_value]
  nlinarith [sq_pos_of_pos
    (compiledFiniteDimensionedSeriesRLC_frequency_pos source channel)]

theorem drivenHighFrequencyWitness_pos
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    0 < (drivenHighFrequencyWitnessAt source channel).value := by
  simp only [drivenHighFrequencyWitnessAt, SIQuantity.smul_value]
  exact mul_pos (by norm_num)
    (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos source channel))

theorem drivenHighFrequency_reactiveCoefficient_eq_four
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    (drivenReactiveCoefficientAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (drivenHighFrequencyWitnessAt source channel)).value = 4 := by
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  have inductancePositive :=
    compiledFiniteDimensionedSeriesRLC_inductance_pos source channel
  have capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel
  have lcPositive :
      0 < (run.inductanceAt channel).value *
        (run.capacitanceAt channel).value :=
    mul_pos inductancePositive capacitancePositive
  have naturalValue :
      (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value =
        1 / ((run.inductanceAt channel).value *
          (run.capacitanceAt channel).value) := by
    simp [finiteDimensionedSeriesRLCNaturalFrequencySqAt]
  have naturalNonnegative :
      0 ≤ (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value :=
    (drivenNaturalFrequencySq_pos source channel).le
  have sqrtSquared := Real.sq_sqrt naturalNonnegative
  simp only [drivenReactiveCoefficientAt_value,
    drivenHighFrequencyWitnessAt, drivenNaturalAngularFrequencyAt,
    SIQuantity.smul_value]
  rw [show
    (2 * Real.sqrt
      (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value) ^ 2 =
        4 * (finiteDimensionedSeriesRLCNaturalFrequencySqAt run channel).value
      by nlinarith]
  rw [naturalValue]
  field_simp [ne_of_gt lcPositive]
  simp only [run]
  exact div_self (ne_of_gt (mul_pos inductancePositive capacitancePositive))

theorem drivenHighFrequency_denominator_ge_nine
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    9 ≤ drivenTransferDenominatorAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
      (drivenHighFrequencyWitnessAt source channel) := by
  have reactive :=
    drivenHighFrequency_reactiveCoefficient_eq_four source channel
  unfold drivenTransferDenominatorAt drivenDetuningAt
  rw [reactive]
  nlinarith [sq_nonneg
    (drivenDampingAt (compileFiniteDimensionedSeriesRLCNetlistRun source)
      channel (drivenHighFrequencyWitnessAt source channel))]

theorem drivenHighFrequency_gainSquared_le_one_ninth
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    1 / drivenTransferDenominatorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenHighFrequencyWitnessAt source channel) ≤ (1 : ℝ) / 9 := by
  have denominatorBound :=
    drivenHighFrequency_denominator_ge_nine source channel
  have denominatorPositive :
      0 < drivenTransferDenominatorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenHighFrequencyWitnessAt source channel) :=
    lt_of_lt_of_le (by norm_num) denominatorBound
  rw [div_le_iff₀ denominatorPositive]
  nlinarith

theorem drivenHighFrequency_response_magnitude_sq_le
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (drive : SIVoltagePhasor) :
    (voltagePhasorMagnitudeSq
      (drivenVoltageResponseAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenHighFrequencyWitnessAt source channel) drive)).value ≤
      ((1 : ℝ) / 9) * (voltagePhasorMagnitudeSq drive).value := by
  have responseMagnitude := congrArg SIQuantity.value
    (drivenVoltageResponse_magnitude_sq source channel
      (drivenHighFrequencyWitnessAt source channel)
      (drivenHighFrequencyWitness_pos source channel) drive)
  simp only [SIQuantity.smul_value] at responseMagnitude
  rw [responseMagnitude]
  exact mul_le_mul_of_nonneg_right
    (drivenHighFrequency_gainSquared_le_one_ninth source channel)
    (by simp [voltagePhasorMagnitudeSq_value]; positivity)

structure FiniteLowPassBandwidthWitnessAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) : Prop where
  dcPass : ∀ drive,
    drivenVoltageResponseAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel 0 drive = drive
  highFrequencyPositive :
    0 < (drivenHighFrequencyWitnessAt source channel).value
  highFrequencyAttenuation : ∀ drive,
    (voltagePhasorMagnitudeSq
      (drivenVoltageResponseAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
        (drivenHighFrequencyWitnessAt source channel) drive)).value ≤
      ((1 : ℝ) / 9) * (voltagePhasorMagnitudeSq drive).value

theorem generatedFiniteLowPassBandwidthWitness
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) :
    FiniteLowPassBandwidthWitnessAt source channel where
  dcPass := drivenVoltageResponseAt_zeroFrequency _ channel
  highFrequencyPositive := drivenHighFrequencyWitness_pos source channel
  highFrequencyAttenuation :=
    drivenHighFrequency_response_magnitude_sq_le source channel

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.drivenVoltageResponse_command_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.drivenVoltageCommandFor_eq_componentKVL
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.generatedFiniteLowPassBandwidthWitness
