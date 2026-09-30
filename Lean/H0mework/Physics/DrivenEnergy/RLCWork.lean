import H0mework.Physics.RLCResponse.Response
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual driven-recipient work and heat in SI units

The existing arbitrary-initial forced RLC trajectory supplies every voltage and current.
Joule storage uses the physical half factors; source work and resistor heat are independent
integrals of the actual branch powers. No settling or endpoint certificate is an input.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface MeasureTheory
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

/-- Physical capacitor and inductor storage, read from one actual recipient state. -/
def drivenRLCStoredEnergy (source : DimensionedSeriesRLCSource)
    (state : FiniteDimensionedSeriesRLCPortState) (channel : FiniteEmbodimentChannel) : SIJoule :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  ⟨(run.capacitanceAt channel).value / 2 * (state.voltageAt channel).value ^ 2 +
    (run.inductanceAt channel).value / 2 * (state.currentAt channel).value ^ 2⟩

variable (source : DimensionedSeriesRLCSource)
  (frequencyAt : FiniteEmbodimentChannel → SIHertz)
  (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
  (initial : FiniteDimensionedSeriesRLCPortState) (channel : FiniteEmbodimentChannel)

def drivenRLCEnergyAt (time : ℝ) : SIJoule :=
  drivenRLCStoredEnergy source (drivenTotalPortStateAt source frequencyAt driveAt initial ⟨time⟩) channel

/-- Signed power from the prescribed source into the actual series current. -/
def drivenRLCSourcePowerAt (time : ℝ) : SIWatt :=
  ⟨(voltageWaveformAt (frequencyAt channel) (driveAt channel) ⟨time⟩).value *
    (drivenTotalCurrentAt source frequencyAt driveAt initial channel ⟨time⟩).value⟩

def drivenRLCHeatPowerAt (time : ℝ) : SIWatt :=
  ⟨((compileFiniteDimensionedSeriesRLCNetlistRun source).seriesResistanceAt channel).value *
    (drivenTotalCurrentAt source frequencyAt driveAt initial channel ⟨time⟩).value ^ 2⟩

theorem drivenRLCStoredEnergy_nonneg (state : FiniteDimensionedSeriesRLCPortState) :
    0 ≤ (drivenRLCStoredEnergy source state channel).value :=
  add_nonneg
    (mul_nonneg (div_nonneg (compiledFiniteDimensionedSeriesRLC_capacitance_pos source channel).le
      (by norm_num)) (sq_nonneg _))
    (mul_nonneg (div_nonneg (compiledFiniteDimensionedSeriesRLC_inductance_pos source channel).le
      (by norm_num)) (sq_nonneg _))

theorem drivenRLCHeatPowerAt_nonneg (time : ℝ) :
    0 ≤ (drivenRLCHeatPowerAt source frequencyAt driveAt initial channel time).value :=
  mul_nonneg (compiledFiniteDimensionedSeriesRLC_resistance_pos source channel).le (sq_nonneg _)

theorem drivenRLCEnergyAt_initial :
    drivenRLCEnergyAt source frequencyAt driveAt initial channel 0 =
      drivenRLCStoredEnergy source initial channel := by
  unfold drivenRLCEnergyAt
  rw [show (⟨(0 : ℝ)⟩ : SISecond) = 0 from rfl, drivenTotalPortState_initial_exact]

/-- The capacitor law and forced KVL pay the exact physical energy derivative. -/
theorem drivenRLCEnergyAt_power_balance
    (frequencyPositive : ∀ channel, 0 < (frequencyAt channel).value) (time : ℝ) :
    HasDerivAt (fun t => (drivenRLCEnergyAt source frequencyAt driveAt initial channel t).value)
      ((drivenRLCSourcePowerAt source frequencyAt driveAt initial channel time).value -
        (drivenRLCHeatPowerAt source frequencyAt driveAt initial channel time).value) time := by
  have capacitor := ((drivenTotalVoltage_hasSIQuantityDerivAt
    source frequencyAt driveAt initial channel ⟨time⟩).valueHasDerivAt.pow 2).const_mul
      (((compileFiniteDimensionedSeriesRLCNetlistRun source).capacitanceAt channel).value / 2)
  have inductor := ((drivenTotalCurrent_hasSIQuantityDerivAt
    source frequencyAt driveAt initial channel ⟨time⟩).valueHasDerivAt.pow 2).const_mul
      (((compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt channel).value / 2)
  have capacitorLaw := congrArg SIQuantity.value
    (drivenTotal_capacitorConstitutiveLaw source frequencyAt driveAt initial channel ⟨time⟩)
  have voltageLaw := congrArg SIQuantity.value
    (drivenTotal_forcedKirchhoffVoltageLaw source frequencyAt frequencyPositive
      driveAt initial channel ⟨time⟩)
  simp only [capacitanceTimesVoltageRate_value, inductanceTimesCurrentRate_value,
    resistanceTimesCurrent_value, SIQuantity.add_value] at capacitorLaw voltageLaw
  convert capacitor.add inductor using 1 <;> first | rfl | (
    dsimp only [drivenRLCSourcePowerAt, drivenRLCHeatPowerAt]
    linear_combination
      -(drivenTotalVoltageAt source frequencyAt driveAt initial channel ⟨time⟩).value * capacitorLaw -
      (drivenTotalCurrentAt source frequencyAt driveAt initial channel ⟨time⟩).value * voltageLaw)

theorem drivenRLCPowers_continuous :
    Continuous (fun t => (drivenRLCSourcePowerAt source frequencyAt driveAt initial channel t).value) ∧
    Continuous (fun t => (drivenRLCHeatPowerAt source frequencyAt driveAt initial channel t).value) := by
  have currentContinuous : Continuous (fun t =>
      (drivenTotalCurrentAt source frequencyAt driveAt initial channel ⟨t⟩).value) :=
    continuous_iff_continuousAt.mpr (fun t => (drivenTotalCurrent_hasSIQuantityDerivAt
      source frequencyAt driveAt initial channel ⟨t⟩).valueHasDerivAt.continuousAt)
  have driveContinuous : Continuous (fun t =>
      (voltageWaveformAt (frequencyAt channel) (driveAt channel) ⟨t⟩).value) :=
    continuous_iff_continuousAt.mpr (fun t => (voltageWaveform_hasSIQuantityDerivAt
      (frequencyAt channel) (driveAt channel) ⟨t⟩).valueHasDerivAt.continuousAt)
  exact ⟨driveContinuous.mul currentContinuous, continuous_const.mul (currentContinuous.pow 2)⟩

/-- Oriented source work on an arbitrary finite physical interval. -/
def drivenRLCWork (start stop : SISecond) : SIJoule :=
  ⟨∫ t in start.value..stop.value, (drivenRLCSourcePowerAt source frequencyAt driveAt initial channel t).value⟩

def drivenRLCHeat (start stop : SISecond) : SIJoule :=
  ⟨∫ t in start.value..stop.value, (drivenRLCHeatPowerAt source frequencyAt driveAt initial channel t).value⟩

theorem drivenRLCHeat_nonneg (start stop : SISecond) (ordered : start.value ≤ stop.value) :
    0 ≤ (drivenRLCHeat source frequencyAt driveAt initial channel start stop).value :=
  intervalIntegral.integral_nonneg_of_forall ordered
    (fun t => drivenRLCHeatPowerAt_nonneg source frequencyAt driveAt initial channel t)

/-- Independent branch-power integrals settle the difference of actual endpoint energies. -/
theorem drivenRLCEnergyAt_integrated_balance
    (frequencyPositive : ∀ channel, 0 < (frequencyAt channel).value) (start stop : SISecond) :
    (drivenRLCEnergyAt source frequencyAt driveAt initial channel stop.value).value -
      (drivenRLCEnergyAt source frequencyAt driveAt initial channel start.value).value =
        (drivenRLCWork source frequencyAt driveAt initial channel start stop).value -
          (drivenRLCHeat source frequencyAt driveAt initial channel start stop).value := by
  obtain ⟨sourceContinuous, heatContinuous⟩ :=
    drivenRLCPowers_continuous source frequencyAt driveAt initial channel
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc start.value stop.value) =>
      drivenRLCEnergyAt_power_balance source frequencyAt driveAt initial channel frequencyPositive t)
    ((sourceContinuous.sub heatContinuous).intervalIntegrable start.value stop.value)
  rw [intervalIntegral.integral_sub (sourceContinuous.intervalIntegrable start.value stop.value)
    (heatContinuous.intervalIntegrable start.value stop.value)] at paid
  exact paid.symm

theorem drivenRLCWork_pays_energy_increase
    (frequencyPositive : ∀ channel, 0 < (frequencyAt channel).value)
    (start stop : SISecond) (ordered : start.value ≤ stop.value) :
    (drivenRLCEnergyAt source frequencyAt driveAt initial channel stop.value).value -
      (drivenRLCEnergyAt source frequencyAt driveAt initial channel start.value).value ≤
        (drivenRLCWork source frequencyAt driveAt initial channel start stop).value := by
  rw [drivenRLCEnergyAt_integrated_balance source frequencyAt driveAt initial channel frequencyPositive]
  exact sub_le_self _ (drivenRLCHeat_nonneg source frequencyAt driveAt initial channel start stop ordered)

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
