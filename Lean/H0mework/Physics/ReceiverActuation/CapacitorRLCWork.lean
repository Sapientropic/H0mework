import H0mework.Physics.ReceiverActuation.CapacitorRLCEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Signed transferred work and both actual heat integrals of the passive load -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer

noncomputable section

variable (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
  (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel)
  (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere)

def capacitorRLCTransferWorkAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time,
    (capacitorRLCTransferPowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value⟩

def capacitorRLCLeakHeatAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time,
    (capacitorRLCLeakPowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value⟩

def capacitorRLCResistiveHeatAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time,
    (capacitorRLCResistivePowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value⟩

theorem capacitorRLCHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (capacitorRLCLeakHeatAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ∧
    0 ≤ (capacitorRLCResistiveHeatAt cell hold plant channel holdInitial voltageInitial currentInitial time).value :=
  ⟨intervalIntegral.integral_nonneg_of_forall nonnegative
      (fun t => capacitorRLCLeakPowerAt_nonneg _ _ _ _ _ _ _ t),
    intervalIntegral.integral_nonneg_of_forall nonnegative
      (fun t => capacitorRLCResistivePowerAt_nonneg _ _ _ _ _ _ _ t)⟩

theorem capacitorRLCPowerFunctions_continuous :
    Continuous (fun t =>
      (capacitorRLCTransferPowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value) ∧
    Continuous (fun t =>
      (capacitorRLCLeakPowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value) ∧
    Continuous (fun t =>
      (capacitorRLCResistivePowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value) := by
  have u : Continuous (fun t =>
      capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial t 0) :=
    continuous_iff_continuousAt.mpr fun t =>
      (capacitorRLCStateAt_hold_hasDerivAt _ _ _ _ _ _ _ t).continuousAt
  have i : Continuous (fun t =>
      capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial t 2) :=
    continuous_iff_continuousAt.mpr fun t =>
      (capacitorRLCStateAt_current_hasDerivAt _ _ _ _ _ _ _ t).continuousAt
  exact ⟨u.mul i, (u.pow 2).div_const _, continuous_const.mul (i.pow 2)⟩

theorem capacitorRLCRecipientEnergyAt_integrated_balance (time : ℝ) :
    (capacitorRLCRecipientEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCRecipientEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value =
      (capacitorRLCTransferWorkAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCResistiveHeatAt cell hold plant channel holdInitial voltageInitial currentInitial time).value := by
  obtain ⟨transferContinuous, _, resistorContinuous⟩ :=
    capacitorRLCPowerFunctions_continuous cell hold plant channel holdInitial voltageInitial currentInitial
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) time) =>
      capacitorRLCRecipientEnergyAt_power_balance cell hold plant channel holdInitial voltageInitial currentInitial t)
    ((transferContinuous.sub resistorContinuous).intervalIntegrable 0 time)
  rw [intervalIntegral.integral_sub (transferContinuous.intervalIntegrable 0 time)
    (resistorContinuous.intervalIntegrable 0 time)] at paid
  exact paid.symm

theorem capacitorRLCHoldEnergyAt_integrated_balance (time : ℝ) :
    (capacitorRLCHoldEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCHoldEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value =
      -(capacitorRLCLeakHeatAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCTransferWorkAt cell hold plant channel holdInitial voltageInitial currentInitial time).value := by
  obtain ⟨transferContinuous, leakContinuous, _⟩ :=
    capacitorRLCPowerFunctions_continuous cell hold plant channel holdInitial voltageInitial currentInitial
  have leakNegative : Continuous (fun t =>
      -(capacitorRLCLeakPowerAt cell hold plant channel holdInitial voltageInitial currentInitial t).value) :=
    leakContinuous.neg
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) time) =>
      capacitorRLCHoldEnergyAt_power_balance cell hold plant channel holdInitial voltageInitial currentInitial t)
    ((leakNegative.sub transferContinuous).intervalIntegrable 0 time)
  rw [intervalIntegral.integral_sub (leakNegative.intervalIntegrable 0 time)
    (transferContinuous.intervalIntegrable 0 time), intervalIntegral.integral_neg] at paid
  exact paid.symm

/-- Signed transfer cancels internally; no external power is minted by connecting the load. -/
theorem capacitorRLCEnergyAt_integrated_balance (time : ℝ) :
    (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value =
      -(capacitorRLCLeakHeatAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCResistiveHeatAt cell hold plant channel holdInitial voltageInitial currentInitial time).value := by
  have held := capacitorRLCHoldEnergyAt_integrated_balance cell hold plant channel holdInitial voltageInitial currentInitial time
  have recipient := capacitorRLCRecipientEnergyAt_integrated_balance cell hold plant channel holdInitial voltageInitial currentInitial time
  dsimp only [capacitorRLCEnergyAt, SIQuantity.add_value]
  linarith

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
