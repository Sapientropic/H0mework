import H0mework.Physics.ReceiverActuation.CapacitorRLCFlow

/-! # Actual load transfer and both dissipations share the same three-state energy ledger -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer

noncomputable section

variable (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
  (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel)
  (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere)

def capacitorRLCHoldEnergyAt (time : ℝ) : SIJoule :=
  ⟨cell.capacitance.value / 2 *
    capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 0 ^ 2⟩

def capacitorRLCRecipientEnergyAt (time : ℝ) : SIJoule :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
  let state := capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time
  ⟨(run.capacitanceAt channel).value / 2 * state 1 ^ 2 +
    (run.inductanceAt channel).value / 2 * state 2 ^ 2⟩

def capacitorRLCEnergyAt (time : ℝ) : SIJoule :=
  capacitorRLCHoldEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time +
    capacitorRLCRecipientEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time

/-- Signed power can flow either way; no transfer sign is installed as a source assumption. -/
def capacitorRLCTransferPowerAt (time : ℝ) : SIWatt :=
  let state := capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time
  ⟨state 0 * state 2⟩

def capacitorRLCLeakPowerAt (time : ℝ) : SIWatt :=
  ⟨capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 0 ^ 2 /
    hold.holdResistance.value⟩

def capacitorRLCResistivePowerAt (time : ℝ) : SIWatt :=
  ⟨((compileFiniteDimensionedSeriesRLCNetlistRun plant).seriesResistanceAt channel).value *
    capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 2 ^ 2⟩

theorem capacitorRLCEnergyAt_nonneg (time : ℝ) :
    0 ≤ (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value := by
  unfold capacitorRLCEnergyAt capacitorRLCHoldEnergyAt capacitorRLCRecipientEnergyAt
  simp only [SIQuantity.add_value]
  exact add_nonneg
    (mul_nonneg (div_nonneg cell.capacitance_pos.le (by norm_num)) (sq_nonneg _))
    (add_nonneg
      (mul_nonneg (div_nonneg (compiledFiniteDimensionedSeriesRLC_capacitance_pos plant channel).le
        (by norm_num)) (sq_nonneg _))
      (mul_nonneg (div_nonneg (compiledFiniteDimensionedSeriesRLC_inductance_pos plant channel).le
        (by norm_num)) (sq_nonneg _)))

theorem capacitorRLCLeakPowerAt_nonneg (time : ℝ) :
    0 ≤ (capacitorRLCLeakPowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value :=
  div_nonneg (sq_nonneg _) hold.holdResistance_pos.le

theorem capacitorRLCResistivePowerAt_nonneg (time : ℝ) :
    0 ≤ (capacitorRLCResistivePowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value :=
  mul_nonneg (compiledFiniteDimensionedSeriesRLC_resistance_pos plant channel).le (sq_nonneg _)

theorem capacitorRLCHoldEnergyAt_power_balance (time : ℝ) :
    HasDerivAt (fun t => (capacitorRLCHoldEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial t).value)
      (-(capacitorRLCLeakPowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCTransferPowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value) time := by
  have derivative := ((capacitorRLCStateAt_hold_hasDerivAt cell hold plant channel
    holdInitial voltageInitial currentInitial time).pow 2).const_mul (cell.capacitance.value / 2)
  convert derivative using 1 <;> first | rfl | (
    dsimp only [capacitorRLCHoldEnergyAt, capacitorRLCLeakPowerAt, capacitorRLCTransferPowerAt]
    field_simp [ne_of_gt cell.capacitance_pos, ne_of_gt hold.holdResistance_pos]
    ring)

theorem capacitorRLCRecipientEnergyAt_power_balance (time : ℝ) :
    HasDerivAt (fun t => (capacitorRLCRecipientEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial t).value)
      ((capacitorRLCTransferPowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCResistivePowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value) time := by
  have capacitor := ((capacitorRLCStateAt_voltage_hasDerivAt cell hold plant channel
    holdInitial voltageInitial currentInitial time).pow 2).const_mul
    (((compileFiniteDimensionedSeriesRLCNetlistRun plant).capacitanceAt channel).value / 2)
  have inductor := ((capacitorRLCStateAt_current_hasDerivAt cell hold plant channel
    holdInitial voltageInitial currentInitial time).pow 2).const_mul
    (((compileFiniteDimensionedSeriesRLCNetlistRun plant).inductanceAt channel).value / 2)
  convert capacitor.add inductor using 1 <;> first | rfl | (
    dsimp only [capacitorRLCRecipientEnergyAt, capacitorRLCTransferPowerAt, capacitorRLCResistivePowerAt]
    have capacitanceNonzero := ne_of_gt (compiledFiniteDimensionedSeriesRLC_capacitance_pos plant channel)
    have inductanceNonzero := ne_of_gt (compiledFiniteDimensionedSeriesRLC_inductance_pos plant channel)
    generalize capacitanceValue : ((compileFiniteDimensionedSeriesRLCNetlistRun plant).capacitanceAt channel).value = C at *
    generalize inductanceValue : ((compileFiniteDimensionedSeriesRLCNetlistRun plant).inductanceAt channel).value = L at *
    field_simp
    ring)

theorem capacitorRLCEnergyAt_power_balance (time : ℝ) :
    HasDerivAt (fun t => (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial t).value)
      (-(capacitorRLCLeakPowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value -
        (capacitorRLCResistivePowerAt cell hold plant channel holdInitial voltageInitial currentInitial time).value) time := by
  have balance := (capacitorRLCHoldEnergyAt_power_balance cell hold plant channel
    holdInitial voltageInitial currentInitial time).add
    (capacitorRLCRecipientEnergyAt_power_balance cell hold plant channel
      holdInitial voltageInitial currentInitial time)
  convert balance using 1 <;> first | rfl | ring

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
