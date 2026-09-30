import H0mework.Physics.ReceiverActuation.CapacitorRLCEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # A source-generated cross energy detects all three passive state directions -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer

noncomputable section

variable (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
  (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel)

/-- This is the physical coefficient `ε √(CL)`; no trajectory or stability ticket selects it. -/
def capacitorRLCCrossWeight : ℝ :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
  let C := (run.capacitanceAt channel).value
  let L := (run.inductanceAt channel).value
  let R := (run.seriesResistanceAt channel).value
  min (Real.sqrt (C * L) / 4)
    (min (L / (2 * hold.holdResistance.value)) (R * C * L / (2 * (L + R ^ 2 * C))))

theorem capacitorRLCCrossWeight_pos : 0 < capacitorRLCCrossWeight cell hold plant channel := by
  have cp := compiledFiniteDimensionedSeriesRLC_capacitance_pos plant channel
  have lp := compiledFiniteDimensionedSeriesRLC_inductance_pos plant channel
  have rp := compiledFiniteDimensionedSeriesRLC_resistance_pos plant channel
  unfold capacitorRLCCrossWeight
  exact lt_min (div_pos (Real.sqrt_pos.mpr (mul_pos cp lp)) (by norm_num))
    (lt_min (div_pos lp (mul_pos (by norm_num) hold.holdResistance_pos))
      (div_pos (mul_pos (mul_pos rp cp) lp)
        (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg lp (mul_nonneg (sq_nonneg _) cp.le)))))

theorem capacitorRLCCrossWeight_bounds :
    let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
    let C := (run.capacitanceAt channel).value
    let L := (run.inductanceAt channel).value
    let R := (run.seriesResistanceAt channel).value
    capacitorRLCCrossWeight cell hold plant channel ≤ Real.sqrt (C * L) / 4 ∧
    capacitorRLCCrossWeight cell hold plant channel ≤ L / (2 * hold.holdResistance.value) ∧
    capacitorRLCCrossWeight cell hold plant channel ≤ R * C * L / (2 * (L + R ^ 2 * C)) := by
  dsimp only
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

def capacitorRLCContractionRate : ℝ :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
  min (1 / (2 * hold.holdResistance.value * cell.capacitance.value))
    (min (capacitorRLCCrossWeight cell hold plant channel /
      (2 * (run.inductanceAt channel).value * (run.capacitanceAt channel).value))
      ((run.seriesResistanceAt channel).value / (2 * (run.inductanceAt channel).value)))

theorem capacitorRLCContractionRate_pos : 0 < capacitorRLCContractionRate cell hold plant channel := by
  have cp := compiledFiniteDimensionedSeriesRLC_capacitance_pos plant channel
  have lp := compiledFiniteDimensionedSeriesRLC_inductance_pos plant channel
  have rp := compiledFiniteDimensionedSeriesRLC_resistance_pos plant channel
  unfold capacitorRLCContractionRate
  exact lt_min (div_pos (by norm_num) (mul_pos (mul_pos (by norm_num)
    hold.holdResistance_pos) cell.capacitance_pos))
    (lt_min (div_pos (capacitorRLCCrossWeight_pos cell hold plant channel)
      (mul_pos (mul_pos (by norm_num) lp) cp)) (div_pos rp (mul_pos (by norm_num) lp)))

theorem capacitorRLCContractionRate_bounds :
    let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
    capacitorRLCContractionRate cell hold plant channel ≤
      1 / (2 * hold.holdResistance.value * cell.capacitance.value) ∧
    capacitorRLCContractionRate cell hold plant channel ≤
      capacitorRLCCrossWeight cell hold plant channel /
        (2 * (run.inductanceAt channel).value * (run.capacitanceAt channel).value) ∧
    capacitorRLCContractionRate cell hold plant channel ≤
      (run.seriesResistanceAt channel).value / (2 * (run.inductanceAt channel).value) := by
  dsimp only
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

variable (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere)

def capacitorRLCStrictEnergyAt (time : ℝ) : SIJoule :=
  let state := capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time
  capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time +
    ⟨capacitorRLCCrossWeight cell hold plant channel * state 1 * state 2⟩

private theorem physical_cross_energy_bounds (Ch C L q U V I : ℝ)
    (chp : 0 < Ch) (cp : 0 < C) (lp : 0 < L) (qp : 0 ≤ q)
    (qb : q ≤ Real.sqrt (C * L) / 4) :
    (Ch * U ^ 2 / 2 + C * V ^ 2 / 2 + L * I ^ 2 / 2) / 2 ≤
      Ch * U ^ 2 / 2 + C * V ^ 2 / 2 + L * I ^ 2 / 2 + q * V * I ∧
    Ch * U ^ 2 / 2 + C * V ^ 2 / 2 + L * I ^ 2 / 2 + q * V * I ≤
      2 * (Ch * U ^ 2 / 2 + C * V ^ 2 / 2 + L * I ^ 2 / 2) := by
  have sqrtC := Real.sq_sqrt cp.le
  have sqrtL := Real.sq_sqrt lp.le
  have sqrtProduct : Real.sqrt C * Real.sqrt L = Real.sqrt (C * L) := (Real.sqrt_mul cp.le L).symm
  have weighted : 2 * Real.sqrt (C * L) * |V * I| ≤ C * V ^ 2 + L * I ^ 2 := by
    by_cases sign : 0 ≤ V * I
    · rw [abs_of_nonneg sign, ← sqrtProduct]
      nlinarith [sq_nonneg (Real.sqrt C * V - Real.sqrt L * I)]
    · rw [abs_of_neg (lt_of_not_ge sign), ← sqrtProduct]
      nlinarith [sq_nonneg (Real.sqrt C * V + Real.sqrt L * I)]
  have weightBound := mul_le_mul_of_nonneg_right qb (abs_nonneg (V * I))
  have crossLow := mul_le_mul_of_nonneg_left (neg_abs_le (V * I)) qp
  have crossHigh := mul_le_mul_of_nonneg_left (le_abs_self (V * I)) qp
  have remaining := mul_nonneg chp.le (sq_nonneg U)
  constructor <;> nlinarith [mul_nonneg cp.le (sq_nonneg V), mul_nonneg lp.le (sq_nonneg I)]

theorem capacitorRLCStrictEnergyAt_bounds (time : ℝ) :
    (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value / 2 ≤
      (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ∧
    (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ≤
      2 * (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value := by
  have bounds := physical_cross_energy_bounds cell.capacitance.value
    ((compileFiniteDimensionedSeriesRLCNetlistRun plant).capacitanceAt channel).value
    ((compileFiniteDimensionedSeriesRLCNetlistRun plant).inductanceAt channel).value
    (capacitorRLCCrossWeight cell hold plant channel)
    (capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 0)
    (capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 1)
    (capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time 2)
    cell.capacitance_pos (compiledFiniteDimensionedSeriesRLC_capacitance_pos plant channel)
    (compiledFiniteDimensionedSeriesRLC_inductance_pos plant channel)
    (capacitorRLCCrossWeight_pos cell hold plant channel).le
    (capacitorRLCCrossWeight_bounds cell hold plant channel).1
  dsimp only [capacitorRLCStrictEnergyAt, capacitorRLCEnergyAt, capacitorRLCHoldEnergyAt,
    capacitorRLCRecipientEnergyAt, SIQuantity.add_value]
  constructor <;> nlinarith [bounds.1, bounds.2]

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
