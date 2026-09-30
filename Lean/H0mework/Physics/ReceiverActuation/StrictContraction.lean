import H0mework.Physics.ReceiverActuation.StrictEnergy
import H0mework.NavierStokes.Galerkin.CriticalGronwall

/-! # Every passive capacitor-loaded RLC source generates a strict decay rate -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section

private theorem weighted_cross_bound (a b x y : ℝ) (ap : 0 < a) :
    b * x * y ≤ a / 2 * x ^ 2 + b ^ 2 / (2 * a) * y ^ 2 := by
  field_simp
  nlinarith [sq_nonneg (a * x - b * y)]

private theorem physical_cross_dissipation_bound (Rh C L R q U V I : ℝ)
    (hp : 0 < Rh) (cp : 0 < C) (lp : 0 < L) (qp : 0 < q)
    (q1 : q ≤ L / (2 * Rh)) (q2 : q ≤ R * C * L / (2 * (L + R ^ 2 * C))) :
    -U ^ 2 / Rh - R * I ^ 2 + q * ((I / C) * I + V * ((U - R * I - V) / L)) ≤
      -U ^ 2 / (2 * Rh) - q / (2 * L) * V ^ 2 - R / 2 * I ^ 2 := by
  have hn := ne_of_gt hp
  have cn := ne_of_gt cp
  have ln := ne_of_gt lp
  have qn := ne_of_gt qp
  have coefficient : (q / L) ^ 2 / (2 * (1 / Rh)) ≤ q / (4 * L) := by
    field_simp at q1 ⊢
    nlinarith [mul_nonneg qp.le (sub_nonneg.mpr q1)]
  have cross1 : q / L * U * V ≤ U ^ 2 / (2 * Rh) + q / (4 * L) * V ^ 2 := by
    have generated := weighted_cross_bound (1 / Rh) (q / L) U V (one_div_pos.mpr hp)
    have scaled := mul_le_mul_of_nonneg_right coefficient (sq_nonneg V)
    ring_nf at generated scaled ⊢
    linarith
  have cross2 : -q * R / L * V * I ≤ q / (4 * L) * V ^ 2 + q * R ^ 2 / L * I ^ 2 := by
    have generated := weighted_cross_bound (q / (2 * L)) (-q * R / L) V I
      (div_pos qp (mul_pos (by norm_num) lp))
    convert generated using 1; field_simp; ring
  have coefficientI : q / C + q * R ^ 2 / L ≤ R / 2 := by
    have positive : 0 < L + R ^ 2 * C := add_pos_of_pos_of_nonneg lp (mul_nonneg (sq_nonneg R) cp.le)
    field_simp at q2 ⊢
    nlinarith
  have scaled := mul_le_mul_of_nonneg_right coefficientI (sq_nonneg I)
  ring_nf at cross1 cross2 scaled ⊢
  linarith

private theorem physical_rate_controls_energy (Ch C L Rh R q rate U V I F : ℝ)
    (chp : 0 < Ch) (cp : 0 < C) (lp : 0 < L) (hp : 0 < Rh) (rp : 0 ≤ rate)
    (h0 : rate ≤ 1 / (2 * Rh * Ch)) (h1 : rate ≤ q / (2 * L * C)) (h2 : rate ≤ R / (2 * L))
    (fb : F ≤ Ch * U ^ 2 + C * V ^ 2 + L * I ^ 2) :
    rate * F ≤ U ^ 2 / (2 * Rh) + q / (2 * L) * V ^ 2 + R / 2 * I ^ 2 := by
  have cn := ne_of_gt cp
  have ln := ne_of_gt lp
  have chn := ne_of_gt chp
  have hn := ne_of_gt hp
  have hu : rate * (Ch * U ^ 2) ≤ U ^ 2 / (2 * Rh) := by
    convert mul_le_mul_of_nonneg_right h0 (mul_nonneg chp.le (sq_nonneg U)) using 1
    all_goals first | rfl | field_simp
  have hv : rate * (C * V ^ 2) ≤ q / (2 * L) * V ^ 2 := by
    convert mul_le_mul_of_nonneg_right h1 (mul_nonneg cp.le (sq_nonneg V)) using 1
    all_goals first | rfl | field_simp
  have hi : rate * (L * I ^ 2) ≤ R / 2 * I ^ 2 := by
    convert mul_le_mul_of_nonneg_right h2 (mul_nonneg lp.le (sq_nonneg I)) using 1
    all_goals first | rfl | field_simp
  have hf := mul_le_mul_of_nonneg_left fb rp
  nlinarith

variable (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
  (plant : DimensionedSeriesRLCSource) (channel : FiniteEmbodimentChannel)
  (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere)

def capacitorRLCStrictEnergyDerivativeAt (time : ℝ) : ℝ :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
  let state := capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time;
  -state 0 ^ 2 / hold.holdResistance.value - (run.seriesResistanceAt channel).value * state 2 ^ 2 +
    capacitorRLCCrossWeight cell hold plant channel *
      ((state 2 / (run.capacitanceAt channel).value) * state 2 +
        state 1 * ((state 0 - (run.seriesResistanceAt channel).value * state 2 - state 1) /
          (run.inductanceAt channel).value))

theorem capacitorRLCStrictEnergyAt_hasDerivAt (time : ℝ) :
    HasDerivAt (fun t => (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial t).value)
      (capacitorRLCStrictEnergyDerivativeAt cell hold plant channel holdInitial voltageInitial currentInitial time) time := by
  have base := capacitorRLCEnergyAt_power_balance cell hold plant channel holdInitial voltageInitial currentInitial time
  have cross := ((capacitorRLCStateAt_voltage_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial time).mul
    (capacitorRLCStateAt_current_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial time)).const_mul
      (capacitorRLCCrossWeight cell hold plant channel)
  convert base.add cross using 1 <;> first | rfl | (
    dsimp only [capacitorRLCStrictEnergyAt, capacitorRLCStrictEnergyDerivativeAt, capacitorRLCLeakPowerAt,
      capacitorRLCResistivePowerAt, SIQuantity.add_value]
    first | (funext t; dsimp only [Pi.add_apply, Pi.mul_apply]; ring) | ring)

theorem capacitorRLCStrictEnergyDerivativeAt_le_neg (time : ℝ) :
    capacitorRLCStrictEnergyDerivativeAt cell hold plant channel holdInitial voltageInitial currentInitial time ≤
      -capacitorRLCContractionRate cell hold plant channel *
        (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value := by
  let run := compileFiniteDimensionedSeriesRLCNetlistRun plant
  let state := capacitorRLCStateAt cell hold plant channel holdInitial voltageInitial currentInitial time
  have cp := compiledFiniteDimensionedSeriesRLC_capacitance_pos plant channel
  have lp := compiledFiniteDimensionedSeriesRLC_inductance_pos plant channel
  have qBounds := capacitorRLCCrossWeight_bounds cell hold plant channel
  have decay := physical_cross_dissipation_bound hold.holdResistance.value (run.capacitanceAt channel).value
    (run.inductanceAt channel).value (run.seriesResistanceAt channel).value
    (capacitorRLCCrossWeight cell hold plant channel) (state 0) (state 1) (state 2)
    hold.holdResistance_pos cp lp (capacitorRLCCrossWeight_pos cell hold plant channel) qBounds.2.1 qBounds.2.2
  have rateBounds := capacitorRLCContractionRate_bounds cell hold plant channel
  have energyBound := (capacitorRLCStrictEnergyAt_bounds cell hold plant channel holdInitial voltageInitial currentInitial time).2
  have physicalBound :
      (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ≤
        cell.capacitance.value * state 0 ^ 2 + (run.capacitanceAt channel).value * state 1 ^ 2 +
          (run.inductanceAt channel).value * state 2 ^ 2 := by
    dsimp only [capacitorRLCEnergyAt, capacitorRLCHoldEnergyAt, capacitorRLCRecipientEnergyAt,
      SIQuantity.add_value] at energyBound
    dsimp only [state, run]
    nlinarith
  have control := physical_rate_controls_energy cell.capacitance.value (run.capacitanceAt channel).value
    (run.inductanceAt channel).value hold.holdResistance.value (run.seriesResistanceAt channel).value
    (capacitorRLCCrossWeight cell hold plant channel) (capacitorRLCContractionRate cell hold plant channel)
    (state 0) (state 1) (state 2) _ cell.capacitance_pos cp lp hold.holdResistance_pos
    (capacitorRLCContractionRate_pos cell hold plant channel).le rateBounds.1 rateBounds.2.1 rateBounds.2.2 physicalBound
  change -state 0 ^ 2 / hold.holdResistance.value - (run.seriesResistanceAt channel).value * state 2 ^ 2 +
    capacitorRLCCrossWeight cell hold plant channel *
      ((state 2 / (run.capacitanceAt channel).value) * state 2 +
        state 1 * ((state 0 - (run.seriesResistanceAt channel).value * state 2 - state 1) /
          (run.inductanceAt channel).value)) ≤ _
  ring_nf at decay control ⊢
  linarith

theorem capacitorRLCStrictEnergyAt_exp_bound (time : ℝ) (nonnegative : 0 ≤ time) :
    (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ≤
      (capacitorRLCStrictEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value *
        Real.exp (-capacitorRLCContractionRate cell hold plant channel * time) := by
  have comparison := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (a := 0) (b := time)
    (fun t _ => capacitorRLCStrictEnergyAt_hasDerivAt cell hold plant channel holdInitial voltageInitial currentInitial t)
    continuous_const.continuousOn
    (fun t _ => capacitorRLCStrictEnergyDerivativeAt_le_neg cell hold plant channel holdInitial voltageInitial currentInitial t)
    time ⟨nonnegative, le_rfl⟩
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using comparison

theorem capacitorRLCEnergyAt_exp_bound (time : ℝ) (nonnegative : 0 ≤ time) :
    (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ≤
      4 * Real.exp (-capacitorRLCContractionRate cell hold plant channel * time) *
        (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value := by
  have lower := (capacitorRLCStrictEnergyAt_bounds cell hold plant channel holdInitial voltageInitial currentInitial time).1
  have upper := (capacitorRLCStrictEnergyAt_bounds cell hold plant channel holdInitial voltageInitial currentInitial 0).2
  have decay := capacitorRLCStrictEnergyAt_exp_bound cell hold plant channel holdInitial voltageInitial currentInitial time nonnegative
  have scaled := mul_le_mul_of_nonneg_right upper
    (Real.exp_pos (-capacitorRLCContractionRate cell hold plant channel * time)).le
  nlinarith

/-- A fixed physical source pays the wait; neither initial energy nor a requested result selects it. -/
def capacitorRLCHalfEnergyWait : SISecond :=
  ⟨8 / capacitorRLCContractionRate cell hold plant channel⟩

theorem capacitorRLCHalfEnergyWait_pos : 0 < (capacitorRLCHalfEnergyWait cell hold plant channel).value :=
  div_pos (by norm_num) (capacitorRLCContractionRate_pos cell hold plant channel)

theorem capacitorRLCEnergyAt_le_half (time : ℝ)
    (late : (capacitorRLCHalfEnergyWait cell hold plant channel).value ≤ time) :
    (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial time).value ≤
      (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value / 2 := by
  let rate := capacitorRLCContractionRate cell hold plant channel
  have ratePositive : 0 < rate := capacitorRLCContractionRate_pos cell hold plant channel
  have scaledTime : 8 ≤ rate * time := by
    have bound := (div_le_iff₀ ratePositive).mp late
    nlinarith
  have expLarge : 8 ≤ Real.exp (rate * time) := by
    linarith [Real.add_one_le_exp (rate * time)]
  have product : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero]
  have scaled := mul_le_mul_of_nonneg_right expLarge (Real.exp_pos (-rate * time)).le
  have factor : 4 * Real.exp (-rate * time) ≤ 1 / 2 := by nlinarith
  have energyNonnegative := capacitorRLCEnergyAt_nonneg cell hold plant channel holdInitial voltageInitial currentInitial 0
  have nonnegative := (capacitorRLCHalfEnergyWait_pos cell hold plant channel).le.trans late
  calc
    _ ≤ 4 * Real.exp (-rate * time) *
        (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value :=
      capacitorRLCEnergyAt_exp_bound cell hold plant channel holdInitial voltageInitial currentInitial time nonnegative
    _ ≤ (1 / 2) * (capacitorRLCEnergyAt cell hold plant channel holdInitial voltageInitial currentInitial 0).value :=
      mul_le_mul_of_nonneg_right factor energyNonnegative
    _ = _ := by ring

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
