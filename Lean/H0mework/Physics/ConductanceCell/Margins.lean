import H0mework.Physics.ConductanceCell.Restoration
import H0mework.Computation.AIGHold.ClockedLeakyHold

/-! # The actual NAND trajectory generates a capacitor-capture margin -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface Set MeasureTheory Storage
open Netlist.Dissipative.Dimensioned.Driven.Producer
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section
namespace LoadedConductanceCellSource

private theorem capture_decay_bound (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last : ℝ) (late : first + source.settlingTime.value ≤ last) :
    source.supply.value * Real.exp (∫ t in first..last, -source.drivenRate left right t) <
      source.supply.value / 8 := by
  have ordered : first ≤ last := by have positive := source.settlingTime_pos; linarith
  have integralBound := source.driven_negativeRate_integral_le left right
    leftContinuous rightContinuous first last ordered
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr integralBound)
    source.supply_pos.le)
  exact positiveExponentialEnvelope_settles source.minimumRate_pos
    (div_pos source.supply_pos (by norm_num)) (by change source.settlingTime.value ≤ last - first; linarith)

theorem driven_capture_low_of_high_high (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, HighBand source (left t) ∧ HighBand source (right t)) :
    CaptureLow source ⟨source.drivenVoltageAt left right initial last⟩ := by
  have ordered : first ≤ last := by have positive := source.settlingTime_pos; linarith
  have ode := source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous
  have coefficient := source.drivenRate_continuous left right leftContinuous rightContinuous
  have compared := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := fun t => source.drivenVoltageAt left right initial t - 4 * source.supply.value / 45)
    (coefficient := fun t => -source.drivenRate left right t)
    (fun t _ => (ode t).sub_const (4 * source.supply.value / 45)) coefficient.neg.continuousOn
    (fun t ht => by
      have bound : (source.equilibrium (left t) (right t)).value ≤ 4 * source.supply.value / 45 := by
        linarith [source.equilibrium_le_four_forty_fifths_of_high_high (left t) (right t)
          (stable t ht).1 (stable t ht).2]
      have forcing := mul_le_mul_of_nonneg_left bound (source.rate_pos (left t) (right t)).le
      change source.drivenRate left right t * (source.equilibrium (left t) (right t)).value ≤
        source.drivenRate left right t * (4 * source.supply.value / 45) at forcing
      rw [← source.drivenForcing_eq_rate_mul_equilibrium left right t] at forcing
      nlinarith)
    last ⟨ordered, le_rfl⟩
  have startRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail first firstNonnegative
  have endRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail last (firstNonnegative.trans ordered)
  have initialBound : source.drivenVoltageAt left right initial first - 4 * source.supply.value / 45 ≤
      source.supply.value := by linarith [startRail.2, source.supply_pos]
  have remainder := compared.trans (mul_le_mul_of_nonneg_right initialBound (Real.exp_pos _).le)
  have strict := source.capture_decay_bound left right leftContinuous rightContinuous first last late
  exact ⟨endRail.1, by change source.drivenVoltageAt left right initial last ≤ _; linarith [source.supply_pos]⟩

theorem driven_capture_high_of_low (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, LowBand source (left t) ∨ LowBand source (right t)) :
    CaptureHigh source ⟨source.drivenVoltageAt left right initial last⟩ := by
  have ordered : first ≤ last := by have positive := source.settlingTime_pos; linarith
  have ode := source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous
  have coefficient := source.drivenRate_continuous left right leftContinuous rightContinuous
  have compared := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := fun t => 41 * source.supply.value / 42 - source.drivenVoltageAt left right initial t)
    (coefficient := fun t => -source.drivenRate left right t)
    (fun t _ => HasDerivAt.const_sub (41 * source.supply.value / 42) (ode t)) coefficient.neg.continuousOn
    (fun t ht => by
      have bound : 41 * source.supply.value / 42 ≤ (source.equilibrium (left t) (right t)).value := by
        rcases stable t ht with leftLow | rightLow
        · linarith [source.forty_one_forty_seconds_le_equilibrium_of_low_left (left t) (right t) leftLow]
        · rw [source.equilibrium_swap]
          linarith [source.forty_one_forty_seconds_le_equilibrium_of_low_left (right t) (left t) rightLow]
      have forcing := mul_le_mul_of_nonneg_left bound (source.rate_pos (left t) (right t)).le
      change source.drivenRate left right t * (41 * source.supply.value / 42) ≤
        source.drivenRate left right t * (source.equilibrium (left t) (right t)).value at forcing
      rw [← source.drivenForcing_eq_rate_mul_equilibrium left right t] at forcing
      nlinarith)
    last ⟨ordered, le_rfl⟩
  have startRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail first firstNonnegative
  have endRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail last (firstNonnegative.trans ordered)
  have initialBound : 41 * source.supply.value / 42 - source.drivenVoltageAt left right initial first ≤
      source.supply.value := by linarith [startRail.1, source.supply_pos]
  have remainder := compared.trans (mul_le_mul_of_nonneg_right initialBound (Real.exp_pos _).le)
  have strict := source.capture_decay_bound left right leftContinuous rightContinuous first last late
  exact ⟨by change _ ≤ source.drivenVoltageAt left right initial last; linarith [source.supply_pos], endRail.2⟩

theorem driven_capture_nand (source : LoadedConductanceCellSource) (leftBit rightBit : Bool)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, BitBand source leftBit (left t) ∧ BitBand source rightBit (right t)) :
    CaptureBand source (!(leftBit && rightBit)) ⟨source.drivenVoltageAt left right initial last⟩ := by
  cases leftBit <;> cases rightBit
  · exact source.driven_capture_high_of_low left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late (fun t ht => Or.inl (stable t ht).1)
  · exact source.driven_capture_high_of_low left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late (fun t ht => Or.inl (stable t ht).1)
  · exact source.driven_capture_high_of_low left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late (fun t ht => Or.inr (stable t ht).2)
  · exact source.driven_capture_low_of_high_high left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late stable

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
