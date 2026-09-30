import H0mework.Physics.ConductanceCell.Invariant
import H0mework.Physics.ConductanceCell.Clock

/-!
# Continuous-input rail restoration from an actual stable interval

The already generated nonautonomous voltage is compared on the actual input
interval. Its coefficients remain time-varying; only independent input-band
consumers are required to stay stable. The existing variable-coefficient
comparison and source waiting-time bound generate the final output band.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface Set MeasureTheory
open Netlist.Dissipative.Dimensioned.Driven.Producer
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section
namespace LoadedConductanceCellSource

theorem driven_negativeRate_integral_le (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last : ℝ) (ordered : first ≤ last) :
    (∫ t in first..last, -source.drivenRate left right t) ≤
      -source.minimumRate * (last - first) := by
  have coefficient := source.drivenRate_continuous left right leftContinuous rightContinuous
  have bound := intervalIntegral.integral_mono_on (μ := volume) ordered
    (coefficient.neg.intervalIntegrable first last)
    (continuous_const.intervalIntegrable first last)
    (fun t _ => neg_le_neg (source.minimumRate_le_rate (left t) (right t)))
  simpa only [Pi.neg_apply, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using bound

private theorem driven_decay_weight_lt_eighth (source : LoadedConductanceCellSource)
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

theorem driven_low_of_high_high (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, HighBand source (left t) ∧ HighBand source (right t)) :
    LowBand source ⟨source.drivenVoltageAt left right initial last⟩ := by
  have ordered : first ≤ last := by have positive := source.settlingTime_pos; linarith
  have ode := source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous
  have coefficient := source.drivenRate_continuous left right leftContinuous rightContinuous
  have compared := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := fun t => source.drivenVoltageAt left right initial t - source.supply.value / 8)
    (coefficient := fun t => -source.drivenRate left right t)
    (fun t _ => (ode t).sub_const (source.supply.value / 8)) coefficient.neg.continuousOn
    (fun t ht => by
      have eqBound := source.equilibrium_le_eighth_of_high_high (left t) (right t)
        (stable t ht).1 (stable t ht).2
      have forcing := mul_le_mul_of_nonneg_left eqBound (source.rate_pos (left t) (right t)).le
      change source.drivenRate left right t * (source.equilibrium (left t) (right t)).value ≤
        source.drivenRate left right t * (source.supply.value / 8) at forcing
      rw [← source.drivenForcing_eq_rate_mul_equilibrium left right t] at forcing
      nlinarith)
    last ⟨ordered, le_rfl⟩
  have startRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail first firstNonnegative
  have endRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail last (firstNonnegative.trans ordered)
  have initialBound : source.drivenVoltageAt left right initial first - source.supply.value / 8 ≤
      source.supply.value := by linarith [startRail.2, source.supply_pos]
  have remainder := compared.trans (mul_le_mul_of_nonneg_right initialBound (Real.exp_pos _).le)
  have strict := source.driven_decay_weight_lt_eighth left right
    leftContinuous rightContinuous first last late
  exact ⟨endRail.1, by change source.drivenVoltageAt left right initial last ≤ _; linarith⟩

theorem driven_high_of_low (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, LowBand source (left t) ∨ LowBand source (right t)) :
    HighBand source ⟨source.drivenVoltageAt left right initial last⟩ := by
  have ordered : first ≤ last := by have positive := source.settlingTime_pos; linarith
  have ode := source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous
  have coefficient := source.drivenRate_continuous left right leftContinuous rightContinuous
  have compared := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := fun t => 7 * source.supply.value / 8 - source.drivenVoltageAt left right initial t)
    (coefficient := fun t => -source.drivenRate left right t)
    (fun t _ => HasDerivAt.const_sub (7 * source.supply.value / 8) (ode t)) coefficient.neg.continuousOn
    (fun t ht => by
      have eqBound : 7 * source.supply.value / 8 ≤ (source.equilibrium (left t) (right t)).value := by
        rcases stable t ht with leftLow | rightLow
        · exact source.seven_eighths_le_equilibrium_of_low_left (left t) (right t) leftLow
        · exact source.seven_eighths_le_equilibrium_of_low_right (left t) (right t) rightLow
      have forcing := mul_le_mul_of_nonneg_left eqBound (source.rate_pos (left t) (right t)).le
      change source.drivenRate left right t * (7 * source.supply.value / 8) ≤
        source.drivenRate left right t * (source.equilibrium (left t) (right t)).value at forcing
      rw [← source.drivenForcing_eq_rate_mul_equilibrium left right t] at forcing
      nlinarith)
    last ⟨ordered, le_rfl⟩
  have startRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail first firstNonnegative
  have endRail := source.drivenVoltageAt_mem_rail left right initial
    leftContinuous rightContinuous initialRail last (firstNonnegative.trans ordered)
  have initialBound : 7 * source.supply.value / 8 - source.drivenVoltageAt left right initial first ≤
      source.supply.value := by linarith [startRail.1, source.supply_pos]
  have remainder := compared.trans (mul_le_mul_of_nonneg_right initialBound (Real.exp_pos _).le)
  have strict := source.driven_decay_weight_lt_eighth left right
    leftContinuous rightContinuous first last late
  exact ⟨by change _ ≤ source.drivenVoltageAt left right initial last; linarith, endRail.2⟩

theorem driven_nand_band (source : LoadedConductanceCellSource) (leftBit rightBit : Bool)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, BitBand source leftBit (left t) ∧ BitBand source rightBit (right t)) :
    BitBand source (!(leftBit && rightBit)) ⟨source.drivenVoltageAt left right initial last⟩ := by
  cases leftBit <;> cases rightBit
  · exact source.driven_high_of_low left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late (fun t ht => Or.inl (stable t ht).1)
  · exact source.driven_high_of_low left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late (fun t ht => Or.inl (stable t ht).1)
  · exact source.driven_high_of_low left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late (fun t ht => Or.inr (stable t ht).2)
  · exact source.driven_low_of_high_high left right initial leftContinuous rightContinuous initialRail
      first last firstNonnegative late stable

theorem driven_nand_read (source : LoadedConductanceCellSource) (leftBit rightBit : Bool)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (initialRail : InRail source initial) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + source.settlingTime.value ≤ last)
    (stable : ∀ t ∈ Icc first last, BitBand source leftBit (left t) ∧ BitBand source rightBit (right t)) :
    railRead? source ⟨source.drivenVoltageAt left right initial last⟩ = some (!(leftBit && rightBit)) := by
  have band := source.driven_nand_band leftBit rightBit left right initial leftContinuous rightContinuous
    initialRail first last firstNonnegative late stable
  cases result : !(leftBit && rightBit)
  · exact railRead?_of_low source _ (by simpa only [result, BitBand, Bool.false_eq_true, ↓reduceIte] using band)
  · exact railRead?_of_high source _ (by simpa only [result, BitBand, ↓reduceIte] using band)

end LoadedConductanceCellSource
end

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
