import H0mework.Physics.ConductanceCell.Restoration

/-! # Actual out-of-rail charge is retained as a generated decaying residual -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface Set MeasureTheory

noncomputable section
namespace LoadedConductanceCellSource

theorem drivenVoltageAt_initial_difference (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial other : SIVolt) (time : ℝ) :
    source.drivenVoltageAt left right initial time - source.drivenVoltageAt left right other time =
      Real.exp (-source.accumulatedRate left right time) * (initial.value - other.value) := by
  simp only [drivenVoltageAt]
  ring

theorem driven_initial_decay_le_one (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (time : ℝ) (nonnegative : 0 ≤ time) :
    Real.exp (-source.accumulatedRate left right time) ≤ 1 := by
  have decay := source.driven_negativeRate_integral_le left right leftContinuous rightContinuous 0 time nonnegative
  rw [intervalIntegral.integral_neg] at decay
  apply Real.exp_le_one_iff.mpr
  change -(∫ s in (0 : ℝ)..time, source.drivenRate left right s) ≤ 0
  have rate := source.minimumRate_pos
  nlinarith

/-- The zero-initial curve is a comparison, not a reset of the actual producer. -/
theorem drivenVoltageAt_initial_envelope (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (time : ℝ) (nonnegative : 0 ≤ time) :
    -|initial.value| ≤ source.drivenVoltageAt left right initial time ∧
      source.drivenVoltageAt left right initial time ≤ source.supply.value + |initial.value| := by
  have zeroRail : InRail source (0 : SIVolt) := ⟨le_rfl, source.supply_pos.le⟩
  have reference := source.drivenVoltageAt_mem_rail left right 0
    leftContinuous rightContinuous zeroRail time nonnegative
  have difference := congrArg abs (source.drivenVoltageAt_initial_difference left right initial 0 time)
  simp only [SIQuantity.zero_value, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)] at difference
  have decayed := mul_le_mul_of_nonneg_right
    (source.driven_initial_decay_le_one left right leftContinuous rightContinuous time nonnegative)
    (abs_nonneg initial.value)
  rw [one_mul, ← difference] at decayed
  have bounds := abs_le.mp decayed
  constructor <;> linarith [reference.1, reference.2, bounds.1, bounds.2]

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
