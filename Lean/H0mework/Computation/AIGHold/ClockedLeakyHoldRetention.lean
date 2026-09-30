import H0mework.Computation.AIGHold.ClockedLeakyHold

/-! # Source-generated finite retention, with actual leakage rather than a constant held bit -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Units.Interface Cells.Conductance Set

noncomputable section
namespace ClockedLeakyHoldSource

variable {source : LoadedConductanceCellSource}

theorem decayFactor_le_one (hold : ClockedLeakyHoldSource source) (elapsed : ℝ)
    (nonnegative : 0 ≤ elapsed) :
    Real.exp (-elapsed / hold.timeConstant.value) ≤ 1 :=
  Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr nonnegative)
    hold.timeConstant_pos.le)

theorem decayFactor_ge_fifteen_sixteenths (hold : ClockedLeakyHoldSource source) (elapsed : ℝ)
    (withinLease : elapsed ≤ hold.retentionTime.value) :
    (15 / 16 : ℝ) ≤ Real.exp (-elapsed / hold.timeConstant.value) := by
  have ratio : elapsed / hold.timeConstant.value ≤ 1 / 16 := by
    apply (div_le_iff₀ hold.timeConstant_pos).mpr
    calc
      elapsed ≤ hold.retentionTime.value := withinLease
      _ = (1 / 16) * hold.timeConstant.value := by dsimp only [retentionTime]; ring
  have lower := Real.add_one_le_exp (-(elapsed / hold.timeConstant.value))
  rw [neg_div]
  linarith

theorem wave_at_elapsed (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime elapsed : ℝ) (nonnegative : 0 ≤ elapsed) :
    (hold.wave input stopTime (stopTime + elapsed)).value =
      (input stopTime).value * Real.exp (-elapsed / hold.timeConstant.value) := by
  change hold.voltageAt input stopTime (stopTime + elapsed) = _
  rw [hold.voltageAt_after input stopTime (stopTime + elapsed) (by linarith)]
  simp only [decayAt, add_sub_cancel_left]

/-- A positive capture really loses voltage: this model is not a copied constant sample. -/
theorem wave_strictly_below_capture (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime elapsed : ℝ) (capturePositive : 0 < (input stopTime).value)
    (elapsedPositive : 0 < elapsed) :
    (hold.wave input stopTime (stopTime + elapsed)).value < (input stopTime).value := by
  rw [hold.wave_at_elapsed input stopTime elapsed elapsedPositive.le]
  have drops : Real.exp (-elapsed / hold.timeConstant.value) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos elapsedPositive) hold.timeConstant_pos)
  simpa only [mul_one] using mul_lt_mul_of_pos_left drops capturePositive

theorem wave_low_of_captureLow (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime elapsed : ℝ) (capture : CaptureLow source (input stopTime))
    (nonnegative : 0 ≤ elapsed) :
    LowBand source (hold.wave input stopTime (stopTime + elapsed)) := by
  have exponential := hold.decayFactor_le_one elapsed nonnegative
  have capNonnegative := capture.1
  change 0 ≤ _ ∧ _ ≤ _
  rw [hold.wave_at_elapsed input stopTime elapsed nonnegative]
  refine ⟨mul_nonneg capNonnegative (Real.exp_pos _).le, ?_⟩
  have upper := mul_le_mul_of_nonneg_left exponential capNonnegative
  have captureUpper := capture.2
  linarith [source.supply_pos]

theorem wave_high_of_captureHigh (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime elapsed : ℝ) (capture : CaptureHigh source (input stopTime))
    (nonnegative : 0 ≤ elapsed) (withinLease : elapsed ≤ hold.retentionTime.value) :
    HighBand source (hold.wave input stopTime (stopTime + elapsed)) := by
  have exponentialUpper := hold.decayFactor_le_one elapsed nonnegative
  have exponentialLower := hold.decayFactor_ge_fifteen_sixteenths elapsed withinLease
  have captureLower := capture.1
  have captureUpper := capture.2
  have capNonnegative : 0 ≤ (input stopTime).value := by linarith [source.supply_pos]
  change _ ≤ _ ∧ _ ≤ _
  rw [hold.wave_at_elapsed input stopTime elapsed nonnegative]
  constructor
  · have lower := mul_le_mul captureLower exponentialLower (by norm_num : (0 : ℝ) ≤ 15 / 16)
      capNonnegative
    linarith [source.supply_pos]
  · have upper := mul_le_mul_of_nonneg_left exponentialUpper capNonnegative
    linarith

theorem retains_captureBand (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime : ℝ) (bit : Bool) (capture : CaptureBand source bit (input stopTime))
    (elapsed : ℝ) (nonnegative : 0 ≤ elapsed) (withinLease : elapsed ≤ hold.retentionTime.value) :
    BitBand source bit (hold.wave input stopTime (stopTime + elapsed)) := by
  cases bit
  · exact hold.wave_low_of_captureLow input stopTime elapsed capture nonnegative
  · exact hold.wave_high_of_captureHigh input stopTime elapsed capture nonnegative withinLease

end ClockedLeakyHoldSource
end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
