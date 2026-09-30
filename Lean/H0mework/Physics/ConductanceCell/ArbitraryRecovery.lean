import H0mework.Physics.ConductanceCell.InitialResidual
import H0mework.Physics.ConductanceCell.InteriorEquilibrium

/-! # The actual initial charge generates a finite recovery wait, without a rail premise -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface Set MeasureTheory
open Netlist.Dissipative.Dimensioned.Driven.Producer
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section
namespace LoadedConductanceCellSource

def arbitraryRecoveryTime (source : LoadedConductanceCellSource) (initial : SIVolt) : SISecond :=
  ⟨positiveExponentialSettlingTime source.minimumRate (source.supply.value + |initial.value|)
    (source.supply.value / 8192)⟩

theorem arbitraryRecoveryTime_pos (source : LoadedConductanceCellSource) (initial : SIVolt) :
    0 < (source.arbitraryRecoveryTime initial).value :=
  positiveExponentialSettlingTime_pos source.minimumRate_pos
    (add_nonneg source.supply_pos.le (abs_nonneg _)) (div_pos source.supply_pos (by norm_num))

private theorem arbitraryRecovery_decay (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last : ℝ) (late : first + (source.arbitraryRecoveryTime initial).value ≤ last) :
    (source.supply.value + |initial.value|) * Real.exp (∫ t in first..last, -source.drivenRate left right t) <
      source.supply.value / 8192 := by
  have ordered : first ≤ last := by have := source.arbitraryRecoveryTime_pos initial; linarith
  have integralBound := source.driven_negativeRate_integral_le left right leftContinuous rightContinuous first last ordered
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr integralBound)
    (add_nonneg source.supply_pos.le (abs_nonneg _)))
  exact positiveExponentialEnvelope_settles source.minimumRate_pos
    (div_pos source.supply_pos (by norm_num)) (by change (source.arbitraryRecoveryTime initial).value ≤ last - first; linarith)

private theorem driven_compare_upper (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last plane : ℝ) (ordered : first ≤ last)
    (upper : ∀ t ∈ Icc first last, (source.equilibrium (left t) (right t)).value ≤ plane) :
    source.drivenVoltageAt left right initial last - plane ≤
      (source.drivenVoltageAt left right initial first - plane) *
        Real.exp (∫ t in first..last, -source.drivenRate left right t) := by
  apply le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := fun t => source.drivenVoltageAt left right initial t - plane)
    (coefficient := fun t => -source.drivenRate left right t)
    (fun t _ => (source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous t).sub_const plane)
    (source.drivenRate_continuous left right leftContinuous rightContinuous).neg.continuousOn
    (fun t ht => ?_) last ⟨ordered, le_rfl⟩
  have bounded := mul_le_mul_of_nonneg_left (upper t ht) (source.rate_pos (left t) (right t)).le
  rw [source.drivenForcing_eq_rate_mul_equilibrium]
  dsimp only [drivenRate] at *
  nlinarith

private theorem driven_compare_lower (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last plane : ℝ) (ordered : first ≤ last)
    (lower : ∀ t ∈ Icc first last, plane ≤ (source.equilibrium (left t) (right t)).value) :
    plane - source.drivenVoltageAt left right initial last ≤
      (plane - source.drivenVoltageAt left right initial first) *
        Real.exp (∫ t in first..last, -source.drivenRate left right t) := by
  apply le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := fun t => plane - source.drivenVoltageAt left right initial t)
    (coefficient := fun t => -source.drivenRate left right t)
    (fun t _ => (source.drivenVoltageAt_hasDerivAt left right initial leftContinuous rightContinuous t).const_sub plane)
    (source.drivenRate_continuous left right leftContinuous rightContinuous).neg.continuousOn
    (fun t ht => ?_) last ⟨ordered, le_rfl⟩
  have bounded := mul_le_mul_of_nonneg_left (lower t ht) (source.rate_pos (left t) (right t)).le
  rw [source.drivenForcing_eq_rate_mul_equilibrium]
  dsimp only [drivenRate] at *
  nlinarith

theorem drivenVoltageAt_recovers_interior (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + (source.arbitraryRecoveryTime initial).value ≤ last)
    (inputRails : ∀ t ∈ Icc first last, InRail source (left t) ∧ InRail source (right t)) :
    source.supply.value / 8192 ≤ source.drivenVoltageAt left right initial last ∧
      source.drivenVoltageAt left right initial last ≤ source.supply.value - source.supply.value / 8192 := by
  have ordered : first ≤ last := by have := source.arbitraryRecoveryTime_pos initial; linarith
  have start := source.drivenVoltageAt_initial_envelope left right initial leftContinuous rightContinuous first firstNonnegative
  have remainder := source.arbitraryRecovery_decay left right initial leftContinuous rightContinuous first last late
  have weight := (Real.exp_pos (∫ t in first..last, -source.drivenRate left right t)).le
  have supply := source.supply_pos
  have lower := source.driven_compare_lower left right initial leftContinuous rightContinuous
    first last (source.supply.value / 4096) ordered
    (fun t ht => (source.equilibrium_interior_of_inputs_in_rail (left t) (right t)
      (inputRails t ht).1 (inputRails t ht).2).1)
  have upper := source.driven_compare_upper left right initial leftContinuous rightContinuous
    first last (source.supply.value - source.supply.value / 4096) ordered
    (fun t ht => (source.equilibrium_interior_of_inputs_in_rail (left t) (right t)
      (inputRails t ht).1 (inputRails t ht).2).2)
  have lowerBound : source.supply.value / 4096 - source.drivenVoltageAt left right initial first ≤
      source.supply.value + |initial.value| := by linarith [start.1]
  have upperBound : source.drivenVoltageAt left right initial first -
      (source.supply.value - source.supply.value / 4096) ≤ source.supply.value + |initial.value| := by linarith [start.2]
  have lo := lower.trans (mul_le_mul_of_nonneg_right lowerBound weight)
  have hi := upper.trans (mul_le_mul_of_nonneg_right upperBound weight)
  constructor <;> linarith

private theorem bitBand_in_rail (source : LoadedConductanceCellSource) (bit : Bool) (voltage : SIVolt)
    (band : BitBand source bit voltage) : InRail source voltage := by
  cases bit
  · exact ⟨band.1, by linarith [band.2, source.supply_pos]⟩
  · exact ⟨by linarith [band.1, source.supply_pos], band.2⟩

theorem driven_nand_from_arbitrary_initial (source : LoadedConductanceCellSource)
    (leftBit rightBit : Bool) (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (late : first + (source.arbitraryRecoveryTime initial).value ≤ last)
    (stable : ∀ t ∈ Icc first last, BitBand source leftBit (left t) ∧ BitBand source rightBit (right t)) :
    BitBand source (!(leftBit && rightBit)) ⟨source.drivenVoltageAt left right initial last⟩ := by
  have ordered : first ≤ last := by have := source.arbitraryRecoveryTime_pos initial; linarith
  have start := source.drivenVoltageAt_initial_envelope left right initial leftContinuous rightContinuous first firstNonnegative
  have interior := source.drivenVoltageAt_recovers_interior left right initial leftContinuous rightContinuous
    first last firstNonnegative late (fun t ht => ⟨source.bitBand_in_rail leftBit (left t) (stable t ht).1,
      source.bitBand_in_rail rightBit (right t) (stable t ht).2⟩)
  have weight := (Real.exp_pos (∫ t in first..last, -source.drivenRate left right t)).le
  have remainder := source.arbitraryRecovery_decay left right initial leftContinuous rightContinuous first last late
  have supply := source.supply_pos
  have high (lowInput : ∀ t ∈ Icc first last, LowBand source (left t) ∨ LowBand source (right t)) :
      HighBand source ⟨source.drivenVoltageAt left right initial last⟩ := by
    have compared := source.driven_compare_lower left right initial leftContinuous rightContinuous
      first last (7 * source.supply.value / 8) ordered (fun t ht => by
        rcases lowInput t ht with leftLow | rightLow
        · exact source.seven_eighths_le_equilibrium_of_low_left (left t) (right t) leftLow
        · exact source.seven_eighths_le_equilibrium_of_low_right (left t) (right t) rightLow)
    have initialBound : 7 * source.supply.value / 8 - source.drivenVoltageAt left right initial first ≤
        source.supply.value + |initial.value| := by linarith [start.1]
    have bounded := compared.trans (mul_le_mul_of_nonneg_right initialBound weight)
    constructor <;> dsimp only <;> linarith [interior.2]
  have low (highInputs : ∀ t ∈ Icc first last, HighBand source (left t) ∧ HighBand source (right t)) :
      LowBand source ⟨source.drivenVoltageAt left right initial last⟩ := by
    have compared := source.driven_compare_upper left right initial leftContinuous rightContinuous
      first last (source.supply.value / 8) ordered (fun t ht =>
        source.equilibrium_le_eighth_of_high_high (left t) (right t) (highInputs t ht).1 (highInputs t ht).2)
    have initialBound : source.drivenVoltageAt left right initial first - source.supply.value / 8 ≤
        source.supply.value + |initial.value| := by linarith [start.2]
    have bounded := compared.trans (mul_le_mul_of_nonneg_right initialBound weight)
    constructor <;> dsimp only <;> linarith [interior.1]
  cases leftBit <;> cases rightBit
  · exact high (fun t ht => Or.inl (stable t ht).1)
  · exact high (fun t ht => Or.inl (stable t ht).1)
  · exact high (fun t ht => Or.inr (stable t ht).2)
  · exact low stable

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
