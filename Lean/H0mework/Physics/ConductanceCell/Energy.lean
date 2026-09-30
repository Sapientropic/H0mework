import H0mework.Physics.ConductanceCell.Dynamics

/-!
# Power and stored energy of the same loaded conductance occurrence

The series midpoint solves its literal two-branch current balance. Power uses
the same branch conductances and output voltage as the existing trajectory.
Capacitor energy balance is derived from that trajectory's KCL, not accepted as
a certificate or installed as a separate evolution.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface

noncomputable section
namespace LoadedConductanceCellSource

def seriesMidpoint (source : LoadedConductanceCellSource) (left right output : SIVolt) : SIVolt :=
  ⟨source.nConductance left * output.value /
    (source.nConductance left + source.nConductance right)⟩

def seriesUpperCurrent (source : LoadedConductanceCellSource)
    (left right output : SIVolt) : SIAmpere :=
  ⟨source.nConductance left * (output.value - (source.seriesMidpoint left right output).value)⟩

def seriesLowerCurrent (source : LoadedConductanceCellSource)
    (left right output : SIVolt) : SIAmpere :=
  ⟨source.nConductance right * (source.seriesMidpoint left right output).value⟩

theorem seriesUpperCurrent_eq_pullDown (source : LoadedConductanceCellSource)
    (left right output : SIVolt) :
    (source.seriesUpperCurrent left right output).value =
      source.pullDown left right * output.value := by
  have nonzero := ne_of_gt (add_pos (source.nConductance_pos left) (source.nConductance_pos right))
  change source.nConductance left *
      (output.value - source.nConductance left * output.value /
        (source.nConductance left + source.nConductance right)) =
    source.nConductance left * source.nConductance right /
      (source.nConductance left + source.nConductance right) * output.value
  field_simp
  ring

theorem seriesLowerCurrent_eq_pullDown (source : LoadedConductanceCellSource)
    (left right output : SIVolt) :
    (source.seriesLowerCurrent left right output).value =
      source.pullDown left right * output.value := by
  change source.nConductance right *
      (source.nConductance left * output.value /
        (source.nConductance left + source.nConductance right)) =
    source.nConductance left * source.nConductance right /
      (source.nConductance left + source.nConductance right) * output.value
  ring

theorem seriesMidpoint_kcl (source : LoadedConductanceCellSource) (left right output : SIVolt) :
    source.seriesUpperCurrent left right output = source.seriesLowerCurrent left right output := by
  apply SIQuantity.ext
  rw [source.seriesUpperCurrent_eq_pullDown, source.seriesLowerCurrent_eq_pullDown]

/-- Eliminating the internal node preserves both branch losses, not only current. -/
theorem series_dissipation_eq (source : LoadedConductanceCellSource) (left right output : SIVolt) :
    source.nConductance left * (output.value - (source.seriesMidpoint left right output).value) ^ 2 +
      source.nConductance right * (source.seriesMidpoint left right output).value ^ 2 =
        source.pullDown left right * output.value ^ 2 := by
  have nonzero := ne_of_gt (add_pos (source.nConductance_pos left) (source.nConductance_pos right))
  dsimp only [seriesMidpoint, pullDown]
  field_simp
  ring

def supplyPower (source : LoadedConductanceCellSource) (left right output : SIVolt) : SIWatt :=
  ⟨source.pullUp left right * source.supply.value * (source.supply.value - output.value)⟩

def dissipatedPower (source : LoadedConductanceCellSource) (left right output : SIVolt) : SIWatt :=
  ⟨source.pullUp left right * (source.supply.value - output.value) ^ 2 +
    source.pullDown left right * output.value ^ 2⟩

theorem dissipatedPower_nonneg (source : LoadedConductanceCellSource)
    (left right output : SIVolt) : 0 ≤ (source.dissipatedPower left right output).value :=
  add_nonneg (mul_nonneg (source.pullUp_pos left right).le (sq_nonneg _))
    (mul_nonneg (source.pullDown_pos left right).le (sq_nonneg _))

def storedEnergyAt (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (time : ℝ) : SIJoule :=
  ⟨source.capacitance.value / 2 * source.voltageAt left right initial time ^ 2⟩

theorem storedEnergyAt_nonneg (source : LoadedConductanceCellSource)
    (left right initial : SIVolt) (time : ℝ) :
    0 ≤ (source.storedEnergyAt left right initial time).value :=
  mul_nonneg (div_nonneg source.capacitance_pos.le (by norm_num)) (sq_nonneg _)

/-- The actual KCL trajectory generates capacitor energy change, supply work and heat together. -/
theorem storedEnergyAt_power_balance (source : LoadedConductanceCellSource)
    (left right initial : SIVolt) (time : ℝ) :
    HasDerivAt (fun t => (source.storedEnergyAt left right initial t).value)
      ((source.supplyPower left right ⟨source.voltageAt left right initial time⟩).value -
        (source.dissipatedPower left right ⟨source.voltageAt left right initial time⟩).value) time := by
  have energyDerivative := ((source.voltageAt_kcl left right initial time).pow 2).const_mul
    (source.capacitance.value / 2)
  have nonzero := ne_of_gt source.capacitance_pos
  convert energyDerivative using 1
  all_goals first | rfl | (
    dsimp [supplyPower, dissipatedPower]
    field_simp
    ring)

end LoadedConductanceCellSource
end

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
