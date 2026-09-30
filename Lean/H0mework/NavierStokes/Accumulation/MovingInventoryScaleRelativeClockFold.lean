import H0mework.NavierStokes.Accumulation.ScaleRelativeClockFold
import H0mework.NavierStokes.Accumulation.TemporalEnstrophyLedger

/-!
# Moving-inventory scale-relative clock fold

The actual contact at stage `n` is the initial state of the stage `n + 1`
receipt.  Therefore the finite mass carried by `modes (n + 1)` at that
boundary lies below `restartCoefficientCeiling n`, while the next moving
inventory edge payment is exactly its successor difference.  This file folds
that commuting square into the variable-exponent clock consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMovingInventoryScaleRelativeClockFold

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartScaleRelativeClockFold

noncomputable section

/-- Positive finite-inventory mass at the contact boundary which generates
the next barrier/clock edge. -/
def shiftedMovingInventoryMassBase
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (index : Nat) : Real :=
  finiteStateVorticityCoefficientEnstrophy (modes (index + 1))
      (run initial (index + 1)).initialState + 1

theorem shiftedMovingInventoryMassBase_pos
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (index : Nat) :
    0 < shiftedMovingInventoryMassBase initial modes index := by
  unfold shiftedMovingInventoryMassBase
  have finiteNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy (modes (index + 1))
        (run initial (index + 1)).initialState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg _
  linarith

/-- The shifted finite material row is a projection of the exact contact
mass used by the restart ceiling. -/
theorem shiftedMovingInventoryMassBase_le_ceiling
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (index : Nat) :
    shiftedMovingInventoryMassBase initial modes index ≤
      restartCoefficientCeiling initial index := by
  unfold shiftedMovingInventoryMassBase
  rw [run_succ_initialState]
  have finiteLeWhole :=
    finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      (modes (index + 1)) (run initial index).contact.physicalState
  unfold restartCoefficientCeiling wholeRestartCoefficientCeiling
    wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
  simpa only [add_comm] using
    (add_le_add_left finiteLeWhole 1).trans (Nat.le_ceil _)

/-- The shifted base difference is literally the next actual moving
inventory payment.  Tail transport and newly captured modes are already
included by the ledger theorem. -/
theorem shiftedMovingInventoryMassBase_sub_eq_edgePayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (index : Nat) :
    shiftedMovingInventoryMassBase initial modes (index + 1) -
        shiftedMovingInventoryMassBase initial modes index =
      runMovingInventoryEdgePayment initial modes (index + 1) := by
  rw [runMovingInventoryEdgePayment_eq_nextFiniteMass_sub_current
    initial modes zeroNotMem (index + 1)]
  unfold shiftedMovingInventoryMassBase
  ring

/-- Complete moving-material consumer.  The source supplies only the local
same-edge payment law on its recursively generated inventory.  Scale growth,
reciprocal-barrier summability and the full contact clock are conclusions. -/
theorem contactTime_summable_of_movingInventoryScaleRelativePayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (exponentLtSeven : exponent < 7)
    (chargePos : 0 < charge)
    (payment : ∀ index : Nat,
      charge /
          shiftedMovingInventoryMassBase initial modes index ^
            (exponent - 1) ≤
        runMovingInventoryEdgePayment initial modes (index + 1)) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  have baseDebit : ∀ index : Nat,
      charge /
          shiftedMovingInventoryMassBase initial modes index ^
            (exponent - 1) ≤
        shiftedMovingInventoryMassBase initial modes (index + 1) -
          shiftedMovingInventoryMassBase initial modes index := by
    intro index
    rw [shiftedMovingInventoryMassBase_sub_eq_edgePayment
      initial modes zeroNotMem index]
    exact payment index
  obtain ⟨amplitude, amplitudePos, growth⟩ :=
    scaled_inverseExponent_scale_growth_of_baseDebit
      initial (shiftedMovingInventoryMassBase initial modes)
      exponent charge oneLtExponent chargePos
      (shiftedMovingInventoryMassBase_pos initial modes)
      (shiftedMovingInventoryMassBase_le_ceiling initial modes)
      baseDebit
  apply (summable_contactTime_iff_reciprocalBarrier initial).2
  exact summable_reciprocalBarrier_of_scaled_inverseExponent_growth
    initial exponent amplitude (lt_trans (by norm_num) oneLtExponent)
      exponentLtSeven amplitudePos growth

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMovingInventoryScaleRelativeClockFold
end NavierStokes
end SaturationMonoid
