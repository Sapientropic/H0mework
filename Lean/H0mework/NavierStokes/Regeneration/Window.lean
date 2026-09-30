import H0mework.NavierStokes.ClockAccount.FullLowMassBranch
import H0mework.NavierStokes.ClockAccount.DensityAccount

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceDensityRegeneration

open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

theorem next_mass_le_current_add_epsilon (stage : Nat) :
    wholeVorticityEuclideanMass (run stackedShortCurrent (stage + 1)).contact.physicalState ≤
      wholeVorticityEuclideanMass (run stackedShortCurrent stage).contact.physicalState +
        WindowMassCoefficient.epsilon := by
  have signed := wholeRestartPrefixTangentSquare_add_massBoundary_le_cubicAction stackedShortCurrent stage
  have cubic := wholeRestartPrefixCubicAction_le_fourthPower stackedShortCurrent stage
  have ceilingOne : 1 ≤ wholeRestartCoefficientCeiling (run stackedShortCurrent stage).contact := by
    have levelPos : 0 < wholeRestartCoefficientLevel (run stackedShortCurrent stage).contact := by
      have positive := wholeRestartCoefficientCeiling_pos (run stackedShortCurrent stage).contact
      unfold wholeRestartCoefficientCeiling at positive
      exact_mod_cast positive
    unfold wholeRestartCoefficientCeiling
    exact_mod_cast Nat.succ_le_iff.mpr levelPos
  have bound := cubic.trans (div_le_self (wholeRestartCubicFourthCoefficient_nonneg butterflyGainViscosity)
    (one_le_pow₀ ceilingOne))
  have boundary : butterflyGainViscosity.coeff *
      (wholeVorticityEuclideanMass (run stackedShortCurrent (stage + 1)).contact.physicalState -
        wholeVorticityEuclideanMass (run stackedShortCurrent stage).contact.physicalState) ≤
      wholeRestartCubicFourthCoefficient butterflyGainViscosity := by
    linarith [wholeRestartPrefixTangentSquare_nonneg stackedShortCurrent stage]
  have growth : wholeVorticityEuclideanMass (run stackedShortCurrent (stage + 1)).contact.physicalState -
      wholeVorticityEuclideanMass (run stackedShortCurrent stage).contact.physicalState ≤
        WindowMassCoefficient.epsilon := by
    apply (le_div_iff₀ butterflyGainViscosity.coeff_pos).mpr
    nlinarith [boundary]
  linarith

theorem window_density_nonneg_of_high (stage : Nat)
    (high : 1 + WindowMassCoefficient.epsilon ≤ wholeVorticityEuclideanMass
      (run stackedShortCurrent (stage + 1)).contact.physicalState) :
    0 ≤ physicalPrefixMass stage - source.clockAt (source.stateAfter stage) := by
  have rectangle := LowMassBranch.nextContact_terminalMass_rectangle (run stackedShortCurrent stage)
  have clock : source.clockAt (source.stateAfter stage) =
      (run stackedShortCurrent stage).nextContact.time.1 := by
    change (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [physicalCurrent_eq_run]
  rw [clock]
  change 1 + WindowMassCoefficient.epsilon ≤ wholeVorticityEuclideanMass
    (run stackedShortCurrent stage).nextContact.physicalState at high
  change _ * (_ - WindowMassCoefficient.epsilon) ≤ physicalPrefixMass stage at rectangle
  have density : 1 ≤ wholeVorticityEuclideanMass
      (run stackedShortCurrent stage).nextContact.physicalState - WindowMassCoefficient.epsilon := by
    linarith
  have paid := (mul_le_mul_of_nonneg_left density
    (run stackedShortCurrent stage).nextContact.time_pos.le).trans rectangle
  simpa only [mul_one, sub_nonneg] using paid

end
end SaturationMonoid.NavierStokes.SourceDensityRegeneration
