import H0mework.NavierStokes.KineticHorizon.Account

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceTerminalSelection

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

theorem rawKineticAccount_eq : KineticSelectionHorizon.rawKinetic /
    (2 * butterflyGainViscosity.coeff) = 50945 / 68 := by
  change puncturedWholeVorticityKineticMass stackedSeedState /
    (2 * butterflyGainViscosity.coeff) = _
  rw [puncturedWholeVorticityKineticMass_eq_finite_of_supported
    butterflyFirstStackModes (by decide) stackedSeedState
    (butterflyFirstStackPhysicalState_supported (-1))]
  unfold stackedSeedState
  simp (config := { maxSteps := 3000000 })
    [butterflyFirstStackPhysicalState, finiteComplexVorticityState_apply,
      butterflyFirstStackModes, butterflyFirstStackRow, butterflyFirstYFaceModes,
      butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
      butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq, sidebandMinusY_eq,
      sidebandPlusZ_eq, sidebandMinusZ_eq, complexCoordinateAmplitudeSq,
      integerWaveViscousMultiplier, integerWaveNormSq, axisWave, pumpY, pumpZ,
      realRow, realGaussian, GaussianRatVector.toComplex, GaussianRat.toComplex,
      Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals norm_num [Complex.normSq_apply]
  all_goals unfold butterflyGainViscosity
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring

theorem initialBank_lt_753 : butterflyInitialTotalClockBank < 753 := by
  have initialTime : concreteCounterexampleInitial.contact.time.1 < 1 := by
    have rawDuration : wholeRestartDuration stackedPhysicalSeed < 1 := by
      let ceiling := wholeRestartCoefficientCeiling stackedPhysicalSeed
      let slope := sourceOwnedWholeStateBarrierSlope butterflyGainViscosity ceiling
      have slopePos : 0 < slope := sourceOwnedWholeStateBarrierSlope_pos _ _
      have coefficientNonneg := sourceOwnedLocalQuadraticCoefficient_nonneg
        butterflyGainViscosity ceiling
      have slopeOne : (1 : Real) ≤ slope := by
        dsimp only [slope, sourceOwnedWholeStateBarrierSlope]
        exact le_add_of_nonneg_left (mul_nonneg coefficientNonneg (sq_nonneg ceiling))
      unfold wholeRestartDuration sourceOwnedWholeStateDuration
      apply (div_lt_iff₀ (mul_pos (by norm_num) slopePos)).2
      nlinarith
    exact concreteCounterexampleInitial.contact.time.2.2.trans_lt
      (stackedShortDuration_le_full.trans_lt rawDuration)
  have kinetic := KineticSelectionHorizon.contactKinetic_le_exp 0
  have timeNonneg : 0 ≤ elapsedTime concreteCounterexampleInitial 1 := by
    simpa only [elapsedTime_succ, elapsedTime_zero, run_zero, zero_add]
      using concreteCounterexampleInitial.contact.time_pos.le
  have expLe : Real.exp (-KineticSelectionHorizon.decayRate *
      elapsedTime concreteCounterexampleInitial 1) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr KineticSelectionHorizon.decayRate_pos.le) timeNonneg)
  have currentLe : KineticSelectionHorizon.contactKinetic 0 ≤ KineticSelectionHorizon.rawKinetic := by
    have scaled := mul_le_mul_of_nonneg_left expLe KineticSelectionHorizon.rawKinetic_nonneg
    nlinarith only [kinetic, scaled]
  have accountLe : physicalKineticAccount 0 ≤ 50945 / 68 := by
    rw [← rawKineticAccount_eq]
    exact (div_le_div_iff_of_pos_right (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos)).mpr currentLe
  have initialEq : butterflyInitialTotalClockBank =
      concreteCounterexampleInitial.contact.time.1 + (physicalKineticAccount 0 + 2) := by
    unfold butterflyInitialTotalClockBank
    change _ + (min (wholeVorticityEuclideanMass stackedShortCurrent.contact.physicalState) 2 +
      physicalKineticAccount 0 + 0) = _
    rw [min_eq_right stackedShortCurrent_contact_wholeMass_gt_two.le]
    ring
  rw [initialEq]
  linarith

end
end SaturationMonoid.NavierStokes.SourceTerminalSelection
