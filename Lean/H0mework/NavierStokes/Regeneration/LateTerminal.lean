import H0mework.NavierStokes.Regeneration.FirstWindow
import H0mework.NavierStokes.Regeneration.Contact
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
open RationalVorticityEvaluator

noncomputable section

variable {stage : Nat} {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
  (reachable : ButterflyCreditClockFaceReachableAt stage face)
  (shortfall : ButterflyCreditClockFaceResidualAt stage face
    (sourceGeneratedStandingActionRunClockDisposition stackedInitialActionMaterialInstruction stage))

include reachable shortfall

theorem residual_late_terminal_account : butterflyInitialTotalClockBank <
    elapsedTime concreteCounterexampleInitial (stage + 2) + physicalKineticAccount (stage + 1) +
      standingActionBarrierTail butterflyGainViscosity
        (source.stateAfter (stage + 1)).1.standing.anchorLevel := by
  have folded := butterflyReachable_elapsedTime_succ_add_potential_eq_initial reachable
  have failed : face.clockState.potential < source.clockAt (source.stateAfter stage) +
      kineticBarrierPotential (source.stateAfter (stage + 1)) := by
    cases face <;> exact shortfall.completeCreditShortfall
  unfold kineticBarrierPotential at failed
  rw [← physicalKineticAccount_eq_source] at failed
  have clockEq : source.clockAt (source.stateAfter stage) =
      (run concreteCounterexampleInitial (stage + 1)).contact.time.1 := by
    change (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [physicalCurrent_eq_run]
    rfl
  rw [clockEq] at failed
  rw [show stage + 2 = (stage + 1) + 1 by omega, elapsedTime_succ]
  linarith

theorem residual_terminal_kineticAccount_bound :
    physicalKineticAccount (stage + 1) < 50 * (1 + WindowMassCoefficient.epsilon) := by
  have low := SourceDensityRegeneration.residual_generates_terminal_low_density_contact reachable shortfall
  rw [physicalCurrent_eq_run] at low
  let terminal := run concreteCounterexampleInitial (stage + 1)
  have poincare := twoPiSq_mul_kineticEuclideanState_norm_sq_le_wholeMass
    terminal.contact.physicalState terminal.contact.physicalState_zero
  rw [puncturedWholeVorticityKineticEuclideanState_norm_sq] at poincare
  have positive : 0 < 2 * butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 :=
    mul_pos (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos) (by positivity)
  calc
    physicalKineticAccount (stage + 1) =
        ((2 * Real.pi) ^ 2 * puncturedWholeVorticityKineticMass terminal.contact.physicalState) /
          (2 * butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) := by
      unfold physicalKineticAccount terminal
      field_simp
      rfl
    _ < (1 + WindowMassCoefficient.epsilon) /
        (2 * butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) :=
      (div_lt_div_iff_of_pos_right positive).mpr (poincare.trans_lt low)
    _ = 50 * (1 + WindowMassCoefficient.epsilon) := by
      rw [mul_assoc, butterflyGainViscosity_scaled]
      ring

theorem residual_terminal_gt_700 : 700 < elapsedTime concreteCounterexampleInitial (stage + 2) := by
  have late := residual_late_terminal_account reachable shortfall
  have kinetic := residual_terminal_kineticAccount_bound reachable shortfall
  have tail := SourceDensityRegeneration.source_tail_le_one (stage + 1)
  have epsilon : WindowMassCoefficient.epsilon < (1 : Real) / 10000 := by
    rw [WindowMassCoefficient.epsilon_eq]
    norm_num
  linarith [initialBank_gt_751_05]

omit reachable shortfall in
theorem contactKineticAccount_le_exp (index : Nat) : physicalKineticAccount index ≤
    (50945 / 68 : Real) * Real.exp (-elapsedTime concreteCounterexampleInitial (index + 1) / 50) := by
  have decay := KineticSelectionHorizon.contactKinetic_le_exp index
  have scaled := div_le_div_of_nonneg_right decay
    (show 0 ≤ 2 * butterflyGainViscosity.coeff from
      (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos).le)
  have rateEq : KineticSelectionHorizon.decayRate = (1 : Real) / 50 := by
    unfold KineticSelectionHorizon.decayRate
    change 2 * butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 = _
    rw [mul_assoc, butterflyGainViscosity_scaled]
    norm_num
  rw [rateEq] at scaled
  change physicalKineticAccount index ≤ _ at scaled
  convert scaled using 1
  rw [show KineticSelectionHorizon.rawKinetic *
      Real.exp (-(1 / 50 : Real) * elapsedTime concreteCounterexampleInitial (index + 1)) /
      (2 * butterflyGainViscosity.coeff) =
      (KineticSelectionHorizon.rawKinetic / (2 * butterflyGainViscosity.coeff)) *
        Real.exp (-(1 / 50 : Real) * elapsedTime concreteCounterexampleInitial (index + 1)) by ring,
    SourceTerminalSelection.rawKineticAccount_eq]
  congr 2
  ring

theorem residual_terminal_kineticAccount_lt_thousandth :
    physicalKineticAccount (stage + 1) < 1 / 1000 := by
  have late := residual_terminal_gt_700 reachable shortfall
  have decay := contactKineticAccount_le_exp (stage + 1)
  have exponent : -elapsedTime concreteCounterexampleInitial (stage + 2) / 50 < (-14 : Real) := by linarith
  have expBound := Real.exp_lt_exp.mpr exponent
  have expLarge : (750000 : Real) < Real.exp 14 := by
    have one : (27 : Real) / 10 < Real.exp 1 := (by norm_num : (27 : Real) / 10 < 2.7182818283).trans Real.exp_one_gt_d9
    have power := pow_lt_pow_left₀ one (by norm_num : (0 : Real) ≤ 27 / 10) (by norm_num : (14 : Nat) ≠ 0)
    rw [← Real.exp_nat_mul] at power
    norm_num at power
    linarith
  have small : (50945 / 68 : Real) * Real.exp (-14) < 1 / 1000 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos 14)).mpr
    linarith
  exact (decay.trans_lt (mul_lt_mul_of_pos_left expBound (by norm_num))).trans small

theorem residual_terminal_gt_750 : 750 < elapsedTime concreteCounterexampleInitial (stage + 2) := by
  have late := residual_late_terminal_account reachable shortfall
  have kinetic := residual_terminal_kineticAccount_lt_thousandth reachable shortfall
  have tail := SourceDensityRegeneration.source_tail_le_one (stage + 1)
  linarith [initialBank_gt_751_05]

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
