import H0mework.NavierStokes.Regeneration.LowPoint
import H0mework.NavierStokes.Regeneration.ContactWindow

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSerrinActionExhaustion
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

/-- The low physical point is located in its original emitted window and
transported to that window's actual contact using the paid epsilon bound. -/
theorem residual_source_lowContact
    {stage : Nat} {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (shortfall : ButterflyCreditClockFaceResidualAt stage face
      (sourceGeneratedStandingActionRunClockDisposition stackedInitialActionMaterialInstruction stage)) :
    ∃ index ≤ stage, wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (index + 1)).contact.physicalState < 1 / 79000 := by
  obtain ⟨actual, inLastWindow, low⟩ := residual_source_late_lowPoint reachable shortfall
  have late := residual_terminal_gt_750 reachable shortfall
  have actualLate : 700 < actual.1 := by
    change elapsedTime concreteCounterexampleInitial (stage + 2) - 50 ≤ actual.1 at inLastWindow
    linarith
  have actualMem : actual.1 ∈ Ioc (0 : Real) (elapsedTime concreteCounterexampleInitial (stage + 2)) :=
    ⟨by linarith, actual.2.2⟩
  obtain ⟨contactIndex, located, _unique⟩ :=
    wholeRestartPhysicalWindow_existsUnique concreteCounterexampleInitial actualMem
  have indexPositive : 0 < contactIndex := by
    by_contra notPositive
    have zero : contactIndex = 0 := by omega
    have before := located.2.2
    rw [zero] at before
    have firstTime : elapsedTime concreteCounterexampleInitial 1 < 1 / 1000 := by
      rw [elapsedTime_succ, elapsedTime_zero, run_zero, zero_add]
      exact stackedShortContactFullTime.2.2.trans_lt rawWindow_duration_lt_thousandth
    linarith
  obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt indexPositive)
  let current := run concreteCounterexampleInitial index
  have window : actual.1 ∈ Ioc (elapsedTime concreteCounterexampleInitial (index + 1))
      (elapsedTime concreteCounterexampleInitial (index + 1 + 1)) := located.2
  let localTime : Icc (0 : Real) current.nextContact.time.1 :=
    ⟨actual.1 - elapsedTime concreteCounterexampleInitial (index + 1),
      by
        constructor
        · linarith [window.1]
        · have upper := window.2
          rw [elapsedTime_succ] at upper
          change actual.1 ≤ elapsedTime concreteCounterexampleInitial (index + 1) +
            current.nextContact.time.1 at upper
          linarith⟩
  have sourcePath := wholeRestartPrefixPhysicalTrajectory_eq_receipt concreteCounterexampleInitial
    located.1 window
  have same : (WholePrefixReceipt.receipt concreteCounterexampleInitial (stage + 1)).wholePath actual =
      current.nextContact.prefixReceipt.wholePath localTime := by
    rw [WholePrefixReceipt.receipt_path, sourcePath]
    change wholeRestartReceiptPhysicalTrajectory current.nextContact.prefixReceipt localTime.1 = _
    rw [wholeRestartReceiptPhysicalTrajectory, projIcc_of_mem _ localTime.2]
  rw [same] at low
  have terminal := nextContact_mass_le_local_add_epsilon index localTime
  have margin : (1 : Real) / 79500 + WindowMassCoefficient.epsilon < 1 / 79000 := by
    rw [WindowMassCoefficient.epsilon_eq]
    norm_num
  have lowPlus : wholeVorticityEuclideanMass (current.nextContact.prefixReceipt.wholePath localTime) +
      WindowMassCoefficient.epsilon < 1 / 79500 + WindowMassCoefficient.epsilon := by linarith
  exact ⟨index, by omega, (terminal.trans_lt lowPlus).trans margin⟩

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
