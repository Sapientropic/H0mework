import H0mework.NavierStokes.Regeneration.SourceBounds
import H0mework.NavierStokes.KineticRestart.ExactKineticDissipation

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter MeasureTheory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedKineticAdvance

noncomputable section

theorem rawWindow_duration_lt_thousandth : wholeRestartDuration stackedPhysicalSeed < 1 / 1000 := by
  have barrier := sourceOwnedWholeStateBarrierSeventh_le butterflyGainViscosity 88 (by norm_num)
  rw [butterflyGainSeventhCoefficient_eq] at barrier
  unfold wholeRestartDuration sourceOwnedWholeStateDuration
  rw [stackedPhysicalSeed_ceiling_eq_eighty_eight]
  apply (div_lt_iff₀ (mul_pos (by norm_num)
    (sourceOwnedWholeStateBarrierSlope_pos butterflyGainViscosity 88))).mpr
  norm_num at barrier
  linarith

theorem firstPrefixMass_lt_tenth :
    wholePrefixVorticityMass stackedShortContactFullTime stackedReceipt.stateLimit < 1 / 10 := by
  let prefixReceipt := restrictWholeContinuousMildSerrinReceipt
    stackedShortContact.time_pos stackedShortContactFullTime.2.2 stackedReceipt
  have full := generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le stackedReplay
  rw [stackedPhysicalSeed_ceiling_eq_eighty_eight] at full
  have massBound : ∀ᵐ actual ∂commonTimeMeasure stackedShortContact.time.1,
      wholeVorticityEuclideanMass (prefixReceipt.wholePath actual) ≤ 88 := by
    exact (commonTimeInclusion_measurePreserving stackedShortContactFullTime.2.2
      |>.quasiMeasurePreserving.tendsto_ae) (MeasureTheory.ae_restrict_le full)
  have stateEq := receiptStateLimit_eq_wholePath_ae prefixReceipt
  have stateBound : ∀ᵐ actual ∂commonTimeMeasure stackedShortContact.time.1,
      wholeVorticityEuclideanMass (prefixReceipt.stateLimit actual) ≤ 88 := by
    filter_upwards [massBound, stateEq] with actual bound same
    rw [same]
    exact bound
  let : IsFiniteMeasure (commonTimeMeasure stackedShortContact.time.1) := by
    unfold commonTimeMeasure
    infer_instance
  have integrated := integral_mono_of_nonneg
    (Eventually.of_forall (fun actual =>
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
        (prefixReceipt.stateLimit actual))) (integrable_const (88 : Real)) stateBound
  have totalTime : (commonTimeMeasure stackedShortContact.time.1).real Set.univ =
      stackedShortContact.time.1 := by
    let terminal : Icc (0 : Real) stackedShortContact.time.1 :=
      ⟨stackedShortContact.time.1, stackedShortContact.time_pos.le, le_rfl⟩
    have generated :=
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation.commonTimeMeasure_Iic_real
        stackedShortContact.time.1 stackedShortContact.time_pos.le terminal
    have terminalIic : Iic terminal = Set.univ := by
      ext actual
      simp only [mem_Iic, mem_univ, iff_true]
      exact actual.2.2
    simpa only [terminalIic, Measure.restrict_univ] using generated
  rw [integral_const, totalTime, smul_eq_mul] at integrated
  have timeSmall : stackedShortContact.time.1 < 1 / 1000 :=
    stackedShortContactFullTime.2.2.trans_lt rawWindow_duration_lt_thousandth
  change wholeSpaceTimeEuclideanMass stackedShortContact.time.1 prefixReceipt.stateLimit < _
  rw [wholeSpaceTimeEuclideanMass_eq_integral]
  linarith

theorem firstContact_kineticAccount_loss_lt_tenth :
    KineticSelectionHorizon.rawKinetic / (2 * butterflyGainViscosity.coeff) -
      physicalKineticAccount 0 < 1 / 10 := by
  have ledger := generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_eq
    stackedReplay stackedShortContactFullTime
  change puncturedWholeVorticityKineticMass (stackedReceipt.wholePath stackedShortContactFullTime) +
    2 * butterflyGainViscosity.coeff * wholePrefixVorticityMass stackedShortContactFullTime stackedReceipt.stateLimit =
      KineticSelectionHorizon.rawKinetic at ledger
  rw [← stackedShortContact_state_eq_full] at ledger
  have denominator : 0 < 2 * butterflyGainViscosity.coeff := mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have divided := congrArg (fun value : Real => value / (2 * butterflyGainViscosity.coeff)) ledger
  rw [add_div, mul_div_cancel_left₀ _ denominator.ne'] at divided
  change physicalKineticAccount 0 + wholePrefixVorticityMass stackedShortContactFullTime stackedReceipt.stateLimit =
    KineticSelectionHorizon.rawKinetic / (2 * butterflyGainViscosity.coeff) at divided
  linarith [firstPrefixMass_lt_tenth]

theorem initialBank_gt_751_05 : (75105 : Real) / 100 < butterflyInitialTotalClockBank := by
  have loss := firstContact_kineticAccount_loss_lt_tenth
  rw [SourceTerminalSelection.rawKineticAccount_eq] at loss
  unfold butterflyInitialTotalClockBank
  change (75105 : Real) / 100 < concreteCounterexampleInitial.contact.time.1 +
    (min (wholeVorticityEuclideanMass stackedShortCurrent.contact.physicalState) 2 + physicalKineticAccount 0 + 0)
  rw [min_eq_right stackedShortCurrent_contact_wholeMass_gt_two.le]
  linarith [concreteCounterexampleInitial.contact.time_pos]

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
