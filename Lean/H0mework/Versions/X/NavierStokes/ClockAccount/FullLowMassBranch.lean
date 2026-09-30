import H0mework.NavierStokes.ClockAccount.FullWindowMass
import H0mework.Versions.X.NavierStokes.ClockAccount.FullWindowMassCoefficient
import H0mework.Versions.X.NavierStokes.ClockAccount.FullBoundary

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.LowMassBranch

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open RationalVorticityEvaluator
open WholeWindowMass WindowMassCoefficient

noncomputable section

/-- The original chosen prefix inherits the generated whole-path ceiling. -/
private theorem nextPrefixMassBound
    {nu : Viscosity} (current : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time ∂(commonTimeMeasure current.nextContact.time.1),
      wholeVorticityEuclideanMass (current.nextContact.prefixReceipt.wholePath time) ≤
        wholeRestartCoefficientCeiling current.contact := by
  have full := generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
    (generatedWholeRestartCanonicalReplay current.contact)
  change ∀ᵐ time ∂(commonTimeMeasure current.nextContact.time.1),
    wholeVorticityEuclideanMass
      (current.nextReceipt.wholePath (commonTimeInclusion current.nextContact.time.2.2 time)) ≤
        wholeRestartCoefficientCeiling current.contact
  exact (commonTimeInclusion_measurePreserving current.nextContact.time.2.2
    |>.quasiMeasurePreserving.tendsto_ae) (MeasureTheory.ae_restrict_le full)

/-- One actual selected window pays its terminal mass up to the source-fixed
cubic remainder. Neither the contact nor the receipt is replaced. -/
theorem nextContact_terminalMass_rectangle
    {nu : Viscosity} (current : GeneratedWholeRestartCurrent nu) :
    current.nextContact.time.1 *
      (wholeVorticityEuclideanMass current.nextContact.physicalState -
        wholeRestartCubicFourthCoefficient nu / nu.coeff) ≤
      wholePrefixVorticityMass current.nextContact.time current.nextReceipt.stateLimit := by
  have ceilingPos := wholeRestartCoefficientCeiling_pos current.contact
  have ceilingOne : 1 ≤ wholeRestartCoefficientCeiling current.contact := by
    have levelPos : 0 < wholeRestartCoefficientLevel current.contact := by
      have positive := ceilingPos
      unfold wholeRestartCoefficientCeiling at positive
      exact_mod_cast positive
    unfold wholeRestartCoefficientCeiling
    exact_mod_cast Nat.succ_le_iff.mpr levelPos
  have fourthOne : 1 ≤ wholeRestartCoefficientCeiling current.contact ^ 4 := by
    exact one_le_pow₀ ceilingOne
  have cubic := wholeRestartPrefixCubicAction_le_fourthPower current 0
  have cubicBound :
      growthCoefficient nu *
        (wholeRestartCoefficientCeiling current.contact ^ 3 * current.nextContact.time.1) ≤
      wholeRestartCubicFourthCoefficient nu := by
    have bound : growthCoefficient nu *
        (wholeRestartCoefficientCeiling current.contact ^ 3 * current.nextContact.time.1) ≤
      wholeRestartCubicFourthCoefficient nu /
        wholeRestartCoefficientCeiling current.contact ^ 4 := by
      change growthCoefficient nu *
        (wholeRestartCoefficientCeiling current.contact ^ 3 * current.nextContact.time.1) ≤
          wholeRestartCubicFourthCoefficient nu /
            wholeRestartCoefficientCeiling current.contact ^ 4 at cubic
      exact cubic
    exact bound.trans (div_le_self (wholeRestartCubicFourthCoefficient_nonneg nu) fourthOne)
  have errorBound := (div_le_div_iff_of_pos_right nu.coeff_pos).mpr cubicBound
  have rectangle := receipt_terminal_mass_rectangle current.nextContact.prefixReceipt
    ceilingPos.le (nextPrefixMassBound current)
  rw [current.nextContact.prefixReceipt_terminal] at rectangle
  change current.nextContact.time.1 *
      (wholeVorticityEuclideanMass current.nextContact.physicalState -
        growthCoefficient nu *
          (wholeRestartCoefficientCeiling current.contact ^ 3 *
            current.nextContact.time.1) / nu.coeff) ≤
    wholePrefixVorticityMass current.nextContact.time current.nextReceipt.stateLimit
    at rectangle
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left errorBound _)
    current.nextContact.time_pos.le).trans rectangle

/-- An old inquiry with unbounded actual elapsed time generates a finite
half-critical successor contact on that same fixed native run. -/
theorem oldInquiry_generates_halfCritical_contact
    (inquiry : SourceGeneratedBoundaryOldInquiryAt concreteCounterexampleInitial) :
    ∃ stage : Nat, wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState ≤
        halfCriticalMass := by
  by_contra none
  have above : ∀ stage : Nat, halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState := by
    intro stage
    exact lt_of_not_ge fun below => none ⟨stage, below⟩
  have criticalPos : 0 < halfCriticalMass := by
    unfold halfCriticalMass
    exact div_pos (mul_pos (sq_pos_of_pos butterflyGainViscosity.coeff_pos)
      (by positivity)) (mul_pos (by norm_num) criticalEnstrophyLatticeConstant_pos)
  have denominatorPos : 0 < butterflyGainViscosity.coeff * halfCriticalMass :=
    mul_pos butterflyGainViscosity.coeff_pos criticalPos
  have timeBound : ∀ stage : Nat,
      (run concreteCounterexampleInitial stage).nextContact.time.1 ≤
        wholeRestartNextKineticDissipationPayment concreteCounterexampleInitial stage /
          (butterflyGainViscosity.coeff * halfCriticalMass) := by
    intro stage
    let current := run concreteCounterexampleInitial stage
    have rectangle := nextContact_terminalMass_rectangle current
    have terminalHigh : halfCriticalMass <
        wholeVorticityEuclideanMass current.nextContact.physicalState := by
      have generated := above stage
      change halfCriticalMass <
        wholeVorticityEuclideanMass current.nextContact.physicalState at generated
      exact generated
    have errorLe := epsilon_le_halfCriticalMass_half
    change wholeRestartCubicFourthCoefficient concreteCounterexampleViscosity /
      concreteCounterexampleViscosity.coeff ≤ halfCriticalMass / 2 at errorLe
    have density : current.nextContact.time.1 * (halfCriticalMass / 2) ≤
        wholePrefixVorticityMass current.nextContact.time current.nextReceipt.stateLimit := by
      have massLower : halfCriticalMass / 2 ≤
          wholeVorticityEuclideanMass current.nextContact.physicalState -
            wholeRestartCubicFourthCoefficient concreteCounterexampleViscosity /
              concreteCounterexampleViscosity.coeff := by linarith
      exact (mul_le_mul_of_nonneg_left massLower current.nextContact.time_pos.le).trans rectangle
    apply (le_div_iff₀ denominatorPos).mpr
    have scaled := mul_le_mul_of_nonneg_left density
      (mul_nonneg (by norm_num : (0 : Real) ≤ 2) butterflyGainViscosity.coeff_pos.le)
    change current.nextContact.time.1 * (butterflyGainViscosity.coeff * halfCriticalMass) ≤
      2 * butterflyGainViscosity.coeff *
        wholePrefixVorticityMass current.nextContact.time current.nextReceipt.stateLimit
    nlinarith [scaled]
  have majorant := (summable_wholeRestartNextKineticDissipationPayment
    concreteCounterexampleInitial).div_const
      (butterflyGainViscosity.coeff * halfCriticalMass)
  have nextSummable : Summable fun stage =>
      (run concreteCounterexampleInitial stage).nextContact.time.1 :=
    majorant.of_nonneg_of_le
      (fun stage => (run concreteCounterexampleInitial stage).nextContact.time_pos.le) timeBound
  have shifted : Summable fun stage =>
      (run concreteCounterexampleInitial (stage + 1)).contact.time.1 := by
    simpa only [run_succ, next_contact] using nextSummable
  have contactSummable : Summable fun stage =>
      (run concreteCounterexampleInitial stage).contact.time.1 :=
    (summable_nat_add_iff 1).mp shifted
  exact inquiry.elapsedUnbounded
    (contactTime_summable_forces_elapsedTime_bddAbove
      concreteCounterexampleInitial contactSummable)

end
end SaturationMonoid.NavierStokes.LowMassBranch
