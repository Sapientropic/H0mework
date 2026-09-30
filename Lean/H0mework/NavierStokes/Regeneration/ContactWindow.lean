import H0mework.NavierStokes.ClockAccount.FullLowMassBranch

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter MeasureTheory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open RationalVorticityEvaluator

noncomputable section

/-- The original source window transports any actual interior mass to its
own selected terminal, paying its already generated cubic remainder. -/
theorem nextContact_mass_le_local_add_epsilon (index : Nat)
    (actual : Icc (0 : Real) (run concreteCounterexampleInitial index).nextContact.time.1) :
    wholeVorticityEuclideanMass (run concreteCounterexampleInitial (index + 1)).contact.physicalState ≤
      wholeVorticityEuclideanMass
        ((run concreteCounterexampleInitial index).nextContact.prefixReceipt.wholePath actual) +
          WindowMassCoefficient.epsilon := by
  let current := run concreteCounterexampleInitial index
  have ceilingPos := wholeRestartCoefficientCeiling_pos current.contact
  have ceilingOne : 1 ≤ wholeRestartCoefficientCeiling current.contact := by
    have levelPos : 0 < wholeRestartCoefficientLevel current.contact := by
      have positive := ceilingPos
      unfold wholeRestartCoefficientCeiling at positive
      exact_mod_cast positive
    unfold wholeRestartCoefficientCeiling
    exact_mod_cast Nat.succ_le_iff.mpr levelPos
  have full := generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
    (generatedWholeRestartCanonicalReplay current.contact)
  have massBound : ∀ᵐ time ∂commonTimeMeasure current.nextContact.time.1,
      wholeVorticityEuclideanMass (current.nextContact.prefixReceipt.wholePath time) ≤
        wholeRestartCoefficientCeiling current.contact := by
    exact (commonTimeInclusion_measurePreserving current.nextContact.time.2.2
      |>.quasiMeasurePreserving.tendsto_ae) (MeasureTheory.ae_restrict_le full)
  have growth := WholeWindowMass.receipt_mass_growth_from_any_time
    current.nextContact.prefixReceipt massBound actual
  rw [current.nextContact.prefixReceipt_terminal] at growth
  have cubic := wholeRestartPrefixCubicAction_le_fourthPower current 0
  change WholeWindowMass.growthCoefficient concreteCounterexampleViscosity *
    (wholeRestartCoefficientCeiling current.contact ^ 3 * current.nextContact.time.1) ≤
      wholeRestartCubicFourthCoefficient concreteCounterexampleViscosity /
        wholeRestartCoefficientCeiling current.contact ^ 4 at cubic
  have fullBound := cubic.trans
    (div_le_self (wholeRestartCubicFourthCoefficient_nonneg _) (one_le_pow₀ ceilingOne))
  have partialBound : WholeWindowMass.growthCoefficient concreteCounterexampleViscosity *
      (wholeRestartCoefficientCeiling current.contact ^ 3 * (current.nextContact.time.1 - actual.1)) ≤
        wholeRestartCubicFourthCoefficient concreteCounterexampleViscosity := by
    apply le_trans _ fullBound
    have coefficientNonneg : 0 ≤ WholeWindowMass.growthCoefficient concreteCounterexampleViscosity := by
      unfold WholeWindowMass.growthCoefficient
      positivity
    gcongr
    exact sub_le_self _ actual.2.1
  have difference : wholeVorticityEuclideanMass current.nextContact.physicalState -
      wholeVorticityEuclideanMass (current.nextContact.prefixReceipt.wholePath actual) ≤
        WindowMassCoefficient.epsilon := by
    apply (le_div_iff₀ butterflyGainViscosity.coeff_pos).mpr
    simpa only [concreteCounterexampleViscosity, mul_comm] using growth.trans partialBound
  change wholeVorticityEuclideanMass current.nextContact.physicalState ≤ _
  linarith

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
