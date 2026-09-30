import H0mework.NavierStokes.EvenLattice.WholePower
import H0mework.NavierStokes.SourceGeometry.SymmetrySource

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open RationalVorticityEvaluator

noncomputable section

theorem receipt_even_netPower_nonpos_below_ae {initial : ComplexVorticityHilbertState} {time : Real}
    (receipt : WholeContinuousMildSerrinReceipt butterflyGainViscosity initial time)
    (initialEven : SourceEvenFrequency.OnEvenLattice initial) :
    ∀ᵐ actual ∂commonTimeMeasure time,
      wholeVorticityEuclideanMass (receipt.wholePath actual) ≤ 8 / 630000 →
        receiptWholeInstantaneousNetPower receipt actual ≤ 0 := by
  filter_upwards [receipt_even_netPower_le_ae receipt initialEven] with actual bound
  intro small
  have root : Real.sqrt ((63 / 8) * wholeVorticityEuclideanMass (receipt.wholePath actual)) ≤ 1 / 100 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith
  rw [butterflyGainViscosity_scaled] at bound
  have gradientNonneg : 0 ≤ wholeStateVorticityGradientMass (receipt.wholePath actual) :=
    tsum_nonneg fun k => mul_nonneg (integerWaveNormSq_nonneg k) (complexCoordinateAmplitudeSq_nonneg _)
  exact bound.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) gradientNonneg)

theorem source_nextReceipt_netPower_nonpos_below_ae (stage : Nat) :
    ∀ᵐ actual ∂commonTimeMeasure (wholeRestartDuration (run concreteCounterexampleInitial stage).contact),
      wholeVorticityEuclideanMass ((run concreteCounterexampleInitial stage).nextReceipt.wholePath actual) ≤ 8 / 630000 →
        receiptWholeInstantaneousNetPower (run concreteCounterexampleInitial stage).nextReceipt actual ≤ 0 :=
  receipt_even_netPower_nonpos_below_ae _ (SourceEvenFrequency.source_contact_even stage)

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
