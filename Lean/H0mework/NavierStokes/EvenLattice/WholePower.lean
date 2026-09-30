import H0mework.NavierStokes.EvenLattice.WholeWork
import H0mework.NavierStokes.SourceGeometry.SymmetryPreservation
import H0mework.NavierStokes.NativeWorkWhole.InstantaneousActionCommuting

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting

noncomputable section

theorem whole_netPower_eq_work_sub_viscous (nu : Viscosity) (field : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse field)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (field k)) :
    (∑' k, instantaneousWholeNetPowerRow nu field k) =
      2 * NonlinearWork.value field - 2 * nu.coeff * (2 * Real.pi) ^ 2 * wholeStateVorticityGradientMass field := by
  have row (k : IntegerWavevector) : instantaneousWholeNetPowerRow nu field k =
      2 * complexCoordinateRealInner (field k) (wholeStateVorticityNonlinearCoefficientAt field k) -
        (2 * nu.coeff * (2 * Real.pi) ^ 2) *
          (integerWaveNormSq k * complexCoordinateAmplitudeSq (field k)) := by
    simp only [instantaneousWholeNetPowerRow, complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_self, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      integerWaveViscousMultiplier]
    ring
  simp_rw [row]
  rw [Summable.tsum_sub ((NonlinearWork.summable field transverse gradient).mul_left 2)
    (gradient.mul_left (2 * nu.coeff * (2 * Real.pi) ^ 2)), tsum_mul_left, tsum_mul_left]
  rfl

theorem whole_even_netPower_le (nu : Viscosity) (field : ComplexVorticityHilbertState)
    (zeroRow : field 0 = 0) (transverse : WholeStateTransverse field)
    (reality : FiniteStateFourierReality field) (even : SourceEvenFrequency.OnEvenLattice field)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (field k)) :
    (∑' k, instantaneousWholeNetPowerRow nu field k) ≤
      2 * (Real.sqrt ((63 / 8) * wholeVorticityEuclideanMass field) - nu.coeff * (2 * Real.pi) ^ 2) *
        wholeStateVorticityGradientMass field := by
  have massNonneg : 0 ≤ wholeVorticityEuclideanMass field := tsum_nonneg fun _ => sq_nonneg _
  have gradientNonneg : 0 ≤ wholeStateVorticityGradientMass field :=
    tsum_nonneg fun k => mul_nonneg (integerWaveNormSq_nonneg k) (complexCoordinateAmplitudeSq_nonneg _)
  have bound := whole_even_work_sq_le field zeroRow transverse reality even gradient
  have squared : NonlinearWork.value field ^ 2 ≤
      (Real.sqrt ((63 / 8) * wholeVorticityEuclideanMass field) * wholeStateVorticityGradientMass field) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt (by positivity)]
  have paid := le_of_sq_le_sq squared (mul_nonneg (Real.sqrt_nonneg _) gradientNonneg)
  rw [whole_netPower_eq_work_sub_viscous nu field transverse gradient]
  nlinarith only [paid]

theorem receipt_even_netPower_le_ae {nu : Viscosity} {initial : ComplexVorticityHilbertState} {time : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initial time)
    (initialEven : SourceEvenFrequency.OnEvenLattice initial) :
    ∀ᵐ actual ∂commonTimeMeasure time,
      receiptWholeInstantaneousNetPower receipt actual ≤
        2 * (Real.sqrt ((63 / 8) * wholeVorticityEuclideanMass (receipt.wholePath actual)) -
          nu.coeff * (2 * Real.pi) ^ 2) * wholeStateVorticityGradientMass (receipt.wholePath actual) := by
  filter_upwards [receiptPointwiseGradient_ae_summable receipt, receiptStateLimit_eq_wholePath_ae receipt,
    wholePath_fourierReality_ae receipt] with actual gradient same reality
  rw [same] at gradient
  exact whole_even_netPower_le nu (receipt.wholePath actual) (receipt.wholePath_zero_row actual)
    (wholePath_transverse receipt actual) reality (SourceEvenFrequency.receipt_on_even_lattice receipt initialEven actual) gradient

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
