import H0mework.NavierStokes.SourceGeometry.VectorWorkReceiptEnergy
import H0mework.NavierStokes.ReferenceErrorReferenceBarrier.Bootstrap

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting
open WholeKineticDecay

noncomputable section

theorem receipt_mass_le_initial_of_local_nonpos
    {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration threshold : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (initialSmall : wholeVorticityEuclideanMass initial < threshold)
    (localPower : ∀ᵐ actual ∂commonTimeMeasure duration,
      wholeVorticityEuclideanMass (receipt.wholePath actual) ≤ threshold →
        receiptWholeInstantaneousNetPower receipt actual ≤ 0) :
    ∀ actual : Icc (0 : ℝ) duration,
      wholeVorticityEuclideanMass (receipt.wholePath actual) ≤ wholeVorticityEuclideanMass initial := by
  have zeroMass : massField receipt 0 = wholeVorticityEuclideanMass initial := by
    rw [massField_at receipt ⟨0, le_rfl, receipt.requestedTimePos.le⟩, receipt.wholePath_initial]
  have measure : commonTimeMeasure duration =
      Measure.comap (Subtype.val : Icc (0 : ℝ) duration → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  have powerBound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) duration),
      massField receipt t ≤ threshold → netPowerField receipt t ≤
        0 * massField receipt t ^ 3 + 0 * massField receipt t + 0 := by
    rw [ae_restrict_iff_subtype measurableSet_Icc, ← measure]
    filter_upwards [localPower] with actual bound
    simpa only [netPowerField, commonTimeZeroExtension_of_mem duration _ actual.1 actual.2,
      massField_at, zero_mul, add_zero] using bound
  have compared := ReferenceBarrier.cubic_local_power_barrier
    (f := massField receipt) (power := netPowerField receipt) (κ := 0)
    (A := fun _ => 0) (R := fun _ => 0)
    (barrier := fun _ => wholeVorticityEuclideanMass initial) (derivative := fun _ => 0)
    (threshold := threshold)
    (massField_continuous receipt).continuousOn continuousOn_const continuousOn_const
    continuousOn_const (fun t _ => hasDerivAt_const t _)
    (netPowerField_integrable receipt)
    (fun t within => mass_prefix_energy receipt ⟨t, within⟩)
    powerBound zeroMass.le (fun _ _ => initialSmall) (fun _ _ => by simp)
  intro actual
  simpa only [massField_at] using compared actual.1 actual.2

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
