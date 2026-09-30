import H0mework.Versions.X.NavierStokes.WholeReceipt.KineticDecay
import H0mework.NavierStokes.VelocityEndpoint.PhysicalRightTrace

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeNormControl

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace

noncomputable section

theorem receipt_velocity_norm_le {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (time : Icc (0 : ℝ) duration) :
    ‖puncturedWholeVelocityEuclideanState (receipt.wholePath time)‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial‖ := by
  have initialTransverse : WholeStateTransverse initial := by
    simpa only [receipt.wholePath_initial] using
      wholePath_transverse receipt ⟨0, le_rfl, receipt.requestedTimePos.le⟩
  have massNonneg := puncturedWholeVorticityKineticMass_nonneg initial
  have exponentNonpos : -2 * nu.coeff * (2 * Real.pi) ^ 2 * time.1 ≤ 0 := by
    have : 0 ≤ 2 * nu.coeff * (2 * Real.pi) ^ 2 * time.1 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) nu.coeff_pos.le) (sq_nonneg _)) time.2.1
    linarith
  have bound := (WholeKineticDecay.kinetic_le_exp receipt time).trans
    (mul_le_of_le_one_right massNonneg (Real.exp_le_one_iff.mpr exponentNonpos))
  rw [← puncturedWholeVelocityEuclideanState_norm_sq _ (wholePath_transverse receipt time),
    ← puncturedWholeVelocityEuclideanState_norm_sq _ initialTransverse] at bound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp bound

theorem contact_velocity_norm_le_initial {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :
    ‖wholeRestartContactVelocityState initial 0‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ := by
  exact receipt_velocity_norm_le initial.receipt initial.contact.time

theorem endpoint_physical_norm_le_initial {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : ℝ) 1) :
    ‖puncturedEuclideanize ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath time)‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ := by
  have bound := velocityEndpointWholeMildState_physical_norm_sq_le_endpoint
    (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).core time
  have first := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp bound
  exact first.trans ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint_norm_le.trans
    (contact_velocity_norm_le_initial initial))

end
end SaturationMonoid.NavierStokes.NativeNormControl
