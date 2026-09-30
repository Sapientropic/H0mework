import H0mework.NavierStokes.SourceEstimates.WholeKineticEnergy
import H0mework.NavierStokes.Galerkin.CriticalGronwall
import H0mework.NavierStokes.WholeSpace.WholeSerrinEnstrophyGronwall

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholeKineticDecay

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section

variable {nu : Viscosity} {initialState : ComplexVorticityHilbertState} {time : Real}
  (receipt : WholeContinuousMildSerrinReceipt nu initialState time)

def massField (actual : Real) : Real :=
  wholeVorticityEuclideanMass (receipt.wholePath (projIcc 0 time receipt.requestedTimePos.le actual))

theorem massField_at (actual : Icc (0 : Real) time) : massField receipt actual.1 =
    wholeVorticityEuclideanMass (receipt.wholePath actual) := by
  simp only [massField, projIcc_of_mem _ actual.2]

theorem massField_continuous : Continuous (massField receipt) :=
  (wholeReceiptVorticityMass_continuous receipt).comp continuous_projIcc

/-- The continuous mass of this exact whole receipt generates its kinetic primitive. -/
def kineticPrimitive (actual : Real) : Real :=
  puncturedWholeVorticityKineticMass initialState - 2 * nu.coeff *
    ∫ earlier in (0 : Real)..actual, massField receipt earlier

theorem kineticPrimitive_eq (actual : Icc (0 : Real) time) :
    kineticPrimitive receipt actual.1 = puncturedWholeVorticityKineticMass (receipt.wholePath actual) := by
  have energy := energy_identity receipt actual
  have integrated : (∫ earlier in Iic actual, power receipt earlier ∂commonTimeMeasure time) =
      (-2 * nu.coeff) * ∫ earlier in (0 : Real)..actual.1, massField receipt earlier := by
    calc
      _ = ∫ earlier in Iic actual, (-2 * nu.coeff) * massField receipt earlier.1
          ∂commonTimeMeasure time := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (power_eq_viscous_ae receipt)] with earlier same
        simpa only [massField_at] using same
      _ = (-2 * nu.coeff) * ∫ earlier in Iic actual, massField receipt earlier.1
          ∂commonTimeMeasure time := integral_const_mul _ _
      _ = _ := congrArg ((-2 * nu.coeff) * ·)
        (commonTime_integral_Iic_eq_intervalIntegral time receipt.requestedTimePos.le actual (massField receipt))
  unfold kineticPrimitive
  linarith

theorem kineticPrimitive_hasDerivAt (actual : Real) :
    HasDerivAt (kineticPrimitive receipt) (-2 * nu.coeff * massField receipt actual) actual := by
  have continuous := massField_continuous receipt
  have primitive := intervalIntegral.integral_hasDerivAt_right (continuous.intervalIntegrable 0 actual)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt
  exact ((hasDerivAt_const actual (puncturedWholeVorticityKineticMass initialState)).sub
    (primitive.const_mul (2 * nu.coeff))).congr_deriv (by ring)

theorem poincare (actual : Icc (0 : Real) time) :
    (2 * Real.pi) ^ 2 * puncturedWholeVorticityKineticMass (receipt.wholePath actual) ≤
      wholeVorticityEuclideanMass (receipt.wholePath actual) := by
  simpa only [puncturedWholeVorticityKineticEuclideanState_norm_sq] using
    twoPiSq_mul_kineticEuclideanState_norm_sq_le_wholeMass (receipt.wholePath actual)
      (receipt.wholePath_zero_row actual)

/-- Every actual whole unforced receipt has the source-normalized kinetic exponential decay. -/
theorem kinetic_le_exp (actual : Icc (0 : Real) time) :
    puncturedWholeVorticityKineticMass (receipt.wholePath actual) ≤
      puncturedWholeVorticityKineticMass initialState *
        Real.exp (-2 * nu.coeff * (2 * Real.pi) ^ 2 * actual.1) := by
  have bounded := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := kineticPrimitive receipt) (f' := fun t => -2 * nu.coeff * massField receipt t)
    (coefficient := fun _ => -2 * nu.coeff * (2 * Real.pi) ^ 2) (a := 0) (b := time)
    (fun t _ => kineticPrimitive_hasDerivAt receipt t) continuous_const.continuousOn
    (fun t within => by
      rw [kineticPrimitive_eq receipt ⟨t, within⟩, massField_at receipt ⟨t, within⟩]
      have paid := mul_le_mul_of_nonneg_left (poincare receipt ⟨t, within⟩) nu.coeff_pos.le
      nlinarith)
  have result := bounded actual.1 actual.2
  rw [kineticPrimitive_eq receipt actual] at result
  simpa only [kineticPrimitive, intervalIntegral.integral_same, mul_zero, zero_mul, sub_zero,
    intervalIntegral.integral_const, smul_eq_mul, mul_comm] using result

end
end SaturationMonoid.NavierStokes.WholeKineticDecay
