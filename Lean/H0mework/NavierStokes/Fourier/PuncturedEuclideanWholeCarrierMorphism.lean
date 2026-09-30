import H0mework.NavierStokes.KineticRestart.KineticWeakEndpoint
import H0mework.NavierStokes.Galerkin.AmbientNorm

/-!
# Punctured Euclidean whole-carrier morphism

The complete nonzero-wave Euclideanization is a bounded linear map on the
original whole-vorticity carrier.  This low-level module contains no endpoint
macro or accumulation-root dependency; downstream balance and endpoint
compilers consume the same map.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped ENNReal

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint

noncomputable section

/-- The nonzero-wave Euclideanization as a complex-linear map. -/
def puncturedEuclideanizeLinearMap :
    ComplexVorticityHilbertState →ₗ[ℂ] WholeRestartKineticEndpointState where
  toFun := puncturedEuclideanize
  map_add' := by
    intro left right
    apply lp.ext
    funext wave
    rfl
  map_smul' := by
    intro scalar state
    apply lp.ext
    funext wave
    rfl

/-- Bounded whole-carrier Euclideanization, independent of frequency
support. -/
def puncturedEuclideanizeCLM :
    ComplexVorticityHilbertState →L[ℂ] WholeRestartKineticEndpointState :=
  LinearMap.mkContinuous puncturedEuclideanizeLinearMap 2 (fun state => by
    change ‖puncturedEuclideanize state‖ ≤ 2 * ‖state‖
    have squareLe := puncturedEuclideanize_norm_sq_le state
    nlinarith [norm_nonneg (puncturedEuclideanize state), norm_nonneg state])

/-- Removing the zero row and replacing the ambient three-vector sup norm
by its Euclidean row preserves the complete square mass. -/
theorem state_norm_sq_le_puncturedEuclideanize_of_zero_row
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    ‖state‖ ^ 2 ≤ ‖puncturedEuclideanize state‖ ^ 2 := by
  have stateNormSummable :
      Summable fun wave : IntegerWavevector => ‖state wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      state.2.summable (by norm_num)
  have amplitudeSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        complexCoordinateAmplitudeSq (state wave.1) := by
    simpa only [← euclideanCoordinateRow_norm_sq,
      ENNReal.toReal_ofNat, Real.rpow_two,
      puncturedEuclideanize_apply] using
      (puncturedEuclideanize state).2.summable (by norm_num)
  rw [show
      ‖state‖ ^ 2 =
        ∑' wave : IntegerWavevector, ‖state wave‖ ^ 2 by
    simpa using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num) state),
    puncturedEuclideanize_norm_sq]
  have complementZero :
      (∑' wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector),
        ‖state wave.1‖ ^ 2) = 0 := by
    rw [show
        (fun wave :
            ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
              Set IntegerWavevector) =>
          ‖state wave.1‖ ^ 2) = 0 by
      funext wave
      have waveZero : wave.1 = 0 := by simpa using wave.2
      simp [waveZero, zeroRow]]
    exact tsum_zero
  have split :=
    stateNormSummable.tsum_subtype_add_tsum_subtype_compl
      { wave : IntegerWavevector | wave ≠ 0 }
  rw [← split, complementZero, add_zero]
  exact
    (stateNormSummable.subtype
      { wave : IntegerWavevector | wave ≠ 0 }).tsum_le_tsum
        (fun wave =>
          complexCoordinateVector_norm_sq_le_amplitudeSq
            (state wave.1))
        amplitudeSummable

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
