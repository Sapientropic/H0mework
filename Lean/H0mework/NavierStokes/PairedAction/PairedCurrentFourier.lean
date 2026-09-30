import H0mework.NavierStokes.SourceAction.PhysicalHistoryCurrent

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativePairedCurrentFourier

open Set MeasureTheory UnitAddTorus
open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction DiracCliffordRepresentation
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativePhysicalFourier NativeStressSource

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def value (velocity : PhysicalSpace) (direction : Fin 4) : ℝ :=
  (NativeCanonicalFluidCoframe.dual velocity
    (diracMatrixMatterAction (diracGamma direction) (NativeCanonicalFluidCoframe.matter velocity))).re

theorem value_spatial (velocity : PhysicalSpace) (direction : Fin 3) : value velocity direction.succ = velocity direction :=
  Stage9CU.Fluid.InitialLift.spatialCurrent_eq velocity direction

theorem value_temporal (velocity : PhysicalSpace) : value velocity 0 = 2 + ‖velocity‖ ^ 2 / 8 := by
  rw [value, NativeCanonicalFluidCoframe.dual, NativeCanonicalFluidCoframe.matter,
    Stage9CU.Fluid.InitialLift.temporalCurrent_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

def field (velocity : ComplexVorticityHilbertState) (direction : Fin 4) (point : Torus) : ℝ :=
  value (realField velocity point) direction

def baseline (wave : IntegerWavevector) : ℂ := mFourierCoeff (fun _ : Torus => (2 : ℂ)) wave

def trace (stress : NativeFluidStressFourierState) (wave : IntegerWavevector) : ℂ :=
  ∑ direction : Coordinate, stress wave direction direction

def coefficient (velocity : NativeFluidVorticityTangent) (stress : NativeFluidStressFourierState)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  Fin.cases (baseline wave - trace stress wave / 8) (fun spatial => velocity wave spatial) direction

private theorem monomial_norm (wave : IntegerWavevector) (point : Torus) : ‖mFourier wave point‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe, Finset.prod_const_one]

private theorem modulated_integrable {field : Torus → ℂ} (integrable : Integrable field volume) (wave : IntegerWavevector) :
    Integrable (fun point => mFourier (-wave) point * field point) volume :=
  integrable.bdd_mul (mFourier (-wave)).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun point => (monomial_norm _ point).le)

theorem temporal_expression (velocity : ComplexVorticityHilbertState) :
    (fun point => (field velocity 0 point : ℂ)) = fun point => (2 : ℂ) -
      (∑ direction : Coordinate, ((-(realField velocity point direction * realField velocity point direction) : ℝ) : ℂ)) / 8 := by
  funext point
  rw [field, value_temporal, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

theorem temporal_fourier (velocity : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality velocity)
    (wave : IntegerWavevector) :
    mFourierCoeff (fun point => (field velocity 0 point : ℂ)) wave = baseline wave - trace (quadraticFlux velocity) wave / 8 := by
  have paid (direction : Coordinate) : Integrable (fun point : Torus =>
      mFourier (-wave) point * ((-(realField velocity point direction * realField velocity point direction) : ℝ) : ℂ)) volume :=
    modulated_integrable (real_product_integrable velocity direction direction).ofReal wave
  have sumPaid : Integrable (fun point : Torus => ∑ direction : Coordinate,
      mFourier (-wave) point * ((-(realField velocity point direction * realField velocity point direction) : ℝ) : ℂ)) volume :=
    integrable_finsetSum _ (fun direction _ => paid direction)
  rw [temporal_expression]
  simp only [mFourierCoeff, smul_eq_mul, mul_sub, ← mul_div_assoc, Finset.mul_sum]
  rw [integral_sub (modulated_integrable (integrable_const (2 : ℂ)) wave) (sumPaid.div_const 8),
    integral_div, integral_finsetSum _ (fun direction _ => paid direction)]
  change baseline wave - (∑ direction : Coordinate,
    mFourierCoeff (fun point : Torus => ((-(realField velocity point direction * realField velocity point direction) : ℝ) : ℂ)) wave) / 8 = _
  simp only [real_flux_fourier velocity reality]
  rfl

theorem spatial_fourier (velocity : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality velocity)
    (direction : Fin 3) (wave : IntegerWavevector) :
    mFourierCoeff (fun point => (field velocity direction.succ point : ℂ)) wave = velocity wave direction := by
  simp only [field, value_spatial]
  exact realField_fourier velocity reality direction wave

theorem current_fourier (velocity : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality velocity)
    (direction : Fin 4) (wave : IntegerWavevector) :
    mFourierCoeff (fun point => (field velocity direction point : ℂ)) wave =
      coefficient velocity (quadraticFlux velocity) direction wave := by
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · exact temporal_fourier velocity reality wave
  · exact spatial_fourier velocity reality spatial wave

theorem baseline_zero : baseline 0 = 2 := by
  simp [baseline, mFourierCoeff, mFourier_zero]

theorem field_ae_continuous (velocity : ComplexVorticityHilbertState)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) (direction : Fin 4) :
    field velocity direction =ᵐ[volume] fun point => value (NativePhysicalContinuous.continuousField velocity point) direction := by
  filter_upwards [NativePhysicalContinuous.continuousField_ae velocity paid] with point same
  exact congrArg (fun velocity : PhysicalSpace => value velocity direction) same

end
end SaturationMonoid.NavierStokes.NativePairedCurrentFourier
