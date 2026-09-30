import H0mework.NavierStokes.MaterialGauge.Variation

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeGaugeFlux

open MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction NativeGaugeMomentum NativeStressCurlAlgebra

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def stress (velocity : PhysicalSpace) (output input : Fin 3) : ℝ :=
  current velocity (momentumVariation velocity input.succ output)

theorem stress_eq (velocity : PhysicalSpace) (output input : Fin 3) :
    stress velocity output input = -(velocity output * velocity input) +
      isotropicTerm velocity * (if output = input then 1 else 0) := by
  rw [stress, momentum_spatial]
  by_cases same : output = input
  · subst input
    simp
  · simp [same, Ne.symm same]
    ring

theorem isotropic_integrable (value : PhysicalField) : Integrable (fun point : Torus => isotropicTerm (value point)) volume :=
  ((Lp.memLp value).norm.integrable_sq.div_const 2).sub (integrable_const 8)

theorem stress_integrable (value : PhysicalField) (output input : Fin 3) :
    Integrable (fun point : Torus => stress (value point) output input) volume := by
  simp_rw [stress_eq]
  have each := memLp_piLp_iff.mp (Lp.memLp value)
  exact (memLp_one_iff_integrable.mp ((each input).mul' (each output))).neg.add
    ((isotropic_integrable value).mul_const _)

private theorem weighted_integrable {value : Torus → ℂ} (integrable : Integrable value volume) (wave : IntegerWavevector) :
    Integrable (fun point => mFourier (-wave) point * value point) volume :=
  integrable.bdd_mul (mFourier (-wave)).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun point => by
      simpa only [mFourier_norm] using (mFourier (-wave)).norm_coe_le_norm point)

def isotropicFourier (value : PhysicalField) (wave : IntegerWavevector) : ℂ :=
  mFourierCoeff (fun point => (isotropicTerm (value point) : ℂ)) wave

def fourier (value : PhysicalField) : NativeFluidStressFourierState :=
  fun wave output input => mFourierCoeff (fun point => (stress (value point) output input : ℂ)) wave

theorem fourier_split (state : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality state)
    (wave : IntegerWavevector) (output input : Fin 3) :
    fourier (realField state) wave output input = NativeStressSource.quadraticFlux state wave output input +
      if output = input then isotropicFourier (realField state) wave else 0 := by
  simp only [fourier, stress_eq]
  have flux : mFourierCoeff (fun point => ((-(realField state point output * realField state point input) : ℝ) : ℂ)) wave =
      NativeStressSource.quadraticFlux state wave output input := by
    simpa only [mul_comm] using real_flux_fourier state reality output input wave
  by_cases same : output = input
  · subst output
    simp only [if_true, mul_one, Complex.ofReal_add]
    have addition : mFourierCoeff
        (fun point => ((-(realField state point input * realField state point input) : ℝ) : ℂ) +
          (isotropicTerm (realField state point) : ℂ)) wave =
        mFourierCoeff (fun point => ((-(realField state point input * realField state point input) : ℝ) : ℂ)) wave +
          isotropicFourier (realField state) wave := by
      simp only [mFourierCoeff, smul_eq_mul, mul_add, isotropicFourier]
      exact integral_add (weighted_integrable (real_product_integrable state input input).ofReal wave)
        (weighted_integrable (isotropic_integrable (realField state)).ofReal wave)
    exact addition.trans (by rw [flux])
  · simp only [same, if_false, mul_zero, add_zero]
    exact flux

theorem fourier_action (state : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality state) :
    nativeFluidConstitutiveVorticityAction (fourier (realField state)) =
      nativeFluidConstitutiveVorticityAction (NativeStressSource.quadraticFlux state) := by
  have split : fourier (realField state) = NativeStressSource.quadraticFlux state +
      (fun wave output input => if output = input then isotropicFourier (realField state) wave else 0) := by
    funext wave output input
    exact fourier_split state reality wave output input
  rw [split, ← wholeStressActionCLM_apply, map_add, wholeStressActionCLM_apply,
    wholeStressActionCLM_apply, NativeConstitutiveFourier.isotropic_action_zero, add_zero]

/-- The original gauge matter-current channel supplies the exact full-frequency vorticity nonlinearity. -/
theorem source_action (state : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality state)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    nativeFluidConstitutiveVorticityAction (fourier (realField (wholeBiotSavartVelocityState state))) wave =
      wholeStateVorticityNonlinearCoefficientAt state wave := by
  rw [fourier_action _ (velocity_reality state reality)]
  exact NativeStressSource.quadraticFlux_biotSavart_action state zero transverse wave

end
end SaturationMonoid.NavierStokes.NativeGaugeFlux
