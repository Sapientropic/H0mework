import H0mework.Versions.X.NavierStokes.ConstitutiveAction.Jet

set_option autoImplicit false
open scoped Matrix BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeConstitutiveFourier

open MeasureTheory Set UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativePhysicalTimeAction NativePhysicalSource
open NativeConstitutiveFlux NativeCartanConstitutive NativePauliCoframeAction NativeStressCurlAlgebra

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem pressure_continuous : Continuous isotropicPressure := by
  have square : Continuous (fun velocity : PhysicalSpace => squared (normalizedVelocity velocity)) := by
    unfold squared normalizedVelocity
    apply continuous_finsetSum
    intro direction _
    exact ((EuclideanSpace.proj direction).continuous.div_const 4).pow 2
  unfold isotropicPressure
  apply Continuous.div <;> try fun_prop
  intro velocity
  have nonnegative : 0 ≤ squared (normalizedVelocity velocity) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

theorem pressure_integrable (field : PhysicalField) :
    Integrable (fun point : Torus => isotropicPressure (field point)) volume := by
  apply ((Lp.memLp field).norm.integrable_sq.div_const 3).mono'
    (pressure_continuous.comp_aestronglyMeasurable (Lp.memLp field).1)
  exact Filter.Eventually.of_forall fun point => by
    rw [Real.norm_eq_abs, abs_of_nonneg (isotropicPressure_nonnegative _)]
    exact isotropicPressure_le _

theorem pressure_mass (field : PhysicalField) :
    (∫ point : Torus, ‖isotropicPressure (field point)‖) ≤ ‖field‖ ^ 2 / 3 := by
  calc
    _ ≤ ∫ point : Torus, ‖field point‖ ^ 2 / 3 :=
      integral_mono (pressure_integrable field).norm ((Lp.memLp field).norm.integrable_sq.div_const 3)
        (fun point => by
          rw [Real.norm_eq_abs, abs_of_nonneg (isotropicPressure_nonnegative _)]
          exact isotropicPressure_le _)
    _ = _ := by
      rw [integral_div, ← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]

theorem stress_integrable (field : PhysicalField) (output input : Fin 3) :
    Integrable (fun point : Torus => stress (field point) (Matrix.single output.succ input.succ 1)) volume := by
  simp_rw [NativeConstitutiveFlux.stress_spatial]
  have each := memLp_piLp_iff.mp (Lp.memLp field)
  exact (memLp_one_iff_integrable.mp ((each input).mul' (each output))).neg.add
    ((pressure_integrable field).mul_const _)

private theorem monomial_norm (wave : Fin 3 → ℤ) (point : Torus) : ‖mFourier wave point‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe, Finset.prod_const_one]

private theorem modulated_integrable {field : Torus → ℂ} (integrable : Integrable field volume) (wave : Fin 3 → ℤ) :
    Integrable (fun point => mFourier (-wave) point * field point) volume :=
  integrable.bdd_mul (mFourier (-wave)).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun point => (monomial_norm _ point).le)

private theorem fourier_add {first second : Torus → ℂ}
    (firstIntegrable : Integrable first volume) (secondIntegrable : Integrable second volume) (wave : Fin 3 → ℤ) :
    mFourierCoeff (fun point => first point + second point) wave =
      mFourierCoeff first wave + mFourierCoeff second wave := by
  simp only [mFourierCoeff, smul_eq_mul, mul_add]
  exact integral_add (modulated_integrable firstIntegrable wave) (modulated_integrable secondIntegrable wave)

def pressureFourier (field : PhysicalField) (wave : IntegerWavevector) : ℂ :=
  mFourierCoeff (fun point => (isotropicPressure (field point) : ℂ)) wave

def fourier (field : PhysicalField) : NativeFluidStressFourierState :=
  fun wave output input => mFourierCoeff
    (fun point => (stress (field point) (Matrix.single output.succ input.succ 1) : ℂ)) wave

theorem fourier_split (velocity : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality velocity)
    (wave : IntegerWavevector) (output input : Fin 3) :
    fourier (realField velocity) wave output input = NativeStressSource.quadraticFlux velocity wave output input +
      if output = input then pressureFourier (realField velocity) wave else 0 := by
  simp only [fourier, NativeConstitutiveFlux.stress_spatial]
  have flux : mFourierCoeff (fun point => ((-(realField velocity point output * realField velocity point input) : ℝ) : ℂ)) wave =
      NativeStressSource.quadraticFlux velocity wave output input := by
    simpa only [mul_comm] using real_flux_fourier velocity reality output input wave
  by_cases same : output = input
  · subst output
    simp only [if_true, mul_one, Complex.ofReal_add]
    have addition := fourier_add (real_product_integrable velocity input input).ofReal
      (pressure_integrable (realField velocity)).ofReal wave
    convert addition.trans (congrArg (fun value => value + pressureFourier (realField velocity) wave) flux) using 1
    rfl
  · simp only [same, if_false, mul_zero, add_zero]
    exact flux

theorem pressureFourier_bound (field : PhysicalField) (wave : IntegerWavevector) :
    ‖pressureFourier field wave‖ ≤ ‖field‖ ^ 2 / 3 := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ point : Torus, ‖mFourier (-wave) point • (isotropicPressure (field point) : ℂ)‖) =
        ∫ point : Torus, ‖isotropicPressure (field point)‖ := by
      congr 1
      funext point
      simp only [norm_smul, monomial_norm, one_mul, Complex.norm_real]
    _ ≤ _ := pressure_mass field

theorem isotropic_action_zero (pressure : IntegerWavevector → ℂ) :
    nativeFluidConstitutiveVorticityAction (fun wave output input => if output = input then pressure wave else 0) = 0 := by
  funext wave coordinate
  fin_cases coordinate <;>
    simp [nativeFluidConstitutiveVorticityAction, nativeFluidStressDivergenceCoefficient,
      fourierCurlCoefficient, cross_apply] <;> ring

theorem fourier_action (velocity : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality velocity) :
    nativeFluidConstitutiveVorticityAction (fourier (realField velocity)) =
      nativeFluidConstitutiveVorticityAction (NativeStressSource.quadraticFlux velocity) := by
  have split : fourier (realField velocity) = NativeStressSource.quadraticFlux velocity +
      (fun wave output input => if output = input then pressureFourier (realField velocity) wave else 0) := by
    funext wave output input
    exact fourier_split velocity reality wave output input
  rw [split, ← wholeStressActionCLM_apply, map_add, wholeStressActionCLM_apply,
    wholeStressActionCLM_apply, isotropic_action_zero, add_zero]

/-- The source mother constitutive action is exactly the original full-frequency vorticity nonlinearity. -/
theorem source_action (state : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality state)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    nativeFluidConstitutiveVorticityAction (fourier (realField (wholeBiotSavartVelocityState state))) wave =
      wholeStateVorticityNonlinearCoefficientAt state wave := by
  rw [fourier_action _ (velocity_reality state reality)]
  exact NativeStressSource.quadraticFlux_biotSavart_action state zero transverse wave

end
end SaturationMonoid.NavierStokes.NativeConstitutiveFourier
