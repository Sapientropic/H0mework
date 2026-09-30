import H0mework.NavierStokes.SourceAction.Synthesis
import H0mework.NavierStokes.UnifiedAction.UnifiedHeatAction
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace

namespace SaturationMonoid.NavierStokes.NativeHeatGaussianPhase
open MeasureTheory ProbabilityTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open NativeFullOrderSynthesis
noncomputable section

def character (offset : PhysicalSpace) (wave : IntegerWavevector) : ℂ := monomial wave offset

theorem character_norm (offset : PhysicalSpace) (wave : IntegerWavevector) : ‖character offset wave‖ = 1 := by
  rw [character, monomial, monomial_phase]
  exact Complex.norm_exp_ofReal_mul_I _

theorem character_add (offset : PhysicalSpace) (left right : IntegerWavevector) :
    character offset (left + right) = character offset left * character offset right :=
  UnitAddTorus.mFourier_add

theorem character_neg (offset : PhysicalSpace) (wave : IntegerWavevector) :
    character offset (-wave) = star (character offset wave) := UnitAddTorus.mFourier_neg

theorem character_sub (offset : PhysicalSpace) (left right : IntegerWavevector) :
    character offset (left - right) = character offset left * star (character offset right) := by
  rw [sub_eq_add_neg, character_add, character_neg]

theorem character_continuous (wave : IntegerWavevector) : Continuous (fun offset => character offset wave) :=
  (monomial_smooth wave).continuous

def scale (nu : Viscosity) (lag : ℝ≥0) : ℝ := Real.sqrt (2 * nu.coeff * lag)
def displacement (nu : Viscosity) (lag : ℝ≥0) (sample : PhysicalSpace) : PhysicalSpace :=
  scale nu lag • sample
def frequencyVector (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) : PhysicalSpace :=
  (scale nu lag * (2 * Real.pi)) • WithLp.toLp 2 (fun coordinate => (wave coordinate : ℝ))

theorem scale_sq (nu : Viscosity) (lag : ℝ≥0) : scale nu lag ^ 2 = 2 * nu.coeff * lag :=
  Real.sq_sqrt (by positivity [nu.coeff_pos])

theorem character_displacement (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector)
    (sample : PhysicalSpace) :
    character (displacement nu lag sample) wave =
      Complex.exp ((inner ℝ sample (frequencyVector nu lag wave) : ℝ) * Complex.I) := by
  rw [character, monomial, monomial_phase]
  unfold profile
  congr 2
  rw [phase_apply]
  simp only [frequencyVector, displacement, inner_smul_right, PiLp.inner_apply,
    RCLike.inner_apply, PiLp.smul_apply]
  congr 1
  simp only [starRingEnd_apply, star_trivial, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

theorem frequencyVector_sq (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) :
    ‖frequencyVector nu lag wave‖ ^ 2 =
      2 * (nu.coeff * integerWaveViscousMultiplier wave) * lag := by
  rw [frequencyVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    mul_pow, scale_sq, EuclideanSpace.real_norm_sq_eq]
  unfold integerWaveViscousMultiplier integerWaveNormSq
  ring

def gaussian : Measure PhysicalSpace := stdGaussian PhysicalSpace
instance gaussian_probability : IsProbabilityMeasure gaussian := inferInstanceAs (IsProbabilityMeasure (stdGaussian PhysicalSpace))

theorem character_integrable (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) :
    Integrable (fun sample => character (displacement nu lag sample) wave) gaussian := by
  apply Integrable.of_bound ((character_continuous wave).comp (by unfold displacement; fun_prop)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun sample => (character_norm _ wave).le

theorem heat_characteristic (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) :
    (∫ sample, character (displacement nu lag sample) wave ∂gaussian) =
      (finiteStateVorticityHeatMultiplier nu.coeff lag wave : ℂ) := by
  simp_rw [character_displacement]
  rw [← charFun_apply, gaussian, charFun_stdGaussian, ← Complex.ofReal_pow, frequencyVector_sq]
  rw [finiteStateVorticityHeatMultiplier, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end
end SaturationMonoid.NavierStokes.NativeHeatGaussianPhase
