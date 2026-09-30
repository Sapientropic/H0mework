import H0mework.Versions.X.NavierStokes.SourceUnheated.BandGradient
import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowJets
import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowEvolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution

namespace SaturationMonoid.NavierStokes.NativeUnheatedWindowJensen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressAction NativeForwardWindowJets NativeUnheatedBandGradient

noncomputable section
variable {nu : Viscosity}

def shiftMeasure : Measure ℝ := volume.restrict (Icc (-2 : ℝ) (-1))

instance : IsProbabilityMeasure shiftMeasure := by
  constructor
  norm_num [shiftMeasure, Real.volume_Icc]

theorem kernel_support (order : ℕ) (shift : ℝ) (nonzero : kernelJet order shift ≠ 0) :
    shift ∈ Icc (-2 : ℝ) (-1) := by
  have inside := kernelJet_support order (subset_closure nonzero)
  change shift ∈ tsupport (NativeForwardWindowSource.bump.normed volume) at inside
  rw [NativeForwardWindowSource.bump.tsupport_normed_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at inside
  change -(1 / 2 : ℝ) ≤ shift - -3 / 2 ∧ shift - -3 / 2 ≤ (1 / 2 : ℝ) at inside
  constructor <;> linarith [inside.1, inside.2]

def row (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) (time : ℝ) :
    ComplexCoordinateEuclidean := (NativeUnifiedCompleteSource.source seed time).fst wave

theorem row_continuous (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) :
    Continuous (row seed wave) := by
  have same : row seed wave = fun time => NativeAbsoluteEventualControl.velocity seed time wave := by
    funext time
    exact congrArg (fun value : WholeRestartVelocityEndpointState => value wave)
      (NativeUnifiedCompleteSource.velocity_read seed time)
  rw [same]
  exact NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed) wave

def integrand (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : NonzeroIntegerWavevector) (shift : ℝ) : ComplexCoordinateEuclidean :=
  kernelJet order shift • row seed wave (time - shift)

theorem integrand_continuous (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : NonzeroIntegerWavevector) : Continuous (integrand seed order time wave) :=
  (kernelJet_smooth order).continuous.smul ((row_continuous seed wave).comp (continuous_const.sub continuous_id))

theorem row_average (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : NonzeroIntegerWavevector) :
    (NativeForwardWindowEvolution.velocityJet seed order time) wave =
      ∫ shift, integrand seed order time wave shift ∂shiftMeasure := by
  let read : FullSpace →L[ℝ] ComplexCoordinateEuclidean :=
    (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).comp
      NativeForwardWindowEvolution.velocityRead
  have integrable : Integrable (fun shift : ℝ => kernelJet order shift •
      NativeUnifiedCompleteSource.source seed (time - shift)) :=
    (kernelJet_compact order).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernelJet_smooth order).continuous (NativeForwardWindowSource.original_locallyIntegrable seed) time
  have original := read.integral_comp_comm integrable
  change read (∫ shift : ℝ, kernelJet order shift • NativeUnifiedCompleteSource.source seed (time - shift)) = _
  rw [← original]
  change (∫ shift : ℝ, integrand seed order time wave shift) = _
  rw [shiftMeasure, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases inside : shift ∈ Icc (-2 : ℝ) (-1)
  · simp only [indicator_of_mem inside]
  · have zero : kernelJet order shift = 0 := by
      by_contra nonzero
      exact inside (kernel_support order shift nonzero)
    simp only [indicator_of_notMem inside, integrand, zero, zero_smul]

theorem row_square_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : NonzeroIntegerWavevector) :
    ‖NativeForwardWindowEvolution.velocityJet seed order time wave‖ ^ 2 ≤
      ∫ shift, kernelJet order shift ^ 2 * ‖row seed wave (time - shift)‖ ^ 2 ∂shiftMeasure := by
  rw [row_average]
  have convex : ConvexOn ℝ (univ : Set ComplexCoordinateEuclidean) (fun value => ‖value‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have controlled := convex.map_integral_le (μ := shiftMeasure) (continuous_norm.pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _)
    ((integrand_continuous seed order time wave).integrableOn_Icc)
    (((integrand_continuous seed order time wave).norm.pow 2).integrableOn_Icc)
  simpa only [Function.comp_def, integrand, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using! controlled


theorem band_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (waves : Finset NonzeroIntegerWavevector) :
    band waves (NativeForwardWindowEvolution.velocityJet seed order time) ≤
      ∫ shift, kernelJet order shift ^ 2 *
        band waves (NativeAbsoluteEventualControl.velocity seed (time - shift)) ∂shiftMeasure := by
  have integrable (wave : NonzeroIntegerWavevector) :
      Integrable (fun shift => integerWaveNormSq wave.1 *
        (kernelJet order shift ^ 2 * ‖row seed wave (time - shift)‖ ^ 2)) shiftMeasure :=
    ((((kernelJet_smooth order).continuous.pow 2).mul
      (((row_continuous seed wave).comp (continuous_const.sub continuous_id)).norm.pow 2)).const_mul _).integrableOn_Icc
  calc
    _ ≤ ∑ wave ∈ waves, integerWaveNormSq wave.1 *
        ∫ shift, kernelJet order shift ^ 2 * ‖row seed wave (time - shift)‖ ^ 2 ∂shiftMeasure :=
      Finset.sum_le_sum fun wave _ => mul_le_mul_of_nonneg_left
        (row_square_bound seed order time wave) (integerWaveNormSq_nonneg wave.1)
    _ = ∫ shift, ∑ wave ∈ waves, integerWaveNormSq wave.1 *
        (kernelJet order shift ^ 2 * ‖row seed wave (time - shift)‖ ^ 2) ∂shiftMeasure := by
      rw [integral_finsetSum _ (fun wave _ => integrable wave)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with shift
      rw [band, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _
      unfold row
      rw [NativeUnifiedCompleteSource.velocity_read]
      ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedWindowJensen
