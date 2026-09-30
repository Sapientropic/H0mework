import H0mework.NavierStokes.SourceUnheated.StressProduct
import H0mework.NavierStokes.StressWholeH1.Mixed
import H0mework.NavierStokes.SourceAction.Convolution
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticEnvelope
open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeEndpointVelocityCarrier
open NativeMovingCriticalProduct NativeMovingCriticalProductScalar NativeCompleteStressCarrier
noncomputable section

theorem amplitude_original (value : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    amplitude value wave = vorticityRowAmplitude value wave := by
  rw [amplitude, vorticityRowAmplitude, ← euclideanCoordinateRow_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem pair_summable (value : wholePhysical) (wave : IntegerWavevector) :
    Summable (fun first => amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first)) := by
  simpa only [amplitude_original] using summable_fixedOutputVorticityAmplitudeProduct (wholeVelocity value.1) (wholeVelocity value.1) wave

def row (value : wholePhysical) (wave : IntegerWavevector) : ℝ :=
  ∑' first, amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first)

theorem row_nonnegative (value : wholePhysical) (wave : IntegerWavevector) : 0 ≤ row value wave :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def constant : ℝ := NativeUnheatedStressProduct.constant

theorem constant_nonnegative : 0 ≤ constant := NativeUnheatedStressProduct.constant_nonnegative

theorem finite_bound (value : wholePhysical) (regular : H1 value) (F : Finset IntegerWavevector) :
    (∑ wave ∈ F, convolution F (amplitude (wholeVelocity value.1)) (amplitude (wholeVelocity value.1)) wave^2) ≤
      constant*gradientMass value^2 := by
  have weighted : Summable (fun wave => ((weight wave)⁻¹)⁻¹^2) := by simpa only [inv_inv] using weight_summable
  have paid := convolution_bound F (fun wave => (weight wave)⁻¹)
    (amplitude (wholeVelocity value.1)) (amplitude (wholeVelocity value.1))
    (fun wave => inv_nonneg.mpr (weight_pos wave).le) (fun wave _ => inv_pos.mpr (weight_pos wave)) weighted
  simp only [inv_inv] at paid
  have identity : mass F (fun wave => (weight wave)⁻¹) (amplitude (wholeVelocity value.1)) =
      ∑ wave ∈ F, gradientDensity value wave :=
    NativeUnheatedStressProduct.finite_mass (wholeVelocity value.1) (wholeVelocity_zero _) F
  rw [identity] at paid
  have partialBound := regular.sum_le_tsum F (fun wave _ => gradient_nonnegative value wave)
  have total0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
  have finite0 : 0 ≤ ∑ wave ∈ F, gradientDensity value wave := Finset.sum_nonneg fun wave _ => gradient_nonnegative value wave
  exact paid.trans ((mul_le_mul (mul_le_mul_of_nonneg_left partialBound constant_nonnegative) partialBound finite0
    (mul_nonneg constant_nonnegative total0)).trans_eq (by unfold gradientMass; ring))

theorem finite_tendsto (value : wholePhysical) (wave : IntegerWavevector) :
    Tendsto (fun radius => convolution (integerWaveFrequencyCube radius)
      (amplitude (wholeVelocity value.1)) (amplitude (wholeVelocity value.1)) wave) atTop (𝓝 (row value wave)) := by
  let term (radius : ℕ) (first : IntegerWavevector) : ℝ :=
    if first ∈ integerWaveFrequencyCube radius then
      if wave-first ∈ integerWaveFrequencyCube radius then
        amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first) else 0 else 0
  have point (first : IntegerWavevector) : Tendsto (fun radius => term radius first) atTop
      (𝓝 (amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [integerWave_eventually_mem_frequencyCube first, integerWave_eventually_mem_frequencyCube (wave-first)] with radius left right
    simp only [term, if_pos left, if_pos right]
  have bounded (radius : ℕ) (first : IntegerWavevector) : ‖term radius first‖ ≤
      amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first) := by
    have nonnegative : 0 ≤ amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first) :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    unfold term
    split_ifs
    · rw [Real.norm_of_nonneg nonnegative]
    · rw [norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · rw [norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have generated := tendsto_tsum_of_dominated_convergence (pair_summable value wave) point (Eventually.of_forall bounded)
  have finite (radius : ℕ) : (∑' first, term radius first) = convolution (integerWaveFrequencyCube radius)
      (amplitude (wholeVelocity value.1)) (amplitude (wholeVelocity value.1)) wave := by
    rw [tsum_eq_sum (s := integerWaveFrequencyCube radius) (fun first outside => by simp only [term, if_neg outside])]
    apply Finset.sum_congr rfl
    intro first member
    simp only [term, if_pos member]
  simpa only [finite, row] using generated

theorem observed_bound (value : wholePhysical) (regular : H1 value) (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed, row value wave^2) ≤ constant*gradientMass value^2 := by
  apply le_of_tendsto (tendsto_finsetSum observed (fun wave _ => (finite_tendsto value wave).pow 2))
  have included : ∀ᶠ radius in atTop, observed ⊆ integerWaveFrequencyCube radius :=
    (eventually_all_finset observed).mpr (fun wave _ => integerWave_eventually_mem_frequencyCube wave)
  filter_upwards [included] with radius subset
  exact (Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => sq_nonneg _)).trans
    (finite_bound value regular (integerWaveFrequencyCube radius))

theorem square_summable (value : wholePhysical) (regular : H1 value) : Summable (fun wave => row value wave^2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (observed_bound value regular)

def envelope (value : wholePhysical) (regular : H1 value) : NativeFullOrderAction.ScalarL2 :=
  ⟨row value, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using square_summable value regular)⟩

theorem envelope_apply (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    envelope value regular wave = ∑' first,
      amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first) := rfl

theorem envelope_nonnegative (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    0 ≤ envelope value regular wave := row_nonnegative value wave

theorem envelope_norm_le (value : wholePhysical) (regular : H1 value) :
    ‖envelope value regular‖ ≤ Real.sqrt constant*gradientMass value := by
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) mass0)).mp
  have identity := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (envelope value regular)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at identity
  rw [identity, mul_pow, Real.sq_sqrt constant_nonnegative]
  exact (square_summable value regular).tsum_le_of_sum_le (observed_bound value regular)

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticEnvelope
