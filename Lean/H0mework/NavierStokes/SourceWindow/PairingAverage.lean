import H0mework.NavierStokes.SourceWindow.PairingMoments

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeForwardWindowPairingAverage

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeForwardWindowPairingReadout NativeForwardWindowPairingMoments
open NativeCofinalStressPositivity NativeStressPairingCarrier

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (family : α → FullSpace)

omit [IsProbabilityMeasure μ] in
theorem linear_average (integrable : Integrable family μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (read : FullSpace →L[ℝ] E) :
    read (∫ sample, family sample ∂μ) = ∫ sample, read (family sample) ∂μ :=
  (read.integral_comp_comm integrable).symm

omit [IsProbabilityMeasure μ] in
theorem mean_reality (integrable : Integrable family μ) (reality : ∀ sample, WholeRestartVelocityEndpointReality (family sample).fst) :
    WholeRestartVelocityEndpointReality (∫ sample, family sample ∂μ).fst := by
  intro wave coordinate
  have same : wholeVelocity (∫ sample, family sample ∂μ).fst
      (nonzeroIntegerWavevectorNeg wave).1 coordinate =
      star (wholeVelocity (∫ sample, family sample ∂μ).fst wave.1 coordinate) := by
    change velocityRead _ _ (∫ sample, family sample ∂μ) = star (velocityRead _ _ (∫ sample, family sample ∂μ))
    rw [linear_average μ family integrable, linear_average μ family integrable]
    have conjugated := integral_conj (μ := μ) (f := fun sample => velocityRead wave.1 coordinate (family sample))
    simp only [starRingEnd_apply] at conjugated
    rw [← conjugated]
    apply integral_congr_ae
    filter_upwards with sample
    exact congrFun (wholeVelocity_reality (family sample).fst (reality sample) wave.1) coordinate
  simpa only [wholeVelocity_nonzero] using same

omit [IsProbabilityMeasure μ] in
theorem square_integrable (integrable : Integrable family μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (square : Integrable (fun sample => ‖family sample‖ ^ 2) μ) (read : FullSpace →L[ℝ] E) :
    Integrable (fun sample => ‖read (family sample)‖ ^ 2) μ := by
  refine (square.const_mul (‖read‖ ^ 2)).mono'
    ((read.integrable_comp integrable).aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards with sample
  change ‖‖read (family sample)‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    ‖read (family sample)‖ ^ 2 ≤ (‖read‖ * ‖family sample‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (read.le_opNorm _) 2
    _ = _ := by ring

theorem mean_square_bound (integrable : Integrable family μ) (square : Integrable (fun sample => ‖family sample‖ ^ 2) μ)
    (coefficients : Index →₀ ℂ) :
    ‖meanTest coefficients (∫ sample, family sample ∂μ)‖ ^ 2 ≤
      ∫ sample, ‖meanTest coefficients (family sample)‖ ^ 2 ∂μ := by
  rw [linear_average μ family integrable]
  have convex : ConvexOn ℝ (univ : Set NativePhysicalFourier.ScalarSequence) (fun value => ‖value‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  exact convex.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) ((meanTest coefficients).integrable_comp integrable)
    (square_integrable μ family integrable square (meanTest coefficients))

def stressMatrix (value : FullSpace) : Matrix Index Index ℂ :=
  fun left right => -stressRead (left.1 - right.1) left.2 right.2 value

theorem covariance_matrix (value : FullSpace) (reality : WholeRestartVelocityEndpointReality value.fst) :
    NativeStressPairingCarrier.covariance value.fst (NativeCompleteStressCarrier.read value.snd) =
      stressMatrix value - Matrix.gram ℂ (shiftedComponent value.fst) := by
  ext left right
  simp only [Matrix.sub_apply, Matrix.gram_apply, shiftedComponent_inner value.fst reality,
    NativeCofinalFluxPairing.bilinearFlux_diagonal]
  change -(NativeCompleteStressCarrier.read value.snd (left.1 - right.1) left.2 right.2 - _) =
    -NativeCompleteStressCarrier.read value.snd (left.1 - right.1) left.2 right.2 - -_
  ring

omit [IsProbabilityMeasure μ] in
theorem stress_hermitian (integrable : Integrable family μ) (reality : ∀ sample, WholeRestartVelocityEndpointReality (family sample).fst)
    (positive : ∀ sample, (NativeStressPairingCarrier.covariance (family sample).fst
      (NativeCompleteStressCarrier.read (family sample).snd)).PosSemidef) :
    (stressMatrix (∫ sample, family sample ∂μ)).IsHermitian := by
  have original (sample : α) : (stressMatrix (family sample)).IsHermitian := by
    have result := (positive sample).1.add (Matrix.isHermitian_gram ℂ (shiftedComponent (family sample).fst))
    rw [covariance_matrix _ (reality sample), sub_add_cancel] at result
    exact result
  apply Matrix.IsHermitian.ext
  intro left right
  change star (-(stressRead (right.1 - left.1) right.2 left.2 (∫ sample, family sample ∂μ))) =
    -(stressRead (left.1 - right.1) left.2 right.2 (∫ sample, family sample ∂μ))
  rw [star_neg, linear_average μ family integrable, linear_average μ family integrable]
  apply congrArg Neg.neg
  have conjugated := integral_conj (μ := μ) (f := fun sample => stressRead (right.1 - left.1) right.2 left.2 (family sample))
  simp only [starRingEnd_apply] at conjugated
  rw [← conjugated]
  apply integral_congr_ae
  filter_upwards with sample
  have same := (original sample).apply left right
  change star (-stressRead _ _ _ _) = -stressRead _ _ _ _ at same
  rw [star_neg] at same
  exact neg_injective same

theorem covariance_positive (integrable : Integrable family μ) (square : Integrable (fun sample => ‖family sample‖ ^ 2) μ)
    (reality : ∀ sample, WholeRestartVelocityEndpointReality (family sample).fst)
    (positive : ∀ sample, (NativeStressPairingCarrier.covariance (family sample).fst
      (NativeCompleteStressCarrier.read (family sample).snd)).PosSemidef) :
    (NativeStressPairingCarrier.covariance (∫ sample, family sample ∂μ).fst
      (NativeCompleteStressCarrier.read (∫ sample, family sample ∂μ).snd)).PosSemidef := by
  constructor
  · rw [covariance_matrix _ (mean_reality μ family integrable reality)]
    exact (stress_hermitian μ family integrable reality positive).sub (Matrix.isHermitian_gram ℂ _)
  · intro coefficients
    have original (sample : α) : 0 ≤ stressTest coefficients (family sample) -
        (‖meanTest coefficients (family sample)‖ ^ 2 : ℂ) := by
      rw [← covariance_test coefficients _ (reality sample)]
      exact (positive sample).2 coefficients
    have integrated : 0 ≤ ∫ sample, stressTest coefficients (family sample) -
        ((‖meanTest coefficients (family sample)‖ ^ 2 : ℝ) : ℂ) ∂μ :=
      integral_nonneg_of_ae (μ := μ) (f := fun sample => stressTest coefficients (family sample) -
          ((‖meanTest coefficients (family sample)‖ ^ 2 : ℝ) : ℂ))
        (Eventually.of_forall fun sample => by
          change (0 : ℂ) ≤ _
          simpa only [Complex.ofReal_pow] using original sample)
    have separated : (∫ sample, stressTest coefficients (family sample) -
        ((‖meanTest coefficients (family sample)‖ ^ 2 : ℝ) : ℂ) ∂μ) =
        (∫ sample, stressTest coefficients (family sample) ∂μ) -
          ((∫ sample, ‖meanTest coefficients (family sample)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      convert! (integral_sub ((stressTest coefficients).integrable_comp integrable)
        (square_integrable μ family integrable square (meanTest coefficients)).ofReal).trans
          (congrArg (fun x => (∫ sample, stressTest coefficients (family sample) ∂μ) - x)
            (integral_ofReal (𝕜 := ℂ) (μ := μ))) using 1
    rw [separated] at integrated
    have variance : 0 ≤ ((∫ sample, ‖meanTest coefficients (family sample)‖ ^ 2 ∂μ) -
        ‖meanTest coefficients (∫ sample, family sample ∂μ)‖ ^ 2 : ℝ) :=
      sub_nonneg.mpr (mean_square_bound μ family integrable square coefficients)
    have positiveVariance : 0 ≤ (((∫ sample, ‖meanTest coefficients (family sample)‖ ^ 2 ∂μ) -
        ‖meanTest coefficients (∫ sample, family sample ∂μ)‖ ^ 2 : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr variance
    rw [covariance_test coefficients _ (mean_reality μ family integrable reality), linear_average μ family integrable]
    convert! add_nonneg integrated positiveVariance using 1
    push_cast
    ring

def data (integrable : Integrable family μ) (square : Integrable (fun sample => ‖family sample‖ ^ 2) μ)
    (reality : ∀ sample, WholeRestartVelocityEndpointReality (family sample).fst)
    (positive : ∀ sample, (NativeStressPairingCarrier.covariance (family sample).fst
      (NativeCompleteStressCarrier.read (family sample).snd)).PosSemidef) : NativeStressPairingCarrier.Data where
  mean := (∫ sample, family sample ∂μ).fst
  reality := mean_reality μ family integrable reality
  stress := NativeCompleteStressCarrier.read (∫ sample, family sample ∂μ).snd
  positive := covariance_positive μ family integrable square reality positive

end
end SaturationMonoid.NavierStokes.NativeForwardWindowPairingAverage
