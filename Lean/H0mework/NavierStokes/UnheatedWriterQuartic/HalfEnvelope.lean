import H0mework.NavierStokes.UnheatedWriterQuartic.RieszKernel
import H0mework.NavierStokes.UnheatedWriterQuartic.EnvelopeSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticHalfEnvelope
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeEndpointVelocityCarrier
open NativeMovingCriticalProduct NativeMovingCriticalProductScalar NativeCompleteStressCarrier
noncomputable section

def density (a : IntegerWavevector → ℝ) (k : IntegerWavevector) : ℝ := (weight k)⁻¹*a k^2
def pairMass (F : Finset IntegerWavevector) (a : IntegerWavevector → ℝ) (k : IntegerWavevector) : ℝ :=
  ∑ p ∈ F, if k-p ∈ F then density a p*density a (k-p) else 0

theorem density_nonnegative (a : IntegerWavevector → ℝ) (k : IntegerWavevector) : 0 ≤ density a k :=
  mul_nonneg (inv_nonneg.mpr (weight_pos k).le) (sq_nonneg _)

theorem finite_row (F : Finset IntegerWavevector) (a : IntegerWavevector → ℝ) (k : IntegerWavevector) :
    Real.sqrt (1+integerWaveNormSq k)*convolution F a a k^2 ≤ NativeUnheatedRieszKernel.constant*pairMass F a k := by
  let kernel := ∑ p ∈ F, if k-p ∈ F then weight p*weight (k-p) else 0
  have mass0 : 0 ≤ pairMass F a k := Finset.sum_nonneg fun p _ => by
    split_ifs
    · exact mul_nonneg (density_nonnegative a p) (density_nonnegative a (k-p))
    · exact le_rfl
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
    (r := fun p => if k-p ∈ F then a p*a (k-p) else 0)
    (f := fun p => if k-p ∈ F then weight p*weight (k-p) else 0)
    (g := fun p => if k-p ∈ F then density a p*density a (k-p) else 0)
    (fun p _ => by split_ifs; exact mul_nonneg (weight_pos p).le (weight_pos (k-p)).le; exact le_rfl)
    (fun p _ => by split_ifs; exact mul_nonneg (density_nonnegative a p) (density_nonnegative a (k-p)); exact le_rfl)
    (fun p _ => by
      by_cases inside : k-p ∈ F
      · simp only [if_pos inside, density]
        apply le_of_eq
        field_simp [(weight_pos p).ne', (weight_pos (k-p)).ne']
      · simp only [if_neg inside, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl])
  have weighted : Real.sqrt (1+integerWaveNormSq k)*kernel ≤ NativeUnheatedRieszKernel.constant := by
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := F) (fun p _ =>
      show (if k-p ∈ F then weight p*weight (k-p) else 0) ≤ weight p*weight (k-p) by
        split_ifs; exact le_rfl; exact mul_nonneg (weight_pos p).le (weight_pos (k-p)).le)) (Real.sqrt_nonneg _)).trans
    exact NativeUnheatedRieszKernel.finite_bound k F
  calc
    _ ≤ Real.sqrt (1+integerWaveNormSq k)*(kernel*pairMass F a k) :=
      mul_le_mul_of_nonneg_left cauchy (Real.sqrt_nonneg _)
    _ = (Real.sqrt (1+integerWaveNormSq k)*kernel)*pairMass F a k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right weighted mass0

theorem pair_aggregate (F : Finset IntegerWavevector) (a : IntegerWavevector → ℝ) :
    (∑ k ∈ F, pairMass F a k) ≤ mass F (fun k => (weight k)⁻¹) a^2 := by
  unfold pairMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ p ∈ F, density a p*mass F (fun k => (weight k)⁻¹) a := by
      apply Finset.sum_le_sum
      intro p _
      have factor : (∑ k ∈ F, if k-p ∈ F then density a p*density a (k-p) else 0) =
          density a p*(∑ k ∈ F, if k-p ∈ F then density a (k-p) else 0) := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      rw [factor]
      have paid := translated_sum_le F (density a) (density_nonnegative a) (fun k => k-p) sub_left_injective
      exact mul_le_mul_of_nonneg_left paid (density_nonnegative a p)
    _ = _ := by rw [← Finset.sum_mul, pow_two]; rfl

theorem finite_control (F : Finset IntegerWavevector) (a : IntegerWavevector → ℝ) :
    (∑ k ∈ F, Real.sqrt (1+integerWaveNormSq k)*convolution F a a k^2) ≤
      NativeUnheatedRieszKernel.constant*mass F (fun k => (weight k)⁻¹) a^2 := by
  have rows := Finset.sum_le_sum (s := F) (fun k _ => finite_row F a k)
  rw [← Finset.mul_sum] at rows
  exact rows.trans (mul_le_mul_of_nonneg_left (pair_aggregate F a) NativeUnheatedRieszKernel.constant_nonnegative)

theorem finite_bound (value : wholePhysical) (regular : H1 value) (F : Finset IntegerWavevector) :
    (∑ k ∈ F, Real.sqrt (1+integerWaveNormSq k)*
      convolution F (amplitude (wholeVelocity value.1)) (amplitude (wholeVelocity value.1)) k^2) ≤
        NativeUnheatedRieszKernel.constant*gradientMass value^2 := by
  have generated := finite_control F (amplitude (wholeVelocity value.1))
  have same : mass F (fun k => (weight k)⁻¹) (amplitude (wholeVelocity value.1)) = ∑ k ∈ F, gradientDensity value k :=
    NativeUnheatedStressProduct.finite_mass (wholeVelocity value.1) (wholeVelocity_zero _) F
  rw [same] at generated
  exact generated.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => gradient_nonnegative value k)
      (regular.sum_le_tsum F (fun k _ => gradient_nonnegative value k)) 2) NativeUnheatedRieszKernel.constant_nonnegative)

theorem observed_bound (value : wholePhysical) (regular : H1 value) (observed : Finset IntegerWavevector) :
    (∑ k ∈ observed, Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.row value k^2) ≤
      NativeUnheatedRieszKernel.constant*gradientMass value^2 := by
  apply le_of_tendsto (tendsto_finsetSum observed (fun k _ =>
    ((NativeUnheatedQuarticEnvelope.finite_tendsto value k).pow 2).const_mul (Real.sqrt (1+integerWaveNormSq k))))
  have included : ∀ᶠ radius in atTop, observed ⊆ integerWaveFrequencyCube radius :=
    (eventually_all_finset observed).mpr (fun wave _ => integerWave_eventually_mem_frequencyCube wave)
  filter_upwards [included] with radius subset
  exact (Finset.sum_le_sum_of_subset_of_nonneg subset (fun k _ _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).trans
    (finite_bound value regular (integerWaveFrequencyCube radius))

theorem square_summable (value : wholePhysical) (regular : H1 value) :
    Summable (fun k => Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.row value k^2) :=
  summable_of_sum_le (fun _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (observed_bound value regular)

theorem mass_bound (value : wholePhysical) (regular : H1 value) :
    (∑' k, Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.row value k^2) ≤
      NativeUnheatedRieszKernel.constant*gradientMass value^2 :=
  (square_summable value regular).tsum_le_of_sum_le (observed_bound value regular)

open NativeUnheatedSourceGradient
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
variable {nu : Viscosity}

theorem source_control_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time →
      Summable (fun k => Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.sourceRow seed k time^2) ∧
      (∑' k, Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.sourceRow seed k time^2) ≤
        NativeUnheatedRieszKernel.constant*mass seed time^2 := by
  filter_upwards [physical_H1_ae seed] with time actual nonnegative
  refine ⟨square_summable (physical seed time nonnegative) (actual nonnegative), ?_⟩
  simpa only [physical_mass] using! mass_bound (physical seed time nonnegative) (actual nonnegative)

def sourceNorm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ :=
  Real.sqrt (∑' k, Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.sourceRow seed k time^2)

theorem sourceNorm_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (sourceNorm seed) (volume : Measure ℝ) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (AEMeasurable.tsum (fun k =>
    (((NativeUnheatedQuarticEnvelope.sourceRow_measurable seed k).pow 2).const_mul (Real.sqrt (1+integerWaveNormSq k))).aemeasurable)).aestronglyMeasurable

theorem sourceNorm_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → sourceNorm seed time ≤ Real.sqrt NativeUnheatedRieszKernel.constant*mass seed time := by
  filter_upwards [source_control_ae seed] with time actual nonnegative
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (mass_nonnegative seed time))).mp
  have nonnegativeSum : 0 ≤ ∑' k, Real.sqrt (1+integerWaveNormSq k)*NativeUnheatedQuarticEnvelope.sourceRow seed k time^2 :=
    tsum_nonneg fun _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  rw [Real.sq_sqrt nonnegativeSum, mul_pow, Real.sq_sqrt NativeUnheatedRieszKernel.constant_nonnegative]
  exact (actual nonnegative).2

theorem sourceNorm_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (sourceNorm seed) (volume.restrict (Icc 0 horizon)) := by
  apply ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt NativeUnheatedRieszKernel.constant)).mono'
    (sourceNorm_measurable seed).restrict
  filter_upwards [ae_restrict_of_ae (sourceNorm_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
  rw [Real.norm_of_nonneg (show 0 ≤ sourceNorm seed time from Real.sqrt_nonneg _)]
  exact actual inside.1

theorem sourceNorm_integral_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, sourceNorm seed time) ≤
      Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  have paid := integral_mono_ae (sourceNorm_integrable seed horizon nonnegative)
    ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt NativeUnheatedRieszKernel.constant)) (by
      filter_upwards [ae_restrict_of_ae (sourceNorm_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
      exact actual inside.1)
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) (Real.sqrt_nonneg _))

theorem sourceNorm_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    sourceNorm seed (response.2.clockAdvance+time) = sourceNorm response.1 time := by
  unfold sourceNorm
  simp only [congrFun (NativeUnheatedQuarticEnvelope.sourceRow_next seed response generated time nonnegative)]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticHalfEnvelope
