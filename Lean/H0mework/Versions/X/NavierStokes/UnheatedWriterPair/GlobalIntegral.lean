import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.GlobalEvolution

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairGlobalEvolution

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeUnheatedPairInverseFlux
open NativeUnheatedPairNegativeKernel NativeUnheatedGlobalNegativeOne NativeUnheatedIntegralBilinear

noncomputable section
variable {nu : Viscosity}

def derivativePair (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  bilinear nu order wave output input (rate seed time) (state seed time) +
    bilinear nu order wave output input (state seed time) (rate seed time)

theorem derivativePair_integrable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Integrable (fun time => derivativePair seed order time wave output input) (volume.restrict (Icc 0 horizon)) := by
  have continuous := (state_continuousOn seed).mono (Icc_subset_Ici_self : Icc 0 horizon ⊆ Ici 0)
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous
  let B := bilinear nu order wave output input
  have field := continuous.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have rateMeas := (rate_measurable seed).restrict (s := Icc 0 horizon)
  have measurable := (B.aestronglyMeasurable_comp₂ rateMeas field).add
    (B.aestronglyMeasurable_comp₂ field rateMeas)
  apply ((rate_integrable seed horizon nonnegative).norm.const_mul (2*‖B‖*bound)).mono' measurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
  have first := (B.le_opNorm₂ (rate seed time) (state seed time)).trans
    (mul_le_mul_of_nonneg_left (bounded time inside) (mul_nonneg (norm_nonneg B) (norm_nonneg _)))
  have second := (B.le_opNorm₂ (state seed time) (rate seed time)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bounded time inside) (norm_nonneg B)) (norm_nonneg _))
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by ring))

theorem sourcePair_integrable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Integrable (fun time => sourcePair seed order time wave output input) (volume.restrict (Icc 0 horizon)) := by
  have velocity := wholeVelocityCLM.continuous.comp_aestronglyMeasurable
    ((WithLp.fstL 2 ℝ _ NativeCompleteStressCarrier.Space).continuous.comp_aestronglyMeasurable
      (NativeUnifiedCompleteSource.source_measurable seed))
  have measurable := (coefficientCLM nu order wave output input).aestronglyMeasurable_comp₂ velocity velocity
  have bound (time : ℝ) : ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst‖ ≤
      NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le _).trans ((WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound seed time))
  apply (integrable_const (rowBudget nu order wave * (3 * NativeUnifiedCompleteSource.budget seed ^ 2))).mono' measurable.restrict
  apply Eventually.of_forall
  intro time
  apply (coefficient_bound order _ _ wave output input).trans
  apply mul_le_mul_of_nonneg_left _ (rowBudget_nonnegative order wave)
  have multiplied := mul_le_mul (bound time) (bound time) (norm_nonneg _) ((norm_nonneg _).trans (bound time))
  change 3 * ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst‖ *
    ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst‖ ≤ _
  nlinarith

theorem sourceTriple_integrable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Integrable (fun time => sourceTriple seed order time wave output input) (volume.restrict (Icc 0 horizon)) := by
  have paid := (derivativePair_integrable seed order horizon nonnegative wave output input).add
    (sourcePair_integrable seed order horizon wave output input)
  apply paid.congr
  filter_upwards [ae_restrict_of_ae (derivative_value_ae seed order wave output input), ae_restrict_mem measurableSet_Icc] with time actual inside
  exact eq_add_of_sub_eq (actual inside.1).symm |>.symm

theorem sourcePair_write (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b)
    (wave : IntegerWavevector) (output input : Coordinate) :
    sourcePair seed (order+1) b wave output input - sourcePair seed (order+1) a wave output input =
      ∫ time in a..b, sourceTriple seed order time wave output input - sourcePair seed order time wave output input := by
  have positiveHorizon : 0 ≤ max a b := a0.trans (le_max_left _ _)
  have interval : uIcc a b ⊆ Icc 0 (max a b) := fun _ inside => ⟨(le_min a0 b0).trans inside.1, inside.2⟩
  have cubic : IntegrableOn (fun time => sourceTriple seed order time wave output input) (Icc 0 (max a b)) :=
    sourceTriple_integrable seed order (max a b) positiveHorizon wave output input
  have quadratic : IntegrableOn (fun time => sourcePair seed order time wave output input) (Icc 0 (max a b)) :=
    sourcePair_integrable seed order (max a b) wave output input
  apply integral_of_ac_derivative _ _ (sourcePair_ac seed order a b a0 b0 wave output input)
    (((cubic.sub quadratic).mono_set interval).intervalIntegrable)
  filter_upwards [sourcePair_hasDerivAt_ae seed order wave output input, volume.ae_ne (0 : ℝ)] with time actual nonzero
  intro inside
  exact actual (lt_of_le_of_ne ((le_min a0 b0).trans inside.1) (Ne.symm nonzero))

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairGlobalEvolution
