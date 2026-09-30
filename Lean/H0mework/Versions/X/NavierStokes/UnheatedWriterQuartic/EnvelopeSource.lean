import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Envelope
import H0mework.Versions.X.NavierStokes.UnheatedWriterTail.Weighted

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticEnvelope
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient
open NativeMovingCriticalProduct
noncomputable section
variable {nu : Viscosity}

def sourceRow (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (time : ℝ) : ℝ :=
  ∑' first, amplitude (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) first*
    amplitude (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) (wave-first)

theorem sourceRow_eq (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector) :
    sourceRow seed wave time = envelope (physical seed time nonnegative) regular wave := rfl

theorem source_envelope_norm_le (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    ‖envelope (physical seed time nonnegative) regular‖ ≤ Real.sqrt constant*mass seed time := by
  simpa only [physical_mass] using envelope_norm_le (physical seed time nonnegative) regular

theorem source_square_summable_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → Summable (fun wave => sourceRow seed wave time^2) := by
  filter_upwards [physical_H1_ae seed] with time actual nonnegative
  exact square_summable (physical seed time nonnegative) (actual nonnegative)

theorem sourceRow_nonnegative (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (time : ℝ) :
    0 ≤ sourceRow seed wave time := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem sourceRow_measurable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    AEStronglyMeasurable (sourceRow seed wave) (volume : Measure ℝ) := by
  have amp (index : IntegerWavevector) :
      AEStronglyMeasurable (fun time => amplitude (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) index)
        (volume : Measure ℝ) := by
    let evaluation := NativeCompleteStressAction.euclideanCLM.comp
      ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ThreeDimensionalPeriodicCoarseFilterCore.Coordinate → ℂ) 2 index).comp wholeVelocityCLM)
    exact (evaluation.continuous.comp_aestronglyMeasurable (NativeUnheatedSourceWeightedTail.velocity_measurable seed)).norm
  exact (AEMeasurable.tsum fun first => ((amp first).mul (amp (wave-first))).aemeasurable).aestronglyMeasurable

def sourceNorm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ :=
  Real.sqrt (∑' wave, sourceRow seed wave time^2)

theorem sourceNorm_eq (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    sourceNorm seed time = ‖envelope (physical seed time nonnegative) regular‖ := by
  have identity := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (envelope (physical seed time nonnegative) regular)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, ← sourceRow_eq seed time nonnegative regular] at identity
  rw [sourceNorm, ← identity, Real.sqrt_sq (norm_nonneg _)]

theorem sourceNorm_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (sourceNorm seed) (volume : Measure ℝ) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable
    (AEMeasurable.tsum fun wave => ((sourceRow_measurable seed wave).pow 2).aemeasurable).aestronglyMeasurable

theorem sourceNorm_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → sourceNorm seed time ≤ Real.sqrt constant*mass seed time := by
  filter_upwards [physical_H1_ae seed] with time actual nonnegative
  rw [sourceNorm_eq seed time nonnegative (actual nonnegative)]
  exact source_envelope_norm_le seed time nonnegative (actual nonnegative)

theorem sourceNorm_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (sourceNorm seed) (volume.restrict (Icc 0 horizon)) := by
  apply ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt constant)).mono' (sourceNorm_measurable seed).restrict
  filter_upwards [ae_restrict_of_ae (sourceNorm_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
  rw [Real.norm_of_nonneg (show 0 ≤ sourceNorm seed time from Real.sqrt_nonneg _)]
  exact actual inside.1

theorem sourceNorm_integral_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, sourceNorm seed time) ≤
      Real.sqrt constant*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  have paid := integral_mono_ae (sourceNorm_integrable seed horizon nonnegative)
    ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt constant)) (by
      filter_upwards [ae_restrict_of_ae (sourceNorm_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
      exact actual inside.1)
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) (Real.sqrt_nonneg _))

theorem sourceRow_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave, sourceRow seed wave time ≤ Real.sqrt constant*mass seed time := by
  filter_upwards [physical_H1_ae seed] with time actual nonnegative wave
  rw [sourceRow_eq seed time nonnegative (actual nonnegative)]
  have evaluated := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num) (envelope (physical seed time nonnegative) (actual nonnegative)) wave
  rw [Real.norm_of_nonneg (envelope_nonnegative _ _ _)] at evaluated
  exact evaluated.trans (source_envelope_norm_le seed time nonnegative (actual nonnegative))

theorem sourceRow_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (sourceRow seed wave) (volume.restrict (Icc 0 horizon)) := by
  apply ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt constant)).mono' (sourceRow_measurable seed wave).restrict
  filter_upwards [ae_restrict_of_ae (sourceRow_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
  rw [Real.norm_of_nonneg (sourceRow_nonnegative seed wave time)]
  exact actual inside.1 wave

theorem sourceRow_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    (fun wave => sourceRow seed wave (response.2.clockAdvance+time)) = fun wave => sourceRow response.1 wave time := by
  simp only [sourceRow, NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

theorem sourceNorm_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    sourceNorm seed (response.2.clockAdvance+time) = sourceNorm response.1 time := by
  unfold sourceNorm
  simp only [congrFun (sourceRow_next seed response generated time nonnegative)]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticEnvelope
