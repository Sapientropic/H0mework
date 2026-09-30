import H0mework.Versions.X.NavierStokes.SourceUnheated.GlobalGradient
import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedCompleteSource
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceGradient

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeEndpointVelocityCarrier NativeUnheatedGlobalGradient NativeUnheatedBandGradient

noncomputable section
variable {nu : Viscosity}

def row (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) (time : ℝ) : ℝ :=
  integerWaveNormSq wave.1 * ‖(NativeUnifiedCompleteSource.source seed time).fst wave‖ ^ 2

theorem row_nonnegative (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) (time : ℝ) :
    0 ≤ row seed wave time := mul_nonneg (integerWaveNormSq_nonneg wave.1) (sq_nonneg _)

theorem row_continuous (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) :
    Continuous (row seed wave) := by
  change Continuous (fun time => integerWaveNormSq wave.1 * ‖(NativeUnifiedCompleteSource.source seed time).fst wave‖ ^ 2)
  simp_rw [NativeUnifiedCompleteSource.velocity_read]
  exact ((NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed) wave).norm.pow 2).const_mul _

theorem row_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) (horizon : ℝ) :
    Integrable (row seed wave) (volume.restrict (Icc 0 horizon)) :=
  (row_continuous seed wave).integrableOn_Icc

theorem finite_integral_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (waves : Finset NonzeroIntegerWavevector) :
    (∑ wave ∈ waves, ∫ time in Icc 0 horizon, row seed wave time) ≤
      budget (NativeEventualTailControl.terminal seed) horizon := by
  rw [← integral_finsetSum waves (fun wave _ => row_integrable seed wave horizon)]
  have actual := source_interval_bound seed 0 horizon le_rfl nonnegative waves
  rw [intervalIntegral.integral_of_le nonnegative, ← integral_Icc_eq_integral_Ioc] at actual
  simpa only [row, NativeUnifiedCompleteSource.velocity_read, band] using actual

theorem integrals_summable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Summable (fun wave => ∫ time in Icc 0 horizon, row seed wave time) :=
  summable_of_sum_le (fun wave => integral_nonneg (row_nonnegative seed wave))
    (finite_integral_bound seed horizon nonnegative)

theorem norm_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Summable (fun wave => ∫ time in Icc 0 horizon, ‖row seed wave time‖) := by
  simpa only [Real.norm_of_nonneg (row_nonnegative seed _ _)] using integrals_summable seed horizon nonnegative

theorem norm_lintegrals_ne_top (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∑' wave, ∫⁻ time in Icc 0 horizon, ‖row seed wave time‖ₑ) ≠ ⊤ := by
  have equal (wave : NonzeroIntegerWavevector) :
      (∫⁻ time in Icc 0 horizon, ‖row seed wave time‖ₑ) =
        ‖∫ time in Icc 0 horizon, ‖row seed wave time‖‖ₑ := by
    rw [Real.enorm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact (ofReal_integral_norm_eq_lintegral_enorm (row_integrable seed wave horizon)).symm
  simp_rw [equal]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr
    (NNReal.summable_coe.mp (norm_integrals_summable seed horizon nonnegative).abs)

theorem row_summable_ae_on (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∀ᵐ time ∂volume.restrict (Icc 0 horizon), Summable (fun wave => row seed wave time) := by
  have finite : ∀ᵐ time ∂volume.restrict (Icc 0 horizon), (∑' wave, ‖row seed wave time‖ₑ) < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum (fun wave => (row_integrable seed wave horizon).aestronglyMeasurable.enorm))
    rw [lintegral_tsum (fun wave => (row_integrable seed wave horizon).aestronglyMeasurable.enorm)]
    exact norm_lintegrals_ne_top seed horizon nonnegative
  filter_upwards [finite] with time finite
  have paid := tsum_enorm_ne_top_iff_summable_norm.mp finite.ne
  simpa only [Real.norm_of_nonneg (row_nonnegative seed _ _)] using paid

def mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ := ∑' wave, row seed wave time

theorem mass_nonnegative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : 0 ≤ mass seed time :=
  tsum_nonneg (fun wave => row_nonnegative seed wave time)

theorem mass_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (mass seed) (volume.restrict (Icc 0 horizon)) := by
  refine ⟨(AEMeasurable.tsum (fun wave => (row_integrable seed wave horizon).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable, ?_⟩
  change (∫⁻ time in Icc 0 horizon, ‖∑' wave, row seed wave time‖ₑ) < ⊤
  apply lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) ?_
  rw [lintegral_tsum (fun wave => (row_integrable seed wave horizon).aestronglyMeasurable.enorm)]
  exact (norm_lintegrals_ne_top seed horizon nonnegative).lt_top

theorem mass_integral_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, mass seed time) ≤ budget (NativeEventualTailControl.terminal seed) horizon := by
  change (∫ time in Icc 0 horizon, ∑' wave, row seed wave time) ≤ _
  rw [← integral_tsum_of_summable_integral_norm (fun wave => row_integrable seed wave horizon)
    (norm_integrals_summable seed horizon nonnegative)]
  exact (integrals_summable seed horizon nonnegative).tsum_le_of_sum_le (finite_integral_bound seed horizon nonnegative)

theorem row_summable_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → Summable (fun wave => row seed wave time) := by
  have every : ∀ᵐ time : ℝ, ∀ horizon : ℕ, time ∈ Icc (0 : ℝ) horizon → Summable (fun wave => row seed wave time) :=
    eventually_countable_forall.mpr (fun horizon => (ae_restrict_iff' measurableSet_Icc).mp
      (row_summable_ae_on seed horizon (Nat.cast_nonneg horizon)))
  filter_upwards [every] with time all nonnegative
  obtain ⟨horizon, bound⟩ := exists_nat_ge time
  exact all horizon ⟨nonnegative, bound⟩

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceGradient
