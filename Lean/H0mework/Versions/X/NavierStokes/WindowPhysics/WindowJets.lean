import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowSource
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
open scoped Topology ENNReal Convolution ContDiff

namespace SaturationMonoid.NavierStokes.NativeForwardWindowJets

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeForwardWindowSource

noncomputable section

def kernelJet (order : ℕ) : ℝ → ℝ := iteratedDeriv order kernel

theorem kernelJet_smooth (order : ℕ) : ContDiff ℝ ∞ (kernelJet order) := by
  rw [kernelJet, iteratedDeriv_eq_iterate]
  exact kernel_smooth.iterate_deriv order

theorem kernelJet_support (order : ℕ) : tsupport (kernelJet order) ⊆ tsupport kernel := by
  induction order with
  | zero => simpa only [kernelJet, iteratedDeriv_zero] using (Subset.rfl : tsupport kernel ⊆ tsupport kernel)
  | succ order previous =>
      rw [kernelJet, iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans previous

theorem kernelJet_compact (order : ℕ) : HasCompactSupport (kernelJet order) :=
  kernel_compact.mono' (fun _ member => kernelJet_support order (subset_closure member))

theorem kernelJet_integrable (order : ℕ) : Integrable (kernelJet order) :=
  (kernelJet_smooth order).continuous.integrable_of_hasCompactSupport (kernelJet_compact order)

theorem kernelJet_nonpositive (order : ℕ) (time : ℝ) (nonzero : kernelJet order time ≠ 0) : time ≤ -1 := by
  have inside := kernelJet_support order (subset_closure nonzero)
  change time ∈ tsupport (bump.normed volume) at inside
  rw [bump.tsupport_normed_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at inside
  change -(1 / 2 : ℝ) ≤ time - -3 / 2 ∧ time - -3 / 2 ≤ (1 / 2 : ℝ) at inside
  linarith [inside.2]

variable {nu : Viscosity}

def jet (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) : ℝ → FullSpace :=
  kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] NativeUnifiedCompleteSource.source seed

theorem jet_smooth (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) : ContDiff ℝ ∞ (jet seed order) :=
  (kernelJet_compact order).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernelJet_smooth order) (original_locallyIntegrable seed)

theorem jet_zero (seed : GeneratedWholeRestartCurrent nu) : jet seed 0 = source seed := by
  simp only [jet, kernelJet, iteratedDeriv_zero, source]

theorem jet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    HasDerivAt (jet seed order) (jet seed (order + 1) time) time := by
  have generated := (kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp)) (original_locallyIntegrable seed) time
  simpa only [jet, kernelJet, iteratedDeriv_succ] using generated

theorem source_iteratedDeriv (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) :
    iteratedDeriv order (source seed) = jet seed order := by
  induction order with
  | zero => rw [iteratedDeriv_zero, jet_zero]
  | succ order previous =>
      rw [iteratedDeriv_succ, previous]
      funext time
      exact (jet_hasDerivAt seed order time).deriv

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) : ℝ :=
  (∫ time : ℝ, ‖kernelJet order time‖) * NativeUnifiedCompleteSource.budget seed

theorem jet_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    ‖jet seed order time‖ ≤ budget seed order := by
  change ‖∫ shift : ℝ, kernelJet order shift • NativeUnifiedCompleteSource.source seed (time - shift)‖ ≤ _
  have dominated : ∀ shift : ℝ,
      ‖kernelJet order shift • NativeUnifiedCompleteSource.source seed (time - shift)‖ ≤
        ‖kernelJet order shift‖ * NativeUnifiedCompleteSource.budget seed := by
    intro shift
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed (time - shift)) (norm_nonneg _)
  have bounded := norm_integral_le_of_norm_le
    ((kernelJet_integrable order).norm.mul_const (NativeUnifiedCompleteSource.budget seed)) (Eventually.of_forall dominated)
  rwa [integral_mul_const] at bounded

theorem source_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set ℝ} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (source seed)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (source seed)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (budget seed order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have bounded : ∀ᵐ time ∂volume.restrict domain, ‖iteratedFDeriv ℝ order (source seed) time‖ ≤ budget seed order := by
    filter_upwards with time
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, source_iteratedDeriv]
    exact jet_bound seed order time
  have continuous := (source_smooth seed).continuous_iteratedFDeriv (m := order)
    (WithTop.coe_le_coe.mpr le_top)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable.restrict (budget seed order) bounded,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bounded⟩

theorem jet_next (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    jet seed order (response.2.clockAdvance + time) = jet response.1 order time := by
  change (∫ shift : ℝ, kernelJet order shift • NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time - shift)) =
    ∫ shift : ℝ, kernelJet order shift • NativeUnifiedCompleteSource.source response.1 (time - shift)
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernelJet order shift = 0
  · simp only [zero, zero_smul]
  · rw [add_sub_assoc, NativeUnifiedCompleteSource.source_generated_next seed response generated (time - shift)
      (by linarith [kernelJet_nonpositive order shift zero])]

end
end SaturationMonoid.NavierStokes.NativeForwardWindowJets
