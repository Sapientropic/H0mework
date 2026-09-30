import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedCompleteSource
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
open scoped Topology ENNReal Convolution ContDiff

namespace SaturationMonoid.NavierStokes.NativeForwardWindowSource

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction

noncomputable section

def bump : ContDiffBump (-3 / 2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def kernel : ℝ → ℝ := bump.normed volume

theorem kernel_smooth : ContDiff ℝ ∞ kernel := bump.contDiff_normed
theorem kernel_compact : HasCompactSupport kernel := bump.hasCompactSupport_normed
theorem kernel_integrable : Integrable kernel := bump.integrable_normed
theorem kernel_nonnegative (time : ℝ) : 0 ≤ kernel time := bump.nonneg_normed time
theorem kernel_mass : ∫ time, kernel time = 1 := bump.integral_normed

theorem kernel_support (time : ℝ) (nonzero : kernel time ≠ 0) : time < -1 := by
  have inside : time ∈ Metric.ball (-3 / 2 : ℝ) (1 / 2) := by
    have member : time ∈ Function.support (bump.normed volume) := nonzero
    rw [bump.support_normed_eq] at member
    exact member
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at inside
  linarith [inside.2]

variable {nu : Viscosity}

def source (seed : GeneratedWholeRestartCurrent nu) : ℝ → FullSpace :=
  kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ] NativeUnifiedCompleteSource.source seed

theorem source_integrand (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    source seed time = ∫ shift : ℝ, kernel shift • NativeUnifiedCompleteSource.source seed (time - shift) := rfl

theorem original_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) :
    LocallyIntegrable (NativeUnifiedCompleteSource.source seed) :=
  (NativeUnifiedCompleteSource.source_Linfty seed).locallyIntegrable le_top

theorem source_smooth (seed : GeneratedWholeRestartCurrent nu) : ContDiff ℝ ∞ (source seed) :=
  kernel_compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    kernel_smooth (original_locallyIntegrable seed)

theorem source_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Integrable (fun shift : ℝ => kernel shift • NativeUnifiedCompleteSource.source seed (time - shift)) :=
  kernel_compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    kernel_smooth.continuous (original_locallyIntegrable seed) time

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖source seed time‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  rw [source_integrand]
  have dominated : ∀ shift : ℝ,
      ‖kernel shift • NativeUnifiedCompleteSource.source seed (time - shift)‖ ≤
        kernel shift * NativeUnifiedCompleteSource.budget seed := by
    intro shift
    rw [norm_smul, Real.norm_of_nonneg (kernel_nonnegative shift)]
    exact mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed (time - shift))
      (kernel_nonnegative shift)
  have bounded := norm_integral_le_of_norm_le
    (kernel_integrable.mul_const (NativeUnifiedCompleteSource.budget seed)) (Eventually.of_forall dominated)
  rwa [integral_mul_const, kernel_mass, one_mul] at bounded

theorem source_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed (response.2.clockAdvance + time) = source response.1 time := by
  rw [source_integrand, source_integrand]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernel shift = 0
  · simp only [zero, zero_smul]
  · rw [add_sub_assoc, NativeUnifiedCompleteSource.source_generated_next seed response generated (time - shift)
      (by linarith [kernel_support shift zero])]

end
end SaturationMonoid.NavierStokes.NativeForwardWindowSource
