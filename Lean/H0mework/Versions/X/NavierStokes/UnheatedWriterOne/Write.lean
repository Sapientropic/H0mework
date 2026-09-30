import H0mework.Versions.X.NavierStokes.UnheatedWriterOne.Rate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedGlobalNegativeOne

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeResolventCompactness NativeWholeH1Pairing NativeNegativeOneInclusion

noncomputable section
variable {nu : Viscosity}

def state (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State :=
  inverseGradient (NativeUnifiedCompleteSource.source seed time).fst

theorem lower_state (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    lowerCLM (state seed time) = NativeGlobalHilbertAction.sourceState seed time := by
  rw [state, lower_inverseGradient, NativeUnifiedCompleteSource.velocity_read]
  rfl

theorem rate_intervalIntegrable (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) : IntervalIntegrable (rate seed) volume a b := by
  have paid : IntegrableOn (rate seed) (Icc 0 (max a b)) :=
    rate_integrable seed (max a b) (a_nonnegative.trans (le_max_left _ _))
  have restricted : IntegrableOn (rate seed) (uIcc a b) := paid.mono_set
    (fun _ inside => ⟨le_trans (le_min a_nonnegative b_nonnegative) inside.1, inside.2⟩)
  exact restricted.intervalIntegrable

theorem source_integral (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    state seed b - state seed a = ∫ time in a..b, rate seed time := by
  apply lower_injective
  rw [map_sub, lower_state, lower_state,
    ← lowerCLM.intervalIntegral_comp_comm (rate_intervalIntegrable seed a b a_nonnegative b_nonnegative),
    NativeUnifiedGlobalActionFeed.source_integral seed a b a_nonnegative b_nonnegative]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [lower_rate_ae seed] with time same
  intro inside
  have nonnegative : 0 ≤ time :=
    (le_min a_nonnegative b_nonnegative).trans (uIoc_subset_uIcc inside).1
  rw [same nonnegative, NativeUnifiedCompleteSource.source_momentum]

def primitive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State :=
  state seed 0 + ∫ actual in 0..time, rate seed actual

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed time = state seed time := by
  rw [primitive, ← source_integral seed 0 time le_rfl nonnegative]
  abel

theorem primitive_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∀ᵐ time : ℝ, time ∈ Icc 0 horizon → HasDerivAt (primitive seed) (rate seed time) time := by
  filter_upwards [(rate_intervalIntegrable seed 0 horizon le_rfl nonnegative).ae_hasDerivAt_integral] with time derivative
  intro inside
  have actual := derivative (by simpa only [uIcc_of_le nonnegative] using inside) 0 (by simp)
  exact actual.const_add (state seed 0)

theorem source_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (state seed) (rate seed time) time := by
  have every := eventually_countable_forall.mpr (fun horizon : ℕ =>
    primitive_hasDerivAt_ae seed horizon (Nat.cast_nonneg horizon))
  filter_upwards [every] with time all positive
  obtain ⟨horizon, bound⟩ := exists_nat_ge time
  apply (all horizon ⟨positive.le, bound⟩).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds positive] with actual inside
  exact (primitive_original seed actual inside.le).symm

theorem state_continuousOn (seed : GeneratedWholeRestartCurrent nu) : ContinuousOn (state seed) (Ici 0) := by
  intro time nonnegative
  change 0 ≤ time at nonnegative
  let horizon := time + 1
  have positiveHorizon : 0 ≤ horizon := by dsimp [horizon]; linarith [nonnegative]
  have primitiveContinuous := intervalIntegral.continuousOn_primitive_interval'
    (rate_intervalIntegrable seed 0 horizon le_rfl positiveHorizon) left_mem_uIcc
  rw [uIcc_of_le positiveHorizon] at primitiveContinuous
  have on : ContinuousOn (state seed) (Icc 0 horizon) := by
    apply ((continuousOn_const : ContinuousOn (fun _ : ℝ => state seed 0) (Icc 0 horizon)).add primitiveContinuous).congr
    intro actual inside
    simpa only [primitive, Pi.add_apply] using! (primitive_original seed actual inside.1).symm
  have eventually : Ici (0 : ℝ) =ᶠ[𝓝 time] Icc 0 horizon := by
    filter_upwards [eventually_lt_nhds (show time < horizon by dsimp [horizon]; linarith)] with actual below
    apply propext
    change 0 ≤ actual ↔ 0 ≤ actual ∧ actual ≤ horizon
    exact ⟨fun nonnegative => ⟨nonnegative, below.le⟩, fun inside => inside.1⟩
  exact (on time ⟨nonnegative, by dsimp [horizon]; linarith⟩).congr_set eventually.symm

theorem state_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    state seed (response.2.clockAdvance + time) = state response.1 time := by
  rw [state, NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]
  rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedGlobalNegativeOne
