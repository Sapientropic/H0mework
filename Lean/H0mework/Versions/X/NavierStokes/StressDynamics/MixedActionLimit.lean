import H0mework.Versions.X.NavierStokes.StressResolvent.ResolventActionGraph
import H0mework.Versions.X.NavierStokes.CofinalReadout.FluxPairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeMixedActionLimit

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeCofinalFluxPairing NativeEndpointVelocityCarrier
open NativeHigherTimeJets

noncomputable section

theorem inner_tendsto_of_rows (family : ℕ → State) (target : State) (f : Filter ℕ)
    (radius : ℝ) (bounded : ∀ index, ‖family index‖ ≤ radius)
    (rows : ∀ wave, Tendsto (fun index => family index wave) f (𝓝 (target wave))) (test : State) :
    Tendsto (fun index => inner ℂ test (family index)) f (𝓝 (inner ℂ test target)) := by
  have radiusNonnegative : 0 ≤ radius := (norm_nonneg _).trans (bounded 0)
  rw [Metric.tendsto_nhds]
  intro epsilon positive
  let cap := radius + ‖target‖ + 1
  have capPositive : 0 < cap := by dsimp [cap]; positivity
  obtain ⟨frequencies, close⟩ :=
    (Metric.tendsto_nhds.mp (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) test)
      (epsilon / (2 * cap)) (by positivity)).exists
  let part : State := ∑ wave ∈ frequencies, lp.single 2 wave (test wave)
  have small : ‖test - part‖ < epsilon / (2 * cap) := by
    rw [dist_eq_norm] at close
    change ‖part - test‖ < epsilon / (2 * cap) at close
    rwa [norm_sub_rev part test] at close
  have finite : Tendsto (fun index => inner ℂ part (family index)) f (𝓝 (inner ℂ part target)) := by
    simpa only [part, sum_inner, lp.inner_single_left] using
      tendsto_finsetSum frequencies (fun wave _ => tendsto_const_nhds.inner (rows wave))
  filter_upwards [Metric.tendsto_nhds.mp finite (epsilon / 2) (by positivity)] with index middle
  rw [dist_eq_norm] at middle ⊢
  have triangle : ‖inner ℂ test (family index) - inner ℂ test target‖ ≤
      ‖test - part‖ * radius + ‖inner ℂ part (family index) - inner ℂ part target‖ +
        ‖test - part‖ * ‖target‖ := by
    have tail := norm_inner_le_norm (𝕜 := ℂ) (part - test) target
    rw [norm_sub_rev part test] at tail
    calc
      _ = ‖inner ℂ (test - part) (family index) +
          (inner ℂ part (family index) - inner ℂ part target) + inner ℂ (part - test) target‖ := by
        congr 1
        simp only [inner_sub_left]
        abel
      _ ≤ ‖inner ℂ (test - part) (family index)‖ +
          ‖inner ℂ part (family index) - inner ℂ part target‖ + ‖inner ℂ (part - test) target‖ := norm_add₃_le ..
      _ ≤ _ := add_le_add
        (add_le_add ((norm_inner_le_norm (𝕜 := ℂ) (test - part) (family index)).trans
          (mul_le_mul_of_nonneg_left (bounded index) (norm_nonneg _))) le_rfl)
        tail
  have scaled := (lt_div_iff₀ (mul_pos (by norm_num) capPositive)).mp small
  dsimp only [cap] at scaled
  nlinarith [norm_nonneg (test - part)]

theorem flux_weak_strong (left right : ℕ → State) (mean target : State) (f : Filter ℕ)
    (radius : ℝ) (bounded : ∀ index, ‖left index‖ ≤ radius)
    (rows : ∀ wave, Tendsto (fun index => left index wave) f (𝓝 (mean wave)))
    (strong : Tendsto right f (𝓝 target)) (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => bilinearFlux (left index) (right index) wave output input) f
      (𝓝 (bilinearFlux mean target wave output input)) := by
  have radiusNonnegative : 0 ≤ radius := (norm_nonneg _).trans (bounded 0)
  have fixed := (inner_tendsto_of_rows left mean f radius bounded rows (fluxTest target wave output input)).neg
  simp only [← bilinearFlux_eq_inner] at fixed
  have errorBound (index : ℕ) :
      ‖bilinearFlux (left index) (right index - target) wave output input‖ ≤
        (3 * radius) * ‖right index - target‖ := by
    have actual := mixedFlux_norm_le (wholeVelocity (left index)) (wholeVelocity (right index - target)) wave output input
    change ‖bilinearFlux (left index) (right index - target) wave output input‖ ≤ _ at actual
    apply actual.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left ((wholeVelocity_norm_le _).trans (bounded index)) (by norm_num))
      (wholeVelocity_norm_le _) (norm_nonneg _) (by positivity : 0 ≤ 3 * radius)
  have zero : Tendsto (fun index => bilinearFlux (left index) (right index - target) wave output input) f (𝓝 0) := by
    apply squeeze_zero_norm (fun index => errorBound index)
    simpa only [sub_self, norm_zero, mul_zero] using ((strong.sub_const target).norm.const_mul (3 * radius))
  have sum := zero.add fixed
  simpa only [bilinearFlux_sub_right, sub_add_cancel, zero_add] using sum

end
end SaturationMonoid.NavierStokes.NativeMixedActionLimit
