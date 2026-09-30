import H0mework.NavierStokes.StressResolvent.TemporalResolventGraph

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeTemporalResolventNext

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeRecoveryEscapeStress NativeRecoveryJointTimeKernel NativeResolventCompactness
open NativeTemporalResolvent NativeTemporalResolventGraph

noncomputable section

theorem source_generated_next_graph {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (anchor : ℝ)
    (inside : anchor ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : anchor ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) :
    let stress := sourceStress initial anchor inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    let last := (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
    ∃ target : State,
      Tendsto (fun index => advancedEndpoint stress pointLe index last)
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint‖ ^ 2 / (2 * last.1 * nu.coeff) ∧
      Tendsto (fun index => advancedAction stress pointLe index last)
        ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (last.1⁻¹ • (target - (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint))) ∧
      Tendsto (fun index => NativeNegativeFourMomentum.embed (correction stress pointLe index last))
        ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (NativeNegativeFourMomentum.embed (puncturedWholeVelocityEuclideanState
          (NativeCofinalUnifiedField.target initial).initialState) - NativeNegativeFourMomentum.embed target)) := by
  dsimp only
  have next : NativeRecoveryEscapeCarrier.endpoint (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time =
      puncturedWholeVelocityEuclideanState (NativeCofinalUnifiedField.target initial).initialState := by
    apply lp.ext
    funext wave
    apply PiLp.ext
    intro coordinate
    exact congrFun ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave.1).symm coordinate
  have actual := source_temporal_graph (sourceStress initial anchor inside uncovered)
    (inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos
  rw [next] at actual
  exact actual

end
end SaturationMonoid.NavierStokes.NativeTemporalResolventNext
