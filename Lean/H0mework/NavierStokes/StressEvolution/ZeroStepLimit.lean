import H0mework.NavierStokes.StressDynamics.ZeroStepAction
import H0mework.NavierStokes.StressWholeH1.Approximation

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeResolventZeroLimit

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeResolventCompactness NativeWholeResolvent NativeWholeResolventLimit NativeOriginalResolventInput
open NativeWholeResolventZeroAction NativeNegativeFourMomentum NativeWholeH1Approximation

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem operator_recovers_input (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℕ → ℝ) (positive : ∀ index, 0 < step index) (vanishes : Tendsto step atTop (𝓝 0))
    (input : wholePhysical) :
    Tendsto (fun index => operator source pointLe node (step index) (positive index) input)
      atTop (𝓝 input) := by
  let value := fun index => (operator source pointLe node (step index) (positive index) input).1
  have bounded (index : ℕ) : ‖value index‖ ≤ ‖input.1‖ :=
    operator_norm_bound source pointLe node (step index) (positive index) input
  have embedded : Tendsto (fun index => embed (value index - input.1)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun index => embedded_error_bound source pointLe node (step index) (positive index) input)
    simpa only [zero_mul] using vanishes.mul_const (‖momentumOperator nu (meanInput source pointLe node).1‖ * ‖input‖)
  have rows (wave : Wave) : Tendsto (fun index => value index wave) atTop (𝓝 (input.1 wave)) := by
    have encoded := (lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.tendsto 0 |>.comp embedded
    have decoded := encoded.const_smul (integerWaveNormSq wave.1 ^ 2)
    simp only [map_zero, smul_zero] at decoded
    change Tendsto (fun index => integerWaveNormSq wave.1 ^ 2 •
      embed (value index - input.1) wave) atTop (𝓝 (0 : ComplexCoordinateEuclidean)) at decoded
    simp only [embed_reconstruct, lp.coeFn_sub, Pi.sub_apply] at decoded
    exact tendsto_sub_nhds_zero_iff.mp decoded
  have complex := NativeMixedActionLimit.inner_tendsto_of_rows value input.1 atTop ‖input.1‖ bounded rows input.1
  have real : Tendsto (fun index => inner ℝ (value index) input.1) atTop (𝓝 (‖input.1‖ ^ 2)) := by
    have converted := Complex.reCLM.continuous.tendsto _ |>.comp complex
    have realPair (index : ℕ) : inner ℝ (value index) input.1 = (inner ℂ input.1 (value index)).re := by
      rw [real_inner_comm, NativePhysicalPairing.physical_real_inner]
    simpa only [Function.comp_def, Complex.reCLM_apply, ← realPair,
      ← NativePhysicalPairing.physical_real_inner, real_inner_self_eq_norm_sq] using converted
  have normControl (index : ℕ) : ‖value index - input.1‖ ^ 2 ≤
      2 * ‖input.1‖ ^ 2 - 2 * inner ℝ (value index) input.1 := by
    rw [norm_sub_sq_real]
    have square := pow_le_pow_left₀ (norm_nonneg _) (bounded index) 2
    linarith
  have difference := normSquare_tendsto_zero (fun index => value index - input.1)
    (fun index => 2 * ‖input.1‖ ^ 2 - 2 * inner ℝ (value index) input.1) normControl
    (by
      have convergence := (tendsto_const_nhds (x := (2 : ℝ) * ‖input.1‖ ^ 2)).sub (real.const_mul (2 : ℝ))
      change Tendsto (fun index => 2 * ‖input.1‖ ^ 2 - 2 * inner ℝ (value index) input.1) atTop
        (𝓝 ((2 : ℝ) * ‖input.1‖ ^ 2 - 2 * ‖input.1‖ ^ 2)) at convergence
      rw [sub_self] at convergence
      exact convergence)
  exact tendsto_subtype_rng.mpr (tendsto_sub_nhds_zero_iff.mp difference)

end
end SaturationMonoid.NavierStokes.NativeWholeResolventZeroLimit
