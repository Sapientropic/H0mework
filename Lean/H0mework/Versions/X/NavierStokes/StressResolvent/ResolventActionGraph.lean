import H0mework.Versions.X.NavierStokes.StressResolvent.SourceResolvent
import H0mework.Versions.X.NavierStokes.MomentumAction.NegativeFourMomentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeResolventActionGraph

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeResolventCompactness NativeSourceResolvent NativeNegativeFourMomentum
open NativeRecoveryTimeGramReadout NativeEndpointVelocityCarrier

noncomputable section

theorem embedded_curl_budget (value : State) (radius : ℝ) (bounded : ‖value‖ ≤ radius) :
    CurlBudget (embed value) ((2 * Real.pi) ^ 2 * radius ^ 2) := by
  have row (wave : Wave) : curlDensity (embed value) wave ≤ (2 * Real.pi) ^ 2 * ‖value wave‖ ^ 2 := by
    have scale : integerWaveViscousMultiplier wave.1 * weight wave.1 ^ 2 =
        (2 * Real.pi) ^ 2 * (integerWaveNormSq wave.1)⁻¹ ^ 3 := by
      unfold integerWaveViscousMultiplier weight
      field_simp
    have inverse : 0 ≤ (integerWaveNormSq wave.1)⁻¹ := inv_nonneg.mpr (integerWaveNormSq_nonneg _)
    have small : (integerWaveNormSq wave.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_integerWaveNormSq wave.1 wave.2)
    have cubed : (integerWaveNormSq wave.1)⁻¹ ^ 3 ≤ 1 := pow_le_one₀ inverse small
    rw [curlDensity, embed_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← mul_assoc, scale]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (sq_nonneg _) cubed) (sq_nonneg _)
  intro frequencies
  have finite := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) value frequencies
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at finite
  calc
    _ ≤ ∑ wave ∈ frequencies, (2 * Real.pi) ^ 2 * ‖value wave‖ ^ 2 := Finset.sum_le_sum fun wave _ => row wave
    _ = (2 * Real.pi) ^ 2 * ∑ wave ∈ frequencies, ‖value wave‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite.trans (pow_le_pow_left₀ (norm_nonneg _) bounded 2)) (sq_nonneg _)

theorem embedded_strong_of_rows (family : ℕ → State) (target : State) (f : Filter ℕ)
    (radius : ℝ) (bounded : ∀ index, ‖family index‖ ≤ radius) (targetBound : ‖target‖ ≤ radius)
    (rows : ∀ wave, Tendsto (fun index => family index wave) f (𝓝 (target wave))) :
    Tendsto (fun index => embed (family index)) f (𝓝 (embed target)) := by
  apply strong_of_rows _ _ f ((2 * Real.pi) ^ 2 * radius ^ 2)
    (fun index => embedded_curl_budget _ radius (bounded index)) (embedded_curl_budget _ radius targetBound)
  intro wave
  exact (rows wave).const_smul (weight wave.1)

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem original_embedded_strong (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) :
    Tendsto (fun index => embed (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node))
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (embed (NativeRecoveryEscapeCarrier.endpoint receipt (physicalTime escape pointLe node)))) := by
  apply embedded_strong_of_rows _ _ _ ‖ledger.family.endpointReceipt.velocityEndpoint‖
    (fun index => velocity_norm_bound escape pointLe (stress.refinement index) node)
    (NativeRecoveryEscapeCarrier.endpoint_norm_bound _)
  intro wave
  have source := (velocity_tendsto stress pointLe node wave.1).mono_left (generated stress pointLe).cofinal
  have converted := (PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Coordinate => ℂ)).tendsto _ |>.comp source
  have row (value : State) : WithLp.toLp 2 (wholeVelocity value wave.1) = value wave := by
    apply PiLp.ext
    intro coordinate
    exact wholeVelocity_nonzero value wave coordinate
  change Tendsto (fun index => NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node wave)
    ((generated stress pointLe).refinement : Filter ℕ)
    (𝓝 (WithLp.toLp 2 (receipt.wholePath (physicalTime escape pointLe node) wave.1)))
  simpa only [Function.comp_def, row] using converted

def acted (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : State :=
  embed (puncturedEuclideanize (NativeCommonAdvectorAction.sourceOperator stress index
    (sample stress pointLe index node).1 (solve stress pointLe index node step nonnegative).1))

theorem acted_eq (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    acted stress pointLe index node step positive.le = step⁻¹ •
      (embed (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) -
        embed (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)) := by
  have original := source_equation stress pointLe index node step positive.le
  have written := congrArg
    (embed.comp (puncturedEuclideanizeCLM.restrictScalars ℝ)) original
  rw [map_sub, map_smul] at written
  have source := NativeRawStressAction.rawField_node stress pointLe index node
  rw [sample, source] at written
  have same (value : State) : puncturedEuclideanize (wholeVelocity value) = value := by
    apply lp.ext
    funext wave
    apply PiLp.ext
    intro coordinate
    exact wholeVelocity_nonzero value wave coordinate
  change embed (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) -
    step • acted stress pointLe index node step positive.le =
      embed (puncturedEuclideanize (wholeVelocity
        (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node))) at written
  rw [same] at written
  have scaled : step • acted stress pointLe index node step positive.le =
      embed (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) -
        embed (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) := by
    rw [← written]
    abel
  rw [← scaled, inv_smul_smul₀ positive.ne']

theorem source_action_graph (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    ∃ target : State,
      Tendsto (fun index => NativeSourceResolvent.endpoint stress pointLe index node step positive.le)
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * step * nu.coeff) ∧
      Tendsto (fun index => acted stress pointLe index node step positive.le)
        ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (step⁻¹ • (embed target -
          embed (NativeRecoveryEscapeCarrier.endpoint receipt (physicalTime escape pointLe node))))) := by
  obtain ⟨target, strong, paid, bounded⟩ := source_strong_limit stress pointLe node step positive
  refine ⟨target, strong, paid, bounded, ?_⟩
  have action := ((embed.continuous.tendsto _ |>.comp strong).sub (original_embedded_strong stress pointLe node)).const_smul step⁻¹
  exact action.congr' (Eventually.of_forall fun index => (acted_eq stress pointLe index node step positive).symm)

end
end SaturationMonoid.NavierStokes.NativeResolventActionGraph
