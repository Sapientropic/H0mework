import H0mework.NavierStokes.StressDynamics.MixedActionLimit
import H0mework.NavierStokes.StressDynamics.ConvectionFlux

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeResolventEquation

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeResolventCompactness NativeSourceResolvent NativeResolventActionGraph NativeMixedActionLimit
open NativeConvectionFlux NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeEndpointVelocityCarrier NativeCofinalFluxPairing NativeNegativeFourMomentum
open NativeRecoveryTimeGramReadout NativeTimeJetCarrier NativeHigherTimeJets

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def mean (_stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) : State :=
  NativeRecoveryEscapeCarrier.endpoint receipt (physicalTime escape pointLe node)

theorem mean_rows (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (wave : Wave) :
    Tendsto (fun index => NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node wave)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (mean stress pointLe node wave)) := by
  have full := original_embedded_strong stress pointLe node
  have row := (lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.tendsto _ |>.comp full
  have read := row.const_smul (integerWaveNormSq wave.1 ^ 2)
  change Tendsto (fun index => integerWaveNormSq wave.1 ^ 2 •
    embed (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) wave)
    ((generated stress pointLe).refinement : Filter ℕ)
    (𝓝 (integerWaveNormSq wave.1 ^ 2 • embed (mean stress pointLe node) wave)) at read
  simpa only [embed_reconstruct] using read

theorem solved_whole (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    wholeVelocity (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) =
      (solve stress pointLe index node step positive.le).1 :=
  NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (physical_supported _ 0 (modes_zero stress index))

theorem acted_stress_row (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (wave : Wave) (inside : wave.1 ∈ modes stress index) :
    acted stress pointLe index node step positive.le wave = weightedRowCLM wave.1
      (projectedDivergenceCLM wave.1 (bilinearFlux
        (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)
        (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) •
          wholeVelocity (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) wave.1) := by
  have original := operator_stress_row (modes stress index) nu (advector stress pointLe index node)
    (solve stress pointLe index node step positive.le).1
    ((NativeRawStressAction.stage stress index).physical _ (sample stress pointLe index node).2).2.1
    (physical_supported _) (physical_transverse _) wave.1 inside wave.2
  have advectorRead : wholeBiotSavartVelocityState (advector stress pointLe index node) =
      wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) := by
    rw [← NativeRawStressAction.rawField_node stress pointLe index node,
      NativeRawStressAction.rawField, NativeRecoveryTimeGramAction.biotSavartCLM_apply]
    rfl
  rw [advectorRead, ← solved_whole stress pointLe index node step positive] at original
  conv_lhs at original => rw [solved_whole stress pointLe index node step positive]
  exact congrArg (weightedRowCLM wave.1) original

theorem acted_tendsto_mixed (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (target : State)
    (strong : Tendsto (fun index => NativeSourceResolvent.endpoint stress pointLe index node step positive.le)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target)) (wave : Wave) :
    Tendsto (fun index => acted stress pointLe index node step positive.le wave)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (weightedRowCLM wave.1
        (projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node) target wave.1) -
          (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity target wave.1))) := by
  have flux : Tendsto (fun index => bilinearFlux
      (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)
      (NativeSourceResolvent.endpoint stress pointLe index node step positive.le) wave.1)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (bilinearFlux (mean stress pointLe node) target wave.1)) := by
    apply tendsto_pi_nhds.mpr
    intro output
    apply tendsto_pi_nhds.mpr
    intro input
    exact flux_weak_strong _ _ _ _ _ ‖ledger.family.endpointReceipt.velocityEndpoint‖
      (fun index => velocity_norm_bound escape pointLe (stress.refinement index) node)
      (mean_rows stress pointLe node) strong wave.1 output input
  have row := (NativeEndpointVelocityCarrier.wholeVelocityCLM.continuous.tendsto _ |>.comp strong)
  have velocity := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave.1).continuous.tendsto _ |>.comp row
  have force := ((projectedDivergenceCLM wave.1).continuous.tendsto _ |>.comp flux).sub
    (velocity.const_smul (nu.coeff * integerWaveViscousMultiplier wave.1))
  have output := (weightedRowCLM wave.1).continuous.tendsto _ |>.comp force
  apply output.congr'
  have included : ∀ᶠ index in atTop, wave.1 ∈ modes stress index :=
    (escape.radius_tendsto.comp stress.refinement_strict.tendsto_atTop)
      (nonzero_integerWave_eventually_mem_puncturedFrequencyCube wave.1 wave.2)
  filter_upwards [included.filter_mono (generated stress pointLe).cofinal] with index inside
  exact (acted_stress_row stress pointLe index node step positive wave inside).symm

theorem source_equation_generated (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    ∃ target : State,
      Tendsto (fun index => NativeSourceResolvent.endpoint stress pointLe index node step positive.le)
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * step * nu.coeff) ∧
      ∀ wave : Wave, wholeVelocity target wave.1 - step •
        (projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node) target wave.1) -
          (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity target wave.1) =
        wholeVelocity (mean stress pointLe node) wave.1 := by
  obtain ⟨target, strong, paid, bounded, action⟩ := source_action_graph stress pointLe node step positive
  refine ⟨target, strong, paid, bounded, ?_⟩
  intro wave
  have source := (lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.tendsto _ |>.comp action
  have same := tendsto_nhds_unique source (acted_tendsto_mixed stress pointLe node step positive target strong wave)
  change step⁻¹ • (embed target wave - embed (mean stress pointLe node) wave) = weightedRowCLM wave.1 _ at same
  have read := congrArg (fun row : ComplexCoordinateEuclidean => integerWaveNormSq wave.1 ^ 2 • row) same
  rw [smul_comm, smul_sub, embed_reconstruct, embed_reconstruct] at read
  change step⁻¹ • (target wave - mean stress pointLe node wave) = _ at read
  have weightPaid : integerWaveNormSq wave.1 ^ 2 * weight wave.1 = 1 := by
    unfold weight
    rw [← mul_pow, mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne', one_pow]
  change _ = integerWaveNormSq wave.1 ^ 2 • (weight wave.1 • euclideanCoordinateRow _) at read
  rw [smul_smul, weightPaid, one_smul] at read
  have unscaled := congrArg (fun row : ComplexCoordinateEuclidean => step • row) read
  rw [smul_inv_smul₀ positive.ne'] at unscaled
  funext coordinate
  have coordinateRead := congrArg (fun row : ComplexCoordinateEuclidean => row coordinate) unscaled
  simp only [PiLp.sub_apply, PiLp.smul_apply, euclideanCoordinateRow_apply] at coordinateRead
  simp only [Pi.sub_apply, Pi.smul_apply, wholeVelocity_nonzero target wave,
    wholeVelocity_nonzero (mean stress pointLe node) wave] at coordinateRead ⊢
  linear_combination coordinateRead

end
end SaturationMonoid.NavierStokes.NativeResolventEquation
