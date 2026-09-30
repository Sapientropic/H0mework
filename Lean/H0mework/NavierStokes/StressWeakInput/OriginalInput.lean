import H0mework.NavierStokes.StressWeakInput.WholeAdjoint
import H0mework.NavierStokes.StressWeakInput.MovingPairing
import H0mework.NavierStokes.StressResolvent.WholeResolventEquation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalResolventInput

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeFiniteActionResolvent NativeWholeResolvent NativeWholeResolventLimit
open NativeResolventCompactness NativePhysicalPairing NativeWholeResolventAdjoint NativeWeakMovingPairing
open NativeEndpointVelocityCarrier NativeResolventEquation NativeRawStressAction

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem weak_moving_input (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (input : ℕ → wholePhysical) (target : wholePhysical) (cap : ℝ)
    (bounded : ∀ index, ‖input index‖ ≤ cap)
    (weak : ∀ test : wholePhysical, Tendsto (fun index => inner ℝ (input index) test)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (inner ℝ target test))) :
    Tendsto (fun index => physicalStage stress pointLe index node step positive.le (input index))
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (operator stress pointLe node step positive target)) := by
  have budget (index : ℕ) :
      Summable (curlDensity (physicalStage stress pointLe index node step positive.le (input index)).1) ∧
        (∑' wave, curlDensity (physicalStage stress pointLe index node step positive.le (input index)).1 wave) ≤
          cap ^ 2 / (2 * step * nu.coeff) := by
    have paid := stage_curl_budget stress pointLe index node step positive (input index)
    refine ⟨paid.1, paid.2.trans ?_⟩
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (bounded index) 2)
      (mul_pos (mul_pos (by norm_num) positive) nu.coeff_pos).le
  obtain ⟨candidate, strong, _⟩ := exists_strong_limit_of_sum
    (fun index => (physicalStage stress pointLe index node step positive.le (input index)).1)
    (generated stress pointLe).refinement _ (fun index => (budget index).1) (fun index => (budget index).2)
  have physical : candidate ∈ wholePhysical := wholePhysical_closed.mem_of_tendsto strong
    (Eventually.of_forall fun index => (physicalStage stress pointLe index node step positive.le (input index)).2)
  let result : wholePhysical := ⟨candidate, physical⟩
  have full : Tendsto (fun index => physicalStage stress pointLe index node step positive.le (input index))
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 result) := tendsto_subtype_rng.mpr strong
  have same : result = operator stress pointLe node step positive target := by
    apply ext_inner_right ℝ
    intro test
    have original := adjoint_output_test ((generated stress pointLe).refinement : Filter ℕ)
      input target cap bounded weak (fun index => physicalStage stress pointLe index node step positive.le)
      (operator stress pointLe node step positive) test (adjoint_tendsto stress pointLe node step positive test)
    exact tendsto_nhds_unique (full.inner tendsto_const_nhds) original
  rwa [same] at full

def originalInput (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) : wholePhysical := by
  refine ⟨NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node, ?_,
    velocity_reality escape pointLe (stress.refinement index) node⟩
  intro wave
  exact complexWavevector_dot_biotSavartVelocityCoefficient wave.1 _

def meanInput (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) : wholePhysical :=
  ⟨mean stress pointLe node, fun wave => NativeRecoveryPhysical.wholeMild_transverse ledger receipt
    (NativeRecoveryTimeGramReadout.physicalTime escape pointLe node) wave.1,
    NativeRecoveryEscapeCarrier.endpoint_reality _⟩

theorem original_weak (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (test : wholePhysical) :
    Tendsto (fun index => inner ℝ (originalInput stress pointLe index node) test)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (inner ℝ (meanInput stress pointLe node) test)) := by
  have complex := NativeMixedActionLimit.inner_tendsto_of_rows _ _ _ ‖ledger.family.endpointReceipt.velocityEndpoint‖
    (fun index => velocity_norm_bound escape pointLe (stress.refinement index) node)
    (mean_rows stress pointLe node) test.1
  have real := Complex.reCLM.continuous.tendsto _ |>.comp complex
  change Tendsto (fun index => (inner ℂ test.1
    (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)).re)
    ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (inner ℂ test.1 (mean stress pointLe node)).re) at real
  simp only [← physical_real_inner] at real
  rw [real_inner_comm (mean stress pointLe node) test.1] at real
  exact real.congr' (Eventually.of_forall fun index =>
    real_inner_comm (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) test.1)

theorem original_restriction (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index)
      (originalInput stress pointLe index node) = load stress pointLe index node := by
  apply Subtype.ext
  change complexSharpSupportProjection (modes stress index) (wholeVelocity
    (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)) =
      (load stress pointLe index node).1
  have raw := rawField_node stress pointLe index node
  rw [← raw]
  exact complexSharpSupportProjection_eq_self_of_supported _ (load stress pointLe index node).1
    (physical_supported _)

theorem original_stage (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    (physicalStage stress pointLe index node step positive.le (originalInput stress pointLe index node)).1 =
      NativeSourceResolvent.endpoint stress pointLe index node step positive.le := by
  change puncturedEuclideanize (physicalResolver _ _ _ nu _ _ step positive.le
    (restrictCLM _ _ _ (originalInput stress pointLe index node))).1 = _
  rw [original_restriction]
  rfl

/-- The original weak source load is resolved by the already generated whole operator. -/
theorem source_original_strong (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    Tendsto (fun index => NativeSourceResolvent.endpoint stress pointLe index node step positive.le)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (operator stress pointLe node step positive (meanInput stress pointLe node)).1) := by
  have actual := tendsto_subtype_rng.mp (weak_moving_input stress pointLe node step positive
    (fun index => originalInput stress pointLe index node) (meanInput stress pointLe node)
    ‖ledger.family.endpointReceipt.velocityEndpoint‖
    (fun index => velocity_norm_bound escape pointLe (stress.refinement index) node) (original_weak stress pointLe node))
  exact actual.congr' (Eventually.of_forall fun index => original_stage stress pointLe index node step positive)

end
end SaturationMonoid.NavierStokes.NativeOriginalResolventInput
