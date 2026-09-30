import H0mework.NavierStokes.StressWeakInput.PhysicalPairing
import H0mework.NavierStokes.StressWeakInput.FiniteAdjoint

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeResolventAdjoint

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent
open NativeWholeResolventLimit NativeResolventCompactness NativePhysicalPairing NativeResolventAdjoint

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def dualStage (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : wholePhysical →L[ℝ] wholePhysical :=
  (includeCLM (modes stress index) (modes_closed stress index)).comp
    ((physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (-advector stress pointLe index node) (negative_reality (advector_reality stress pointLe index node))
      step nonnegative).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index)))

theorem source_pairing (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) (value test : wholePhysical) :
    inner ℝ (physicalStage stress pointLe index node step nonnegative value) test =
      inner ℝ value (dualStage stress pointLe index node step nonnegative test) := by
  change inner ℝ (includeCLM (modes stress index) (modes_closed stress index)
    (physicalResolver _ _ _ nu _ _ step nonnegative (restrictCLM _ _ _ value))) test = _
  rw [include_inner _ (modes_zero stress index), resolver_adjoint]
  rw [real_inner_comm (dualStage stress pointLe index node step nonnegative test) value]
  change _ = inner ℝ (includeCLM (modes stress index) (modes_closed stress index)
    (physicalResolver _ _ _ nu _ _ step nonnegative (restrictCLM _ _ _ test))) value
  rw [include_inner _ (modes_zero stress index), pairing_symmetric]

theorem dualStage_eq_adjoint (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) :
    dualStage stress pointLe index node step nonnegative =
      (physicalStage stress pointLe index node step nonnegative).adjoint := by
  apply ContinuousLinearMap.ext
  intro test
  apply ext_inner_left ℝ
  intro value
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (source_pairing stress pointLe index node step nonnegative value test).symm

theorem dual_curl_budget (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    Summable (curlDensity (dualStage stress pointLe index node step positive.le value).1) ∧
      (∑' wave, curlDensity (dualStage stress pointLe index node step positive.le value).1 wave) ≤
        ‖value‖ ^ 2 / (2 * step * nu.coeff) := by
  let input := restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value
  let solved := physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (-advector stress pointLe index node) (negative_reality (advector_reality stress pointLe index node)) step positive.le input
  change Summable (curlDensity (puncturedEuclideanize solved.1)) ∧ _
  refine ⟨physical_curl_summable _ solved, ?_⟩
  change (∑' wave, curlDensity (puncturedEuclideanize solved.1) wave) ≤ _
  rw [physical_curl_sum _ (modes_zero stress index)]
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) positive) nu.coeff_pos)).mpr
  have balance := physicalResolver_balance (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (-advector stress pointLe index node) (negative_reality (advector_reality stress pointLe index node)) step positive.le input
  have loadPaid := restrict_energy (modes stress index) (modes_zero stress index) (modes_closed stress index) value
  change ‖coefficients (modes stress index) input‖ ≤ ‖value‖ at loadPaid
  change ‖coefficients (modes stress index) input‖ ^ 2 = ‖coefficients (modes stress index) solved‖ ^ 2 +
    ‖coefficients (modes stress index) (input - solved)‖ ^ 2 +
    2 * step * nu.coeff * curlPair (modes stress index) solved.1 solved.1 at balance
  nlinarith [sq_nonneg ‖coefficients (modes stress index) solved‖,
    sq_nonneg ‖coefficients (modes stress index) (input - solved)‖, norm_nonneg (coefficients (modes stress index) input)]

theorem adjoint_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    Tendsto (fun index => (physicalStage stress pointLe index node step positive.le).adjoint value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 ((operator stress pointLe node step positive).adjoint value)) := by
  obtain ⟨target, strong, _⟩ := exists_strong_limit_of_sum
    (fun index => (dualStage stress pointLe index node step positive.le value).1)
    (generated stress pointLe).refinement _
    (fun index => (dual_curl_budget stress pointLe index node step positive value).1)
    (fun index => (dual_curl_budget stress pointLe index node step positive value).2)
  have physical : target ∈ wholePhysical := wholePhysical_closed.mem_of_tendsto strong
    (Eventually.of_forall (fun index => (dualStage stress pointLe index node step positive.le value).2))
  let result : wholePhysical := ⟨target, physical⟩
  have full : Tendsto (fun index => dualStage stress pointLe index node step positive.le value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 result) := tendsto_subtype_rng.mpr strong
  have same : result = (operator stress pointLe node step positive).adjoint value := by
    apply ext_inner_left ℝ
    intro test
    have left : Tendsto (fun index => inner ℝ test (dualStage stress pointLe index node step positive.le value))
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (inner ℝ test result)) := tendsto_const_nhds.inner full
    have right : Tendsto (fun index => inner ℝ (physicalStage stress pointLe index node step positive.le test) value)
        ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℝ test ((operator stress pointLe node step positive).adjoint value))) := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact (operator_tendsto stress pointLe node step positive test).inner tendsto_const_nhds
    exact tendsto_nhds_unique left (right.congr' (Eventually.of_forall fun index =>
      source_pairing stress pointLe index node step positive.le test value))
  rw [same] at full
  simpa only [dualStage_eq_adjoint] using full

end
end SaturationMonoid.NavierStokes.NativeWholeResolventAdjoint
