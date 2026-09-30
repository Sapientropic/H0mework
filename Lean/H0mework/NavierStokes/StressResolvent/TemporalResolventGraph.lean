import H0mework.NavierStokes.StressResolvent.TemporalResolvent
import H0mework.NavierStokes.UnifiedAction.UnifiedSourceActionFeed

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeTemporalResolventGraph

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeFiniteActionResolvent NativeCommonAdvectorAction NativeRawStressAction
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeRecoveryTimeGramAction
open NativeTemporalResolvent NativeResolventActionGraph

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem initial_velocity (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) :
    NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed zeroTime) =
      wholeRestartVelocityEndpointGalerkinInitialVelocity
        (NativeRecoveryEscapeCarrier.radius escape (stress.refinement index)) ledger.family.endpointReceipt.velocityEndpoint := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  change biotSavartVelocityCoefficient wave.1 ((stage stress index).trajectory 0 wave.1) coordinate = _
  rw [(stage stress index).initial]
  exact (congrFun (wholeRestartVelocityEndpointGalerkinInitialVelocity_eq_biotSavart _ _
    ledger.family.endpointReceipt.velocityEndpoint_transverse wave) coordinate).symm

theorem initial_strong (stress : StressAt escape) (pointLe : point ≤ 1) :
    Tendsto (fun index => NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed zeroTime))
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 ledger.family.endpointReceipt.velocityEndpoint) := by
  simp_rw [initial_velocity]
  exact ((wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto _).comp
    (escape.radius_tendsto.comp stress.refinement_strict.tendsto_atTop)).mono_left (generated stress pointLe).cofinal

def advancedAction (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) : State :=
  puncturedEuclideanize (sourceOperator stress index last.1 (advance stress pointLe index last).1)

theorem advance_action_eq (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) (positive : 0 < last.1) :
    advancedAction stress pointLe index last = last.1⁻¹ •
      (advancedEndpoint stress pointLe index last -
        NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed zeroTime)) := by
  let A := physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index (.fixed last)) (advector_reality stress pointLe index (.fixed last))
  have written := resolver_write A (pairing (modes stress index)) (pairing_faithful _)
    (physicalOperator_dissipative _ _ _ _ _ _) last.1 last.2.1 (load stress pointLe index (.fixed zeroTime))
  have raw := congrArg (fun value : physicalSpace (modes stress index) => value.1) written
  change (advance stress pointLe index last).1 - last.1 •
    sourceOperator stress index last.1 (advance stress pointLe index last).1 = rawField stress index 0 at raw
  have euclidean := congrArg (puncturedEuclideanizeCLM.restrictScalars ℝ) raw
  rw [map_sub, map_smul] at euclidean
  have whole : puncturedEuclideanize (rawField stress index 0) =
      NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed zeroTime) := by
    rw [rawField, biotSavartCLM_apply]
    rfl
  change advancedEndpoint stress pointLe index last - last.1 • advancedAction stress pointLe index last =
    puncturedEuclideanize (rawField stress index 0) at euclidean
  rw [whole] at euclidean
  have difference : advancedEndpoint stress pointLe index last -
      NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed zeroTime) =
        last.1 • advancedAction stress pointLe index last := by rw [← euclidean]; abel
  rw [difference, inv_smul_smul₀ positive.ne']

def correction (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) : State :=
  puncturedEuclideanize (transition stress pointLe index last (workRemainder stress pointLe index last)).1

theorem correction_eq (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (last : Icc (0 : ℝ) 1) :
    correction stress pointLe index last =
      NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed last) -
        advancedEndpoint stress pointLe index last := by
  have source := congrArg (fun value : physicalSpace (modes stress index) => value.1)
    (transition_reconstructs stress pointLe index last)
  have mapped := congrArg puncturedEuclideanizeCLM source
  rw [Submodule.coe_add, map_add] at mapped
  have read : puncturedEuclideanize (load stress pointLe index (.fixed last)).1 =
      NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed last) := by
    change puncturedEuclideanize (rawField stress index last.1) = _
    rw [rawField, biotSavartCLM_apply]
    rfl
  change advancedEndpoint stress pointLe index last + correction stress pointLe index last =
    puncturedEuclideanize (load stress pointLe index (.fixed last)).1 at mapped
  rw [read] at mapped
  rw [← mapped]
  abel

theorem source_temporal_graph (stress : StressAt escape) (pointLe : point ≤ 1)
    (last : Icc (0 : ℝ) 1) (positive : 0 < last.1) :
    ∃ target : State,
      Tendsto (fun index => advancedEndpoint stress pointLe index last)
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * last.1 * nu.coeff) ∧
      Tendsto (fun index => advancedAction stress pointLe index last)
        ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (last.1⁻¹ • (target - ledger.family.endpointReceipt.velocityEndpoint))) ∧
      Tendsto (fun index => NativeNegativeFourMomentum.embed (correction stress pointLe index last))
        ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (NativeNegativeFourMomentum.embed (NativeRecoveryEscapeCarrier.endpoint receipt last) -
          NativeNegativeFourMomentum.embed target)) := by
  obtain ⟨target, strong, paid, bounded⟩ := advance_strong_limit stress pointLe last positive
  refine ⟨target, strong, paid, bounded, ?_, ?_⟩
  · have actual := (strong.sub (initial_strong stress pointLe)).const_smul last.1⁻¹
    exact actual.congr' (Eventually.of_forall fun index => (advance_action_eq stress pointLe index last positive).symm)
  · have actual := (original_embedded_strong stress pointLe (.fixed last)).sub
      (NativeNegativeFourMomentum.embed.continuous.tendsto _ |>.comp strong)
    simpa only [correction_eq, map_sub, Function.comp_def, NativeRecoveryTimeGramReadout.physicalTime] using actual

end
end SaturationMonoid.NavierStokes.NativeTemporalResolventGraph
