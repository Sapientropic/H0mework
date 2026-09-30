import H0mework.Versions.X.NavierStokes.StressResolvent.WholeResolventLimit

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeResolventEquation

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeSourceResolvent NativeRawStressAction
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativeWholeResolventLimit
open NativeResolventEquation NativeMixedActionLimit NativeConvectionFlux NativeCofinalFluxPairing NativeTimeJetCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def inputProjection (stress : StressAt escape) (index : ℕ) (value : wholePhysical) : State :=
  puncturedEuclideanize (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value).1

theorem inputProjection_eq (stress : StressAt escape) (index : ℕ) (value : wholePhysical) :
    inputProjection stress index value = wholeRestartVelocityEndpointGalerkinInitialVelocity
      (NativeRecoveryEscapeCarrier.radius escape (stress.refinement index)) value.1 := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  change (complexSharpSupportProjection (modes stress index) (wholeVelocity value.1) wave.1) coordinate = _
  rw [complexSharpSupportProjection_apply, wholeRestartVelocityEndpointGalerkinInitialVelocity_apply]
  change (if wave.1 ∈ modes stress index then wholeVelocity value.1 wave.1 else 0) coordinate =
    (if wave.1 ∈ modes stress index then value.1 wave else 0) coordinate
  by_cases included : wave.1 ∈ modes stress index
  · rw [if_pos included, if_pos included]
    exact wholeVelocity_nonzero value.1 wave coordinate
  · rw [if_neg included, if_neg included]
    rfl

theorem inputProjection_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (value : wholePhysical) :
    Tendsto (fun index => inputProjection stress index value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 value.1) := by
  simp_rw [inputProjection_eq]
  exact ((wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto value.1).comp
    (escape.radius_tendsto.comp stress.refinement_strict.tendsto_atTop)).mono_left (generated stress pointLe).cofinal

def solved (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) (value : wholePhysical) : physicalSpace (modes stress index) :=
  physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative
    (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value)

theorem solved_whole (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) (value : wholePhysical) :
    wholeVelocity (stageOperator stress pointLe index node step nonnegative value) =
      (solved stress pointLe index node step nonnegative value).1 :=
  NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (physical_supported _ 0 (modes_zero stress index))

/-- The original generator acts on every solved full input before the refinement limit. -/
def actionAt (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) (value : wholePhysical) : State :=
  puncturedEuclideanize (sourceOperator stress index (sample stress pointLe index node).1
    (wholeVelocity (stageOperator stress pointLe index node step nonnegative value)))

theorem actionAt_eq (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    actionAt stress pointLe index node step positive.le value = step⁻¹ •
      (stageOperator stress pointLe index node step positive.le value - inputProjection stress index value) := by
  have original := resolver_write
    (physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index node) (advector_reality stress pointLe index node))
    (pairing (modes stress index)) (pairing_faithful _) (physicalOperator_dissipative _ _ _ _ _ _)
    step positive.le (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value)
  have raw := congrArg (fun field : physicalSpace (modes stress index) => field.1) original
  change (solved stress pointLe index node step positive.le value).1 -
    step • sourceOperator stress index (sample stress pointLe index node).1
      (solved stress pointLe index node step positive.le value).1 =
    (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value).1 at raw
  have written := congrArg (puncturedEuclideanizeCLM.restrictScalars ℝ) raw
  rw [map_sub, map_smul] at written
  have same := solved_whole stress pointLe index node step positive.le value
  change stageOperator stress pointLe index node step positive.le value - step •
    puncturedEuclideanize (sourceOperator stress index (sample stress pointLe index node).1
      (solved stress pointLe index node step positive.le value).1) = inputProjection stress index value at written
  rw [← same] at written
  change stageOperator stress pointLe index node step positive.le value -
    step • actionAt stress pointLe index node step positive.le value = inputProjection stress index value at written
  have scaled : step • actionAt stress pointLe index node step positive.le value =
      stageOperator stress pointLe index node step positive.le value - inputProjection stress index value := by
    rw [← written]
    abel
  rw [← scaled, inv_smul_smul₀ positive.ne']

theorem actionAt_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    Tendsto (fun index => actionAt stress pointLe index node step positive.le value)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (step⁻¹ • ((operator stress pointLe node step positive value).1 - value.1))) := by
  have resolved := tendsto_subtype_rng.mp (operator_tendsto stress pointLe node step positive value)
  have actual := (resolved.sub (inputProjection_tendsto stress pointLe value)).const_smul step⁻¹
  exact actual.congr' (Eventually.of_forall fun index => (actionAt_eq stress pointLe index node step positive value).symm)

theorem actionAt_row (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) (wave : Wave)
    (inside : wave.1 ∈ modes stress index) :
    wholeVelocity (actionAt stress pointLe index node step positive.le value) wave.1 =
      projectedDivergenceCLM wave.1 (bilinearFlux
        (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)
        (stageOperator stress pointLe index node step positive.le value) wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) •
        wholeVelocity (stageOperator stress pointLe index node step positive.le value) wave.1 := by
  have original := operator_stress_row (modes stress index) nu (advector stress pointLe index node)
    (solved stress pointLe index node step positive.le value).1
    ((NativeRawStressAction.stage stress index).physical _ (sample stress pointLe index node).2).2.1
    (physical_supported _) (physical_transverse _) wave.1 inside wave.2
  have advectorRead : wholeBiotSavartVelocityState (advector stress pointLe index node) =
      wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) := by
    rw [← rawField_node stress pointLe index node, rawField, NativeRecoveryTimeGramAction.biotSavartCLM_apply]
    rfl
  rw [advectorRead, ← solved_whole stress pointLe index node step positive.le value] at original
  change wholeVelocity (puncturedEuclideanize (frozenOperator (modes stress index) nu
    (advector stress pointLe index node)
    (wholeVelocity (stageOperator stress pointLe index node step positive.le value)))) wave.1 = _
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (operator_supported (modes stress index) nu (advector stress pointLe index node) _ 0 (modes_zero stress index))]
  exact original

theorem actionAt_mixed_limit (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) (wave : Wave) :
    Tendsto (fun index => wholeVelocity (actionAt stress pointLe index node step positive.le value) wave.1)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node)
        (operator stress pointLe node step positive value).1 wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) •
          wholeVelocity (operator stress pointLe node step positive value).1 wave.1)) := by
  have strong := tendsto_subtype_rng.mp (operator_tendsto stress pointLe node step positive value)
  have flux : Tendsto (fun index => bilinearFlux
      (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)
      (stageOperator stress pointLe index node step positive.le value) wave.1)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (bilinearFlux (mean stress pointLe node) (operator stress pointLe node step positive value).1 wave.1)) := by
    apply tendsto_pi_nhds.mpr
    intro output
    apply tendsto_pi_nhds.mpr
    intro input
    exact flux_weak_strong _ _ _ _ _ ‖ledger.family.endpointReceipt.velocityEndpoint‖
      (fun index => velocity_norm_bound escape pointLe (stress.refinement index) node)
      (mean_rows stress pointLe node) strong wave.1 output input
  have velocity := ((evaluation wave.1).comp wholeVelocityCLM).continuous.tendsto _ |>.comp strong
  have force := ((projectedDivergenceCLM wave.1).continuous.tendsto _ |>.comp flux).sub
    (velocity.const_smul (nu.coeff * integerWaveViscousMultiplier wave.1))
  apply force.congr'
  have included : ∀ᶠ index in atTop, wave.1 ∈ modes stress index :=
    (escape.radius_tendsto.comp stress.refinement_strict.tendsto_atTop)
      (nonzero_integerWave_eventually_mem_puncturedFrequencyCube wave.1 wave.2)
  filter_upwards [included.filter_mono (generated stress pointLe).cofinal] with index inside
  exact (actionAt_row stress pointLe index node step positive value wave inside).symm

/-- Every complete physical input satisfies the same original mixed resolvent equation. -/
theorem operator_equation (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) (wave : Wave) :
    wholeVelocity (operator stress pointLe node step positive value).1 wave.1 - step •
      (projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node)
        (operator stress pointLe node step positive value).1 wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) •
          wholeVelocity (operator stress pointLe node step positive value).1 wave.1) = wholeVelocity value.1 wave.1 := by
  have actual := ((evaluation wave.1).comp wholeVelocityCLM).continuous.tendsto _ |>.comp
    (actionAt_tendsto stress pointLe node step positive value)
  have same := tendsto_nhds_unique actual (actionAt_mixed_limit stress pointLe node step positive value wave)
  change wholeVelocityCLM (step⁻¹ • ((operator stress pointLe node step positive value).1 - value.1)) wave.1 = _ at same
  rw [map_smul, map_sub] at same
  have written := congrArg (fun row : ComplexCoordinateVector => step • row) same
  simp only [lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_inv_smul₀ positive.ne'] at written
  change wholeVelocity (operator stress pointLe node step positive value).1 wave.1 -
    wholeVelocity value.1 wave.1 = _ at written
  rw [← written]
  abel

end
end SaturationMonoid.NavierStokes.NativeWholeResolventEquation
