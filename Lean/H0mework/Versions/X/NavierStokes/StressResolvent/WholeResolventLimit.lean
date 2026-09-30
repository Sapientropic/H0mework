import H0mework.Versions.X.NavierStokes.StressResolvent.WholeResolvent
import H0mework.NavierStokes.StressDynamics.StrongOperatorLimit
import H0mework.Versions.X.NavierStokes.StressResolvent.TemporalResolventNext

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeResolventLimit

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeResolventCompactness NativeWholeResolvent
open NativeEndpointVelocityCarrier NativeSourceResolvent NativeRawStressAction
open NativeFiniteActionResolvent
open NativeTemporalResolvent NativeTemporalResolventGraph

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def physicalStage (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : wholePhysical →L[ℝ] wholePhysical :=
  (stageOperator stress pointLe index node step nonnegative).codRestrict wholePhysical
    (stage_physical stress pointLe index node step nonnegative)

theorem physicalStage_contractive (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : ‖physicalStage stress pointLe index node step nonnegative‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  change ‖stageOperator stress pointLe index node step nonnegative value‖ ≤ 1 * ‖value‖
  simpa only [one_mul] using stage_bound stress pointLe index node step nonnegative value

theorem physical_pointwise (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    ∃ target : wholePhysical, Tendsto (fun index => physicalStage stress pointLe index node step positive.le value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) := by
  obtain ⟨target, converges, _⟩ := source_pointwise stress pointLe node step positive value
  have physical : target ∈ wholePhysical := wholePhysical_closed.mem_of_tendsto converges
    (Eventually.of_forall (fun index => stage_physical stress pointLe index node step positive.le value))
  exact ⟨⟨target, physical⟩, tendsto_subtype_rng.mpr converges⟩

def operator (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) : wholePhysical →L[ℝ] wholePhysical :=
  NativeStrongOperatorLimit.limitOperator ((generated stress pointLe).refinement : Filter ℕ)
    (fun index => physicalStage stress pointLe index node step positive.le)
    (fun index => physicalStage_contractive stress pointLe index node step positive.le)
    (physical_pointwise stress pointLe node step positive)

theorem operator_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    Tendsto (fun index => physicalStage stress pointLe index node step positive.le value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (operator stress pointLe node step positive value)) :=
  NativeStrongOperatorLimit.limitOperator_tendsto _ _ _ _ value

theorem operator_norm (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) : ‖operator stress pointLe node step positive‖ ≤ 1 :=
  NativeStrongOperatorLimit.limitOperator_norm _ _ _ _

theorem operator_curl (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    Summable (curlDensity (operator stress pointLe node step positive value).1) ∧
      (∑' wave, curlDensity (operator stress pointLe node step positive value).1 wave) ≤
        ‖value‖ ^ 2 / (2 * step * nu.coeff) := by
  obtain ⟨target, converges, paid⟩ := source_pointwise stress pointLe node step positive value
  have same : (operator stress pointLe node step positive value).1 = target :=
    tendsto_nhds_unique (tendsto_subtype_rng.mp (operator_tendsto stress pointLe node step positive value)) converges
  rw [same]
  exact paid

theorem moving_input (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) {input : ℕ → wholePhysical} {target : wholePhysical}
    (actual : Tendsto input ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target)) :
    Tendsto (fun index => physicalStage stress pointLe index node step positive.le (input index))
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (operator stress pointLe node step positive target)) :=
  NativeStrongOperatorLimit.moving_load _ _ _ _ actual

theorem repeated_action (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (order : ℕ) (value : wholePhysical) :
    Tendsto (fun index => (physicalStage stress pointLe index node step positive.le)^[order] value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 ((operator stress pointLe node step positive)^[order] value)) := by
  induction order with
  | zero => exact tendsto_const_nhds
  | succ order ih =>
      simpa only [Function.iterate_succ_apply'] using moving_input stress pointLe node step positive ih

def initialInput (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) : wholePhysical :=
  ⟨ledger.family.endpointReceipt.velocityEndpoint, ledger.family.endpointReceipt.velocityEndpoint_transverse,
    ledger.family.endpointReceipt.velocityEndpoint_reality⟩

theorem restrict_initial (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) :
    restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) (initialInput ledger) =
      load stress pointLe index (.fixed zeroTime) := by
  apply Subtype.ext
  change complexSharpSupportProjection (modes stress index) (wholeVelocity ledger.family.endpointReceipt.velocityEndpoint) =
    rawField stress index 0
  have raw := rawField_node stress pointLe index (.fixed zeroTime)
  change rawField stress index 0 = _ at raw
  rw [raw, initial_velocity stress pointLe index]
  apply lp.ext
  funext wave coordinate
  by_cases zero : wave = 0
  · subst wave
    simp
  · rw [complexSharpSupportProjection_apply, wholeVelocity_nonzero _ ⟨wave, zero⟩,
      wholeRestartVelocityEndpointGalerkinInitialVelocity_apply]
    change (if wave ∈ modes stress index then wholeVelocity ledger.family.endpointReceipt.velocityEndpoint wave else 0) coordinate =
      (if wave ∈ modes stress index then ledger.family.endpointReceipt.velocityEndpoint ⟨wave, zero⟩ else 0) coordinate
    by_cases included : wave ∈ modes stress index
    · rw [if_pos included, if_pos included]
      exact wholeVelocity_nonzero _ ⟨wave, zero⟩ coordinate
    · rw [if_neg included, if_neg included]
      rfl

theorem advance_as_operator (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) (positive : 0 < last.1) :
    (physicalStage stress pointLe index (.fixed last) last.1 positive.le (initialInput ledger)).1 =
      advancedEndpoint stress pointLe index last := by
  change puncturedEuclideanize (physicalResolver _ _ _ nu _ _ last.1 positive.le
    (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) (initialInput ledger))).1 = _
  rw [restrict_initial stress pointLe index]
  rfl

theorem advance_operator_tendsto (stress : StressAt escape) (pointLe : point ≤ 1)
    (last : Icc (0 : ℝ) 1) (positive : 0 < last.1) :
    Tendsto (fun index => advancedEndpoint stress pointLe index last)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (operator stress pointLe (.fixed last) last.1 positive (initialInput ledger)).1) := by
  have original := tendsto_subtype_rng.mp
    (operator_tendsto stress pointLe (.fixed last) last.1 positive (initialInput ledger))
  exact original.congr' (Eventually.of_forall fun index => advance_as_operator stress pointLe index last positive)

theorem operator_generated_next (initial : GeneratedWholeRestartCurrent nu) (anchor : ℝ)
    (inside : anchor ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : anchor ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) :
    let stress := sourceStress initial anchor inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    let last := (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
    let resolved := operator stress pointLe (.fixed last) last.1
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos
      (initialInput (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial))
    Tendsto (fun index => NativeNegativeFourMomentum.embed (correction stress pointLe index last))
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (NativeNegativeFourMomentum.embed (puncturedWholeVelocityEuclideanState
        (NativeCofinalUnifiedField.target initial).initialState) - NativeNegativeFourMomentum.embed resolved.1)) := by
  dsimp only
  obtain ⟨target, strong, _, _, _, corrected⟩ :=
    NativeTemporalResolventNext.source_generated_next_graph initial anchor inside uncovered
  have same := tendsto_nhds_unique strong (advance_operator_tendsto (sourceStress initial anchor inside uncovered)
    (inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos)
  rw [same] at corrected
  exact corrected

end
end SaturationMonoid.NavierStokes.NativeWholeResolventLimit
