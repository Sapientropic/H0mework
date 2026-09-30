import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramForce
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryTimeMomentumWrite
import H0mework.Versions.X.NavierStokes.MomentumAction.NegativeFourMomentum
import H0mework.Versions.X.NavierStokes.GlobalAction.GlobalHilbertAction
import H0mework.Versions.X.NavierStokes.MacroAction.FiniteMacroEvolution
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedSourceActionFeed

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramReadout NativeEndpointVelocityCarrier NativeStressSource NativeTimeJetCarrier
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

private theorem raw_stress (index : ℕ) (node : TimeNode) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (output input : Coordinate) :
    quadraticFlux (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node)) wave output input =
      -gram escape pointLe index (.inr (node, wave, output)) (.inr (node, 0, input)) := by
  change _ = -inner ℂ
    (NativeCofinalStressPositivity.shiftedComponent
      (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) (wave, output))
    (NativeCofinalStressPositivity.shiftedComponent
      (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) (0, input))
  rw [NativeCofinalStressPositivity.shiftedComponent_inner _ (velocity_reality escape pointLe index node),
    NativeCofinalFluxPairing.bilinearFlux_diagonal, sub_zero, neg_neg]

private theorem stress_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) :
    Tendsto (fun index => quadraticFlux
      (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)) wave)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (stressRead stress pointLe node wave)) := by
  apply tendsto_pi_nhds.mpr
  intro output
  apply tendsto_pi_nhds.mpr
  intro input
  simpa only [raw_stress, stressRead] using
    (pairing_tendsto stress pointLe (.inr (node, wave, output)) (.inr (node, 0, input))).neg

def budget (_receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) : ℝ :=
  NativeNegativeFourMomentum.actionBudget nu ‖ledger.family.endpointReceipt.velocityEndpoint‖

private def finiteAction (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (index : ℕ) : WholeRestartVelocityEndpointState :=
  NativeNegativeFourMomentum.actionState nu
    (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)

private theorem finiteAction_bound (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (index : ℕ) : ‖finiteAction stress pointLe node index‖ ≤ budget receipt :=
  NativeNegativeFourMomentum.actionState_norm_le nu _ _
    (velocity_norm_bound escape pointLe (stress.refinement index) node)

private theorem action_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) :
    Tendsto (fun index wave => finiteAction stress pointLe node index wave)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 fun wave : NonzeroIntegerWavevector => NativeNegativeFourMomentum.weightedRowCLM wave.1
        (NativeRecoveryTimeGramForce.momentum stress pointLe node wave.1)) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  have mean := (velocity_tendsto stress pointLe node wave.1).mono_left (generated stress pointLe).cofinal
  have same : receipt.wholePath (physicalTime escape pointLe node) wave.1 = velocityRead stress pointLe node wave.1 :=
    (funext (source_velocity stress pointLe node wave.1)).symm
  rw [same] at mean
  have force := ((projectedDivergenceCLM wave.1).continuous.tendsto _ |>.comp
    (stress_tendsto stress pointLe node wave.1)).sub
      (mean.const_smul (nu.coeff * integerWaveViscousMultiplier wave.1))
  simpa only [finiteAction, NativeNegativeFourMomentum.actionState_apply,
    NativeMomentumIntegral.action, NativeMomentumIntegral.row, NativeRecoveryTimeGramForce.momentum,
    Function.comp_def] using
    (NativeNegativeFourMomentum.weightedRowCLM wave.1).continuous.tendsto _ |>.comp force

/-- The complete stress action is realized in the same H⁻⁴ carrier by the
original finite actions and their existing kinetic bound. -/
def actionAt (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) :
    WholeRestartVelocityEndpointState :=
  ⟨fun wave => NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeRecoveryTimeGramForce.momentum stress pointLe node wave.1),
    lp.memℓp_of_tendsto
      (isBounded_iff_forall_norm_le.mpr ⟨budget receipt, by
        rintro _ ⟨index, rfl⟩
        exact finiteAction_bound stress pointLe node index⟩)
      (action_tendsto stress pointLe node)⟩

theorem actionAt_bound (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) :
    ‖actionAt stress pointLe node‖ ≤ budget receipt :=
  lp.norm_le_of_tendsto (Eventually.of_forall (finiteAction_bound stress pointLe node))
    (l := ((generated stress pointLe).refinement : Filter ℕ)) (action_tendsto stress pointLe node)

def action (stress : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) : WholeRestartVelocityEndpointState :=
  actionAt stress pointLe (.fixed (projIcc (0 : ℝ) 1 zero_le_one time))

theorem action_row (stress : StressAt escape) (pointLe : point ≤ 1)
    (time : ℝ) (wave : NonzeroIntegerWavevector) :
    action stress pointLe time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeRecoveryTimeMomentumWrite.action stress pointLe wave.1 time) := rfl

theorem action_intervalIntegrable (stress : StressAt escape) (pointLe : point ≤ 1) :
    IntervalIntegrable (action stress pointLe) volume 0 1 := by
  have coordinate (wave : NonzeroIntegerWavevector) : AEStronglyMeasurable
      (fun time => action stress pointLe time wave) (volume.restrict (Icc (0 : ℝ) 1)) := by
    simp only [action_row]
    exact (NativeNegativeFourMomentum.weightedRowCLM wave.1).continuous.comp_aestronglyMeasurable
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
        (NativeRecoveryTimeMomentumWrite.action_integrable stress pointLe wave.1)).aestronglyMeasurable
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : WholeRestartVelocityEndpointState :=
    ∑ wave ∈ observed, lp.single 2 wave (action stress pointLe time wave)
  have measurable (observed : Finset NonzeroIntegerWavevector) :
      AEStronglyMeasurable (partialSum observed) (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  have whole : AEStronglyMeasurable (action stress pointLe) (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) measurable
    exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (action stress pointLe time)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  exact IntegrableOn.of_bound (isCompact_Icc.measure_lt_top (μ := volume)) whole (budget receipt)
    (Eventually.of_forall fun time => actionAt_bound stress pointLe _)

def state (time : Icc (0 : ℝ) 1) : WholeRestartVelocityEndpointState :=
  NativeNegativeFourMomentum.embed (NativeRecoveryEscapeCarrier.endpoint receipt time)

theorem state_row (stress : StressAt escape) (pointLe : point ≤ 1)
    (time : Icc (0 : ℝ) 1) (wave : NonzeroIntegerWavevector) :
    state (receipt := receipt) time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (velocityRead stress pointLe (.fixed time) wave.1) := by
  rw [state, ← NativeNegativeFourMomentum.weightedRowCLM_row]
  congr 1
  rw [NativeMomentumIntegral.row, NativeRecoveryEscapeCarrier.endpoint,
    NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _ (NativeRecoveryPhysical.wholeMild_zero ledger receipt time)]
  exact (funext (source_velocity stress pointLe (.fixed time) wave.1)).symm

theorem source_integral (stress : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) :
    (∫ actual in 0..time.1, action stress pointLe actual) =
      state (receipt := receipt) time - state (receipt := receipt) ⟨0, le_rfl, zero_le_one⟩ := by
  have integrable := (action_intervalIntegrable stress pointLe).mono_set
    (show uIcc (0 : ℝ) time.1 ⊆ uIcc 0 1 by
      rw [uIcc_of_le time.2.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl time.2.2)
  apply lp.ext
  funext wave
  change (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
    (∫ actual in 0..time.1, action stress pointLe actual) =
      state (receipt := receipt) time wave - state (receipt := receipt) ⟨0, le_rfl, zero_le_one⟩ wave
  rw [← (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).intervalIntegral_comp_comm integrable]
  change (∫ actual in 0..time.1, action stress pointLe actual wave) =
    state (receipt := receipt) time wave - state (receipt := receipt) ⟨0, le_rfl, zero_le_one⟩ wave
  simp only [action_row, state_row stress pointLe]
  have rawIntegrable := (NativeRecoveryTimeMomentumWrite.action_integrable stress pointLe wave.1).mono_set
    (show uIcc (0 : ℝ) time.1 ⊆ uIcc 0 1 by
      rw [uIcc_of_le time.2.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl time.2.2)
  rw [(NativeNegativeFourMomentum.weightedRowCLM wave.1).intervalIntegral_comp_comm rawIntegrable,
    NativeRecoveryTimeMomentumWrite.source_integral, map_sub]

def profile (stress : StressAt escape) (pointLe : point ≤ 1) (point : BasePoint) : WholeRestartVelocityEndpointState :=
  action stress pointLe (canonicalTimeProjection point)

def generatedState (stress : StressAt escape) (pointLe : point ≤ 1) (point : BasePoint) : WholeRestartVelocityEndpointState :=
  state (receipt := receipt) ⟨0, le_rfl, zero_le_one⟩ + canonicalTimePrimitive (profile stress pointLe) point

theorem generatedState_original (stress : StressAt escape) (pointLe : point ≤ 1)
    (time : Icc (0 : ℝ) 1) (space : StageNineSpatialPoint) :
    generatedState stress pointLe (canonicalCauchySlicePoint time.1 space) = state (receipt := receipt) time := by
  simpa [generatedState, canonicalTimePrimitive, profile, add_comm] using
    (eq_add_of_sub_eq (source_integral stress pointLe time).symm).symm

theorem generatedState_velocity (stress : StressAt escape) (pointLe : point ≤ 1)
    (time : Icc (0 : ℝ) 1) (space : StageNineSpatialPoint) (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 ^ 2 •
        generatedState stress pointLe (canonicalCauchySlicePoint time.1 space) wave =
      NativeRecoveryEscapeCarrier.endpoint receipt time wave := by
  rw [generatedState_original, state, NativeNegativeFourMomentum.embed_reconstruct]

theorem actionAt_reconstruct (stress : StressAt escape) (pointLe : point ≤ 1)
    (node : TimeNode) (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 ^ 2 • actionAt stress pointLe node wave =
      euclideanCoordinateRow (NativeRecoveryTimeGramForce.momentum stress pointLe node wave.1) := by
  change integerWaveNormSq wave.1 ^ 2 • (NativeNegativeFourMomentum.weight wave.1 •
    euclideanCoordinateRow (NativeRecoveryTimeGramForce.momentum stress pointLe node wave.1)) = _
  rw [NativeNegativeFourMomentum.weight, smul_smul, ← mul_pow,
    mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne', one_pow, one_smul]

theorem source_anchor_action (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 ^ 2 • actionAt stress pointLe .anchor wave =
      euclideanCoordinateRow (NativeRecoveryEscapeMomentum.momentum stress pointLe wave.1) := by
  rw [actionAt_reconstruct, NativeRecoveryTimeGramForce.source_anchor_momentum]

theorem source_generated_next (initial : GeneratedWholeRestartCurrent nu) (anchor : ℝ)
    (inside : anchor ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : anchor ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (space : StageNineSpatialPoint) :
    let stress := sourceStress initial anchor inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    generatedState stress pointLe
        (canonicalCauchySlicePoint (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 space) =
      NativeNegativeFourMomentum.embed
        (puncturedWholeVelocityEuclideanState (NativeCofinalUnifiedField.target initial).initialState) := by
  dsimp only
  rw [generatedState_original, state]
  apply congrArg NativeNegativeFourMomentum.embed
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  exact congrFun ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave.1).symm coordinate

theorem global_source_write (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeGlobalHilbertAction.sourceState seed time = NativeGlobalHilbertAction.sourceState seed 0 +
      canonicalTimePrimitive
        (fun point => NativeGlobalHilbertAction.sourceAction seed (canonicalTimeProjection point))
        (canonicalCauchySlicePoint time 0) := by
  have write := NativeGlobalHilbertAction.source_integral_write seed 0 time le_rfl nonnegative
  simpa [canonicalTimePrimitive, add_comm] using eq_add_of_sub_eq write

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem global_generated_next {seed : GeneratedWholeRestartCurrent nu}
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeGlobalHilbertAction.sourceState seed 0 +
        canonicalTimePrimitive
          (fun point => NativeGlobalHilbertAction.sourceAction seed (canonicalTimeProjection point))
          (canonicalCauchySlicePoint (response.2.clockAdvance + time) 0) =
      NativeGlobalHilbertAction.sourceState response.1 0 +
        canonicalTimePrimitive
          (fun point => NativeGlobalHilbertAction.sourceAction response.1 (canonicalTimeProjection point))
          (canonicalCauchySlicePoint time 0) := by
  rw [← global_source_write seed (response.2.clockAdvance + time)
      (add_nonneg response.2.clockAdvance_pos.le nonnegative),
    ← global_source_write response.1 time nonnegative]
  unfold NativeGlobalHilbertAction.sourceState
  rw [NativeFiniteMacroEvolution.source_generated_next_evolution response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnifiedSourceActionFeed
