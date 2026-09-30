import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedSourceActionFeed
import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedCofinalActionFeed
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryJointAction
import H0mework.Versions.X.NavierStokes.MacroAction.MacroMomentumIntegral

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedRootActionFeed

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
open NativeRecoveryUnifiedCurrent NativeRecoveryJointCurrent NativeRecoveryAEWindows NativeRecoveryEscapeStress
open NativeEndpointVelocityCarrier NativeTimeJetCarrier
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

variable {nu : Viscosity}

def ordinaryAction (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  NativeNegativeFourMomentum.actionState nu (NativeMacroMomentumIntegral.recoveryCurve (receipt initial) time)

/-- Eliminate the original joint-current branches. The caller supplies only
the original current and its physical time. -/
def interiorAction (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) : WholeRestartVelocityEndpointState := by
  classical
  exact if regular : time.1 ∈ regularSet (receipt initial) (terminal initial) then ordinaryAction initial time.1
    else NativeUnifiedSourceActionFeed.actionAt (sourceStress initial time.1 time.2 regular) (clock initial time).2.2 .anchor

theorem ordinaryAction_row (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : NonzeroIntegerWavevector) :
    ordinaryAction initial time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeMomentumIntegral.action nu (NativeMacroMomentumIntegral.recoveryCurve (receipt initial) time) wave.1) := rfl

theorem ordinaryAction_source (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) :
    NativeMomentumIntegral.action nu (NativeMacroMomentumIntegral.recoveryCurve (receipt initial) time.1) wave =
      NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeStressSource.quadraticFlux (velocity initial time.1) wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) • velocity initial time.1 wave := by
  unfold NativeMomentumIntegral.action NativeMomentumIntegral.row NativeMacroMomentumIntegral.recoveryCurve
  unfold NativeRecoveryRowAction.velocity
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (NativeRecoveryPhysical.wholeMild_zero _ _ _)]
  rfl

theorem interiorAction_row (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : NonzeroIntegerWavevector) :
    interiorAction initial time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeRecoveryJointCurrent.momentum initial time wave.1) := by
  classical
  by_cases regular : time.1 ∈ regularSet (receipt initial) (terminal initial)
  · rw [interiorAction, dif_pos regular, ordinaryAction_row, ordinaryAction_source,
      NativeRecoveryJointCurrent.momentum, stress_regular initial time regular]
  · rw [interiorAction, dif_neg regular, momentum_uncovered initial time regular]
    change NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeRecoveryTimeGramForce.momentum _ _ .anchor wave.1) = _
    exact congrArg (NativeNegativeFourMomentum.weightedRowCLM wave.1)
      (NativeRecoveryTimeGramForce.source_anchor_momentum (sourceStress initial time.1 time.2 regular)
        (clock initial time).2.2 wave.1)

def budget (initial : GeneratedWholeRestartCurrent nu) : ℝ := NativeUnifiedSourceActionFeed.budget (receipt initial)

theorem ordinaryAction_bound (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖ordinaryAction initial time‖ ≤ budget initial :=
  NativeNegativeFourMomentum.actionState_norm_le nu _ _ (NativeRecoveryEscapeCarrier.endpoint_norm_bound _)

theorem interiorAction_bound (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    ‖interiorAction initial time‖ ≤ budget initial := by
  classical
  by_cases regular : time.1 ∈ regularSet (receipt initial) (terminal initial)
  · rw [interiorAction, dif_pos regular]
    exact ordinaryAction_bound initial time.1
  · rw [interiorAction, dif_neg regular]
    exact NativeUnifiedSourceActionFeed.actionAt_bound _ _ _

theorem ordinaryAction_intervalIntegrable (initial : GeneratedWholeRestartCurrent nu) :
    IntervalIntegrable (ordinaryAction initial) volume 0 1 := by
  have coordinate (wave : NonzeroIntegerWavevector) : AEStronglyMeasurable
      (fun time => ordinaryAction initial time wave) (volume.restrict (Icc (0 : ℝ) 1)) := by
    simp only [ordinaryAction_row]
    exact (NativeNegativeFourMomentum.weightedRowCLM wave.1).continuous.comp_aestronglyMeasurable
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
        (NativeMacroMomentumIntegral.recovery_writes (receipt initial) wave.1).1).aestronglyMeasurable
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : WholeRestartVelocityEndpointState :=
    ∑ wave ∈ observed, lp.single 2 wave (ordinaryAction initial time wave)
  have measurable (observed : Finset NonzeroIntegerWavevector) :
      AEStronglyMeasurable (partialSum observed) (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  have whole : AEStronglyMeasurable (ordinaryAction initial) (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) measurable
    exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (ordinaryAction initial time)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  exact IntegrableOn.of_bound (isCompact_Icc.measure_lt_top (μ := volume)) whole (budget initial)
    (Eventually.of_forall (ordinaryAction_bound initial))

def action (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState := by
  classical
  exact if time = 0 then NativeUnifiedCofinalActionFeed.actionAt initial else
    if inside : time ∈ Ioo (0 : ℝ) (terminal initial) then interiorAction initial ⟨time, inside⟩
      else ordinaryAction initial time

theorem action_zero (initial : GeneratedWholeRestartCurrent nu) :
    action initial 0 = NativeUnifiedCofinalActionFeed.actionAt initial := by simp [action]

theorem action_at_time (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    action initial time.1 = interiorAction initial time := by
  simp only [action, if_neg time.2.1.ne', dif_pos time.2]

theorem action_ae_ordinary (initial : GeneratedWholeRestartCurrent nu) :
    action initial =ᵐ[volume] ordinaryAction initial := by
  classical
  have regular := (ae_restrict_iff' measurableSet_Ioo).mp
    (ae_regularSet (receipt initial) (terminal initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2)
  filter_upwards [regular, (volume : Measure ℝ).ae_ne 0] with time regular nonzero
  by_cases inside : time ∈ Ioo (0 : ℝ) (terminal initial)
  · rw [action, if_neg nonzero, dif_pos inside, interiorAction, dif_pos (regular inside)]
  · rw [action, if_neg nonzero, dif_neg inside]

theorem action_bound (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖action initial time‖ ≤ max (budget initial) (NativeUnifiedCofinalActionFeed.budget initial) := by
  classical
  by_cases zero : time = 0
  · rw [action, if_pos zero]
    exact (NativeUnifiedCofinalActionFeed.actionAt_norm_le initial).trans (le_max_right _ _)
  · rw [action, if_neg zero]
    split_ifs with inside
    · exact (interiorAction_bound initial ⟨time, inside⟩).trans (le_max_left _ _)
    · exact (ordinaryAction_bound initial time).trans (le_max_left _ _)

theorem source_action_read (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    NativeUnifiedCofinalActionFeed.read (action initial time.1) = NativeRecoveryJointCurrent.momentum initial time := by
  rw [action_at_time]
  funext wave
  by_cases nonzero : wave ≠ 0
  · funext coordinate
    change integerWaveNormSq wave ^ 2 • wholeVelocity (interiorAction initial time) wave coordinate = _
    rw [wholeVelocity_nonzero _ ⟨wave, nonzero⟩, interiorAction_row]
    change integerWaveNormSq wave ^ 2 • (NativeNegativeFourMomentum.weight wave •
      NativeRecoveryJointCurrent.momentum initial time wave coordinate) = _
    rw [NativeNegativeFourMomentum.weight, smul_smul, ← mul_pow,
      mul_inv_cancel₀ (integerWaveNormSq_pos nonzero).ne', one_pow, one_smul]
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [NativeUnifiedCofinalActionFeed.read, NativeRecoveryJointCurrent.momentum,
      NativeTimeJetCarrier.projectedDivergenceCLM_apply,
      transverseProjection, integerWaveViscousMultiplier, integerWaveNormSq]

theorem action_intervalIntegrable (initial : GeneratedWholeRestartCurrent nu) :
    IntervalIntegrable (action initial) volume 0 1 :=
  (ordinaryAction_intervalIntegrable initial).congr_ae (ae_restrict_of_ae (action_ae_ordinary initial).symm)

def state (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  NativeNegativeFourMomentum.embed (NativeMacroMomentumIntegral.recoveryCurve (receipt initial) time)

theorem source_integral (initial : GeneratedWholeRestartCurrent nu) (time : Icc (0 : ℝ) 1) :
    state initial time.1 - state initial 0 = ∫ actual in 0..time.1, action initial actual := by
  rw [intervalIntegral.integral_congr_ae ((action_ae_ordinary initial).mono fun _ same _ => same)]
  have integrable := (ordinaryAction_intervalIntegrable initial).mono_set
    (show uIcc (0 : ℝ) time.1 ⊆ uIcc 0 1 by
      rw [uIcc_of_le time.2.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl time.2.2)
  apply lp.ext
  funext wave
  change state initial time.1 wave - state initial 0 wave =
    (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
      (∫ actual in 0..time.1, ordinaryAction initial actual)
  rw [← (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).intervalIntegral_comp_comm integrable]
  change state initial time.1 wave - state initial 0 wave = ∫ actual in 0..time.1, ordinaryAction initial actual wave
  simp only [ordinaryAction_row]
  have rawIntegrable := ((NativeMacroMomentumIntegral.recovery_writes (receipt initial)).mono time.2.1 time.2.2 wave.1).1
  rw [(NativeNegativeFourMomentum.weightedRowCLM wave.1).intervalIntegral_comp_comm rawIntegrable]
  have write := (NativeMacroMomentumIntegral.recovery_writes (receipt initial) wave.1).2 time.1 time.2
  rw [← write, map_sub, NativeNegativeFourMomentum.weightedRowCLM_row,
    NativeNegativeFourMomentum.weightedRowCLM_row]
  rfl

def profile (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) : WholeRestartVelocityEndpointState :=
  action initial (canonicalTimeProjection point)

def generatedState (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) : WholeRestartVelocityEndpointState :=
  state initial 0 + canonicalTimePrimitive (profile initial) point

theorem generatedState_original (initial : GeneratedWholeRestartCurrent nu) (time : Icc (0 : ℝ) 1)
    (space : StageNineSpatialPoint) :
    generatedState initial (canonicalCauchySlicePoint time.1 space) = state initial time.1 := by
  simpa [generatedState, canonicalTimePrimitive, profile, add_comm] using
    (eq_add_of_sub_eq (source_integral initial time)).symm

theorem source_generated_next (initial : GeneratedWholeRestartCurrent nu) (space : StageNineSpatialPoint) :
    generatedState initial (canonicalCauchySlicePoint (terminal initial) space) =
      NativeNegativeFourMomentum.embed
        (puncturedWholeVelocityEuclideanState (NativeCofinalUnifiedField.target initial).initialState) := by
  change generatedState initial
    (canonicalCauchySlicePoint (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 space) = _
  rw [generatedState_original initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time,
    state, NativeMacroMomentumIntegral.recoveryCurve, NativeRecoveryRowAction.velocity,
    projIcc_of_mem zero_le_one (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2]
  apply congrArg NativeNegativeFourMomentum.embed
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  exact congrFun ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave.1).symm coordinate

end
end SaturationMonoid.NavierStokes.NativeUnifiedRootActionFeed
