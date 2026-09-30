import H0mework.Versions.X.NavierStokes.StressNegativeOne.Rate

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalNegativeOneWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeOriginalResolventInput NativeWholeH1Pairing NativeResolventCompactness
open NativeNegativeOneInclusion NativeOriginalNegativeOneRate
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def action (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) : State :=
  rate source pointLe (projIcc (0 : ℝ) 1 zero_le_one time)

private theorem common_measure : commonTimeMeasure 1 =
    Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

theorem action_intervalIntegrable (source : StressAt escape) (pointLe : point ≤ 1) :
    IntervalIntegrable (action source pointLe) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc, ← common_measure]
  simpa only [action, Function.comp_def, projIcc_val] using rate_integrable source pointLe

theorem lower_action_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time : ℝ, time ∈ Icc (0 : ℝ) 1 →
      lowerCLM (action source pointLe time) = NativeUnifiedSourceActionFeed.action source pointLe time := by
  apply (ae_restrict_iff' measurableSet_Icc).mp
  rw [ae_restrict_iff_subtype measurableSet_Icc, ← common_measure]
  filter_upwards [lower_rate_ae source pointLe] with time same
  simpa only [action, projIcc_val, NativeUnifiedSourceActionFeed.action] using same

def state (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) : State :=
  inverseGradient (meanInput source pointLe (.fixed time)).1

theorem lower_state (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) :
    lowerCLM (state source pointLe time) = NativeUnifiedSourceActionFeed.state (receipt := receipt) time :=
  lower_inverseGradient _

theorem source_integral (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) :
    (∫ actual in 0..time.1, action source pointLe actual) =
      state source pointLe time - state source pointLe ⟨0, le_rfl, zero_le_one⟩ := by
  have integrable := (action_intervalIntegrable source pointLe).mono_set
    (show uIcc (0 : ℝ) time.1 ⊆ uIcc 0 1 by
      rw [uIcc_of_le time.2.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl time.2.2)
  apply lower_injective
  rw [← lowerCLM.intervalIntegral_comp_comm integrable, map_sub, lower_state, lower_state]
  rw [show (∫ actual in 0..time.1, lowerCLM (action source pointLe actual)) =
      ∫ actual in 0..time.1, NativeUnifiedSourceActionFeed.action source pointLe actual by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [lower_action_ae source pointLe] with actual same
    intro inside
    rw [uIoc_of_le time.2.1] at inside
    exact same ⟨inside.1.le, inside.2.trans time.2.2⟩]
  exact NativeUnifiedSourceActionFeed.source_integral source pointLe time

def profile (source : StressAt escape) (pointLe : point ≤ 1) (point : BasePoint) : State :=
  action source pointLe (canonicalTimeProjection point)

def generatedState (source : StressAt escape) (pointLe : point ≤ 1) (point : BasePoint) : State :=
  state source pointLe ⟨0, le_rfl, zero_le_one⟩ + canonicalTimePrimitive (profile source pointLe) point

theorem generatedState_original (source : StressAt escape) (pointLe : point ≤ 1)
    (time : Icc (0 : ℝ) 1) (space : StageNineSpatialPoint) :
    generatedState source pointLe (canonicalCauchySlicePoint time.1 space) = state source pointLe time := by
  simpa [generatedState, canonicalTimePrimitive, profile, add_comm] using
    (eq_add_of_sub_eq (source_integral source pointLe time).symm).symm

theorem source_generated_next (initial : GeneratedWholeRestartCurrent nu) (anchor : ℝ)
    (inside : anchor ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : anchor ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (space : StageNineSpatialPoint) :
    let source := sourceStress initial anchor inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    generatedState source pointLe
        (canonicalCauchySlicePoint (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 space) =
      inverseGradient (puncturedWholeVelocityEuclideanState (NativeCofinalUnifiedField.target initial).initialState) := by
  dsimp only
  apply lower_injective
  rw [generatedState_original, lower_state, lower_inverseGradient]
  rw [← NativeUnifiedSourceActionFeed.generatedState_original _ _ _ space]
  exact NativeUnifiedSourceActionFeed.source_generated_next initial anchor inside uncovered space

end
end SaturationMonoid.NavierStokes.NativeOriginalNegativeOneWrite
