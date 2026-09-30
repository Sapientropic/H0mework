import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramRaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeStrongRefinement

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryEscapeCarrier
open NativeRecoveryTimeGramRaw NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem wholeState_eq_original (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (time : Icc (0 : ℝ) 1) :
    generatedVelocityEndpointGalerkinWholeState ledger (radius escape index) time =
      wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index (.fixed time)) := by
  apply lp.ext
  funext wave
  rw [generatedVelocityEndpointGalerkinWholeState_apply]
  unfold NativeRecoveryTimeGramRaw.velocity
  rw [wholeVelocity_punctured]
  by_cases inside : wave ∈ wholeRestartModes (radius escape index)
  · simp only [inside, if_pos]
    rfl
  · simp only [inside]
    have zero := ((ledger.family.stage (radius escape index)).physical time.1 time.2).2.1 wave inside
    change 0 = biotSavartVelocityCoefficient wave
      ((ledger.family.stage (radius escape index)).trajectory time.1 wave)
    rw [zero]
    simp

theorem source_path_tendsto (stress : StressAt escape) :
    Tendsto (fun index => generatedVelocityEndpointGalerkinSpaceTimePath ledger (radius escape (stress.refinement index)))
      atTop (𝓝 receipt.core.stateLimit) := by
  exact receipt.core.state_tendsto.comp
    ((escape.extraction_strict.tendsto_atTop.comp (tendsto_atTop_mono escape.index_ge tendsto_id)).comp
      stress.refinement_strict.tendsto_atTop)

structure StrongRefinement (stress : StressAt escape) (pointLe : point ≤ 1) where
  index : ℕ → ℕ
  strict : StrictMono index
  converges : ∀ᵐ time ∂commonTimeMeasure 1,
    Tendsto (fun n => wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement (index n)) (.fixed time)))
      atTop (𝓝 (receipt.wholePath time))

def generated (stress : StressAt escape) (pointLe : point ≤ 1) : StrongRefinement stress pointLe := Classical.choice (by
  obtain ⟨index, strict, strong⟩ := (tendstoInMeasure_of_tendsto_Lp (source_path_tendsto stress)).exists_seq_tendsto_ae
  refine ⟨⟨index, strict, ?_⟩⟩
  have raw : ∀ᵐ time ∂commonTimeMeasure 1, ∀ n : ℕ,
      generatedVelocityEndpointGalerkinSpaceTimePath ledger (radius escape (stress.refinement (index n))) time =
        generatedVelocityEndpointGalerkinWholeState ledger (radius escape (stress.refinement (index n))) time := by
    apply ae_all_iff.mpr
    intro n
    exact BoundedContinuousFunction.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeBoundedPath ledger (radius escape (stress.refinement (index n))))
  filter_upwards [strong, raw, receipt.stateLimit_ae] with time source raw same
  rw [← same] at source
  apply source.congr'
  exact Eventually.of_forall fun n => (raw n).trans (wholeState_eq_original escape pointLe _ time))

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeStrongRefinement
