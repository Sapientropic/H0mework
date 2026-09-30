import H0mework.NavierStokes.VelocityEndpoint.WholeMildReadWrite
import H0mework.NavierStokes.SourceReadout.Action
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryNonlinear

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinNonlinearSpaceTimePassage
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

theorem galerkin_state_ae (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) (radius : ℕ) :
    (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius) =ᵐ[commonTimeMeasure 1]
      generatedVelocityEndpointGalerkinWholeState ledger radius :=
  BoundedContinuousFunction.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure 1) ℂ
    (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius)

theorem galerkin_nonlinear_ae (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (wave : IntegerWavevector) :
    (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath ledger radius wave) =ᵐ[commonTimeMeasure 1]
      fun time => wholeStateVelocityNonlinearCoefficientAt (generatedVelocityEndpointGalerkinWholeState ledger radius time) wave :=
  BoundedContinuousFunction.coeFn_toLp (p := (1 : ℝ≥0∞)) (μ := commonTimeMeasure 1) ℂ
    (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath ledger radius wave)

theorem core_nonlinearLimit_eq_source (core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (wave : IntegerWavevector) :
    core.nonlinearLimit wave =ᵐ[commonTimeMeasure 1]
      fun time => wholeStateVelocityNonlinearCoefficientAt (core.stateLimit time) wave := by
  obtain ⟨stateSequence, stateMono, stateAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp core.state_tendsto).exists_seq_tendsto_ae
  obtain ⟨nonlinearSequence, nonlinearMono, nonlinearAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((core.nonlinear_tendsto wave).comp stateMono.tendsto_atTop)).exists_seq_tendsto_ae
  have stateRead := ae_all_iff.mpr (fun radius => galerkin_state_ae ledger radius)
  have nonlinearRead := ae_all_iff.mpr (fun radius => galerkin_nonlinear_ae ledger radius wave)
  filter_upwards [stateAE, nonlinearAE, stateRead, nonlinearRead, core.transverse_ae]
    with time stateAt nonlinearAt stateOriginal nonlinearOriginal transverse
  have actualState : Tendsto (fun index => generatedVelocityEndpointGalerkinWholeState ledger
        (core.subsequence (stateSequence (nonlinearSequence index))) time) atTop (𝓝 (core.stateLimit time)) := by
    apply (stateAt.comp nonlinearMono.tendsto_atTop).congr'
    exact Eventually.of_forall fun index => stateOriginal (core.subsequence (stateSequence (nonlinearSequence index)))
  have actualNonlinear : Tendsto (fun index => wholeStateVelocityNonlinearCoefficientAt
      (generatedVelocityEndpointGalerkinWholeState ledger
        (core.subsequence (stateSequence (nonlinearSequence index))) time) wave)
      atTop (𝓝 (core.nonlinearLimit wave time)) := by
    apply nonlinearAt.congr'
    exact Eventually.of_forall fun index => nonlinearOriginal (core.subsequence (stateSequence (nonlinearSequence index)))
  have source := tendsto_wholeStateVelocityNonlinearCoefficientAt _ (core.stateLimit time)
    (fun index => generatedVelocityEndpointGalerkinWholeStateAtTime_transverse ledger
      (core.subsequence (stateSequence (nonlinearSequence index))) time.1)
    transverse actualState wave
  exact tendsto_nhds_unique actualNonlinear source

theorem core_nonlinearLimit_eq_source_all (core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger) :
    ∀ᵐ time ∂commonTimeMeasure 1, ∀ wave : IntegerWavevector,
      core.nonlinearLimit wave time = wholeStateVelocityNonlinearCoefficientAt (core.stateLimit time) wave :=
  ae_all_iff.mpr (fun wave => core_nonlinearLimit_eq_source core wave)

theorem wholeMild_nonlinearLimit_eq_source (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) :
    ∀ᵐ time ∂commonTimeMeasure 1, ∀ wave : IntegerWavevector,
      receipt.core.nonlinearLimit wave time = wholeStateVelocityNonlinearCoefficientAt (receipt.wholePath time) wave := by
  filter_upwards [core_nonlinearLimit_eq_source_all receipt.core, receipt.stateLimit_ae] with time source same wave
  rw [same]
  exact source wave

theorem wholeMild_nonlinear_integrable (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) :
    Integrable (fun time => wholeStateVelocityNonlinearCoefficientAt (receipt.wholePath time) wave) (commonTimeMeasure 1) := by
  apply memLp_one_iff_integrable.mp
  have same : receipt.core.nonlinearLimit wave =ᵐ[commonTimeMeasure 1]
      fun time => wholeStateVelocityNonlinearCoefficientAt (receipt.wholePath time) wave := by
    filter_upwards [wholeMild_nonlinearLimit_eq_source receipt] with time source
    exact source wave
  exact (memLp_congr_ae same).mp (Lp.memLp (receipt.core.nonlinearLimit wave))

theorem wholeMild_lerayLimit_eq_source (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) :
    wholeVelocityLerayProjectionSpaceTime wave (receipt.core.nonlinearLimit wave) =ᵐ[commonTimeMeasure 1]
      fun time => transverseProjection wave (wholeStateVelocityNonlinearCoefficientAt (receipt.wholePath time) wave) := by
  have projected := (transverseProjectionCLM wave).coeFn_compLpL (receipt.core.nonlinearLimit wave)
  filter_upwards [projected, wholeMild_nonlinearLimit_eq_source receipt] with time projection source
  change ((transverseProjectionCLM wave).compLpL 1 (commonTimeMeasure 1) (receipt.core.nonlinearLimit wave)) time = _
  rw [projection, source wave]
  rfl

theorem wholeMild_lerayLimit_eq_flux (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) :
    wholeVelocityLerayProjectionSpaceTime wave (receipt.core.nonlinearLimit wave) =ᵐ[commonTimeMeasure 1]
      fun time => transverseProjection wave
        (nativeFluidStressDivergenceCoefficient (NativeStressSource.quadraticFlux (receipt.wholePath time)) wave) := by
  filter_upwards [wholeMild_lerayLimit_eq_source receipt wave, receipt.core.transverse_ae, receipt.stateLimit_ae]
    with time same transverse state
  have actualTransverse : WholeStateTransverse (receipt.wholePath time) := state.symm ▸ transverse
  rw [same, NativeStressSource.quadraticFlux_divergence _ actualTransverse wave]

end
end SaturationMonoid.NavierStokes.NativeRecoveryNonlinear
