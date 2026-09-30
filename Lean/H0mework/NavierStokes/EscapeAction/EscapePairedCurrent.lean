import H0mework.NavierStokes.RecoveryAction.RecoveryCurrentAction
import H0mework.NavierStokes.EscapeAction.EscapeMomentum

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeEscapePairedCurrent

open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeRecoveryCoverage NativeRecoveryEscapeCarrier NativeRecoveryEscapeStress NativeRecoveryEscapeMomentum
open NativeEndpointVelocityCarrier NativePairedCurrentFourier NativeStressSource

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem actual_reality (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) :
    FiniteStateFourierReality (wholeBiotSavartVelocityState (state escape index)) := by
  have physical := (ledger.family.stage (radius escape index)).physical _ (sampleTime escape pointLe index).2
  exact NativePhysicalSource.velocity_reality _ physical.2.2.2

def actual (escape : SourceActionEscape receipt point) (index : ℕ) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  mFourierCoeff (fun place => (field (wholeBiotSavartVelocityState (state escape index)) direction place : ℂ)) wave

theorem actual_coefficient (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (direction : Fin 4) (wave : IntegerWavevector) :
    actual escape index direction wave = coefficient (wholeBiotSavartVelocityState (state escape index))
      (actualStress escape index) direction wave := by
  rw [actual, current_fourier _ (actual_reality escape pointLe index), actualStress_eq]

def inherited (stress : StressAt escape) (pointLe : point ≤ 1) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  coefficient (wholeVelocity (fixedEndpoint escape pointLe)) stress.stress direction wave

theorem inherited_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => actual escape (stress.refinement index) direction wave) atTop (𝓝 (inherited stress pointLe direction wave)) := by
  have rows : Tendsto (fun index => fun frequency =>
      wholeBiotSavartVelocityState (state escape (stress.refinement index)) frequency) atTop
        (𝓝 (fun frequency => wholeVelocity (fixedEndpoint escape pointLe) frequency)) := by
    apply tendsto_pi_nhds.mpr
    intro frequency
    rw [fixedEndpoint_reads_original]
    exact (velocity_row_tendsto escape pointLe frequency).comp stress.refinement_strict.tendsto_atTop
  have joint := rows.prodMk_nhds stress.stress_tendsto
  have original := (NativeCofinalPairedCurrent.coefficient_continuous direction wave).tendsto _ |>.comp joint
  apply original.congr'
  exact Eventually.of_forall fun index => (actual_coefficient escape pointLe (stress.refinement index) direction wave).symm

theorem inherited_spatial (stress : StressAt escape) (pointLe : point ≤ 1) (direction : Fin 3) (wave : IntegerWavevector) :
    inherited stress pointLe direction.succ wave = mFourierCoeff (fun place =>
      (field (receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩) direction.succ place : ℂ)) wave := by
  rw [spatial_fourier _ (NativeRecoveryPhysical.wholeMild_reality ledger receipt _) direction wave]
  change wholeVelocity (fixedEndpoint escape pointLe) wave direction = _
  rw [fixedEndpoint_reads_original]

theorem inherited_temporal_defect (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    inherited stress pointLe 0 wave - mFourierCoeff (fun place =>
      (field (receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩) 0 place : ℂ)) wave =
        -trace (defect stress pointLe) wave / 8 := by
  rw [temporal_fourier _ (NativeRecoveryPhysical.wholeMild_reality ledger receipt _)]
  change (baseline wave - trace stress.stress wave / 8) -
    (baseline wave - trace (quadraticFlux (receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩)) wave / 8) = _
  rw [← fixedEndpoint_reads_original escape pointLe]
  simp only [defect, trace, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem inherited_mean_defect (stress : StressAt escape) (pointLe : point ≤ 1) :
    (inherited stress pointLe 0 0 - mFourierCoeff (fun place =>
      (field (receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩) 0 place : ℂ)) 0).re =
        kineticDefect stress pointLe / 8 := by
  rw [inherited_temporal_defect]
  simp only [Complex.div_ofNat_re, Complex.neg_re, trace, Complex.re_sum, kineticDefect]

theorem inherited_mean_defect_nonnegative (stress : StressAt escape) (pointLe : point ≤ 1) :
    0 ≤ (inherited stress pointLe 0 0 - mFourierCoeff (fun place =>
      (field (receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩) 0 place : ℂ)) 0).re := by
  rw [inherited_mean_defect]
  exact div_nonneg (kineticDefect_nonnegative stress pointLe) (by norm_num)

def source (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) : Fin 4 → IntegerWavevector → ℂ :=
  inherited (sourceStress initial point inside uncovered) (inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2)

theorem source_current_tendsto (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => actual (sourceUncoveredAction initial point inside uncovered)
      ((sourceStress initial point inside uncovered).refinement index) direction wave) atTop
        (𝓝 (source initial point inside uncovered direction wave)) := inherited_tendsto _ _ direction wave

end
end SaturationMonoid.NavierStokes.NativeEscapePairedCurrent
