import H0mework.Versions.X.NavierStokes.WindowSchurMean.CofinalSource
import H0mework.Versions.X.NavierStokes.SourceUnheated.Energy
import H0mework.Versions.X.NavierStokes.WindowSchurMean.GraphLimit

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanResidualRead
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed row finiteRow)
open NativePhysicalPairing (includeCLM restrict_include)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowHistoryMeanResidualLoad (residualLoad)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeForwardWindowEvolution (velocityJet)
open NativeWindowHistoryMeanCofinalSource (value read_row value_original)
open NativeViewEnergyWork (residualRow)
noncomputable section
variable {nu : Viscosity}

theorem mean_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : NonzeroIntegerWavevector) (inside : k.1∈modes M) :
    (mean (finiteHistory seed time M)).1 k=velocityJet seed 0 time k := by
  rw [NativeWindowHistoryMeanTime.source_mean,NativeWindowHistoryMeanTime.jet,read_row,if_pos inside]

theorem mean_rate_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : NonzeroIntegerWavevector) (inside : k.1∈modes M) :
    (mean (NativeWindowHistoryOseen.rateHistory seed M time)).1 k=velocityJet seed 1 time k := by
  rw [NativeWindowHistoryMeanTime.source_rate,NativeWindowHistoryMeanTime.jet,read_row,if_pos inside]

theorem drift_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : NonzeroIntegerWavevector) (inside : k.1∈modes M) :
    (drift seed M time (mean (finiteHistory seed time M))).1 k=
      NativeCompleteStressAction.euclideanCLM (finiteRow M (value seed time) (value seed time) k.1) := by
  rw [← NativeWindowHistoryMeanResidualLoad.include_zero seed M time,NativeWindowHistoryMeanDrift.drift_original,restrict_include]
  have actual : NativeWindowHistoryMeanPhysicalJet.physicalJet seed M 0 time=
      NativeWholeH1Mixed.restrict M (value seed time) := by
    rw [NativeWindowHistoryMeanResidualLoad.jet_zero_mean]
    rfl
  rw [actual]
  change euclideanCoordinateRow ((NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWholeH1Mixed.restrict M (value seed time)) (NativeWholeH1Mixed.restrict M (value seed time))).1 k.1)=_
  rw [NativeWindowHistoryMeanStrongBilinear.transport_stress nu (modes M) (modes_zero M) (modes_closed M) _ _ k.1 inside]
  rfl

theorem original_residual_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (k : NonzeroIntegerWavevector) :
    residualRow seed 0 time k=velocityJet seed 1 time k+
      (nu.coeff*integerWaveViscousMultiplier k.1) • velocityJet seed 0 time k-
        NativeCompleteStressAction.euclideanCLM (row (value seed time) (value seed time) k.1) := by
  have source:=NativeViewEnergyWork.momentum_rate_row seed 0 time valid k
  simp only [NativeWindowHeatEvolution.velocityJet,NativeZeroHeatWindow.jet_zero,NativeZeroHeatWindow.source_zero] at source
  change velocityJet seed 1 time k=NativeCompleteStressAction.euclideanCLM
    (NativeTimeJetCarrier.projectedDivergenceCLM k.1
      (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd k.1))-
      (nu.coeff*integerWaveViscousMultiplier k.1) • velocityJet seed 0 time k at source
  rw [source]
  simp only [residualRow,NativeZeroHeatWindow.source_zero,NativeHeatPairingAverage.residual_read,Pi.sub_apply,map_sub,
    row,value,NativeWindowHistoryMeanProjection.source_mean,NativeHigherTimeJets.mixedFlux_diagonal]
  abel

theorem residualLoad_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time)
    (k : NonzeroIntegerWavevector) (inside : k.1∈modes M) :
    (residualLoad seed M time).1 k=residualRow seed 0 time k+
      NativeCompleteStressAction.euclideanCLM (row (value seed time) (value seed time) k.1-
        finiteRow M (value seed time) (value seed time) k.1) := by
  have source:=congrArg (fun v : wholePhysical => v.1 k)
    (NativeWindowHistoryMeanResidualLoad.source_mean_balance seed M time)
  change (mean (NativeWindowHistoryOseen.rateHistory seed M time)).1 k+
    nu.coeff • (laplacianFiber nu M (mean (finiteHistory seed time M))).1 k=
      (drift seed M time (mean (finiteHistory seed time M))).1 k+(residualLoad seed M time).1 k at source
  rw [mean_rate_row seed M time k inside,NativeWindowHistoryMeanGraphLimit.laplacian_row,if_pos inside,
    mean_row seed M time k inside,smul_smul,drift_row seed M time k inside] at source
  rw [original_residual_row seed time valid k,map_sub]
  exact (eq_sub_of_add_eq' source.symm).trans (by abel)

private theorem sum_nonzero (M : ℕ) (f : IntegerWavevector→ℝ) :
    (∑k : (modes M).subtype (fun k => k≠0),f k.1.1)=∑k∈modes M,f k := by
  exact (Finset.sum_coe_sort ((modes M).subtype (fun k => k≠0)) (fun k => f k.1)).trans
    (Finset.sum_subtype_of_mem f (fun k member (zero : k=0) => modes_zero M (zero ▸ member)))

theorem source_physical_error (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∀M ≥ low,∀time∈Icc (0:ℝ) horizon,
      (∑k : (modes M).subtype (fun k => k≠0),
        ‖(residualLoad seed M time).1 k.1-residualRow seed 0 time k.1‖^2) ≤ epsilon := by
  obtain ⟨low,paid⟩:=NativeWindowHistoryMeanCofinalSource.source_strong_error seed horizon epsilon positive
  refine ⟨low,fun M above time inside => ?_⟩
  have valid:-1<time:=by linarith [inside.1]
  let error:=fun k => ‖NativeCompleteStressAction.euclideanCLM
    (row (value seed time) (value seed time) k-finiteRow M (value seed time) (value seed time) k)‖^2
  have same : (∑k : (modes M).subtype (fun k => k≠0),
      ‖(residualLoad seed M time).1 k.1-residualRow seed 0 time k.1‖^2)=
        ∑k : (modes M).subtype (fun k => k≠0),error k.1.1 := by
    apply Finset.sum_congr rfl
    intro k _
    have covered : k.1.1∈modes M := (Finset.mem_subtype.mp k.2)
    rw [residualLoad_row seed M time valid k.1 covered,add_sub_cancel_left]
  rw [same,sum_nonzero M error]
  exact paid M above time inside (modes M)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanResidualRead
