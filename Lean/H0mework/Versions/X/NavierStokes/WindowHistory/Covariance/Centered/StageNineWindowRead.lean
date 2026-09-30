import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Word
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryEnergy
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Recovery

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow (integerWaveFrequencyCube)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeFiniteActionResolvent (pairing coefficients)
open NativePhysicalPairing (include_norm)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceWholeHistory (norm_square)
open NativeCommonAdvectorAction (curlPair)
attribute [local fun_prop] NativeWindowHierarchyPairWindow.pair_continuous
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

theorem history_word_sample_energy (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    ‖NativeWindowHistorySpatialWords.history seed M directions time‖^2=
      ∫shift, pairing (modes M)
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
        ∂averageMeasure := by
  rw [norm_square]
  apply integral_congr_ae
  filter_upwards [NativeWindowHistorySpatialWords.history_original
    seed M directions time] with shift actual
  rw [actual,include_norm (modes M) (modes_zero M) (modes_closed M)]
  exact (real_inner_self_eq_norm_sq _).symm

theorem history_word_sample_gradient (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    NativeWindowTraceWholeHistory.gradient M
      (NativeWindowHistorySpatialWords.history seed M directions time)=
      ∫shift, curlPair (modes M)
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift)).1
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift)).1
        ∂averageMeasure := by
  rw [NativeWindowTraceWholeHistory.gradient]
  apply integral_congr_ae
  filter_upwards [NativeWindowHistorySpatialWords.history_original
    seed M directions time] with shift actual
  rw [actual,NativePhysicalPairing.restrict_include]

theorem mean_word_sample_gradient_le (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    NativeWindowTraceWholeHistory.gradient M
      (NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryAllOrderWord.value seed M directions time))≤
      ∫shift, curlPair (modes M)
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift)).1
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift)).1
        ∂averageMeasure := by
  rw [← history_word_sample_gradient seed M directions time]
  rw [NativeWindowHistoryAllOrderWord.value_original]
  exact NativeWindowHistoryMeanGradient.gradient_projection_le seed M _

theorem mean_word_sample_energy_le (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    ‖NativeWindowHistoryAllOrderWord.value seed M directions time‖^2≤
      ∫shift, pairing (modes M)
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
        ∂averageMeasure := by
  rw [NativeWindowHistoryAllOrderWord.value_original]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (NativeWindowHistoryMeanRecovery.mean_norm_le _) 2).trans_eq
      (history_word_sample_energy seed M directions time)

theorem sample_mass_integrable (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    Integrable (fun shift => pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift)))
      averageMeasure := by
  have original := (Lp.memLp
    (NativeWindowHistorySpatialWords.history seed M directions time)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  apply original.congr
  filter_upwards [NativeWindowHistorySpatialWords.history_original
    seed M directions time] with shift actual
  rw [actual,include_norm (modes M) (modes_zero M) (modes_closed M)]
  exact (real_inner_self_eq_norm_sq _).symm

theorem sample_gradient_integrable (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    Integrable (fun shift => curlPair (modes M)
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift)).1
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift)).1)
      averageMeasure := by
  have original := NativeWindowTraceWholeHistory.gradient_integrable nu M
    (NativeWindowHistorySpatialWords.history seed M directions time)
  apply original.congr
  filter_upwards [NativeWindowHistorySpatialWords.history_original
    seed M directions time] with shift actual
  rw [actual,NativePhysicalPairing.restrict_include]

theorem all_word_window_gradient_le (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) :
    (∑index : FixedMatterSpatialWordIndex order,
      NativeWindowTraceWholeHistory.gradient M
        (NativeWindowHistoryMeanProjection.embed
          (NativeWindowHistoryAllOrderWord.value seed M index.toList time)))≤
      ∫shift, (∑index : FixedMatterSpatialWordIndex order,
        curlPair (modes M)
          (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)).1
          (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)).1)
        ∂averageMeasure := by
  let f (index : FixedMatterSpatialWordIndex order) (shift : ℝ) :=
    curlPair (modes M)
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)).1
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)).1
  have integrated : (∫shift,∑index : FixedMatterSpatialWordIndex order,
      f index shift ∂averageMeasure)=
      ∑index : FixedMatterSpatialWordIndex order,
        ∫shift,f index shift ∂averageMeasure :=
    integral_finsetSum Finset.univ (fun index _ =>
      sample_gradient_integrable seed M index.toList time)
  change (∑index : FixedMatterSpatialWordIndex order,
    NativeWindowTraceWholeHistory.gradient M
      (NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryAllOrderWord.value seed M index.toList time)))≤
    ∫shift,∑index : FixedMatterSpatialWordIndex order,f index shift ∂averageMeasure
  rw [integrated]
  exact Finset.sum_le_sum fun index _ =>
    mean_word_sample_gradient_le seed M index.toList time

theorem hierarchy_history_lag (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) (time : ℝ) :
    NativeWindowHierarchyHistory.history seed M order F radius 0 time=
      ∫shift,NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift)
        ∂averageMeasure := by
  rw [NativeWindowHierarchyHistory.history_original,
    NativeForwardWindowPairingReadout.density_integral]
  change (∫sample in time+1..time+2,
      NativeUnheatedStressPairEvolution.kernelWeight 0 time 0 sample •
        NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius sample)=
    ∫shift,NativeForwardWindowJets.kernelJet 0 shift •
      NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift)
  exact (NativeWindowStressHeatTime.kernel_integral
    (NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius) 0 time).symm

theorem sample_energy_integrable (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) (time : ℝ) :
    Integrable (fun shift => NativeWindowHierarchyHistory.sampleEnergy
      seed time M order F radius (time-shift)) averageMeasure := by
  have continuous : Continuous (NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius) := by
    simp only [funext (NativeWindowHierarchyHistory.sampleEnergy_original seed time M order F radius)]
    fun_prop
  apply (integrable_withDensity_iff_integrable_smul
    NativeForwardWindowPairingReadout.density_measurable).mpr
  have moved : Continuous (fun shift =>
      NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift)) :=
    continuous.comp (continuous_const.sub continuous_id)
  have product : Continuous (fun shift => NativeForwardWindowSource.kernel shift •
      NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift)) :=
    NativeForwardWindowSource.kernel_smooth.continuous.smul moved
  have compact : HasCompactSupport (fun shift => NativeForwardWindowSource.kernel shift •
      NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift)) := by
    change HasCompactSupport
      ((NativeForwardWindowJets.kernelJet 0) •
        fun shift => NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift))
    exact (NativeForwardWindowJets.kernelJet_compact 0).smul_right
  exact product.integrable_of_hasCompactSupport compact

theorem all_word_window_energy_le (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) :
    NativeWindowHistoryAllOrderWord.energy seed M order time≤
      ∫shift, (∑index : FixedMatterSpatialWordIndex order,
        pairing (modes M)
          (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
          (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)))
        ∂averageMeasure := by
  let f (index : FixedMatterSpatialWordIndex order) (shift : ℝ) :=
    pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
  have integrated : (∫ shift,∑index : FixedMatterSpatialWordIndex order,
      f index shift ∂averageMeasure)=
      ∑index : FixedMatterSpatialWordIndex order,
        ∫shift,f index shift ∂averageMeasure :=
    integral_finsetSum Finset.univ (fun index _ =>
      sample_mass_integrable seed M index.toList time)
  change (∑index : FixedMatterSpatialWordIndex order,
    ‖NativeWindowHistoryAllOrderWord.value seed M index.toList time‖^2)≤
    ∫shift,∑index : FixedMatterSpatialWordIndex order,f index shift ∂averageMeasure
  rw [integrated]
  exact Finset.sum_le_sum fun index _ =>
    mean_word_sample_energy_le seed M index.toList time

end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
