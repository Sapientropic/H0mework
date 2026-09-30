import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowGraph

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeFiniteActionResolvent (pairing)
open NativePhysicalPairing (restrict_include include_inner)
open NativeForwardWindowPairingReadout (averageMeasure)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

def fullMetricFiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWholeResolvent.wholePhysical →L[ℝ] NativeWholeResolvent.wholePhysical :=
  NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap
    (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius))

def fullMetricAction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowTraceWholeHistory.H →L[ℝ] NativeWindowTraceWholeHistory.H :=
  (fullMetricFiber seed time M F radius).compLpL 2 averageMeasure

theorem history_word_full_metric (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    inner ℝ (NativeWindowHistorySpatialWords.history seed M directions time)
      (fullMetricAction seed time M F radius
        (NativeWindowHistorySpatialWords.history seed M directions time))=
    ∫shift,pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
      (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift)))
      ∂averageMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fullMetricFiber seed time M F radius).coeFn_compLpL
      (NativeWindowHistorySpatialWords.history seed M directions time),
    NativeWindowHistorySpatialWords.history_original seed M directions time]
      with shift applied original
  change inner ℝ (NativeWindowHistorySpatialWords.history seed M directions time shift)
    (((fullMetricFiber seed time M F radius).compLpL 2 averageMeasure
      (NativeWindowHistorySpatialWords.history seed M directions time)) shift)=_
  rw [applied,original]
  dsimp only [fullMetricFiber]
  rw [NativeWindowHistoryOseen.lift_included]
  rw [include_inner (modes M) (modes_zero M) (modes_closed M),restrict_include]
  rfl

theorem full_metric_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (v : NativeWindowTraceWholeHistory.H) :
    inner ℝ v (fullMetricAction seed time M F radius v)=
      inner ℝ (NativeWindowHistoryMeanProjection.projection v)
        (fullMetricAction seed time M F radius
          (NativeWindowHistoryMeanProjection.projection v))+
      inner ℝ (NativeWindowHistoryMeanProjection.residual v)
        (fullMetricAction seed time M F radius
          (NativeWindowHistoryMeanProjection.residual v)) :=
  NativeWindowHistoryMeanProjection.comp_energy_split
    (fullMetricFiber seed time M F radius) v

private theorem full_metric_point (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (v : NativeWholeResolvent.wholePhysical) :
    inner ℝ v (fullMetricFiber seed time M F radius v)=
      pairing (modes M)
        (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
        (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
          (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  dsimp only [fullMetricFiber]
  rw [NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
  rw [real_inner_comm,include_inner (modes M) (modes_zero M) (modes_closed M),
    NativeResolventAdjoint.pairing_symmetric]
  rfl

theorem full_metric_coercive (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (coercive : ∀x : NativeFiniteActionResolvent.physicalSpace (modes M),
      pairing (modes M) x x+(nu.coeff/2)*
        NativeCommonAdvectorAction.curlPair (modes M) x.1 x.1≤
          pairing (modes M) x
            (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius x))
    (v : NativeWindowTraceWholeHistory.H) :
    ‖NativeWindowTraceWholeHistory.projected M v‖^2+
      (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M v≤
        inner ℝ v (fullMetricAction seed time M F radius v) := by
  let P:=NativeWindowTraceWholeHistory.projected M
  let A:=fullMetricFiber seed time M F radius
  have mass := (Lp.memLp (P v)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have cost := NativeWindowTraceWholeHistory.gradient_integrable nu M v
  have target := L2.integrable_inner (𝕜 := ℝ) v (fullMetricAction seed time M F radius v)
  have estimate := integral_mono_ae (mass.add (cost.const_mul (nu.coeff/2))) target (by
    filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL v,
      A.coeFn_compLpL v] with shift projected applied
    change ‖P v shift‖^2+(nu.coeff/2)*_ ≤
      inner ℝ (v shift) ((A.compLpL 2 averageMeasure v) shift)
    change ‖((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure v) shift‖^2+
      (nu.coeff/2)*_ ≤ inner ℝ (v shift) ((A.compLpL 2 averageMeasure v) shift)
    rw [projected,applied,NativeWindowTraceWholeHistory.projection_square,
      full_metric_point]
    exact coercive _)
  have massRead := NativeWindowTraceWholeHistory.norm_square (P v)
  have costRead : (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M v=
      ∫shift,(nu.coeff/2)*NativeCommonAdvectorAction.curlPair (modes M)
        (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1
        (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1
        ∂averageMeasure := (integral_const_mul (nu.coeff/2) _).symm
  have sumRead := (congrArg₂ (fun x y : ℝ => x+y) massRead costRead).trans
    (integral_add mass (cost.const_mul (nu.coeff/2))).symm
  have targetRead := L2.inner_def (𝕜 := ℝ) v (fullMetricAction seed time M F radius v)
  exact sumRead.trans_le (estimate.trans_eq targetRead.symm)

theorem source_full_metric_coercive (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∀radius≥low,∀outerRadius M : ℕ,∀time∈Icc 0 horizon,
      ∀v : NativeWindowTraceWholeHistory.H,
      ‖NativeWindowTraceWholeHistory.projected M v‖^2+
        (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M v≤
          inner ℝ v (fullMetricAction seed time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v) := by
  obtain ⟨low,paid⟩:=NativeWindowAugmentedCoercivity.source_coercivity
    seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M time inside v => ?_⟩
  apply full_metric_coercive seed M time _ radius
  · intro x
    exact paid radius above (modes M) _ (modes_zero M) (modes_closed M)
      (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside x

theorem history_word_projected (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    NativeWindowTraceWholeHistory.projected M
      (NativeWindowHistorySpatialWords.history seed M directions time)=
        NativeWindowHistorySpatialWords.history seed M directions time := by
  apply Lp.ext
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL
      (NativeWindowHistorySpatialWords.history seed M directions time),
    NativeWindowHistorySpatialWords.history_original seed M directions time]
      with shift applied original
  change ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure
    (NativeWindowHistorySpatialWords.history seed M directions time)) shift=_
  rw [applied,original]
  change NativePhysicalPairing.includeCLM (modes M) (modes_closed M)
    (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (NativePhysicalPairing.includeCLM (modes M) (modes_closed M)
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))))=_
  rw [restrict_include]

theorem history_word_residual_projected (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    NativeWindowTraceWholeHistory.projected M
      (NativeWindowHistoryMeanProjection.residual
        (NativeWindowHistorySpatialWords.history seed M directions time))=
      NativeWindowHistoryMeanProjection.residual
        (NativeWindowHistorySpatialWords.history seed M directions time) := by
  have commute:=NativeWindowHistoryMeanProjection.residual_comp
    (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowHistorySpatialWords.history seed M directions time)
  change NativeWindowHistoryMeanProjection.residual
    (NativeWindowTraceWholeHistory.projected M
      (NativeWindowHistorySpatialWords.history seed M directions time))=_ at commute
  rw [history_word_projected seed M directions time] at commute
  exact commute.symm

theorem history_word_mean_projected (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    NativeWindowTraceWholeHistory.projected M
      (NativeWindowHistoryMeanProjection.projection
        (NativeWindowHistorySpatialWords.history seed M directions time))=
      NativeWindowHistoryMeanProjection.projection
        (NativeWindowHistorySpatialWords.history seed M directions time) := by
  have commute:=NativeWindowHistoryMeanProjection.projection_comp
    (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowHistorySpatialWords.history seed M directions time)
  change NativeWindowHistoryMeanProjection.projection
    (NativeWindowTraceWholeHistory.projected M
      (NativeWindowHistorySpatialWords.history seed M directions time))=_ at commute
  rw [history_word_projected seed M directions time] at commute
  exact commute.symm
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
