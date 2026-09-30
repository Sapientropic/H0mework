import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedTemporalResponse

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedTemporalWork
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem source_temporal_work_bound (horizon epsilon : ℝ) (nonnegative : 0 ≤ horizon)
    (positive : 0 < epsilon) (M : ℕ) (time : ℝ)
    (inside : time ∈ Icc (-2 : ℝ) horizon) (v : physicalSpace (modes M)) :
    |inner ℝ (includeCLM (modes M) (modes_closed M) v)
      (NativeWindowHistorySchurAction.remainder stackedShortCurrent M time-
        NativeWindowHistoryMeanProjection.mean
          (NativeWindowHistoryOseen.forcingHistory stackedShortCurrent M time))| ≤
      (epsilon/2)*curlPair (modes M) v.1 v.1+
      (NativeStageNinePreparedSchurPotential.potentialBudget horizon epsilon/2)*
        pairing (modes M) v v+
      NativeStageNinePreparedTemporalResponse.temporalBudget horizon/
        (2*butterflyGainViscosity.coeff) := by
  let z := NativeWindowHistorySchurTemporalControl.temporalResponse stackedShortCurrent M time
  have pos := NativeWindowHistorySchurWeakPairing.creation_young stackedShortCurrent M time v z 1
  have neg := NativeWindowHistorySchurWeakPairing.creation_young stackedShortCurrent M time v z (-1)
  have absolute : |inner ℝ (NativeWindowHistoryMeanAction.creation stackedShortCurrent M time
      (includeCLM (modes M) (modes_closed M) v)) z| ≤
      (NativeWindowHistorySchurWeakPairing.potential stackedShortCurrent M time v+
        NativeWindowTraceWholeHistory.gradient M z)/2 := by
    rw [abs_le]
    constructor <;> nlinarith only [pos,neg]
  have grad : NativeWindowTraceWholeHistory.gradient M z ≤
      NativeStageNinePreparedTemporalResponse.temporalBudget horizon/
        butterflyGainViscosity.coeff := by
    apply (le_div_iff₀ butterflyGainViscosity.coeff_pos).mpr
    have paid := NativeStageNinePreparedTemporalResponse.source_temporal_energy
      horizon nonnegative M time inside
    unfold NativeWindowHistorySchurTemporalControl.energy at paid
    nlinarith only [paid,sq_nonneg ‖z‖]
  rw [NativeWindowHistorySchurTemporalControl.temporal_pairing,abs_neg]
  exact absolute.trans ((div_le_div_of_nonneg_right (add_le_add
    (NativeStageNinePreparedSchurPotential.source_potential_bound horizon epsilon
      nonnegative positive M time inside v) grad)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedTemporalWork
