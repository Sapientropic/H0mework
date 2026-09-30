import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedSchurPotential

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedTemporalResponse
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

def responseBudget (horizon : ℝ) : ℝ :=
  NativeStageNinePreparedGraph.graphBudget 0 horizon+
    NativeStageNinePreparedSchurPotential.formBudget horizon 1*
      NativeWindowHistorySchurTemporalControl.massBudget stackedShortCurrent

theorem responseBudget_nonnegative (horizon : ℝ) : 0 ≤ responseBudget horizon := by
  unfold responseBudget
  exact add_nonneg (NativeStageNinePreparedGraph.graphBudget_nonnegative 0 horizon)
    (mul_nonneg (NativeStageNinePreparedSchurPotential.formBudget_nonnegative horizon 1 (by norm_num))
      (NativeWindowHistorySchurTemporalControl.massBudget_nonnegative _))

theorem source_response_energy (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    NativeWindowHistorySchurTemporalControl.energy butterflyGainViscosity M
      (NativeWindowHistorySchurAction.response stackedShortCurrent M time
        (mean (finiteHistory stackedShortCurrent time M))) ≤ responseBudget horizon := by
  let h := finiteHistory stackedShortCurrent time M
  let v := NativeWindowHistoryMeanGradient.meanValue M h
  have projected := congrArg mean
    (NativeWindowHistoryMeanGradient.source_projection stackedShortCurrent M time)
  have original : mean h = includeCLM (modes M) (modes_closed M) v := by
    simpa only [NativeWindowHistoryMeanProjection.projection,ContinuousLinearMap.comp_apply,
      NativeWindowHistoryMeanProjection.mean_embed] using projected
  have split := NativeWindowHistoryMeanProjection.energy_split h
  have mass : pairing (modes M) v v ≤
      NativeWindowHistorySchurTemporalControl.massBudget stackedShortCurrent := by
    have same : ‖NativeWindowHistoryMeanProjection.projection h‖^2 = pairing (modes M) v v := by
      change ‖embed (mean h)‖^2 = _
      rw [NativeWindowHistoryMeanProjection.embed_norm,original,
        NativePhysicalPairing.include_norm (modes M) (modes_zero M)]
      exact (real_inner_self_eq_norm_sq _).symm
    have bound := NativeStageNinePreparedSchurMass.history_mass_total stackedShortCurrent M time
    nlinarith only [split,same,bound,sq_nonneg ‖NativeWindowHistoryMeanProjection.residual h‖]
  have gbound : curlPair (modes M) v.1 v.1 ≤
      NativeStageNinePreparedGraph.graphBudget 0 horizon :=
    (NativeWindowHistoryMeanGradient.source_mean_gradient stackedShortCurrent M time).trans
      (NativeStageNinePreparedGraph.history_gradient_bound horizon nonnegative M time inside)
  change NativeWindowHistorySchurAction.cost stackedShortCurrent M time (mean h) ≤ _
  rw [original]
  have paid := NativeStageNinePreparedSchurPotential.source_form_bound
    horizon 1 nonnegative (by norm_num) M time inside v
  rw [one_mul] at paid
  exact paid.trans (add_le_add gbound (mul_le_mul_of_nonneg_left mass
    (NativeStageNinePreparedSchurPotential.formBudget_nonnegative horizon 1 (by norm_num))))

def temporalBudget (horizon : ℝ) : ℝ :=
  2*NativeStageNinePreparedTemporalResidual.residualBudget horizon+2*responseBudget horizon

theorem temporalBudget_nonnegative (horizon : ℝ) : 0 ≤ temporalBudget horizon := by
  unfold temporalBudget
  exact add_nonneg
    (mul_nonneg (by norm_num) (NativeStageNinePreparedTemporalResidual.residualBudget_nonnegative horizon))
    (mul_nonneg (by norm_num) (responseBudget_nonnegative horizon))

theorem source_temporal_energy (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    NativeWindowHistorySchurTemporalControl.energy butterflyGainViscosity M
      (NativeWindowHistorySchurTemporalControl.temporalResponse stackedShortCurrent M time) ≤
      temporalBudget horizon := by
  rw [NativeWindowHistorySchurTemporalControl.temporal_original]
  exact (NativeWindowHistorySchurTemporalControl.energy_sub stackedShortCurrent M _ _).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (NativeStageNinePreparedTemporalResidual.source_residual_energy horizon nonnegative M time inside)
        (by norm_num))
      (mul_le_mul_of_nonneg_left
        (source_response_energy horizon nonnegative M time inside) (by norm_num)))

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedTemporalResponse
