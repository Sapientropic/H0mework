import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedGraph

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedTemporalResidual
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

def residualBudget (horizon : ℝ) : ℝ :=
  NativeWindowHistorySchurTemporalControl.massBudget stackedShortCurrent+
    butterflyGainViscosity.coeff*NativeStageNinePreparedGraph.graphBudget 0 horizon

theorem residualBudget_nonnegative (horizon : ℝ) : 0 ≤ residualBudget horizon := by
  unfold residualBudget
  exact add_nonneg (NativeWindowHistorySchurTemporalControl.massBudget_nonnegative _)
    (mul_nonneg butterflyGainViscosity.coeff_pos.le
      (NativeStageNinePreparedGraph.graphBudget_nonnegative 0 horizon))

theorem source_residual_energy (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    NativeWindowHistorySchurTemporalControl.energy butterflyGainViscosity M
        (NativeWindowHistoryMeanProjection.residual (finiteHistory stackedShortCurrent time M)) ≤
      residualBudget horizon := by
  let h := finiteHistory stackedShortCurrent time M
  have split := NativeWindowHistoryMeanProjection.energy_split h
  have below : ‖NativeWindowHistoryMeanProjection.residual h‖^2 ≤ ‖h‖^2 := by
    nlinarith only [split,sq_nonneg ‖NativeWindowHistoryMeanProjection.projection h‖]
  have mass : ‖NativeWindowHistoryMeanProjection.residual h‖^2 ≤
      NativeWindowHistorySchurTemporalControl.massBudget stackedShortCurrent :=
    below.trans (NativeStageNinePreparedSchurMass.history_mass_total stackedShortCurrent M time)
  exact add_le_add mass (mul_le_mul_of_nonneg_left
    ((NativeWindowHistoryMeanGradient.gradient_residual_le stackedShortCurrent M h).trans
      (NativeStageNinePreparedGraph.history_gradient_bound horizon nonnegative M time inside))
        butterflyGainViscosity.coeff_pos.le)

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedTemporalResidual
