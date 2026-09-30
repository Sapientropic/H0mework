import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedDrift
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeRelative

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeCommonAdvectorAction
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowOperatorGreen (laplacian)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanDrift (drift)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem prepared_creation_mixed (horizon delta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<delta) (M : ℕ) (time : ℝ)
    (inside : time∈Icc (-2 : ℝ) horizon) (u : wholePhysical) :
    ‖creation stackedShortCurrent M time u‖^2≤
      delta*‖laplacianFiber butterflyGainViscosity M u‖^2+
        preparedCreationBudget horizon delta*‖u‖*‖laplacianFiber butterflyGainViscosity M u‖ := by
  let v:=restrictCLM (modes M) (modes_zero M) (modes_closed M) u
  have source:=prepared_creation_bound horizon delta nonnegative positive M time inside v
  have bounded : curlPair (modes M) v.1 v.1≤
      ‖u‖*‖laplacianFiber butterflyGainViscosity M u‖ := by
    rw [← NativeWindowMetricGraphHistory.fiber_gradient butterflyGainViscosity M u]
    exact real_inner_le_norm u (laplacianFiber butterflyGainViscosity M u)
  have paid:=mul_le_mul_of_nonneg_left bounded
    (preparedCreationBudget_nonnegative horizon delta positive)
  have normed:=real_inner_self_eq_norm_sq
    (coefficients (modes M) (laplacian (modes M) (modes_zero M)
      (modes_closed M) butterflyGainViscosity v))
  change pairing (modes M) _ _=‖coefficients (modes M) _‖^2 at normed
  rw [normed,← NativeWindowMetricGraphHistory.laplacian_norm] at source
  have same : creation stackedShortCurrent M time u=
      creation stackedShortCurrent M time
        (includeCLM (modes M) (modes_closed M) v) :=
    NativeWindowHistoryCreationSource.creation_restrict stackedShortCurrent M time u
  rw [same]
  nlinarith only [source,paid]

theorem prepared_creation_relative (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
      ∀u : wholePhysical,
        ‖creation stackedShortCurrent M time u‖^2≤
          eta*‖laplacianFiber butterflyGainViscosity M u‖^2+C*‖u‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let B:=preparedCreationBudget horizon delta
  let C:=B^2/(2*eta)
  refine ⟨C,by dsimp only [C]; positivity,fun M time inside u => ?_⟩
  have source:=prepared_creation_mixed horizon delta nonnegative delta0 M time inside u
  change ‖creation stackedShortCurrent M time u‖^2≤
    delta*‖laplacianFiber butterflyGainViscosity M u‖^2+
      B*‖u‖*‖laplacianFiber butterflyGainViscosity M u‖ at source
  exact NativeStageNineWindowEnergy.relative_from_mixed _ _ _ eta B positive source

theorem prepared_drift_mixed (horizon delta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<delta) (M : ℕ) (time : ℝ)
    (inside : time∈Icc (-2 : ℝ) horizon) (u : wholePhysical) :
    ‖drift stackedShortCurrent M time u‖^2≤
      delta*‖laplacianFiber butterflyGainViscosity M u‖^2+
        preparedCreationBudget horizon delta*‖u‖*‖laplacianFiber butterflyGainViscosity M u‖ := by
  let v:=restrictCLM (modes M) (modes_zero M) (modes_closed M) u
  have source:=prepared_drift_bound horizon delta nonnegative positive M time inside v
  have bounded : curlPair (modes M) v.1 v.1≤
      ‖u‖*‖laplacianFiber butterflyGainViscosity M u‖ := by
    rw [← NativeWindowMetricGraphHistory.fiber_gradient butterflyGainViscosity M u]
    exact real_inner_le_norm u (laplacianFiber butterflyGainViscosity M u)
  have paid:=mul_le_mul_of_nonneg_left bounded
    (preparedCreationBudget_nonnegative horizon delta positive)
  have normed:=real_inner_self_eq_norm_sq
    (coefficients (modes M) (laplacian (modes M) (modes_zero M)
      (modes_closed M) butterflyGainViscosity v))
  change pairing (modes M) _ _=‖coefficients (modes M) _‖^2 at normed
  rw [normed,← NativeWindowMetricGraphHistory.laplacian_norm] at source
  have same : drift stackedShortCurrent M time u=
      drift stackedShortCurrent M time
        (includeCLM (modes M) (modes_closed M) v) := by
    rw [NativeWindowHistoryMeanDrift.drift_original,
      NativeWindowHistoryMeanDrift.drift_original,restrict_include]
  rw [same]
  nlinarith only [source,paid]

theorem prepared_drift_relative (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
      ∀u : wholePhysical,
        ‖drift stackedShortCurrent M time u‖^2≤
          eta*‖laplacianFiber butterflyGainViscosity M u‖^2+C*‖u‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let B:=preparedCreationBudget horizon delta
  let C:=B^2/(2*eta)
  refine ⟨C,by dsimp only [C]; positivity,fun M time inside u => ?_⟩
  have source:=prepared_drift_mixed horizon delta nonnegative delta0 M time inside u
  change ‖drift stackedShortCurrent M time u‖^2≤
    delta*‖laplacianFiber butterflyGainViscosity M u‖^2+
      B*‖u‖*‖laplacianFiber butterflyGainViscosity M u‖ at source
  exact NativeStageNineWindowEnergy.relative_from_mixed _ _ _ eta B positive source
end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
