import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineBathSource
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Coupling
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Mean

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
variable {nu : Viscosity}

theorem relative_from_mixed (a d m eta B : ℝ) (positive : 0<eta)
    (source : a^2≤(eta/2)*d^2+B*m*d) :
    a^2≤eta*d^2+(B^2/(2*eta))*m^2 := by
  have half : 0<eta/2 := by positivity
  have young:=scalar_young (B*m) d (eta/2) half
  have normalize : (B*m)^2/(4*(eta/2))=(B^2/(2*eta))*m^2 := by ring
  rw [normalize] at young
  nlinarith only [source,young]

theorem source_drift_relative (seed : GeneratedWholeRestartCurrent nu)
    (horizon eta : ℝ) (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      ∀u : NativeWholeResolvent.wholePhysical,
      ‖NativeWindowHistoryMeanDrift.drift seed M time u‖^2≤
        eta*‖laplacianFiber nu M u‖^2+C*‖u‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  let B:=NativeWindowHistoryCreationSource.budget seed horizon delta
  let C:=B^2/(2*eta)
  refine ⟨C,by dsimp only [C]; positivity,fun M time inside u => ?_⟩
  have source:=NativeWindowMetricGraphMean.drift_bound seed horizon delta delta0 M time inside u
  change ‖NativeWindowHistoryMeanDrift.drift seed M time u‖^2≤
    delta*‖laplacianFiber nu M u‖^2+B*‖u‖*‖laplacianFiber nu M u‖ at source
  exact relative_from_mixed _ _ _ eta B positive source

theorem source_creation_relative (seed : GeneratedWholeRestartCurrent nu)
    (horizon eta : ℝ) (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      ∀u : NativeWholeResolvent.wholePhysical,
      ‖NativeWindowHistoryMeanAction.creation seed M time u‖^2≤
        eta*‖laplacianFiber nu M u‖^2+C*‖u‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  let B:=NativeWindowHistoryCreationSource.budget seed horizon delta
  let C:=B^2/(2*eta)
  refine ⟨C,by dsimp only [C]; positivity,fun M time inside u => ?_⟩
  have source:=NativeWindowMetricGraphCoupling.creation_estimate seed horizon delta delta0 M time inside u
  change ‖NativeWindowHistoryMeanAction.creation seed M time u‖^2≤
    delta*‖laplacianFiber nu M u‖^2+B*‖u‖*‖laplacianFiber nu M u‖ at source
  exact relative_from_mixed _ _ _ eta B positive source

theorem source_annihilation_relative (seed : GeneratedWholeRestartCurrent nu)
    (horizon eta : ℝ) (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      ∀q : NativeWindowTraceWholeHistory.H,
      ‖NativeWindowHistoryMeanBlocks.annihilation seed M time q‖^2≤
        eta*‖laplacianAction nu M q‖^2+C*‖q‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  let B:=NativeWindowHistoryAnnihilationControl.budget seed horizon delta
  let C:=B^2/(2*eta)
  refine ⟨C,by dsimp only [C]; positivity,fun M time inside q => ?_⟩
  have source:=NativeWindowMetricGraphCoupling.annihilation_estimate seed horizon delta delta0 M time inside q
  change ‖NativeWindowHistoryMeanBlocks.annihilation seed M time q‖^2≤
    delta*‖laplacianAction nu M q‖^2+B*‖q‖*‖laplacianAction nu M q‖ at source
  exact relative_from_mixed _ _ _ eta B positive source

theorem source_x_relative (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon)
    (eta : ℝ) (positive : 0<eta) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀(time : ℝ),time∈Icc 0 horizon →
      ∀q : NativeWindowTraceWholeHistory.H,
      ‖NativeWindowHistoryMeanProjection.residual
        (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)‖^2≤
        eta*‖laplacianAction nu M q‖^2+C*‖q‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  obtain ⟨low,B,B0,paid⟩:=NativeWindowHistorySchurAdvectorAction.source_graph_bound
    seed horizon nonnegative delta delta0
  let C:=B^2/(2*eta)
  refine ⟨low,C,by dsimp only [C]; positivity,fun M above time inside q => ?_⟩
  have source:=paid M above time inside q
  have gradient:=NativeWindowMetricGraphHistory.gradient_bound nu M q
  have scaled:=mul_le_mul_of_nonneg_left gradient B0
  have bound : ‖NativeWindowHistorySchurAdvectorAction.xAction seed M time q‖^2≤
      delta*‖laplacianAction nu M q‖^2+B*‖q‖*‖laplacianAction nu M q‖ := by
    nlinarith only [source,scaled]
  have residual:=NativeWindowHistorySchurCenteredGraph.residual_norm_square
    (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)
  have mixed : ‖NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)‖^2≤
      delta*‖laplacianAction nu M q‖^2+B*‖q‖*‖laplacianAction nu M q‖ :=
    residual.trans bound
  exact relative_from_mixed _ _ _ eta B positive mixed
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
