import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceImplicit

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual Filter Metric
open scoped Topology
noncomputable section

theorem nearbySolution_at_source (p : BandPoint) :
    nearbySolution p (ContinuousParameterMap.initialMap 0 4 p.val) = actualPath p :=
  ((pathResidual_hasStrictFDerivAt p).eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (pathResidual_right_invertible p)).self_of_nhds.mp rfl

theorem nearbySolution_tendsto (p : BandPoint) :
    Tendsto (nearbySolution p) (𝓝 (ContinuousParameterMap.initialMap 0 4 p.val)) (𝓝 (actualPath p)) :=
  (pathResidual_hasStrictFDerivAt p).tendsto_implicitFunctionOfProdDomain (pathResidual_right_invertible p)

theorem nearbySolution_solves (p : BandPoint) :
    ∀ᶠ x in 𝓝 (ContinuousParameterMap.initialMap 0 4 p.val),
      nearbySolution p x = pathConst x + volterra (pathGradient (nearbySolution p x)) := by
  filter_upwards [(pathResidual_hasStrictFDerivAt p).eventually_apply_implicitFunctionOfProdDomain
    (pathResidual_right_invertible p)] with x hx
  rw [actualPath_residual_zero] at hx
  change nearbySolution p x - pathConst x - volterra (pathGradient (nearbySolution p x)) = 0 at hx
  linear_combination hx

theorem nearbySolution_in_cube (p : BandPoint) :
    ∀ᶠ x in 𝓝 (ContinuousParameterMap.initialMap 0 4 p.val),
      ∀ t : Time, nearbySolution p x t ∈ sourceCube := by
  have near := (nearbySolution_tendsto p).eventually
    (ball_mem_nhds (actualPath p) (show (0 : ℝ) < 1 / 100 by norm_num))
  filter_upwards [near] with x hx t
  exact path_near_actual_in_cube p (nearbySolution p x) hx t

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
