import H0mework.Chemistry.LAlanineBandCellDifferential.Implicit
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential Filter Metric
open scoped Topology
noncomputable section

theorem cell0_nearbySolution_tendsto (p : Cell0Point) :
    Tendsto (cell0_nearbySolution p) (𝓝 (cellSeed 0 p.val)) (𝓝 (rawPath (cellSeed 0 p.val))) :=
  (cell0_pathResidual_hasStrictFDerivAt p).tendsto_implicitFunctionOfProdDomain
    (cell0_pathResidual_right_invertible p)

theorem cell0_nearbySolution_solves (p : Cell0Point) :
    ∀ᶠ x in 𝓝 (cellSeed 0 p.val),
      cell0_nearbySolution p x = pathConst x + volterra (pathGradient (cell0_nearbySolution p x)) := by
  filter_upwards [(cell0_pathResidual_hasStrictFDerivAt p).eventually_apply_implicitFunctionOfProdDomain
    (cell0_pathResidual_right_invertible p)] with x hx
  rw [cell0_rawPath_residual_zero] at hx
  change cell0_nearbySolution p x - pathConst x - volterra (pathGradient (cell0_nearbySolution p x)) = 0 at hx
  linear_combination hx

theorem cell0_nearbySolution_in_cube (p : Cell0Point) :
    ∀ᶠ x in 𝓝 (cellSeed 0 p.val), ∀ t : Time, cell0_nearbySolution p x t ∈ sourceCube := by
  have near := (cell0_nearbySolution_tendsto p).eventually
    (ball_mem_nhds (rawPath (cellSeed 0 p.val)) (show (0 : ℝ) < 1/200 by norm_num))
  filter_upwards [near] with x hx t
  exact path_near_cell0_in_cube p (cell0_nearbySolution p x) hx t

theorem cell0_nearbySolution_eq_rawPath (p : Cell0Point) :
    cell0_nearbySolution p =ᶠ[𝓝 (cellSeed 0 p.val)] rawPath := by
  filter_upwards [cell0_nearbySolution_solves p, cell0_nearbySolution_in_cube p] with x equation inside
  exact solvedPath_eq_rawPath x (cell0_nearbySolution p x) equation inside

def cell0_sourceResponse (p : Cell0Point) : Space →L[ℝ] Path :=
  (1 - cell0_volterraHessian p).inverse.comp pathConst

theorem cell0_rawPath_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt rawPath (cell0_sourceResponse p) (cellSeed 0 p.val) := by
  have generated : HasStrictFDerivAt (cell0_nearbySolution p) (cell0_sourceResponse p) (cellSeed 0 p.val) := by
    simpa only [cell0_sourceResponse, cell0_residualDerivative, ContinuousLinearMap.coprod_comp_inr,
      ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.comp_neg, neg_neg] using
      cell0_nearbySolution_hasStrictFDerivAt p
  exact generated.congr_of_eventuallyEq (cell0_nearbySolution_eq_rawPath p)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
