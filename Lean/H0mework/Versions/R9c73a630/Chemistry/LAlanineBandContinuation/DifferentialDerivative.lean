import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialImplicit
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceRecognition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential
open Filter Metric
open scoped Topology
noncomputable section

theorem nearbySolution_tendsto (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    Tendsto (nearbySolution c fields bounds p inside) (𝓝 (cellSeed c p)) (𝓝 (rawPath (cellSeed c p))) :=
  (residual_strictDerivative c p).tendsto_implicitFunctionOfProdDomain
    (residual_right_invertible c fields bounds p inside)

theorem nearbySolution_solves (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ∀ᶠ x in 𝓝 (cellSeed c p), nearbySolution c fields bounds p inside x =
      pathConst x + volterra (pathGradient (nearbySolution c fields bounds p inside x)) := by
  filter_upwards [(residual_strictDerivative c p).eventually_apply_implicitFunctionOfProdDomain
    (residual_right_invertible c fields bounds p inside)] with x hx
  rw [rawPath_residual_zero c fields p inside] at hx
  change nearbySolution c fields bounds p inside x - pathConst x -
    volterra (pathGradient (nearbySolution c fields bounds p inside x)) = 0 at hx
  linear_combination hx

theorem nearbySolution_in_cube (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ∀ᶠ x in 𝓝 (cellSeed c p), ∀ t : Time, nearbySolution c fields bounds p inside x t ∈ sourceCube := by
  have near := (nearbySolution_tendsto c fields bounds p inside).eventually
    (ball_mem_nhds (rawPath (cellSeed c p)) (show (0 : ℝ) < 1/200 by norm_num))
  filter_upwards [near] with x hx t
  exact path_near_in_cube c fields bounds p inside (nearbySolution c fields bounds p inside x) hx t

theorem nearbySolution_eq_rawPath (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    nearbySolution c fields bounds p inside =ᶠ[𝓝 (cellSeed c p)] rawPath := by
  filter_upwards [nearbySolution_solves c fields bounds p inside, nearbySolution_in_cube c fields bounds p inside]
    with x equation cube
  exact solvedPath_eq_rawPath x (nearbySolution c fields bounds p inside x) equation cube

def sourceResponse (c : FullBandCell) (p : Point) : Space →L[ℝ] Path :=
  (1 - volterraHessian c p).inverse.comp pathConst

theorem rawPath_hasStrictFDerivAt (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    HasStrictFDerivAt rawPath (sourceResponse c p) (cellSeed c p) := by
  have generated : HasStrictFDerivAt (nearbySolution c fields bounds p inside) (sourceResponse c p) (cellSeed c p) := by
    simpa only [sourceResponse, residualDerivative, ContinuousLinearMap.coprod_comp_inr,
      ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.comp_neg, neg_neg] using
      nearbySolution_hasStrictFDerivAt c fields bounds p inside
  exact generated.congr_of_eventuallyEq (nearbySolution_eq_rawPath c fields bounds p inside)

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
