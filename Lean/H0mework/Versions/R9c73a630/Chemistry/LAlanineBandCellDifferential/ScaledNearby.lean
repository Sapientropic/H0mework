import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.ScaledImplicit
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledRecognition

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandActual WholeBandGeometry WholeBandCell0Continuation TrueFlowDifferential Filter Metric
open scoped Topology
noncomputable section

theorem cell0_scaledSolution_at_source (p : Cell0Point) :
    cell0_scaledSolution p (cell0_sourceInput p) = cell0_scaledActualPath p :=
  ((cell0_scaledResidual_hasStrictFDerivAt p).eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (cell0_scaledResidual_right_invertible p)).self_of_nhds.mp rfl

theorem cell0_scaledSolution_tendsto (p : Cell0Point) :
    Tendsto (cell0_scaledSolution p) (𝓝 (cell0_sourceInput p)) (𝓝 (cell0_scaledActualPath p)) :=
  (cell0_scaledResidual_hasStrictFDerivAt p).tendsto_implicitFunctionOfProdDomain
    (cell0_scaledResidual_right_invertible p)

theorem cell0_scaledSolution_solves (p : Cell0Point) :
    ∀ᶠ z in 𝓝 (cell0_sourceInput p),
      cell0_scaledSolution p z = pathConst z.1 + z.2 • volterra (pathGradient (cell0_scaledSolution p z)) := by
  filter_upwards [(cell0_scaledResidual_hasStrictFDerivAt p).eventually_apply_implicitFunctionOfProdDomain
    (cell0_scaledResidual_right_invertible p)] with z hz
  rw [cell0_scaledActual_residual_zero] at hz
  change cell0_scaledSolution p z - pathConst z.1 - z.2 • volterra (pathGradient (cell0_scaledSolution p z)) = 0 at hz
  linear_combination hz

theorem cell0_scaledSolution_in_cube (p : Cell0Point) :
    ∀ᶠ z in 𝓝 (cell0_sourceInput p), ∀ t : Time, cell0_scaledSolution p z t ∈ sourceCube := by
  have near := (cell0_scaledSolution_tendsto p).eventually
    (ball_mem_nhds (cell0_scaledActualPath p) (show (0 : ℝ) < 1 / 200 by norm_num))
  filter_upwards [near] with z hz t
  exact path_near_cell0_scaled_in_cube p (cell0_scaledSolution p z) hz t

theorem cell0_scaledSolution_eq_rawPath (p : Cell0Point) :
    ∀ᶠ z in 𝓝 (cell0_sourceInput p), |z.2| ≤ 1 → cell0_scaledSolution p z = scaledRawPath z.1 z.2 := by
  filter_upwards [cell0_scaledSolution_solves p, cell0_scaledSolution_in_cube p] with z equation inside allowed
  exact solvedScaledPath_eq_rawPath z.1 z.2 (cell0_scaledSolution p z) allowed equation inside

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
