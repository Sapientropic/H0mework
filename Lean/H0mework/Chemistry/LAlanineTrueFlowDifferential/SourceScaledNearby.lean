import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceScaledImplicit
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceScaledRecognition

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual Filter Metric
open scoped Topology
noncomputable section

theorem scaledSolution_at_source (p : BandPoint) :
    scaledSolution p (sourceInput p) = scaledActualPath p :=
  ((scaledResidual_hasStrictFDerivAt p).eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (scaledResidual_right_invertible p)).self_of_nhds.mp rfl

theorem scaledSolution_tendsto (p : BandPoint) :
    Tendsto (scaledSolution p) (𝓝 (sourceInput p)) (𝓝 (scaledActualPath p)) :=
  (scaledResidual_hasStrictFDerivAt p).tendsto_implicitFunctionOfProdDomain
    (scaledResidual_right_invertible p)

theorem scaledSolution_solves (p : BandPoint) :
    ∀ᶠ z in 𝓝 (sourceInput p),
      scaledSolution p z = pathConst z.1 + z.2 • volterra (pathGradient (scaledSolution p z)) := by
  filter_upwards [(scaledResidual_hasStrictFDerivAt p).eventually_apply_implicitFunctionOfProdDomain
    (scaledResidual_right_invertible p)] with z hz
  rw [scaledActual_residual_zero] at hz
  change scaledSolution p z - pathConst z.1 - z.2 • volterra (pathGradient (scaledSolution p z)) = 0 at hz
  linear_combination hz

theorem scaledSolution_in_cube (p : BandPoint) :
    ∀ᶠ z in 𝓝 (sourceInput p), ∀ t : Time, scaledSolution p z t ∈ sourceCube := by
  have near := (scaledSolution_tendsto p).eventually
    (ball_mem_nhds (scaledActualPath p) (show (0 : ℝ) < 1 / 100 by norm_num))
  filter_upwards [near] with z hz t
  exact path_near_scaled_actual_in_cube p (scaledSolution p z) hz t

theorem scaledSolution_eq_rawPath (p : BandPoint) :
    ∀ᶠ z in 𝓝 (sourceInput p), |z.2| ≤ 1 → scaledSolution p z = scaledRawPath z.1 z.2 := by
  filter_upwards [scaledSolution_solves p, scaledSolution_in_cube p] with z equation inside allowed
  exact solvedScaledPath_eq_rawPath z.1 z.2 (scaledSolution p z) allowed equation inside

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
