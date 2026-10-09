import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterScaledImplicit
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledRecognition

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationDifferential TrueFlowDifferential Filter Metric
open scoped Topology
noncomputable section

theorem scaledSolution_at_source (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    scaledSolution c fields bounds p inside (sourceInput c p) = scaledActualPath c p :=
  ((scaledResidual_hasStrictFDerivAt c p).eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (scaledResidual_right_invertible c fields bounds p inside)).self_of_nhds.mp rfl

theorem scaledSolution_tendsto (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    Tendsto (scaledSolution c fields bounds p inside) (𝓝 (sourceInput c p)) (𝓝 (scaledActualPath c p)) :=
  (scaledResidual_hasStrictFDerivAt c p).tendsto_implicitFunctionOfProdDomain
    (scaledResidual_right_invertible c fields bounds p inside)

theorem scaledSolution_solves (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ∀ᶠ z in 𝓝 (sourceInput c p), scaledSolution c fields bounds p inside z =
      pathConst z.1 + z.2 • volterra (pathGradient (scaledSolution c fields bounds p inside z)) := by
  filter_upwards [(scaledResidual_hasStrictFDerivAt c p).eventually_apply_implicitFunctionOfProdDomain
    (scaledResidual_right_invertible c fields bounds p inside)] with z hz
  rw [scaledActual_residual_zero c fields p inside] at hz
  change scaledSolution c fields bounds p inside z - pathConst z.1 -
    z.2 • volterra (pathGradient (scaledSolution c fields bounds p inside z)) = 0 at hz
  linear_combination hz

theorem scaledSolution_in_cube (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ∀ᶠ z in 𝓝 (sourceInput c p), ∀ t : Time, scaledSolution c fields bounds p inside z t ∈ sourceCube := by
  have near := (scaledSolution_tendsto c fields bounds p inside).eventually
    (ball_mem_nhds (scaledActualPath c p) (show (0 : ℝ) < 1 / 200 by norm_num))
  filter_upwards [near] with z hz t
  exact path_near_scaled_in_cube c fields bounds p inside (scaledSolution c fields bounds p inside z) hz t

theorem scaledSolution_eq_rawPath (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ∀ᶠ z in 𝓝 (sourceInput c p), |z.2| ≤ 1 →
      scaledSolution c fields bounds p inside z = scaledRawPath z.1 z.2 := by
  filter_upwards [scaledSolution_solves c fields bounds p inside, scaledSolution_in_cube c fields bounds p inside]
    with z equation in_cube allowed
  exact solvedScaledPath_eq_rawPath z.1 z.2 (scaledSolution c fields bounds p inside z) allowed equation in_cube

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
