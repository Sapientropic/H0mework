import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterScaledNearby
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Images
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceParameterMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandSource WholeBandGeometry
open WholeBandContinuation WholeBandContinuationDifferential TrueFlowDifferential Set Filter
open scoped Topology
noncomputable section

def parameterInput (c : FullBandCell) (q : Point) : InitialScale := (cellSeed c q, 2 * q 2)

def parameterInputDerivative (c : FullBandCell) (q : Point) : Point →L[ℝ] InitialScale :=
  (bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) q).prod
    ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))

theorem parameterInput_hasFDerivAt (c : FullBandCell) (q : Point) :
    HasFDerivAt (parameterInput c) (parameterInputDerivative c q) q := by
  have time : HasFDerivAt (fun x : Point => 2 * x 2)
      ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)) q := by
    change HasFDerivAt (⇑((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))) _ q
    exact ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)).hasFDerivAt
  exact (bandSeed_hasFDerivAt (cellSegment c) (Geometry.Source.epsilon 0) q).prodMk time

theorem parameterInput_eq_source (c : FullBandCell) (p : Point) : parameterInput c p = sourceInput c p := rfl

def trueJacobian (c : FullBandCell) (p : Point) : Point →L[ℝ] Point :=
  (ContinuousMap.evalCLM ℝ endpointTime).comp ((scaledResponse c p).comp (parameterInputDerivative c p))

theorem scaled_endpoint_is_parameterMap (c : FullBandCell) (q : Point) (inside : q ∈ cellDomain c) :
    scaledRawPath (parameterInput c q).1 (parameterInput c q).2 endpointTime = sourceParameterMap c q := by
  have allowed : |(parameterInput c q).2| ≤ 1 := scaleAt_abs_le_one c q inside
  rw [scaledRawPath_eq_scaledRawFlow _ _ allowed]
  change rawFlow (cellSeed c q) ((2 * q 2) * (1/2)) = _
  rw [show (2 * q 2) * (1/2 : ℝ) = q 2 by ring]
  rfl

theorem actualMap_hasFDerivWithinAt (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    HasFDerivWithinAt (sourceParameterMap c) (trueJacobian c p) (cellDomain c) p := by
  have input := parameterInput_hasFDerivAt c p
  have pathDerivative := (scaledSolution_hasStrictFDerivAt c fields bounds p inside).hasFDerivAt.comp p input
  have generated := (ContinuousMap.evalCLM ℝ endpointTime).hasFDerivAt.comp p pathDerivative
  have agreement : (fun q => scaledSolution c fields bounds p inside (parameterInput c q) endpointTime)
      =ᶠ[𝓝[cellDomain c] p] sourceParameterMap c := by
    have near := input.continuousAt.tendsto.eventually (scaledSolution_eq_rawPath c fields bounds p inside)
    filter_upwards [near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hinside
    have allowed : |(parameterInput c q).2| ≤ 1 := scaleAt_abs_le_one c q hinside
    rw [hq allowed]
    exact scaled_endpoint_is_parameterMap c q hinside
  exact generated.hasFDerivWithinAt.congr_of_eventuallyEq agreement.symm
    (agreement.eq_of_nhdsWithin inside).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
