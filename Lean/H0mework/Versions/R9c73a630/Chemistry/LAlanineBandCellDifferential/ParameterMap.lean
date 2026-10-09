import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.ScaledNearby
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.GeometryCell0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceParameterMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandGeometry WholeBandActual
open TrueFlowDifferential WholeBandCell0Geometry Set Filter
open scoped Topology
noncomputable section

def cell0_parameterInput (q : Point) : InitialScale := (cellSeed 0 q, 2 * q 2)

def cell0_parameterInputDerivative (q : Point) : Point →L[ℝ] InitialScale :=
  (bandSeedDerivative 0 (Geometry.Source.epsilon 0) q).prod
    ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))

theorem cell0_parameterInput_hasFDerivAt (q : Point) :
    HasFDerivAt cell0_parameterInput (cell0_parameterInputDerivative q) q := by
  have time : HasFDerivAt (fun x : Point => 2 * x 2)
      ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)) q := by
    change HasFDerivAt (⇑((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))) _ q
    exact ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)).hasFDerivAt
  exact (bandSeed_hasFDerivAt 0 (Geometry.Source.epsilon 0) q).prodMk time

theorem cell0_parameterInput_eq_source (p : Cell0Point) : cell0_parameterInput p.val = cell0_sourceInput p := rfl

def cell0_trueJacobian (p : Cell0Point) : Point →L[ℝ] Point :=
  (ContinuousMap.evalCLM ℝ endpointTime).comp
    ((cell0_scaledResponse p).comp (cell0_parameterInputDerivative p.val))

theorem cell0_scaled_endpoint_is_parameterMap (q : Point) (inside : q ∈ cellDomain 0) :
    scaledRawPath (cell0_parameterInput q).1 (cell0_parameterInput q).2 endpointTime = cell0ParameterMap q := by
  have allowed : |(cell0_parameterInput q).2| ≤ 1 := cell0_scaleAt_abs_le_one ⟨q,inside⟩
  rw [scaledRawPath_eq_scaledRawFlow _ _ allowed]
  change rawFlow (cellSeed 0 q) ((2 * q 2) * (1/2)) = _
  rw [show (2 * q 2) * (1/2 : ℝ) = q 2 by ring]
  rfl

theorem cell0_actualMap_hasFDerivWithinAt (p : Cell0Point) :
    HasFDerivWithinAt cell0ParameterMap (cell0_trueJacobian p) (cellDomain 0) p.val := by
  have input := cell0_parameterInput_hasFDerivAt p.val
  have pathDerivative := (cell0_scaledSolution_hasStrictFDerivAt p).hasFDerivAt.comp p.val input
  have generated := (ContinuousMap.evalCLM ℝ endpointTime).hasFDerivAt.comp p.val pathDerivative
  have agreement : (fun q => cell0_scaledSolution p (cell0_parameterInput q) endpointTime)
      =ᶠ[𝓝[cellDomain 0] p.val] cell0ParameterMap := by
    have near := input.continuousAt.tendsto.eventually (cell0_scaledSolution_eq_rawPath p)
    filter_upwards [near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq inside
    have allowed : |(cell0_parameterInput q).2| ≤ 1 := cell0_scaleAt_abs_le_one ⟨q,inside⟩
    rw [hq allowed]
    exact cell0_scaled_endpoint_is_parameterMap q inside
  exact generated.hasFDerivWithinAt.congr_of_eventuallyEq agreement.symm
    (agreement.eq_of_nhdsWithin p.property).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
