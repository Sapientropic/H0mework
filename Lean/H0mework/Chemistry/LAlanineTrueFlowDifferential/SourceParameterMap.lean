import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceScaledNearby
import H0mework.Chemistry.LAlanineParametric.SeedDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed TrueTubeWholeActual WholeCellPartition
open Set Filter
open scoped Topology
noncomputable section

def endpointTime : Time := ⟨1 / 2, by constructor <;> norm_num⟩

def parameterInput (q : Point) : InitialScale :=
  (ContinuousParameterMap.initialMap 0 4 q, 2 * q 2)

def parameterInputDerivative (q : Point) : Point →L[ℝ] InitialScale :=
  (bandSeedDerivative 4 (Geometry.Source.epsilon 0) q).prod
    ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))

theorem parameterInput_hasFDerivAt (q : Point) :
    HasFDerivAt parameterInput (parameterInputDerivative q) q := by
  have time : HasFDerivAt (fun x : Point => 2 * x 2)
      ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)) q := by
    change HasFDerivAt (⇑((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))) _ q
    exact ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)).hasFDerivAt
  exact (bandSeed_hasFDerivAt 4 (Geometry.Source.epsilon 0) q).prodMk time

theorem parameterInput_eq_source (p : BandPoint) : parameterInput p.val = sourceInput p := rfl

def trueParameterMap (q : Point) : Point :=
  rawFlow (ContinuousParameterMap.initialMap 0 4 q) (q 2)

theorem trueParameterMap_is_actual (p : BandPoint) : trueParameterMap p.val = fullFlow p (p.val 2) := rfl

def trueJacobian (p : BandPoint) : Point →L[ℝ] Point :=
  (ContinuousMap.evalCLM ℝ endpointTime).comp ((scaledResponse p).comp (parameterInputDerivative p.val))

theorem scaled_endpoint_is_parameterMap (q : Point) (inside : q ∈ fullDomain) :
    scaledRawPath (parameterInput q).1 (parameterInput q).2 endpointTime = trueParameterMap q := by
  have allowed : |(parameterInput q).2| ≤ 1 := scaleAt_abs_le_one ⟨q, inside⟩
  rw [scaledRawPath_eq_scaledRawFlow _ _ allowed]
  change rawFlow (ContinuousParameterMap.initialMap 0 4 q) ((2 * q 2) * (1 / 2)) = _
  rw [show (2 * q 2) * (1 / 2 : ℝ) = q 2 by ring]
  rfl

theorem actualMap_hasFDerivWithinAt (p : BandPoint) :
    HasFDerivWithinAt trueParameterMap (trueJacobian p) fullDomain p.val := by
  have input := parameterInput_hasFDerivAt p.val
  have pathDerivative := (scaledSolution_hasStrictFDerivAt p).hasFDerivAt.comp p.val input
  have generated := (ContinuousMap.evalCLM ℝ endpointTime).hasFDerivAt.comp p.val pathDerivative
  have agreement : (fun q => scaledSolution p (parameterInput q) endpointTime) =ᶠ[𝓝[fullDomain] p.val]
      trueParameterMap := by
    have near := input.continuousAt.tendsto.eventually (scaledSolution_eq_rawPath p)
    filter_upwards [near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq inside
    have allowed : |(parameterInput q).2| ≤ 1 := scaleAt_abs_le_one ⟨q, inside⟩
    rw [hq allowed]
    exact scaled_endpoint_is_parameterMap q inside
  exact generated.hasFDerivWithinAt.congr_of_eventuallyEq agreement.symm
    (agreement.eq_of_nhdsWithin p.property).symm

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
