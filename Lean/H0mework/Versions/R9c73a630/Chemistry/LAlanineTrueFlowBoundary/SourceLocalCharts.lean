import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.ResponseNondegenerate
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundary

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousSeed TrueFlowDifferential TrueFlowGeometry TrueTubeWholeActual
open WholeCellPartition Set Filter Metric
open scoped Topology
noncomputable section

theorem parameterInput_strictDerivative (q : Point) :
    HasStrictFDerivAt parameterInput (parameterInputDerivative q) q := by
  have seed := (bandSeed_contDiff 4 (Geometry.Source.epsilon 0) 1).contDiffAt.hasStrictFDerivAt'
    (bandSeed_hasFDerivAt 4 (Geometry.Source.epsilon 0) q) (by norm_num)
  have time : HasStrictFDerivAt (fun x : Point => 2 * x 2)
      ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)) q := by
    change HasStrictFDerivAt (⇑((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))) _ q
    exact ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)).hasStrictFDerivAt
  exact seed.prodMk time

def localExtension (p : BandPoint) (q : Point) : Point :=
  scaledSolution p (parameterInput q) endpointTime

theorem localExtension_strictDerivative (p : BandPoint) :
    HasStrictFDerivAt (localExtension p) (trueJacobian p) p.val :=
  (ContinuousMap.evalCLM ℝ endpointTime).hasStrictFDerivAt.comp p.val
    ((scaledSolution_hasStrictFDerivAt p).comp p.val (parameterInput_strictDerivative p.val))

theorem localExtension_agrees (p : BandPoint) :
    localExtension p =ᶠ[𝓝[fullDomain] p.val] trueParameterMap := by
  have near := (parameterInput_hasFDerivAt p.val).continuousAt.tendsto.eventually
    (scaledSolution_eq_rawPath p)
  filter_upwards [near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq inside
  have allowed : |(parameterInput q).2| ≤ 1 := scaleAt_abs_le_one ⟨q, inside⟩
  change scaledSolution p (parameterInput q) endpointTime = _
  rw [hq allowed]
  exact scaled_endpoint_is_parameterMap q inside

theorem actual_local_extension (p : BandPoint) :
    ∃ e : OpenPartialHomeomorph Point Point,
      p.val ∈ e.source ∧ EqOn e trueParameterMap (fullDomain ∩ e.source) := by
  have derivative : HasStrictFDerivAt (localExtension p)
      (trueJacobianEquiv p : Point →L[ℝ] Point) p.val := localExtension_strictDerivative p
  let original := derivative.toOpenPartialHomeomorph (localExtension p)
  have near := eventually_nhdsWithin_iff.mp (localExtension_agrees p)
  obtain ⟨radius, positive, agrees⟩ := Metric.eventually_nhds_iff_ball.mp near
  let chart := original.restrOpen (ball p.val radius) isOpen_ball
  refine ⟨chart, ⟨derivative.mem_toOpenPartialHomeomorph_source, mem_ball_self positive⟩, ?_⟩
  intro q hq
  exact agrees q hq.2.2 hq.1

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
