import H0mework.Chemistry.LAlanineBandCellDifferential.Nondegenerate
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousSeed WholeBandActual WholeBandGeometry WholeBandCell0Geometry
open WholeBandCell0Differential TrueFlowDifferential Set Filter Metric
open scoped Topology
noncomputable section

theorem cell0_parameterInput_strictDerivative (q : Point) :
    HasStrictFDerivAt cell0_parameterInput (cell0_parameterInputDerivative q) q := by
  have seed := (bandSeed_contDiff 0 (Geometry.Source.epsilon 0) 1).contDiffAt.hasStrictFDerivAt'
    (bandSeed_hasFDerivAt 0 (Geometry.Source.epsilon 0) q) (by norm_num)
  have time : HasStrictFDerivAt (fun x : Point => 2 * x 2)
      ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)) q := by
    change HasStrictFDerivAt (⇑((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))) _ q
    exact ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)).hasStrictFDerivAt
  exact seed.prodMk time

def cell0_localExtension (p : Cell0Point) (q : Point) : Point :=
  cell0_scaledSolution p (cell0_parameterInput q) endpointTime

theorem cell0_localExtension_strictDerivative (p : Cell0Point) :
    HasStrictFDerivAt (cell0_localExtension p) (cell0_trueJacobian p) p.val :=
  (ContinuousMap.evalCLM ℝ endpointTime).hasStrictFDerivAt.comp p.val
    ((cell0_scaledSolution_hasStrictFDerivAt p).comp p.val (cell0_parameterInput_strictDerivative p.val))

theorem cell0_localExtension_agrees (p : Cell0Point) :
    cell0_localExtension p =ᶠ[𝓝[cellDomain 0] p.val] cell0ParameterMap := by
  have near := (cell0_parameterInput_hasFDerivAt p.val).continuousAt.tendsto.eventually
    (cell0_scaledSolution_eq_rawPath p)
  filter_upwards [near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq inside
  have allowed : |(cell0_parameterInput q).2| ≤ 1 := cell0_scaleAt_abs_le_one ⟨q, inside⟩
  change cell0_scaledSolution p (cell0_parameterInput q) endpointTime = _
  rw [hq allowed]
  exact cell0_scaled_endpoint_is_parameterMap q inside

theorem cell0_actual_local_extension (p : Cell0Point) :
    ∃ e : OpenPartialHomeomorph Point Point,
      p.val ∈ e.source ∧ EqOn e cell0ParameterMap (cellDomain 0 ∩ e.source) := by
  have derivative : HasStrictFDerivAt (cell0_localExtension p)
      (cell0_trueJacobianEquiv p : Point →L[ℝ] Point) p.val := cell0_localExtension_strictDerivative p
  let original := derivative.toOpenPartialHomeomorph (cell0_localExtension p)
  have near := eventually_nhdsWithin_iff.mp (cell0_localExtension_agrees p)
  obtain ⟨radius, positive, agrees⟩ := Metric.eventually_nhds_iff_ball.mp near
  let chart := original.restrOpen (ball p.val radius) isOpen_ball
  refine ⟨chart, ⟨derivative.mem_toOpenPartialHomeomorph_source, mem_ball_self positive⟩, ?_⟩
  intro q hq
  exact agrees q hq.2.2 hq.1

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
