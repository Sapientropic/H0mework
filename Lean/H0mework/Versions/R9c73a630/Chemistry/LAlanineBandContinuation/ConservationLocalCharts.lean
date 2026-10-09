import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ConservationOrientation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousSeed WholeBandSource WholeBandGeometry TrueFlowDifferential
open WholeBandContinuation WholeBandContinuationDifferential WholeBandContinuationParameter Set Filter Metric
open scoped Topology
noncomputable section

theorem parameterInput_strictDerivative (c : FullBandCell) (q : Point) :
    HasStrictFDerivAt (parameterInput c) (parameterInputDerivative c q) q := by
  have seed := (bandSeed_contDiff (cellSegment c) (Geometry.Source.epsilon 0) 1).contDiffAt.hasStrictFDerivAt'
    (bandSeed_hasFDerivAt (cellSegment c) (Geometry.Source.epsilon 0) q) (by norm_num)
  have time : HasStrictFDerivAt (fun x : Point => 2 * x 2)
      ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)) q := by
    change HasStrictFDerivAt (⇑((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ))) _ q
    exact ((2 : ℝ) • (ContinuousLinearMap.proj 2 : Point →L[ℝ] ℝ)).hasStrictFDerivAt
  exact seed.prodMk time

def localExtension (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (q : Point) : Point :=
  scaledSolution c fields bounds p inside (parameterInput c q) endpointTime

theorem localExtension_strictDerivative (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    HasStrictFDerivAt (localExtension c fields bounds p inside) (trueJacobian c p) p :=
  (ContinuousMap.evalCLM ℝ endpointTime).hasStrictFDerivAt.comp p
    ((scaledSolution_hasStrictFDerivAt c fields bounds p inside).comp p (parameterInput_strictDerivative c p))

theorem localExtension_agrees_on_time_slab (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    localExtension c fields bounds p inside =ᶠ[𝓝[{q : Point | |2 * q 2| ≤ 1}] p] sourceParameterMap c := by
  have near := (parameterInput_hasFDerivAt c p).continuousAt.tendsto.eventually (scaledSolution_eq_rawPath c fields bounds p inside)
  filter_upwards [near.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq allowed
  change scaledSolution c fields bounds p inside (parameterInput c q) endpointTime = _
  rw [hq allowed]
  change scaledRawPath (cellSeed c q) (2 * q 2) endpointTime = _
  rw [scaledRawPath_eq_scaledRawFlow _ _ allowed]
  change rawFlow (cellSeed c q) ((2 * q 2) * (1/2)) = _
  rw [show (2 * q 2) * (1/2 : ℝ) = q 2 by ring]
  rfl

theorem actual_local_extension_on_time_slab (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    ∃ e : OpenPartialHomeomorph Point Point,
      p ∈ e.source ∧ EqOn e (sourceParameterMap c) ({q : Point | |2 * q 2| ≤ 1} ∩ e.source) := by
  have derivative : HasStrictFDerivAt (localExtension c fields bounds p inside)
      (trueJacobianEquiv c fields bounds positive p inside : Point →L[ℝ] Point) p :=
    localExtension_strictDerivative c fields bounds p inside
  let original := derivative.toOpenPartialHomeomorph (localExtension c fields bounds p inside)
  have near := eventually_nhdsWithin_iff.mp (localExtension_agrees_on_time_slab c fields bounds p inside)
  obtain ⟨radius,positiveRadius,agrees⟩ := Metric.eventually_nhds_iff_ball.mp near
  let chart := original.restrOpen (ball p radius) isOpen_ball
  refine ⟨chart,⟨derivative.mem_toOpenPartialHomeomorph_source,mem_ball_self positiveRadius⟩,?_⟩
  intro q hq
  exact agrees q hq.2.2 hq.1

end
end LAlanine40K2025.BasinRefinement.WholeBandConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
