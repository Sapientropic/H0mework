import H0mework.Chemistry.LAlanineBandContinuation.ConservationRetime
import H0mework.Chemistry.LAlanineBandContinuation.ConservationTimeIntegral
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed WholeBandSource WholeBandGeometry
open TrueFlowDifferential TrueFlowGeometry WholeBandContinuation WholeBandContinuationDifferential
open WholeBandContinuationParameter Matrix Set MeasureTheory
open scoped Matrix
noncomputable section

theorem seedFlowDerivative_det (c : FullBandCell) (p : Point) :
    LinearMap.det (seedFlowDerivative c p).toLinearMap =
      bandWidth (cellSegment c) (Geometry.Source.epsilon 0) (p 1) *
        (seedNormal ⬝ᵥ sourceGradient (cellSeed c p)) := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_three, seedNormal_eq_cross]
  simp [LinearMap.toMatrix'_apply, WholeBandContinuationParameter.seedFlowDerivative, bandSeedDerivative, bandUDerivative,
    cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem seedFlowDerivative_det_pos (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    0 < LinearMap.det (seedFlowDerivative c p).toLinearMap := by
  rw [seedFlowDerivative_det]
  have transverse := actual_transverse c fields positive p inside 0 (by constructor <;> norm_num)
  rw [rawFlow_starts] at transverse
  exact mul_pos (bandWidth_positive _ _ _ source_epsilon_positive (cell_parameter_in_segment c p inside)) transverse

theorem evolvingJacobian_zero (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    evolvingJacobian c p 0 = LinearMap.toMatrix' (seedFlowDerivative c p).toLinearMap := by
  ext i j
  change extendPath (sourceResponse c p (seedFlowDerivative c p (Pi.single j 1)))
    (zeroTime : ℝ) i = seedFlowDerivative c p (Pi.single j 1) i
  rw [extendPath_coe, sourceResponse_starts c fields bounds p inside]

theorem evolvingJacobian_det_pos (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    0 < (evolvingJacobian c p s).det := by
  have initial : 0 < (evolvingJacobian c p 0).det := by
    rw [evolvingJacobian_zero c fields bounds p inside, LinearMap.det_toMatrix']
    exact seedFlowDerivative_det_pos c fields positive p inside
  by_contra failed
  have zero_mem : (0 : ℝ) ∈ Icc (-(1/2 : ℝ)) (1/2) := by constructor <;> norm_num
  obtain ⟨t,ht,vanished⟩ :=
    (isPreconnected_Icc.intermediate_value s.property zero_mem
      (evolvingJacobian_det_continuous c p).continuousOn) ⟨le_of_not_gt failed,initial.le⟩
  exact evolvingJacobian_det_ne_zero c fields bounds positive p inside ⟨t,ht⟩ vanished

theorem actualJacobian_det_pos (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    0 < LinearMap.det (trueJacobian c p).toLinearMap := by
  rw [← evolvingJacobian_det_is_actual c fields bounds p inside]
  exact evolvingJacobian_det_pos c fields bounds positive p inside (actualParameterTime c p inside)

end
end LAlanine40K2025.BasinRefinement.WholeBandConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
